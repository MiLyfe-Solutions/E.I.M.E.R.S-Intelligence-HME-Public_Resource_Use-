import V185TrunkScan23Chunk1178

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6985305 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 1, 4, 2]
def baseStart_6985305 : Nat := 118140960795 + 6985305 * 2 ^ 59
def prefixEnd_6985305 : Nat := 4983230072969 + 3 ^ 40 * 6985305 * 2
def baseEnd_6985305 : Nat := 3586818983254897695762673

theorem tailTrace_6985305 : CollatzResearch.WordTrace tailWord_6985305 prefixEnd_6985305 3586818983254897695762673 := by
  unfold tailWord_6985305
  simp only [CollatzResearch.WordTrace]
  refine ⟨254775003958440454959917369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169850002638960303306611579 254775003958440454959917369)
  ·
    refine ⟨191081252968830341219938027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254775003958440454959917369 191081252968830341219938027)
    ·
      refine ⟨286621879453245511829907041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191081252968830341219938027 286621879453245511829907041)
      ·
        refine ⟨214966409589934133872430281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286621879453245511829907041 214966409589934133872430281)
        ·
          refine ⟨161224807192450600404322711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214966409589934133872430281 161224807192450600404322711)
          ·
            refine ⟨241837210788675900606484067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161224807192450600404322711 241837210788675900606484067)
            ·
              refine ⟨362755816183013850909726101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241837210788675900606484067 362755816183013850909726101)
              ·
                refine ⟨17004178883578774261393411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 362755816183013850909726101 17004178883578774261393411)
                ·
                  refine ⟨25506268325368161392090117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17004178883578774261393411 25506268325368161392090117)
                  ·
                    refine ⟨4782425311006530261016897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25506268325368161392090117 4782425311006530261016897)
                    ·
                      refine ⟨3586818983254897695762673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782425311006530261016897 3586818983254897695762673)
                      ·
                        rfl

theorem cell23_6985305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_6985305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985305 prefixEnd_6985305 := by exact prefixLift 6985305
  have htrace : WordTrace (prefixWord ++ tailWord_6985305) baseStart_6985305 baseEnd_6985305 := by
    simpa [prefixWord, tailWord_6985305, baseEnd_6985305] using wordTrace_append hprefix tailTrace_6985305
  have hstable : (prefixWord ++ tailWord_6985305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985305).length < 2 ^ (prefixWord ++ tailWord_6985305).sum := by decide
  have hdescent : baseEnd_6985305 < baseStart_6985305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985365 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_6985365 : Nat := 118140960795 + 6985365 * 2 ^ 59
def prefixEnd_6985365 : Nat := 4983230072969 + 3 ^ 40 * 6985365 * 2
def baseEnd_6985365 : Nat := 3586849792094167461012397

theorem tailTrace_6985365 : CollatzResearch.WordTrace tailWord_6985365 prefixEnd_6985365 3586849792094167461012397 := by
  unfold tailWord_6985365
  simp only [CollatzResearch.WordTrace]
  refine ⟨254777192338223085207101549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169851461558815390138067699 254777192338223085207101549)
  ·
    refine ⟨95541447126833656952663081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254777192338223085207101549 95541447126833656952663081)
    ·
      refine ⟨71656085345125242714497311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95541447126833656952663081 71656085345125242714497311)
      ·
        refine ⟨107484128017687864071745967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71656085345125242714497311 107484128017687864071745967)
        ·
          refine ⟨161226192026531796107618951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107484128017687864071745967 161226192026531796107618951)
          ·
            refine ⟨241839288039797694161428427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161226192026531796107618951 241839288039797694161428427)
            ·
              refine ⟨362758932059696541242142641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241839288039797694161428427 362758932059696541242142641)
              ·
                refine ⟨272069199044772405931606981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362758932059696541242142641 272069199044772405931606981)
                ·
                  refine ⟨51012974820894826112176309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272069199044772405931606981 51012974820894826112176309)
                  ·
                    refine ⟨4782466389458889948016529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51012974820894826112176309 4782466389458889948016529)
                    ·
                      refine ⟨3586849792094167461012397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782466389458889948016529 3586849792094167461012397)
                      ·
                        rfl

theorem cell23_6985365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_6985365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985365 prefixEnd_6985365 := by exact prefixLift 6985365
  have htrace : WordTrace (prefixWord ++ tailWord_6985365) baseStart_6985365 baseEnd_6985365 := by
    simpa [prefixWord, tailWord_6985365, baseEnd_6985365] using wordTrace_append hprefix tailTrace_6985365
  have hstable : (prefixWord ++ tailWord_6985365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985365).length < 2 ^ (prefixWord ++ tailWord_6985365).sum := by decide
  have hdescent : baseEnd_6985365 < baseStart_6985365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985412 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_6985412 : Nat := 118140960795 + 6985412 * 2 ^ 59
def prefixEnd_6985412 : Nat := 4983230072969 + 3 ^ 40 * 6985412 * 2
def baseEnd_6985412 : Nat := 3586873925684928777124681

theorem tailTrace_6985412 : CollatzResearch.WordTrace tailWord_6985412 prefixEnd_6985412 3586873925684928777124681 := by
  unfold tailWord_6985412
  simp only [CollatzResearch.WordTrace]
  refine ⟨127389453284526406117031245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169852604379368541489374993 127389453284526406117031245)
  ·
    refine ⟨47771044981697402293886717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127389453284526406117031245 47771044981697402293886717)
    ·
      refine ⟨17914141868136525860207519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47771044981697402293886717 17914141868136525860207519)
      ·
        refine ⟨26871212802204788790311279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17914141868136525860207519 26871212802204788790311279)
        ·
          refine ⟨40306819203307183185466919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26871212802204788790311279 40306819203307183185466919)
          ·
            refine ⟨60460228804960774778200379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40306819203307183185466919 60460228804960774778200379)
            ·
              refine ⟨90690343207441162167300569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60460228804960774778200379 90690343207441162167300569)
              ·
                refine ⟨68017757405580871625475427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90690343207441162167300569 68017757405580871625475427)
                ·
                  refine ⟨102026636108371307438213141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68017757405580871625475427 102026636108371307438213141)
                  ·
                    refine ⟨4782498567579905036166241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102026636108371307438213141 4782498567579905036166241)
                    ·
                      refine ⟨3586873925684928777124681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782498567579905036166241 3586873925684928777124681)
                      ·
                        rfl

theorem cell23_6985412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_6985412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985412 prefixEnd_6985412 := by exact prefixLift 6985412
  have htrace : WordTrace (prefixWord ++ tailWord_6985412) baseStart_6985412 baseEnd_6985412 := by
    simpa [prefixWord, tailWord_6985412, baseEnd_6985412] using wordTrace_append hprefix tailTrace_6985412
  have hstable : (prefixWord ++ tailWord_6985412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985412).length < 2 ^ (prefixWord ++ tailWord_6985412).sum := by decide
  have hdescent : baseEnd_6985412 < baseStart_6985412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985415 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_6985415 : Nat := 118140960795 + 6985415 * 2 ^ 59
def prefixEnd_6985415 : Nat := 4983230072969 + 3 ^ 40 * 6985415 * 2
def baseEnd_6985415 : Nat := 3586875466126892265387167

theorem tailTrace_6985415 : CollatzResearch.WordTrace tailWord_6985415 prefixEnd_6985415 3586875466126892265387167 := by
  unfold tailWord_6985415
  simp only [CollatzResearch.WordTrace]
  refine ⟨254779015988041943746421699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169852677325361295830947799 254779015988041943746421699)
  ·
    refine ⟨382168523982062915619632549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254779015988041943746421699 382168523982062915619632549)
    ·
      refine ⟨71656598246636796678681103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382168523982062915619632549 71656598246636796678681103)
      ·
        refine ⟨107484897369955195018021655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71656598246636796678681103 107484897369955195018021655)
        ·
          refine ⟨161227346054932792527032483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107484897369955195018021655 161227346054932792527032483)
          ·
            refine ⟨241841019082399188790548725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161227346054932792527032483 241841019082399188790548725)
            ·
              refine ⟨22672595538974923949113943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241841019082399188790548725 22672595538974923949113943)
              ·
                refine ⟨34008893308462385923670915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22672595538974923949113943 34008893308462385923670915)
                ·
                  refine ⟨51013339962693578885506373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34008893308462385923670915 51013339962693578885506373)
                  ·
                    refine ⟨9565001243005046041032445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51013339962693578885506373 9565001243005046041032445)
                    ·
                      refine ⟨3586875466126892265387167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9565001243005046041032445 3586875466126892265387167)
                      ·
                        rfl

theorem cell23_6985415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_6985415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985415 prefixEnd_6985415 := by exact prefixLift 6985415
  have htrace : WordTrace (prefixWord ++ tailWord_6985415) baseStart_6985415 baseEnd_6985415 := by
    simpa [prefixWord, tailWord_6985415, baseEnd_6985415] using wordTrace_append hprefix tailTrace_6985415
  have hstable : (prefixWord ++ tailWord_6985415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985415).length < 2 ^ (prefixWord ++ tailWord_6985415).sum := by decide
  have hdescent : baseEnd_6985415 < baseStart_6985415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985482 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_6985482 : Nat := 118140960795 + 6985482 * 2 ^ 59
def prefixEnd_6985482 : Nat := 4983230072969 + 3 ^ 40 * 6985482 * 2
def baseEnd_6985482 : Nat := 1195636623110247834416453

theorem tailTrace_6985482 : CollatzResearch.WordTrace tailWord_6985482 prefixEnd_6985482 1195636623110247834416453 := by
  unfold tailWord_6985482
  simp only [CollatzResearch.WordTrace]
  refine ⟨63695364919699803547277675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169854306452532809459407133 63695364919699803547277675)
  ·
    refine ⟨95543047379549705320916513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63695364919699803547277675 95543047379549705320916513)
    ·
      refine ⟨71657285534662278990687385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95543047379549705320916513 71657285534662278990687385)
      ·
        refine ⟨53742964150996709243015539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71657285534662278990687385 53742964150996709243015539)
        ·
          refine ⟨80614446226495063864523309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53742964150996709243015539 80614446226495063864523309)
          ·
            refine ⟨30230417334935648949196241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80614446226495063864523309 30230417334935648949196241)
            ·
              refine ⟨22672813001201736711897181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30230417334935648949196241 22672813001201736711897181)
              ·
                refine ⟨8502304875450651266961443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22672813001201736711897181 8502304875450651266961443)
                ·
                  refine ⟨12753457313175976900442165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502304875450651266961443 12753457313175976900442165)
                  ·
                    refine ⟨1195636623110247834416453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12753457313175976900442165 1195636623110247834416453)
                    ·
                      rfl

theorem cell23_6985482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_6985482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985482 prefixEnd_6985482 := by exact prefixLift 6985482
  have htrace : WordTrace (prefixWord ++ tailWord_6985482) baseStart_6985482 baseEnd_6985482 := by
    simpa [prefixWord, tailWord_6985482, baseEnd_6985482] using wordTrace_append hprefix tailTrace_6985482
  have hstable : (prefixWord ++ tailWord_6985482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985482).length < 2 ^ (prefixWord ++ tailWord_6985482).sum := by decide
  have hdescent : baseEnd_6985482 < baseStart_6985482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985529 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 1, 6]
def baseStart_6985529 : Nat := 118140960795 + 6985529 * 2 ^ 59
def prefixEnd_6985529 : Nat := 4983230072969 + 3 ^ 40 * 6985529 * 2
def baseEnd_6985529 : Nat := 1195644667640501606453881

theorem tailTrace_6985529 : CollatzResearch.WordTrace tailWord_6985529 prefixEnd_6985529 1195644667640501606453881 := by
  unfold tailWord_6985529
  simp only [CollatzResearch.WordTrace]
  refine ⟨254783173909628941216071641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169855449273085960810714427 254783173909628941216071641)
  ·
    refine ⟨191087380432221705912053731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254783173909628941216071641 191087380432221705912053731)
    ·
      refine ⟨286631070648332558868080597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191087380432221705912053731 286631070648332558868080597)
      ·
        refine ⟨6717915718320294348470639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 286631070648332558868080597 6717915718320294348470639)
        ·
          refine ⟨10076873577480441522705959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717915718320294348470639 10076873577480441522705959)
          ·
            refine ⟨15115310366220662284058939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10076873577480441522705959 15115310366220662284058939)
            ·
              refine ⟨22672965549330993426088409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15115310366220662284058939 22672965549330993426088409)
              ·
                refine ⟨17004724161998245069566307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22672965549330993426088409 17004724161998245069566307)
                ·
                  refine ⟨25507086242997367604349461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17004724161998245069566307 25507086242997367604349461)
                  ·
                    refine ⟨1195644667640501606453881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25507086242997367604349461 1195644667640501606453881)
                    ·
                      rfl

theorem cell23_6985529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 6].length) (baseStart_6985529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985529 prefixEnd_6985529 := by exact prefixLift 6985529
  have htrace : WordTrace (prefixWord ++ tailWord_6985529) baseStart_6985529 baseEnd_6985529 := by
    simpa [prefixWord, tailWord_6985529, baseEnd_6985529] using wordTrace_append hprefix tailTrace_6985529
  have hstable : (prefixWord ++ tailWord_6985529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985529).length < 2 ^ (prefixWord ++ tailWord_6985529).sum := by decide
  have hdescent : baseEnd_6985529 < baseStart_6985529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985553 : List Nat := [1, 2, 2, 1, 5, 2, 1, 4, 1, 2, 2]
def baseStart_6985553 : Nat := 118140960795 + 6985553 * 2 ^ 59
def prefixEnd_6985553 : Nat := 4983230072969 + 3 ^ 40 * 6985553 * 2
def baseEnd_6985553 : Nat := 3586946326457212725461533

theorem tailTrace_6985553 : CollatzResearch.WordTrace tailWord_6985553 prefixEnd_6985553 3586946326457212725461533 := by
  unfold tailWord_6985553
  simp only [CollatzResearch.WordTrace]
  refine ⟨254784049261541993314945313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169856032841027995543296875 254784049261541993314945313)
  ·
    refine ⟨191088036946156494986208985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254784049261541993314945313 191088036946156494986208985)
    ·
      refine ⟨143316027709617371239656739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191088036946156494986208985 143316027709617371239656739)
      ·
        refine ⟨214974041564426056859485109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143316027709617371239656739 214974041564426056859485109)
        ·
          refine ⟨20153816396664942830576729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214974041564426056859485109 20153816396664942830576729)
          ·
            refine ⟨15115362297498707122932547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20153816396664942830576729 15115362297498707122932547)
            ·
              refine ⟨22673043446248060684398821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15115362297498707122932547 22673043446248060684398821)
              ·
                refine ⟨4251195646171511378324779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22673043446248060684398821 4251195646171511378324779)
                ·
                  refine ⟨6376793469257267067487169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251195646171511378324779 6376793469257267067487169)
                  ·
                    refine ⟨4782595101942950300615377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6376793469257267067487169 4782595101942950300615377)
                    ·
                      refine ⟨3586946326457212725461533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782595101942950300615377 3586946326457212725461533)
                      ·
                        rfl

theorem cell23_6985553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 1, 2, 2].length) (baseStart_6985553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985553 prefixEnd_6985553 := by exact prefixLift 6985553
  have htrace : WordTrace (prefixWord ++ tailWord_6985553) baseStart_6985553 baseEnd_6985553 := by
    simpa [prefixWord, tailWord_6985553, baseEnd_6985553] using wordTrace_append hprefix tailTrace_6985553
  have hstable : (prefixWord ++ tailWord_6985553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985553).length < 2 ^ (prefixWord ++ tailWord_6985553).sum := by decide
  have hdescent : baseEnd_6985553 < baseStart_6985553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985559 : List Nat := [1, 1, 3, 2, 6, 1, 1, 8]
def baseStart_6985559 : Nat := 118140960795 + 6985559 * 2 ^ 59
def prefixEnd_6985559 : Nat := 4983230072969 + 3 ^ 40 * 6985559 * 2
def baseEnd_6985559 : Nat := 132849978049671840814315

theorem tailTrace_6985559 : CollatzResearch.WordTrace tailWord_6985559 prefixEnd_6985559 132849978049671840814315 := by
  unfold tailWord_6985559
  simp only [CollatzResearch.WordTrace]
  refine ⟨254784268099520256339663731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169856178733013504226442487 254784268099520256339663731)
  ·
    refine ⟨382176402149280384509495597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254784268099520256339663731 382176402149280384509495597)
    ·
      refine ⟨143316150805980144191060849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382176402149280384509495597 143316150805980144191060849)
      ·
        refine ⟨107487113104485108143295637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143316150805980144191060849 107487113104485108143295637)
        ·
          refine ⟨5038458426772739444216983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107487113104485108143295637 5038458426772739444216983)
          ·
            refine ⟨7557687640159109166325475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5038458426772739444216983 7557687640159109166325475)
            ·
              refine ⟨11336531460238663749488213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7557687640159109166325475 11336531460238663749488213)
              ·
                refine ⟨132849978049671840814315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11336531460238663749488213 132849978049671840814315)
                ·
                  rfl

theorem cell23_6985559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 8].length) (baseStart_6985559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985559 prefixEnd_6985559 := by exact prefixLift 6985559
  have htrace : WordTrace (prefixWord ++ tailWord_6985559) baseStart_6985559 baseEnd_6985559 := by
    simpa [prefixWord, tailWord_6985559, baseEnd_6985559] using wordTrace_append hprefix tailTrace_6985559
  have hstable : (prefixWord ++ tailWord_6985559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985559).length < 2 ^ (prefixWord ++ tailWord_6985559).sum := by decide
  have hdescent : baseEnd_6985559 < baseStart_6985559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985569 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_6985569 : Nat := 118140960795 + 6985569 * 2 ^ 59
def prefixEnd_6985569 : Nat := 4983230072969 + 3 ^ 40 * 6985569 * 2
def baseEnd_6985569 : Nat := 3586954542147684662861459

theorem tailTrace_6985569 : CollatzResearch.WordTrace tailWord_6985569 prefixEnd_6985569 3586954542147684662861459 := by
  unfold tailWord_6985569
  simp only [CollatzResearch.WordTrace]
  refine ⟨254784632829484028047527761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169856421886322685365018507 254784632829484028047527761)
  ·
    refine ⟨191088474622113021035645821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254784632829484028047527761 191088474622113021035645821)
    ·
      refine ⟨71658177983292382888367183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191088474622113021035645821 71658177983292382888367183)
      ·
        refine ⟨107487266974938574332550775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71658177983292382888367183 107487266974938574332550775)
        ·
          refine ⟨161230900462407861498826163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107487266974938574332550775 161230900462407861498826163)
          ·
            refine ⟨241846350693611792248239245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161230900462407861498826163 241846350693611792248239245)
            ·
              refine ⟨90692381510104422093089717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241846350693611792248239245 90692381510104422093089717)
              ·
                refine ⟨8502410766572289571227161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90692381510104422093089717 8502410766572289571227161)
                ·
                  refine ⟨6376808074929217178420371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8502410766572289571227161 6376808074929217178420371)
                  ·
                    refine ⟨9565212112393825767630557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6376808074929217178420371 9565212112393825767630557)
                    ·
                      refine ⟨3586954542147684662861459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9565212112393825767630557 3586954542147684662861459)
                      ·
                        rfl

theorem cell23_6985569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_6985569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985569 prefixEnd_6985569 := by exact prefixLift 6985569
  have htrace : WordTrace (prefixWord ++ tailWord_6985569) baseStart_6985569 baseEnd_6985569 := by
    simpa [prefixWord, tailWord_6985569, baseEnd_6985569] using wordTrace_append hprefix tailTrace_6985569
  have hstable : (prefixWord ++ tailWord_6985569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985569).length < 2 ^ (prefixWord ++ tailWord_6985569).sum := by decide
  have hdescent : baseEnd_6985569 < baseStart_6985569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985579 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 1, 3, 2]
def baseStart_6985579 : Nat := 118140960795 + 6985579 * 2 ^ 59
def prefixEnd_6985579 : Nat := 4983230072969 + 3 ^ 40 * 6985579 * 2
def baseEnd_6985579 : Nat := 3586959676954229623736413

theorem tailTrace_6985579 : CollatzResearch.WordTrace tailWord_6985579 prefixEnd_6985579 3586959676954229623736413 := by
  unfold tailWord_6985579
  simp only [CollatzResearch.WordTrace]
  refine ⟨254784997559447799755391791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169856665039631866503594527 254784997559447799755391791)
  ·
    refine ⟨382177496339171699633087687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254784997559447799755391791 382177496339171699633087687)
    ·
      refine ⟨573266244508757549449631531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382177496339171699633087687 573266244508757549449631531)
      ·
        refine ⟨859899366763136324174447297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573266244508757549449631531 859899366763136324174447297)
        ·
          refine ⟨644924525072352243130835473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859899366763136324174447297 644924525072352243130835473)
          ·
            refine ⟨483693393804264182348126605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644924525072352243130835473 483693393804264182348126605)
            ·
              refine ⟨181385022676599068380547477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483693393804264182348126605 181385022676599068380547477)
              ·
                refine ⟨8502422937965581330338163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181385022676599068380547477 8502422937965581330338163)
                ·
                  refine ⟨12753634406948371995507245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502422937965581330338163 12753634406948371995507245)
                  ·
                    refine ⟨4782612902605639498315217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12753634406948371995507245 4782612902605639498315217)
                    ·
                      refine ⟨3586959676954229623736413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782612902605639498315217 3586959676954229623736413)
                      ·
                        rfl

theorem cell23_6985579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 3, 2].length) (baseStart_6985579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985579 prefixEnd_6985579 := by exact prefixLift 6985579
  have htrace : WordTrace (prefixWord ++ tailWord_6985579) baseStart_6985579 baseEnd_6985579 := by
    simpa [prefixWord, tailWord_6985579, baseEnd_6985579] using wordTrace_append hprefix tailTrace_6985579
  have hstable : (prefixWord ++ tailWord_6985579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985579).length < 2 ^ (prefixWord ++ tailWord_6985579).sum := by decide
  have hdescent : baseEnd_6985579 < baseStart_6985579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985585 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 1, 8]
def baseStart_6985585 : Nat := 118140960795 + 6985585 * 2 ^ 59
def prefixEnd_6985585 : Nat := 4983230072969 + 3 ^ 40 * 6985585 * 2
def baseEnd_6985585 : Nat := 1195654252612718866753795

theorem tailTrace_6985585 : CollatzResearch.WordTrace tailWord_6985585 prefixEnd_6985585 1195654252612718866753795 := by
  unfold tailWord_6985585
  simp only [CollatzResearch.WordTrace]
  refine ⟨254785216397426062780110209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169856810931617375186740139 254785216397426062780110209)
  ·
    refine ⟨191088912298069547085082657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254785216397426062780110209 191088912298069547085082657)
    ·
      refine ⟨143316684223552160313811993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191088912298069547085082657 143316684223552160313811993)
      ·
        refine ⟨107487513167664120235358995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143316684223552160313811993 107487513167664120235358995)
        ·
          refine ⟨161231269751496180353038493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107487513167664120235358995 161231269751496180353038493)
          ·
            refine ⟨60461726156811067632389435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161231269751496180353038493 60461726156811067632389435)
            ·
              refine ⟨90692589235216601448584153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60461726156811067632389435 90692589235216601448584153)
              ·
                refine ⟨68019441926412451086438115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90692589235216601448584153 68019441926412451086438115)
                ·
                  refine ⟨102029162889618676629657173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68019441926412451086438115 102029162889618676629657173)
                  ·
                    refine ⟨1195654252612718866753795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102029162889618676629657173 1195654252612718866753795)
                    ·
                      rfl

theorem cell23_6985585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_6985585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985585 prefixEnd_6985585 := by exact prefixLift 6985585
  have htrace : WordTrace (prefixWord ++ tailWord_6985585) baseStart_6985585 baseEnd_6985585 := by
    simpa [prefixWord, tailWord_6985585, baseEnd_6985585] using wordTrace_append hprefix tailTrace_6985585
  have hstable : (prefixWord ++ tailWord_6985585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985585).length < 2 ^ (prefixWord ++ tailWord_6985585).sum := by decide
  have hdescent : baseEnd_6985585 < baseStart_6985585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985590 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_6985590 : Nat := 118140960795 + 6985590 * 2 ^ 59
def prefixEnd_6985590 : Nat := 4983230072969 + 3 ^ 40 * 6985590 * 2
def baseEnd_6985590 : Nat := 3586965325241429080698863

theorem tailTrace_6985590 : CollatzResearch.WordTrace tailWord_6985590 prefixEnd_6985590 3586965325241429080698863 := by
  unfold tailWord_6985590
  simp only [CollatzResearch.WordTrace]
  refine ⟨15924087422650496789627639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169856932508271965756028149 15924087422650496789627639)
  ·
    refine ⟨23886131133975745184441459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15924087422650496789627639 23886131133975745184441459)
    ·
      refine ⟨35829196700963617776662189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23886131133975745184441459 35829196700963617776662189)
      ·
        refine ⟨13435948762861356666248321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35829196700963617776662189 13435948762861356666248321)
        ·
          refine ⟨10076961572146017499686241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13435948762861356666248321 10076961572146017499686241)
          ·
            refine ⟨7557721179109513124764681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10076961572146017499686241 7557721179109513124764681)
            ·
              refine ⟨5668290884332134843573511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7557721179109513124764681 5668290884332134843573511)
              ·
                refine ⟨8502436326498202265360267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5668290884332134843573511 8502436326498202265360267)
                ·
                  refine ⟨12753654489747303398040401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502436326498202265360267 12753654489747303398040401)
                  ·
                    refine ⟨9565240867310477548530301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12753654489747303398040401 9565240867310477548530301)
                    ·
                      refine ⟨3586965325241429080698863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9565240867310477548530301 3586965325241429080698863)
                      ·
                        rfl

theorem cell23_6985590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_6985590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985590 prefixEnd_6985590 := by exact prefixLift 6985590
  have htrace : WordTrace (prefixWord ++ tailWord_6985590) baseStart_6985590 baseEnd_6985590 := by
    simpa [prefixWord, tailWord_6985590, baseEnd_6985590] using wordTrace_append hprefix tailTrace_6985590
  have hstable : (prefixWord ++ tailWord_6985590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985590).length < 2 ^ (prefixWord ++ tailWord_6985590).sum := by decide
  have hdescent : baseEnd_6985590 < baseStart_6985590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985592 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 2, 8, 2]
def baseStart_6985592 : Nat := 118140960795 + 6985592 * 2 ^ 59
def prefixEnd_6985592 : Nat := 4983230072969 + 3 ^ 40 * 6985592 * 2
def baseEnd_6985592 : Nat := 3586966352202738072873853

theorem tailTrace_6985592 : CollatzResearch.WordTrace tailWord_6985592 prefixEnd_6985592 3586966352202738072873853 := by
  unfold tailWord_6985592
  simp only [CollatzResearch.WordTrace]
  refine ⟨127392735854200351487807515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169856981138933801983743353 127392735854200351487807515)
  ·
    refine ⟨191089103781300527231711273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127392735854200351487807515 191089103781300527231711273)
    ·
      refine ⟨143316827835975395423783455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191089103781300527231711273 143316827835975395423783455)
      ·
        refine ⟨214975241753963093135675183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143316827835975395423783455 214975241753963093135675183)
        ·
          refine ⟨322462862630944639703512775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214975241753963093135675183 322462862630944639703512775)
          ·
            refine ⟨483694293946416959555269163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322462862630944639703512775 483694293946416959555269163)
            ·
              refine ⟨725541440919625439332903745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483694293946416959555269163 725541440919625439332903745)
              ·
                refine ⟨544156080689719079499677809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725541440919625439332903745 544156080689719079499677809)
                ·
                  refine ⟨408117060517289309624758357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544156080689719079499677809 408117060517289309624758357)
                  ·
                    refine ⟨4782621802936984097165137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 408117060517289309624758357 4782621802936984097165137)
                    ·
                      refine ⟨3586966352202738072873853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782621802936984097165137 3586966352202738072873853)
                      ·
                        rfl

theorem cell23_6985592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_6985592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985592 prefixEnd_6985592 := by exact prefixLift 6985592
  have htrace : WordTrace (prefixWord ++ tailWord_6985592) baseStart_6985592 baseEnd_6985592 := by
    simpa [prefixWord, tailWord_6985592, baseEnd_6985592] using wordTrace_append hprefix tailTrace_6985592
  have hstable : (prefixWord ++ tailWord_6985592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985592).length < 2 ^ (prefixWord ++ tailWord_6985592).sum := by decide
  have hdescent : baseEnd_6985592 < baseStart_6985592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985595 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 5]
def baseStart_6985595 : Nat := 118140960795 + 6985595 * 2 ^ 59
def prefixEnd_6985595 : Nat := 4983230072969 + 3 ^ 40 * 6985595 * 2
def baseEnd_6985595 : Nat := 3586967892644701561136339

theorem tailTrace_6985595 : CollatzResearch.WordTrace tailWord_6985595 prefixEnd_6985595 3586967892644701561136339 := by
  unfold tailWord_6985595
  simp only [CollatzResearch.WordTrace]
  refine ⟨254785581127389834487974239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169857054084926556325316159 254785581127389834487974239)
  ·
    refine ⟨382178371691084751731961359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254785581127389834487974239 382178371691084751731961359)
    ·
      refine ⟨573267557536627127597942039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382178371691084751731961359 573267557536627127597942039)
      ·
        refine ⟨859901336304940691396913059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573267557536627127597942039 859901336304940691396913059)
        ·
          refine ⟨1289852004457411037095369589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859901336304940691396913059 1289852004457411037095369589)
          ·
            refine ⟨120923625417882284727690899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1289852004457411037095369589 120923625417882284727690899)
            ·
              refine ⟨181385438126823427091536349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120923625417882284727690899 181385438126823427091536349)
              ·
                refine ⟨68019539297558785159326131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181385438126823427091536349 68019539297558785159326131)
                ·
                  refine ⟨102029308946338177738989197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68019539297558785159326131 102029308946338177738989197)
                  ·
                    refine ⟨38260990854876816652120949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102029308946338177738989197 38260990854876816652120949)
                    ·
                      refine ⟨3586967892644701561136339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38260990854876816652120949 3586967892644701561136339)
                      ·
                        rfl

theorem cell23_6985595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_6985595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985595 prefixEnd_6985595 := by exact prefixLift 6985595
  have htrace : WordTrace (prefixWord ++ tailWord_6985595) baseStart_6985595 baseEnd_6985595 := by
    simpa [prefixWord, tailWord_6985595, baseEnd_6985595] using wordTrace_append hprefix tailTrace_6985595
  have hstable : (prefixWord ++ tailWord_6985595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985595).length < 2 ^ (prefixWord ++ tailWord_6985595).sum := by decide
  have hdescent : baseEnd_6985595 < baseStart_6985595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985626 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2]
def baseStart_6985626 : Nat := 118140960795 + 6985626 * 2 ^ 59
def prefixEnd_6985626 : Nat := 4983230072969 + 3 ^ 40 * 6985626 * 2
def baseEnd_6985626 : Nat := 3586983810544990939848697

theorem tailTrace_6985626 : CollatzResearch.WordTrace tailWord_6985626 prefixEnd_6985626 3586983810544990939848697 := by
  unfold tailWord_6985626
  simp only [CollatzResearch.WordTrace]
  refine ⟨63696677947569381695588183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169857807860185017854901821 63696677947569381695588183)
  ·
    refine ⟨95545016921354072543382275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63696677947569381695588183 95545016921354072543382275)
    ·
      refine ⟨143317525382031108815073413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95545016921354072543382275 143317525382031108815073413)
      ·
        refine ⟨26872036009130832902826265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143317525382031108815073413 26872036009130832902826265)
        ·
          refine ⟨20154027006848124677119699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26872036009130832902826265 20154027006848124677119699)
          ·
            refine ⟨30231040510272187015679549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20154027006848124677119699 30231040510272187015679549)
            ·
              refine ⟨11336640191352070130879831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30231040510272187015679549 11336640191352070130879831)
              ·
                refine ⟨17004960287028105196319747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11336640191352070130879831 17004960287028105196319747)
                ·
                  refine ⟨25507440430542157794479621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17004960287028105196319747 25507440430542157794479621)
                  ·
                    refine ⟨4782645080726654586464929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25507440430542157794479621 4782645080726654586464929)
                    ·
                      refine ⟨3586983810544990939848697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782645080726654586464929 3586983810544990939848697)
                      ·
                        rfl

theorem cell23_6985626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_6985626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985626 prefixEnd_6985626 := by exact prefixLift 6985626
  have htrace : WordTrace (prefixWord ++ tailWord_6985626) baseStart_6985626 baseEnd_6985626 := by
    simpa [prefixWord, tailWord_6985626, baseEnd_6985626] using wordTrace_append hprefix tailTrace_6985626
  have hstable : (prefixWord ++ tailWord_6985626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985626).length < 2 ^ (prefixWord ++ tailWord_6985626).sum := by decide
  have hdescent : baseEnd_6985626 < baseStart_6985626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985672 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_6985672 : Nat := 118140960795 + 6985672 * 2 ^ 59
def prefixEnd_6985672 : Nat := 4983230072969 + 3 ^ 40 * 6985672 * 2
def baseEnd_6985672 : Nat := 3587007430655097759873485

theorem tailTrace_6985672 : CollatzResearch.WordTrace tailWord_6985672 prefixEnd_6985672 3587007430655097759873485 := by
  unfold tailWord_6985672
  simp only [CollatzResearch.WordTrace]
  refine ⟨127394194774055438319263635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169858926365407251092351513 127394194774055438319263635)
  ·
    refine ⟨191091292161083157478895453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127394194774055438319263635 191091292161083157478895453)
    ·
      refine ⟨71659234560406184054585795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191091292161083157478895453 71659234560406184054585795)
      ·
        refine ⟨107488851840609276081878693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71659234560406184054585795 107488851840609276081878693)
        ·
          refine ⟨20154159720114239265352255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107488851840609276081878693 20154159720114239265352255)
          ·
            refine ⟨30231239580171358898028383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20154159720114239265352255 30231239580171358898028383)
            ·
              refine ⟨45346859370257038347042575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30231239580171358898028383 45346859370257038347042575)
              ·
                refine ⟨68020289055385557520563863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45346859370257038347042575 68020289055385557520563863)
                ·
                  refine ⟨102030433583078336280845795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68020289055385557520563863 102030433583078336280845795)
                  ·
                    refine ⟨153045650374617504421268693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102030433583078336280845795 153045650374617504421268693)
                    ·
                      refine ⟨3587007430655097759873485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153045650374617504421268693 3587007430655097759873485)
                      ·
                        rfl

theorem cell23_6985672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_6985672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985672 prefixEnd_6985672 := by exact prefixLift 6985672
  have htrace : WordTrace (prefixWord ++ tailWord_6985672) baseStart_6985672 baseEnd_6985672 := by
    simpa [prefixWord, tailWord_6985672, baseEnd_6985672] using wordTrace_append hprefix tailTrace_6985672
  have hstable : (prefixWord ++ tailWord_6985672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985672).length < 2 ^ (prefixWord ++ tailWord_6985672).sum := by decide
  have hdescent : baseEnd_6985672 < baseStart_6985672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985699 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6985699 : Nat := 118140960795 + 6985699 * 2 ^ 59
def prefixEnd_6985699 : Nat := 4983230072969 + 3 ^ 40 * 6985699 * 2
def baseEnd_6985699 : Nat := 3587021294632769154235861

theorem tailTrace_6985699 : CollatzResearch.WordTrace tailWord_6985699 prefixEnd_6985699 3587021294632769154235861 := by
  unfold tailWord_6985699
  simp only [CollatzResearch.WordTrace]
  refine ⟨254789374319013060249760151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169859582879342040166506767 254789374319013060249760151)
  ·
    refine ⟨382184061478519590374640227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254789374319013060249760151 382184061478519590374640227)
    ·
      refine ⟨573276092217779385561960341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382184061478519590374640227 573276092217779385561960341)
      ·
        refine ⟨26872316822708408698216891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 573276092217779385561960341 26872316822708408698216891)
        ·
          refine ⟨40308475234062613047325337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26872316822708408698216891 40308475234062613047325337)
          ·
            refine ⟨30231356425546959785494003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40308475234062613047325337 30231356425546959785494003)
            ·
              refine ⟨45347034638320439678241005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30231356425546959785494003 45347034638320439678241005)
              ·
                refine ⟨17005137989370164879340377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45347034638320439678241005 17005137989370164879340377)
                ·
                  refine ⟨12753853492027623659505283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17005137989370164879340377 12753853492027623659505283)
                  ·
                    refine ⟨19130780238041435489257925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12753853492027623659505283 19130780238041435489257925)
                    ·
                      refine ⟨3587021294632769154235861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19130780238041435489257925 3587021294632769154235861)
                      ·
                        rfl

theorem cell23_6985699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6985699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985699 prefixEnd_6985699 := by exact prefixLift 6985699
  have htrace : WordTrace (prefixWord ++ tailWord_6985699) baseStart_6985699 baseEnd_6985699 := by
    simpa [prefixWord, tailWord_6985699, baseEnd_6985699] using wordTrace_append hprefix tailTrace_6985699
  have hstable : (prefixWord ++ tailWord_6985699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985699).length < 2 ^ (prefixWord ++ tailWord_6985699).sum := by decide
  have hdescent : baseEnd_6985699 < baseStart_6985699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985783 : List Nat := [1, 1, 3, 1, 2, 2, 4, 4, 1, 1, 3]
def baseStart_6985783 : Nat := 118140960795 + 6985783 * 2 ^ 59
def prefixEnd_6985783 : Nat := 4983230072969 + 3 ^ 40 * 6985783 * 2
def baseEnd_6985783 : Nat := 3587064427007746825585475

theorem tailTrace_6985783 : CollatzResearch.WordTrace tailWord_6985783 prefixEnd_6985783 3587064427007746825585475 := by
  unfold tailWord_6985783
  simp only [CollatzResearch.WordTrace]
  refine ⟨254792438050708742595818003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169861625367139161730545335 254792438050708742595818003)
  ·
    refine ⟨382188657076063113893727005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254792438050708742595818003 382188657076063113893727005)
    ·
      refine ⟨143320746403523667710147627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382188657076063113893727005 143320746403523667710147627)
      ·
        refine ⟨214981119605285501565221441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143320746403523667710147627 214981119605285501565221441)
        ·
          refine ⟨161235839703964126173916081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214981119605285501565221441 161235839703964126173916081)
          ·
            refine ⟨120926879777973094630437061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161235839703964126173916081 120926879777973094630437061)
            ·
              refine ⟨22673789958369955243206949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120926879777973094630437061 22673789958369955243206949)
              ·
                refine ⟨4251335617194366608101303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22673789958369955243206949 4251335617194366608101303)
                ·
                  refine ⟨6377003425791549912151955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251335617194366608101303 6377003425791549912151955)
                  ·
                    refine ⟨9565505138687324868227933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6377003425791549912151955 9565505138687324868227933)
                    ·
                      refine ⟨3587064427007746825585475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9565505138687324868227933 3587064427007746825585475)
                      ·
                        rfl

theorem cell23_6985783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 1, 3].length) (baseStart_6985783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985783 prefixEnd_6985783 := by exact prefixLift 6985783
  have htrace : WordTrace (prefixWord ++ tailWord_6985783) baseStart_6985783 baseEnd_6985783 := by
    simpa [prefixWord, tailWord_6985783, baseEnd_6985783] using wordTrace_append hprefix tailTrace_6985783
  have hstable : (prefixWord ++ tailWord_6985783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985783).length < 2 ^ (prefixWord ++ tailWord_6985783).sum := by decide
  have hdescent : baseEnd_6985783 < baseStart_6985783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985806 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_6985806 : Nat := 118140960795 + 6985806 * 2 ^ 59
def prefixEnd_6985806 : Nat := 4983230072969 + 3 ^ 40 * 6985806 * 2
def baseEnd_6985806 : Nat := 3587076237062800235597869

theorem tailTrace_6985806 : CollatzResearch.WordTrace tailWord_6985806 prefixEnd_6985806 3587076237062800235597869 := by
  unfold tailWord_6985806
  simp only [CollatzResearch.WordTrace]
  refine ⟨31849159616203177190488159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169862184619750278349270181 31849159616203177190488159)
  ·
    refine ⟨47773739424304765785732239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31849159616203177190488159 47773739424304765785732239)
    ·
      refine ⟨71660609136457148678598359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47773739424304765785732239 71660609136457148678598359)
      ·
        refine ⟨107490913704685723017897539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71660609136457148678598359 107490913704685723017897539)
        ·
          refine ⟨161236370557028584526846309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107490913704685723017897539 161236370557028584526846309)
          ·
            refine ⟨30231819479442859598783683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161236370557028584526846309 30231819479442859598783683)
            ·
              refine ⟨45347729219164289398175525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30231819479442859598783683 45347729219164289398175525)
              ·
                refine ⟨8502699228593304262157911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45347729219164289398175525 8502699228593304262157911)
                ·
                  refine ⟨12754048842889956393236867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502699228593304262157911 12754048842889956393236867)
                  ·
                    refine ⟨19131073264334934589855301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12754048842889956393236867 19131073264334934589855301)
                    ·
                      refine ⟨3587076237062800235597869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19131073264334934589855301 3587076237062800235597869)
                      ·
                        rfl

theorem cell23_6985806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_6985806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985806 prefixEnd_6985806 := by exact prefixLift 6985806
  have htrace : WordTrace (prefixWord ++ tailWord_6985806) baseStart_6985806 baseEnd_6985806 := by
    simpa [prefixWord, tailWord_6985806, baseEnd_6985806] using wordTrace_append hprefix tailTrace_6985806
  have hstable : (prefixWord ++ tailWord_6985806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985806).length < 2 ^ (prefixWord ++ tailWord_6985806).sum := by decide
  have hdescent : baseEnd_6985806 < baseStart_6985806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985829 : List Nat := [1, 3, 1, 3, 2, 4, 9]
def baseStart_6985829 : Nat := 118140960795 + 6985829 * 2 ^ 59
def prefixEnd_6985829 : Nat := 4983230072969 + 3 ^ 40 * 6985829 * 2
def baseEnd_6985829 : Nat := 44285037618738933896423

theorem tailTrace_6985829 : CollatzResearch.WordTrace tailWord_6985829 prefixEnd_6985829 44285037618738933896423 := by
  unfold tailWord_6985829
  simp only [CollatzResearch.WordTrace]
  refine ⟨254794115808542092451992541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169862743872361394967995027 254794115808542092451992541)
  ·
    refine ⟨95547793428203284669497203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254794115808542092451992541 95547793428203284669497203)
    ·
      refine ⟨143321690142304927004245805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95547793428203284669497203 143321690142304927004245805)
      ·
        refine ⟨53745633803364347626592177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143321690142304927004245805 53745633803364347626592177)
        ·
          refine ⟨40309225352523260719944133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53745633803364347626592177 40309225352523260719944133)
          ·
            refine ⟨7557979753598111384989525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40309225352523260719944133 7557979753598111384989525)
            ·
              refine ⟨44285037618738933896423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7557979753598111384989525 44285037618738933896423)
              ·
                rfl

theorem cell23_6985829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 9].length) (baseStart_6985829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985829 prefixEnd_6985829 := by exact prefixLift 6985829
  have htrace : WordTrace (prefixWord ++ tailWord_6985829) baseStart_6985829 baseEnd_6985829 := by
    simpa [prefixWord, tailWord_6985829, baseEnd_6985829] using wordTrace_append hprefix tailTrace_6985829
  have hstable : (prefixWord ++ tailWord_6985829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985829).length < 2 ^ (prefixWord ++ tailWord_6985829).sum := by decide
  have hdescent : baseEnd_6985829 < baseStart_6985829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985840 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 3, 2, 2]
def baseStart_6985840 : Nat := 118140960795 + 6985840 * 2 ^ 59
def prefixEnd_6985840 : Nat := 4983230072969 + 3 ^ 40 * 6985840 * 2
def baseEnd_6985840 : Nat := 3587093695405053102572713

theorem tailTrace_6985840 : CollatzResearch.WordTrace tailWord_6985840 prefixEnd_6985840 3587093695405053102572713 := by
  unfold tailWord_6985840
  simp only [CollatzResearch.WordTrace]
  refine ⟨127397258505751120665321487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169863011341001494220428649 127397258505751120665321487)
  ·
    refine ⟨191095887758626680997982231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127397258505751120665321487 191095887758626680997982231)
    ·
      refine ⟨286643831637940021496973347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191095887758626680997982231 286643831637940021496973347)
      ·
        refine ⟨429965747456910032245460021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286643831637940021496973347 429965747456910032245460021)
        ·
          refine ⟨40309288824085315523011877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 429965747456910032245460021 40309288824085315523011877)
          ·
            refine ⟨7557991654515996660564727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40309288824085315523011877 7557991654515996660564727)
            ·
              refine ⟨11336987481773994990847091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7557991654515996660564727 11336987481773994990847091)
              ·
                refine ⟨17005481222660992486270637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11336987481773994990847091 17005481222660992486270637)
                ·
                  refine ⟨6377055458497872182351489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17005481222660992486270637 6377055458497872182351489)
                  ·
                    refine ⟨4782791593873404136763617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6377055458497872182351489 4782791593873404136763617)
                    ·
                      refine ⟨3587093695405053102572713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782791593873404136763617 3587093695405053102572713)
                      ·
                        rfl

theorem cell23_6985840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 3, 2, 2].length) (baseStart_6985840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985840 prefixEnd_6985840 := by exact prefixLift 6985840
  have htrace : WordTrace (prefixWord ++ tailWord_6985840) baseStart_6985840 baseEnd_6985840 := by
    simpa [prefixWord, tailWord_6985840, baseEnd_6985840] using wordTrace_append hprefix tailTrace_6985840
  have hstable : (prefixWord ++ tailWord_6985840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985840).length < 2 ^ (prefixWord ++ tailWord_6985840).sum := by decide
  have hdescent : baseEnd_6985840 < baseStart_6985840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985846 : List Nat := [5, 1, 1, 2, 1, 3, 2, 8]
def baseStart_6985846 : Nat := 118140960795 + 6985846 * 2 ^ 59
def prefixEnd_6985846 : Nat := 4983230072969 + 3 ^ 40 * 6985846 * 2
def baseEnd_6985846 : Nat := 132855436158851114040655

theorem tailTrace_6985846 : CollatzResearch.WordTrace tailWord_6985846 prefixEnd_6985846 132855436158851114040655 := by
  unfold tailWord_6985846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15924670990592531522210087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169863157232987002903574261 15924670990592531522210087)
  ·
    refine ⟨23887006485888797283315131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15924670990592531522210087 23887006485888797283315131)
    ·
      refine ⟨35830509728833195924972697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23887006485888797283315131 35830509728833195924972697)
      ·
        refine ⟨26872882296624896943729523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35830509728833195924972697 26872882296624896943729523)
        ·
          refine ⟨40309323444937345415594285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26872882296624896943729523 40309323444937345415594285)
          ·
            refine ⟨15115996291851504530847857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40309323444937345415594285 15115996291851504530847857)
            ·
              refine ⟨11336997218888628398135893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15115996291851504530847857 11336997218888628398135893)
              ·
                refine ⟨132855436158851114040655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11336997218888628398135893 132855436158851114040655)
                ·
                  rfl

theorem cell23_6985846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_6985846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985846 prefixEnd_6985846 := by exact prefixLift 6985846
  have htrace : WordTrace (prefixWord ++ tailWord_6985846) baseStart_6985846 baseEnd_6985846 := by
    simpa [prefixWord, tailWord_6985846, baseEnd_6985846] using wordTrace_append hprefix tailTrace_6985846
  have hstable : (prefixWord ++ tailWord_6985846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985846).length < 2 ^ (prefixWord ++ tailWord_6985846).sum := by decide
  have hdescent : baseEnd_6985846 < baseStart_6985846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985890 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_6985890 : Nat := 118140960795 + 6985890 * 2 ^ 59
def prefixEnd_6985890 : Nat := 4983230072969 + 3 ^ 40 * 6985890 * 2
def baseEnd_6985890 : Nat := 3587119369437777906947483

theorem tailTrace_6985890 : CollatzResearch.WordTrace tailWord_6985890 prefixEnd_6985890 3587119369437777906947483 := by
  unfold tailWord_6985890
  simp only [CollatzResearch.WordTrace]
  refine ⟨63699085165330274967490781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169864227107547399913308749 63699085165330274967490781)
  ·
    refine ⟨23887156936998853112809043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63699085165330274967490781 23887156936998853112809043)
    ·
      refine ⟨35830735405498279669213565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23887156936998853112809043 35830735405498279669213565)
      ·
        refine ⟨13436525777061854875955087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35830735405498279669213565 13436525777061854875955087)
        ·
          refine ⟨20154788665592782313932631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13436525777061854875955087 20154788665592782313932631)
          ·
            refine ⟨30232182998389173470898947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20154788665592782313932631 30232182998389173470898947)
            ·
              refine ⟨45348274497583760206348421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30232182998389173470898947 45348274497583760206348421)
              ·
                refine ⟨8502801468296955038690329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45348274497583760206348421 8502801468296955038690329)
                ·
                  refine ⟨6377101101222716279017747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8502801468296955038690329 6377101101222716279017747)
                  ·
                    refine ⟨9565651651834074418526621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6377101101222716279017747 9565651651834074418526621)
                    ·
                      refine ⟨3587119369437777906947483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9565651651834074418526621 3587119369437777906947483)
                      ·
                        rfl

theorem cell23_6985890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_6985890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985890 prefixEnd_6985890 := by exact prefixLift 6985890
  have htrace : WordTrace (prefixWord ++ tailWord_6985890) baseStart_6985890 baseEnd_6985890 := by
    simpa [prefixWord, tailWord_6985890, baseEnd_6985890] using wordTrace_append hprefix tailTrace_6985890
  have hstable : (prefixWord ++ tailWord_6985890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985890).length < 2 ^ (prefixWord ++ tailWord_6985890).sum := by decide
  have hdescent : baseEnd_6985890 < baseStart_6985890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985913 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 1, 4, 2]
def baseStart_6985913 : Nat := 118140960795 + 6985913 * 2 ^ 59
def prefixEnd_6985913 : Nat := 4983230072969 + 3 ^ 40 * 6985913 * 2
def baseEnd_6985913 : Nat := 3587131179492831316959877

theorem tailTrace_6985913 : CollatzResearch.WordTrace tailWord_6985913 prefixEnd_6985913 3587131179492831316959877 := by
  unfold tailWord_6985913
  simp only [CollatzResearch.WordTrace]
  refine ⟨254797179540237774798050393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169864786360158516532033595 254797179540237774798050393)
  ·
    refine ⟨191097884655178331098537795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254797179540237774798050393 191097884655178331098537795)
    ·
      refine ⟨286646826982767496647806693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191097884655178331098537795 286646826982767496647806693)
      ·
        refine ⟨53746280059268905621463755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286646826982767496647806693 53746280059268905621463755)
        ·
          refine ⟨80619420088903358432195633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53746280059268905621463755 80619420088903358432195633)
          ·
            refine ⟨60464565066677518824146725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80619420088903358432195633 60464565066677518824146725)
            ·
              refine ⟨11337105950002034779527511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60464565066677518824146725 11337105950002034779527511)
              ·
                refine ⟨17005658925003052169291267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11337105950002034779527511 17005658925003052169291267)
                ·
                  refine ⟨25508488387504578253936901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17005658925003052169291267 25508488387504578253936901)
                  ·
                    refine ⟨4782841572657108422613169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25508488387504578253936901 4782841572657108422613169)
                    ·
                      refine ⟨3587131179492831316959877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782841572657108422613169 3587131179492831316959877)
                      ·
                        rfl

theorem cell23_6985913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_6985913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985913 prefixEnd_6985913 := by exact prefixLift 6985913
  have htrace : WordTrace (prefixWord ++ tailWord_6985913) baseStart_6985913 baseEnd_6985913 := by
    simpa [prefixWord, tailWord_6985913, baseEnd_6985913] using wordTrace_append hprefix tailTrace_6985913
  have hstable : (prefixWord ++ tailWord_6985913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985913).length < 2 ^ (prefixWord ++ tailWord_6985913).sum := by decide
  have hdescent : baseEnd_6985913 < baseStart_6985913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985946 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_6985946 : Nat := 118140960795 + 6985946 * 2 ^ 59
def prefixEnd_6985946 : Nat := 4983230072969 + 3 ^ 40 * 6985946 * 2
def baseEnd_6985946 : Nat := 3587148124354429687847225

theorem tailTrace_6985946 : CollatzResearch.WordTrace tailWord_6985946 prefixEnd_6985946 3587148124354429687847225 := by
  unfold tailWord_6985946
  simp only [CollatzResearch.WordTrace]
  refine ⟨63699595787279555358500423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169865588766078814289334461 63699595787279555358500423)
  ·
    refine ⟨95549393680919333037750635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63699595787279555358500423 95549393680919333037750635)
    ·
      refine ⟨143324090521378999556625953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95549393680919333037750635 143324090521378999556625953)
      ·
        refine ⟨107493067891034249667469465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143324090521378999556625953 107493067891034249667469465)
        ·
          refine ⟨80619800918275687250602099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107493067891034249667469465 80619800918275687250602099)
          ·
            refine ⟨120929701377413530875903149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80619800918275687250602099 120929701377413530875903149)
            ·
              refine ⟨45348638016530074078463681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120929701377413530875903149 45348638016530074078463681)
              ·
                refine ⟨34011478512397555558847761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45348638016530074078463681 34011478512397555558847761)
                ·
                  refine ⟨25508608884298166669135821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34011478512397555558847761 25508608884298166669135821)
                  ·
                    refine ⟨9565728331611812500925933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25508608884298166669135821 9565728331611812500925933)
                    ·
                      refine ⟨3587148124354429687847225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9565728331611812500925933 3587148124354429687847225)
                      ·
                        rfl

theorem cell23_6985946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_6985946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985946 prefixEnd_6985946 := by exact prefixLift 6985946
  have htrace : WordTrace (prefixWord ++ tailWord_6985946) baseStart_6985946 baseEnd_6985946 := by
    simpa [prefixWord, tailWord_6985946, baseEnd_6985946] using wordTrace_append hprefix tailTrace_6985946
  have hstable : (prefixWord ++ tailWord_6985946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985946).length < 2 ^ (prefixWord ++ tailWord_6985946).sum := by decide
  have hdescent : baseEnd_6985946 < baseStart_6985946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985999 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_6985999 : Nat := 118140960795 + 6985999 * 2 ^ 59
def prefixEnd_6985999 : Nat := 4983230072969 + 3 ^ 40 * 6985999 * 2
def baseEnd_6985999 : Nat := 3587175338829117980484481

theorem tailTrace_6985999 : CollatzResearch.WordTrace tailWord_6985999 prefixEnd_6985999 3587175338829117980484481 := by
  unfold tailWord_6985999
  simp only [CollatzResearch.WordTrace]
  refine ⟨254800316217926211485681051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169866877478617474323787367 254800316217926211485681051)
  ·
    refine ⟨382200474326889317228521577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254800316217926211485681051 382200474326889317228521577)
    ·
      refine ⟨286650355745166987921391183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382200474326889317228521577 286650355745166987921391183)
      ·
        refine ⟨429975533617750481882086775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286650355745166987921391183 429975533617750481882086775)
        ·
          refine ⟨644963300426625722823130163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429975533617750481882086775 644963300426625722823130163)
          ·
            refine ⟨967444950639938584234695245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644963300426625722823130163 967444950639938584234695245)
            ·
              refine ⟨362791856489976969088010717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 967444950639938584234695245 362791856489976969088010717)
              ·
                refine ⟨136046946183741363408004019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362791856489976969088010717 136046946183741363408004019)
                ·
                  refine ⟨204070419275612045112006029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136046946183741363408004019 204070419275612045112006029)
                  ·
                    refine ⟨76526407228354516917002261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204070419275612045112006029 76526407228354516917002261)
                    ·
                      refine ⟨3587175338829117980484481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76526407228354516917002261 3587175338829117980484481)
                      ·
                        rfl

theorem cell23_6985999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_6985999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985999 prefixEnd_6985999 := by exact prefixLift 6985999
  have htrace : WordTrace (prefixWord ++ tailWord_6985999) baseStart_6985999 baseEnd_6985999 := by
    simpa [prefixWord, tailWord_6985999, baseEnd_6985999] using wordTrace_append hprefix tailTrace_6985999
  have hstable : (prefixWord ++ tailWord_6985999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985999).length < 2 ^ (prefixWord ++ tailWord_6985999).sum := by decide
  have hdescent : baseEnd_6985999 < baseStart_6985999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986063 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 4, 3, 2]
def baseStart_6986063 : Nat := 118140960795 + 6986063 * 2 ^ 59
def prefixEnd_6986063 : Nat := 4983230072969 + 3 ^ 40 * 6986063 * 2
def baseEnd_6986063 : Nat := 3587208201591005730084187

theorem tailTrace_6986063 : CollatzResearch.WordTrace tailWord_6986063 prefixEnd_6986063 3587208201591005730084187 := by
  unfold tailWord_6986063
  simp only [CollatzResearch.WordTrace]
  refine ⟨254802650489694350416010843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169868433659796233610673895 254802650489694350416010843)
  ·
    refine ⟨382203975734541525624016265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254802650489694350416010843 382203975734541525624016265)
    ·
      refine ⟨286652981800906144218012199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382203975734541525624016265 286652981800906144218012199)
      ·
        refine ⟨429979472701359216327018299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286652981800906144218012199 429979472701359216327018299)
        ·
          refine ⟨644969209052038824490527449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429979472701359216327018299 644969209052038824490527449)
          ·
            refine ⟨483726906789029118367895587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644969209052038824490527449 483726906789029118367895587)
            ·
              refine ⟨725590360183543677551843381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483726906789029118367895587 725590360183543677551843381)
              ·
                refine ⟨68024096267207219770485317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 725590360183543677551843381 68024096267207219770485317)
                ·
                  refine ⟨12754518050101353706965997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68024096267207219770485317 12754518050101353706965997)
                  ·
                    refine ⟨4782944268788007640112249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12754518050101353706965997 4782944268788007640112249)
                    ·
                      refine ⟨3587208201591005730084187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782944268788007640112249 3587208201591005730084187)
                      ·
                        rfl

theorem cell23_6986063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 3, 2].length) (baseStart_6986063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986063 prefixEnd_6986063 := by exact prefixLift 6986063
  have htrace : WordTrace (prefixWord ++ tailWord_6986063) baseStart_6986063 baseEnd_6986063 := by
    simpa [prefixWord, tailWord_6986063, baseEnd_6986063] using wordTrace_append hprefix tailTrace_6986063
  have hstable : (prefixWord ++ tailWord_6986063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986063).length < 2 ^ (prefixWord ++ tailWord_6986063).sum := by decide
  have hdescent : baseEnd_6986063 < baseStart_6986063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986093 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_6986093 : Nat := 118140960795 + 6986093 * 2 ^ 59
def prefixEnd_6986093 : Nat := 4983230072969 + 3 ^ 40 * 6986093 * 2
def baseEnd_6986093 : Nat := 3587223606010640612709049

theorem tailTrace_6986093 : CollatzResearch.WordTrace tailWord_6986093 prefixEnd_6986093 3587223606010640612709049 := by
  unfold tailWord_6986093
  simp only [CollatzResearch.WordTrace]
  refine ⟨254803744679585665539602933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169869163119723777026401955 254803744679585665539602933)
  ·
    refine ⟨23887851063711156144337775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254803744679585665539602933 23887851063711156144337775)
    ·
      refine ⟨35831776595566734216506663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23887851063711156144337775 35831776595566734216506663)
      ·
        refine ⟨53747664893350101324759995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35831776595566734216506663 53747664893350101324759995)
        ·
          refine ⟨80621497340025151987139993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53747664893350101324759995 80621497340025151987139993)
          ·
            refine ⟨60466123005018863990354995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80621497340025151987139993 60466123005018863990354995)
            ·
              refine ⟨90699184507528295985532493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60466123005018863990354995 90699184507528295985532493)
              ·
                refine ⟨34012194190323110994574685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90699184507528295985532493 34012194190323110994574685)
                ·
                  refine ⟨12754572821371166622965507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34012194190323110994574685 12754572821371166622965507)
                  ·
                    refine ⟨19131859232056749934448261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12754572821371166622965507 19131859232056749934448261)
                    ·
                      refine ⟨3587223606010640612709049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19131859232056749934448261 3587223606010640612709049)
                      ·
                        rfl

theorem cell23_6986093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_6986093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986093 prefixEnd_6986093 := by exact prefixLift 6986093
  have htrace : WordTrace (prefixWord ++ tailWord_6986093) baseStart_6986093 baseEnd_6986093 := by
    simpa [prefixWord, tailWord_6986093, baseEnd_6986093] using wordTrace_append hprefix tailTrace_6986093
  have hstable : (prefixWord ++ tailWord_6986093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986093).length < 2 ^ (prefixWord ++ tailWord_6986093).sum := by decide
  have hdescent : baseEnd_6986093 < baseStart_6986093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986116 : List Nat := [2, 3, 2, 1, 1, 2, 12]
def baseStart_6986116 : Nat := 118140960795 + 6986116 * 2 ^ 59
def prefixEnd_6986116 : Nat := 4983230072969 + 3 ^ 40 * 6986116 * 2
def baseEnd_6986116 : Nat := 44286856988465358305203

theorem tailTrace_6986116 : CollatzResearch.WordTrace tailWord_6986116 prefixEnd_6986116 44286856988465358305203 := by
  unfold tailWord_6986116
  simp only [CollatzResearch.WordTrace]
  refine ⟨127402291779251170233845101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169869722372334893645126801 127402291779251170233845101)
  ·
    refine ⟨47775859417219188837691913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127402291779251170233845101 47775859417219188837691913)
    ·
      refine ⟨35831894562914391628268935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47775859417219188837691913 35831894562914391628268935)
      ·
        refine ⟨53747841844371587442403403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35831894562914391628268935 53747841844371587442403403)
        ·
          refine ⟨80621762766557381163605105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53747841844371587442403403 80621762766557381163605105)
          ·
            refine ⟨60466322074918035872703829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80621762766557381163605105 60466322074918035872703829)
            ·
              refine ⟨44286856988465358305203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 60466322074918035872703829 44286856988465358305203)
              ·
                rfl

theorem cell23_6986116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 12].length) (baseStart_6986116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986116 prefixEnd_6986116 := by exact prefixLift 6986116
  have htrace : WordTrace (prefixWord ++ tailWord_6986116) baseStart_6986116 baseEnd_6986116 := by
    simpa [prefixWord, tailWord_6986116, baseEnd_6986116] using wordTrace_append hprefix tailTrace_6986116
  have hstable : (prefixWord ++ tailWord_6986116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986116).length < 2 ^ (prefixWord ++ tailWord_6986116).sum := by decide
  have hdescent : baseEnd_6986116 < baseStart_6986116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986153 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 2, 7, 2]
def baseStart_6986153 : Nat := 118140960795 + 6986153 * 2 ^ 59
def prefixEnd_6986153 : Nat := 4983230072969 + 3 ^ 40 * 6986153 * 2
def baseEnd_6986153 : Nat := 3587254414849910377958773

theorem tailTrace_6986153 : CollatzResearch.WordTrace tailWord_6986153 prefixEnd_6986153 3587254414849910377958773 := by
  unfold tailWord_6986153
  simp only [CollatzResearch.WordTrace]
  refine ⟨254805933059368295786787113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169870622039578863857858075 254805933059368295786787113)
  ·
    refine ⟨191104449794526221840090335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254805933059368295786787113 191104449794526221840090335)
    ·
      refine ⟨286656674691789332760135503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191104449794526221840090335 286656674691789332760135503)
      ·
        refine ⟨429985012037683999140203255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286656674691789332760135503 429985012037683999140203255)
        ·
          refine ⟨644977518056525998710304883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429985012037683999140203255 644977518056525998710304883)
          ·
            refine ⟨967466277084788998065457325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644977518056525998710304883 967466277084788998065457325)
            ·
              refine ⟨362799853906795874274546497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 967466277084788998065457325 362799853906795874274546497)
              ·
                refine ⟨272099890430096905705909873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362799853906795874274546497 272099890430096905705909873)
                ·
                  refine ⟨204074917822572679279432405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272099890430096905705909873 204074917822572679279432405)
                  ·
                    refine ⟨4783005886466547170611697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 204074917822572679279432405 4783005886466547170611697)
                    ·
                      refine ⟨3587254414849910377958773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4783005886466547170611697 3587254414849910377958773)
                      ·
                        rfl

theorem cell23_6986153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 7, 2].length) (baseStart_6986153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986153 prefixEnd_6986153 := by exact prefixLift 6986153
  have htrace : WordTrace (prefixWord ++ tailWord_6986153) baseStart_6986153 baseEnd_6986153 := by
    simpa [prefixWord, tailWord_6986153, baseEnd_6986153] using wordTrace_append hprefix tailTrace_6986153
  have hstable : (prefixWord ++ tailWord_6986153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986153).length < 2 ^ (prefixWord ++ tailWord_6986153).sum := by decide
  have hdescent : baseEnd_6986153 < baseStart_6986153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986161 : List Nat := [1, 2, 2, 4, 1, 4, 1, 3, 1, 2, 2]
def baseStart_6986161 : Nat := 118140960795 + 6986161 * 2 ^ 59
def prefixEnd_6986161 : Nat := 4983230072969 + 3 ^ 40 * 6986161 * 2
def baseEnd_6986161 : Nat := 3587258522695146346658737

theorem tailTrace_6986161 : CollatzResearch.WordTrace tailWord_6986161 prefixEnd_6986161 3587258522695146346658737 := by
  unfold tailWord_6986161
  simp only [CollatzResearch.WordTrace]
  refine ⟨254806224843339313153078337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169870816562226208768718891 254806224843339313153078337)
  ·
    refine ⟨191104668632504484864808753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254806224843339313153078337 191104668632504484864808753)
    ·
      refine ⟨143328501474378363648606565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191104668632504484864808753 143328501474378363648606565)
      ·
        refine ⟨26874094026445943184113731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143328501474378363648606565 26874094026445943184113731)
        ·
          refine ⟨40311141039668914776170597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26874094026445943184113731 40311141039668914776170597)
          ·
            refine ⟨7558338944937921520531987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40311141039668914776170597 7558338944937921520531987)
            ·
              refine ⟨11337508417406882280797981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7558338944937921520531987 11337508417406882280797981)
              ·
                refine ⟨4251565656527580855299243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11337508417406882280797981 4251565656527580855299243)
                ·
                  refine ⟨6377348484791371282948865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251565656527580855299243 6377348484791371282948865)
                  ·
                    refine ⟨4783011363593528462211649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6377348484791371282948865 4783011363593528462211649)
                    ·
                      refine ⟨3587258522695146346658737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4783011363593528462211649 3587258522695146346658737)
                      ·
                        rfl

theorem cell23_6986161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_6986161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986161 prefixEnd_6986161 := by exact prefixLift 6986161
  have htrace : WordTrace (prefixWord ++ tailWord_6986161) baseStart_6986161 baseEnd_6986161 := by
    simpa [prefixWord, tailWord_6986161, baseEnd_6986161] using wordTrace_append hprefix tailTrace_6986161
  have hstable : (prefixWord ++ tailWord_6986161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986161).length < 2 ^ (prefixWord ++ tailWord_6986161).sum := by decide
  have hdescent : baseEnd_6986161 < baseStart_6986161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986164 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6986164 : Nat := 118140960795 + 6986164 * 2 ^ 59
def prefixEnd_6986164 : Nat := 4983230072969 + 3 ^ 40 * 6986164 * 2
def baseEnd_6986164 : Nat := 3587260063137109834921223

theorem tailTrace_6986164 : CollatzResearch.WordTrace tailWord_6986164 prefixEnd_6986164 3587260063137109834921223 := by
  unfold tailWord_6986164
  simp only [CollatzResearch.WordTrace]
  refine ⟨127403167131164222332718773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169870889508218963110291697 127403167131164222332718773)
  ·
    refine ⟨11944046918546645843692385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127403167131164222332718773 11944046918546645843692385)
    ·
      refine ⟨8958035188909984382769289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11944046918546645843692385 8958035188909984382769289)
      ·
        refine ⟨6718526391682488287076967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8958035188909984382769289 6718526391682488287076967)
        ·
          refine ⟨10077789587523732430615451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6718526391682488287076967 10077789587523732430615451)
          ·
            refine ⟨15116684381285598645923177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10077789587523732430615451 15116684381285598645923177)
            ·
              refine ⟨11337513285964198984442383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15116684381285598645923177 11337513285964198984442383)
              ·
                refine ⟨17006269928946298476663575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11337513285964198984442383 17006269928946298476663575)
                ·
                  refine ⟨25509404893419447714995363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17006269928946298476663575 25509404893419447714995363)
                  ·
                    refine ⟨38264107340129171572493045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25509404893419447714995363 38264107340129171572493045)
                    ·
                      refine ⟨3587260063137109834921223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38264107340129171572493045 3587260063137109834921223)
                      ·
                        rfl

theorem cell23_6986164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6986164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986164 prefixEnd_6986164 := by exact prefixLift 6986164
  have htrace : WordTrace (prefixWord ++ tailWord_6986164) baseStart_6986164 baseEnd_6986164 := by
    simpa [prefixWord, tailWord_6986164, baseEnd_6986164] using wordTrace_append hprefix tailTrace_6986164
  have hstable : (prefixWord ++ tailWord_6986164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986164).length < 2 ^ (prefixWord ++ tailWord_6986164).sum := by decide
  have hdescent : baseEnd_6986164 < baseStart_6986164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986200 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 1, 4, 2]
def baseStart_6986200 : Nat := 118140960795 + 6986200 * 2 ^ 59
def prefixEnd_6986200 : Nat := 4983230072969 + 3 ^ 40 * 6986200 * 2
def baseEnd_6986200 : Nat := 3587278548440671694071057

theorem tailTrace_6986200 : CollatzResearch.WordTrace tailWord_6986200 prefixEnd_6986200 3587278548440671694071057 := by
  unfold tailWord_6986200
  simp only [CollatzResearch.WordTrace]
  refine ⟨127403823645099011406874027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169871764860132015209165369 127403823645099011406874027)
  ·
    refine ⟨191105735467648517110311041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127403823645099011406874027 191105735467648517110311041)
    ·
      refine ⟨143329301600736387832733281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191105735467648517110311041 143329301600736387832733281)
      ·
        refine ⟨107496976200552290874549961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143329301600736387832733281 107496976200552290874549961)
        ·
          refine ⟨80622732150414218155912471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107496976200552290874549961 80622732150414218155912471)
          ·
            refine ⟨120934098225621327233868707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80622732150414218155912471 120934098225621327233868707)
            ·
              refine ⟨181401147338431990850803061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120934098225621327233868707 181401147338431990850803061)
              ·
                refine ⟨17006357562977999142262787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181401147338431990850803061 17006357562977999142262787)
                ·
                  refine ⟨25509536344466998713394181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17006357562977999142262787 25509536344466998713394181)
                  ·
                    refine ⟨4783038064587562258761409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25509536344466998713394181 4783038064587562258761409)
                    ·
                      refine ⟨3587278548440671694071057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4783038064587562258761409 3587278548440671694071057)
                      ·
                        rfl

theorem cell23_6986200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_6986200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986200 prefixEnd_6986200 := by exact prefixLift 6986200
  have htrace : WordTrace (prefixWord ++ tailWord_6986200) baseStart_6986200 baseEnd_6986200 := by
    simpa [prefixWord, tailWord_6986200, baseEnd_6986200] using wordTrace_append hprefix tailTrace_6986200
  have hstable : (prefixWord ++ tailWord_6986200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986200).length < 2 ^ (prefixWord ++ tailWord_6986200).sum := by decide
  have hdescent : baseEnd_6986200 < baseStart_6986200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986221 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_6986221 : Nat := 118140960795 + 6986221 * 2 ^ 59
def prefixEnd_6986221 : Nat := 4983230072969 + 3 ^ 40 * 6986221 * 2
def baseEnd_6986221 : Nat := 3587289331534416111908461

theorem tailTrace_6986221 : CollatzResearch.WordTrace tailWord_6986221 prefixEnd_6986221 3587289331534416111908461 := by
  unfold tailWord_6986221
  simp only [CollatzResearch.WordTrace]
  refine ⟨254808413223121943400262517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169872275482081295600175011 254808413223121943400262517)
  ·
    refine ⟨23888288739667682193774611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254808413223121943400262517 23888288739667682193774611)
    ·
      refine ⟨35832433109501523290661917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23888288739667682193774611 35832433109501523290661917)
      ·
        refine ⟨13437162416063071233998219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35832433109501523290661917 13437162416063071233998219)
        ·
          refine ⟨20155743624094606850997329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13437162416063071233998219 20155743624094606850997329)
          ·
            refine ⟨15116807718070955138247997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20155743624094606850997329 15116807718070955138247997)
            ·
              refine ⟨5668802894276608176842999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15116807718070955138247997 5668802894276608176842999)
              ·
                refine ⟨8503204341414912265264499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5668802894276608176842999 8503204341414912265264499)
                ·
                  refine ⟨12754806512122368397896749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8503204341414912265264499 12754806512122368397896749)
                  ·
                    refine ⟨4783052442045888149211281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12754806512122368397896749 4783052442045888149211281)
                    ·
                      refine ⟨3587289331534416111908461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4783052442045888149211281 3587289331534416111908461)
                      ·
                        rfl

theorem cell23_6986221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_6986221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986221 prefixEnd_6986221 := by exact prefixLift 6986221
  have htrace : WordTrace (prefixWord ++ tailWord_6986221) baseStart_6986221 baseEnd_6986221 := by
    simpa [prefixWord, tailWord_6986221, baseEnd_6986221] using wordTrace_append hprefix tailTrace_6986221
  have hstable : (prefixWord ++ tailWord_6986221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986221).length < 2 ^ (prefixWord ++ tailWord_6986221).sum := by decide
  have hdescent : baseEnd_6986221 < baseStart_6986221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986230 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6986230 : Nat := 118140960795 + 6986230 * 2 ^ 59
def prefixEnd_6986230 : Nat := 4983230072969 + 3 ^ 40 * 6986230 * 2
def baseEnd_6986230 : Nat := 3587293952860306576695919

theorem tailTrace_6986230 : CollatzResearch.WordTrace tailWord_6986230 prefixEnd_6986230 3587293952860306576695919 := by
  unfold tailWord_6986230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15925546342505583621083759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169872494320059558624893429 15925546342505583621083759)
  ·
    refine ⟨23888319513758375431625639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15925546342505583621083759 23888319513758375431625639)
    ·
      refine ⟨35832479270637563147438459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23888319513758375431625639 35832479270637563147438459)
      ·
        refine ⟨53748718905956344721157689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35832479270637563147438459 53748718905956344721157689)
        ·
          refine ⟨40311539179467258540868267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53748718905956344721157689 40311539179467258540868267)
          ·
            refine ⟨60467308769200887811302401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40311539179467258540868267 60467308769200887811302401)
            ·
              refine ⟨45350481576900665858476801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60467308769200887811302401 45350481576900665858476801)
              ·
                refine ⟨34012861182675499393857601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45350481576900665858476801 34012861182675499393857601)
                ·
                  refine ⟨25509645887006624545393201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34012861182675499393857601 25509645887006624545393201)
                  ·
                    refine ⟨19132234415254968409044901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25509645887006624545393201 19132234415254968409044901)
                    ·
                      refine ⟨3587293952860306576695919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19132234415254968409044901 3587293952860306576695919)
                      ·
                        rfl

theorem cell23_6986230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6986230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986230 prefixEnd_6986230 := by exact prefixLift 6986230
  have htrace : WordTrace (prefixWord ++ tailWord_6986230) baseStart_6986230 baseEnd_6986230 := by
    simpa [prefixWord, tailWord_6986230, baseEnd_6986230] using wordTrace_append hprefix tailTrace_6986230
  have hstable : (prefixWord ++ tailWord_6986230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986230).length < 2 ^ (prefixWord ++ tailWord_6986230).sum := by decide
  have hdescent : baseEnd_6986230 < baseStart_6986230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986250 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_6986250 : Nat := 118140960795 + 6986250 * 2 ^ 59
def prefixEnd_6986250 : Nat := 4983230072969 + 3 ^ 40 * 6986250 * 2
def baseEnd_6986250 : Nat := 3587304222473396498445827

theorem tailTrace_6986250 : CollatzResearch.WordTrace tailWord_6986250 prefixEnd_6986250 3587304222473396498445827 := by
  unfold tailWord_6986250
  simp only [CollatzResearch.WordTrace]
  refine ⟨63702367735004220338267051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169872980626677920902045469 63702367735004220338267051)
  ·
    refine ⟨95553551602506330507400577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63702367735004220338267051 95553551602506330507400577)
    ·
      refine ⟨71665163701879747880550433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95553551602506330507400577 71665163701879747880550433)
      ·
        refine ⟨53748872776409810910412825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71665163701879747880550433 53748872776409810910412825)
        ·
          refine ⟨40311654582307358182809619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53748872776409810910412825 40311654582307358182809619)
          ·
            refine ⟨60467481873461037274214429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40311654582307358182809619 60467481873461037274214429)
            ·
              refine ⟨22675305702547888977830411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60467481873461037274214429 22675305702547888977830411)
              ·
                refine ⟨34012958553821833466745617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22675305702547888977830411 34012958553821833466745617)
                ·
                  refine ⟨25509718915366375100059213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34012958553821833466745617 25509718915366375100059213)
                  ·
                    refine ⟨9566144593262390662522205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25509718915366375100059213 9566144593262390662522205)
                    ·
                      refine ⟨3587304222473396498445827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9566144593262390662522205 3587304222473396498445827)
                      ·
                        rfl

theorem cell23_6986250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_6986250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986250 prefixEnd_6986250 := by exact prefixLift 6986250
  have htrace : WordTrace (prefixWord ++ tailWord_6986250) baseStart_6986250 baseEnd_6986250 := by
    simpa [prefixWord, tailWord_6986250, baseEnd_6986250] using wordTrace_append hprefix tailTrace_6986250
  have hstable : (prefixWord ++ tailWord_6986250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986250).length < 2 ^ (prefixWord ++ tailWord_6986250).sum := by decide
  have hdescent : baseEnd_6986250 < baseStart_6986250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986290 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_6986290 : Nat := 118140960795 + 6986290 * 2 ^ 59
def prefixEnd_6986290 : Nat := 4983230072969 + 3 ^ 40 * 6986290 * 2
def baseEnd_6986290 : Nat := 3587324761699576341945643

theorem tailTrace_6986290 : CollatzResearch.WordTrace tailWord_6986290 prefixEnd_6986290 3587324761699576341945643 := by
  unfold tailWord_6986290
  simp only [CollatzResearch.WordTrace]
  refine ⟨63702732464967992046131081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169873953239914645456349549 63702732464967992046131081)
  ·
    refine ⟨47777049348725994034598311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63702732464967992046131081 47777049348725994034598311)
    ·
      refine ⟨71665574023088991051897467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47777049348725994034598311 71665574023088991051897467)
      ·
        refine ⟨107498361034633486577846201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71665574023088991051897467 107498361034633486577846201)
        ·
          refine ⟨80623770775975114933384651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107498361034633486577846201 80623770775975114933384651)
          ·
            refine ⟨120935656163962672400076977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80623770775975114933384651 120935656163962672400076977)
            ·
              refine ⟨90701742122972004300057733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120935656163962672400076977 90701742122972004300057733)
              ·
                refine ⟨17006576648057250806260825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90701742122972004300057733 17006576648057250806260825)
                ·
                  refine ⟨12754932486042938104695619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17006576648057250806260825 12754932486042938104695619)
                  ·
                    refine ⟨19132398729064407157043429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12754932486042938104695619 19132398729064407157043429)
                    ·
                      refine ⟨3587324761699576341945643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19132398729064407157043429 3587324761699576341945643)
                      ·
                        rfl

theorem cell23_6986290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_6986290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986290 prefixEnd_6986290 := by exact prefixLift 6986290
  have htrace : WordTrace (prefixWord ++ tailWord_6986290) baseStart_6986290 baseEnd_6986290 := by
    simpa [prefixWord, tailWord_6986290, baseEnd_6986290] using wordTrace_append hprefix tailTrace_6986290
  have hstable : (prefixWord ++ tailWord_6986290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986290).length < 2 ^ (prefixWord ++ tailWord_6986290).sum := by decide
  have hdescent : baseEnd_6986290 < baseStart_6986290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986303 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_6986303 : Nat := 118140960795 + 6986303 * 2 ^ 59
def prefixEnd_6986303 : Nat := 4983230072969 + 3 ^ 40 * 6986303 * 2
def baseEnd_6986303 : Nat := 3587331436948084791083083

theorem tailTrace_6986303 : CollatzResearch.WordTrace tailWord_6986303 prefixEnd_6986303 3587331436948084791083083 := by
  unfold tailWord_6986303
  simp only [CollatzResearch.WordTrace]
  refine ⟨254811404008824871404747563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169874269339216580936498375 254811404008824871404747563)
  ·
    refine ⟨382217106013237307107121345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254811404008824871404747563 382217106013237307107121345)
    ·
      refine ⟨286662829509927980330341009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382217106013237307107121345 286662829509927980330341009)
      ·
        refine ⟨214997122132445985247755757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286662829509927980330341009 214997122132445985247755757)
        ·
          refine ⟨80623920799667244467908409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214997122132445985247755757 80623920799667244467908409)
          ·
            refine ⟨60467940599750433350931307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80623920799667244467908409 60467940599750433350931307)
            ·
              refine ⟨90701910899625650026396961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60467940599750433350931307 90701910899625650026396961)
              ·
                refine ⟨68026433174719237519797721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90701910899625650026396961 68026433174719237519797721)
                ·
                  refine ⟨51019824881039428139848291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68026433174719237519797721 51019824881039428139848291)
                  ·
                    refine ⟨76529737321559142209772437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51019824881039428139848291 76529737321559142209772437)
                    ·
                      refine ⟨3587331436948084791083083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76529737321559142209772437 3587331436948084791083083)
                      ·
                        rfl

theorem cell23_6986303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_6986303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986303 prefixEnd_6986303 := by exact prefixLift 6986303
  have htrace : WordTrace (prefixWord ++ tailWord_6986303) baseStart_6986303 baseEnd_6986303 := by
    simpa [prefixWord, tailWord_6986303, baseEnd_6986303] using wordTrace_append hprefix tailTrace_6986303
  have hstable : (prefixWord ++ tailWord_6986303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986303).length < 2 ^ (prefixWord ++ tailWord_6986303).sum := by decide
  have hdescent : baseEnd_6986303 < baseStart_6986303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986344 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6986344 : Nat := 118140960795 + 6986344 * 2 ^ 59
def prefixEnd_6986344 : Nat := 4983230072969 + 3 ^ 40 * 6986344 * 2
def baseEnd_6986344 : Nat := 3587352489654919130670395

theorem tailTrace_6986344 : CollatzResearch.WordTrace tailWord_6986344 prefixEnd_6986344 3587352489654919130670395 := by
  unfold tailWord_6986344
  simp only [CollatzResearch.WordTrace]
  refine ⟨127406449700838167703495043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169875266267784223604660057 127406449700838167703495043)
  ·
    refine ⟨191109674551257251555242565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127406449700838167703495043 191109674551257251555242565)
    ·
      refine ⟨35833063978360734666607981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191109674551257251555242565 35833063978360734666607981)
      ·
        refine ⟨13437398991885275499977993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35833063978360734666607981 13437398991885275499977993)
        ·
          refine ⟨10078049243913956624983495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13437398991885275499977993 10078049243913956624983495)
          ·
            refine ⟨15117073865870934937475243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10078049243913956624983495 15117073865870934937475243)
            ·
              refine ⟨22675610798806402406212865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15117073865870934937475243 22675610798806402406212865)
              ·
                refine ⟨17006708099104801804659649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22675610798806402406212865 17006708099104801804659649)
                ·
                  refine ⟨12755031074328601353494737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17006708099104801804659649 12755031074328601353494737)
                  ·
                    refine ⟨9566273305746451015121053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12755031074328601353494737 9566273305746451015121053)
                    ·
                      refine ⟨3587352489654919130670395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9566273305746451015121053 3587352489654919130670395)
                      ·
                        rfl

theorem cell23_6986344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6986344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986344 prefixEnd_6986344 := by exact prefixLift 6986344
  have htrace : WordTrace (prefixWord ++ tailWord_6986344) baseStart_6986344 baseEnd_6986344 := by
    simpa [prefixWord, tailWord_6986344, baseEnd_6986344] using wordTrace_append hprefix tailTrace_6986344
  have hstable : (prefixWord ++ tailWord_6986344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986344).length < 2 ^ (prefixWord ++ tailWord_6986344).sum := by decide
  have hdescent : baseEnd_6986344 < baseStart_6986344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986353 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_6986353 : Nat := 118140960795 + 6986353 * 2 ^ 59
def prefixEnd_6986353 : Nat := 4983230072969 + 3 ^ 40 * 6986353 * 2
def baseEnd_6986353 : Nat := 3587357110980809595457853

theorem tailTrace_6986353 : CollatzResearch.WordTrace tailWord_6986353 prefixEnd_6986353 3587357110980809595457853 := by
  unfold tailWord_6986353
  simp only [CollatzResearch.WordTrace]
  refine ⟨254813227658643729944067713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169875485105762486629378475 254813227658643729944067713)
  ·
    refine ⟨191109920743982797458050785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254813227658643729944067713 191109920743982797458050785)
    ·
      refine ⟨143332440557987098093538089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191109920743982797458050785 143332440557987098093538089)
      ·
        refine ⟨107499330418490323570153567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143332440557987098093538089 107499330418490323570153567)
        ·
          refine ⟨161248995627735485355230351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107499330418490323570153567 161248995627735485355230351)
          ·
            refine ⟨241873493441603228032845527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161248995627735485355230351 241873493441603228032845527)
            ·
              refine ⟨362810240162404842049268291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241873493441603228032845527 362810240162404842049268291)
              ·
                refine ⟨544215360243607263073902437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362810240162404842049268291 544215360243607263073902437)
                ·
                  refine ⟨102040380045676361826356707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544215360243607263073902437 102040380045676361826356707)
                  ·
                    refine ⟨153060570068514542739535061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102040380045676361826356707 153060570068514542739535061)
                    ·
                      refine ⟨3587357110980809595457853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153060570068514542739535061 3587357110980809595457853)
                      ·
                        rfl

theorem cell23_6986353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_6986353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986353 prefixEnd_6986353 := by exact prefixLift 6986353
  have htrace : WordTrace (prefixWord ++ tailWord_6986353) baseStart_6986353 baseEnd_6986353 := by
    simpa [prefixWord, tailWord_6986353, baseEnd_6986353] using wordTrace_append hprefix tailTrace_6986353
  have hstable : (prefixWord ++ tailWord_6986353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986353).length < 2 ^ (prefixWord ++ tailWord_6986353).sum := by decide
  have hdescent : baseEnd_6986353 < baseStart_6986353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986397 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_6986397 : Nat := 118140960795 + 6986397 * 2 ^ 59
def prefixEnd_6986397 : Nat := 4983230072969 + 3 ^ 40 * 6986397 * 2
def baseEnd_6986397 : Nat := 3587379704129607423307651

theorem tailTrace_6986397 : CollatzResearch.WordTrace tailWord_6986397 prefixEnd_6986397 3587379704129607423307651 := by
  unfold tailWord_6986397
  simp only [CollatzResearch.WordTrace]
  refine ⟨254814832470484325458669445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169876554980322883639112963 254814832470484325458669445)
  ·
    refine ⟨47777781088215811023500521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254814832470484325458669445 47777781088215811023500521)
    ·
      refine ⟨35833335816161858267625391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47777781088215811023500521 35833335816161858267625391)
      ·
        refine ⟨53750003724242787401438087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35833335816161858267625391 53750003724242787401438087)
        ·
          refine ⟨80625005586364181102157131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53750003724242787401438087 80625005586364181102157131)
          ·
            refine ⟨120937508379546271653235697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80625005586364181102157131 120937508379546271653235697)
            ·
              refine ⟨90703131284659703739926773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120937508379546271653235697 90703131284659703739926773)
              ·
                refine ⟨8503418557936847225618135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90703131284659703739926773 8503418557936847225618135)
                ·
                  refine ⟨12755127836905270838427203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8503418557936847225618135 12755127836905270838427203)
                  ·
                    refine ⟨19132691755357906257640805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12755127836905270838427203 19132691755357906257640805)
                    ·
                      refine ⟨3587379704129607423307651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19132691755357906257640805 3587379704129607423307651)
                      ·
                        rfl

theorem cell23_6986397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_6986397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986397 prefixEnd_6986397 := by exact prefixLift 6986397
  have htrace : WordTrace (prefixWord ++ tailWord_6986397) baseStart_6986397 baseEnd_6986397 := by
    simpa [prefixWord, tailWord_6986397, baseEnd_6986397] using wordTrace_append hprefix tailTrace_6986397
  have hstable : (prefixWord ++ tailWord_6986397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986397).length < 2 ^ (prefixWord ++ tailWord_6986397).sum := by decide
  have hdescent : baseEnd_6986397 < baseStart_6986397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986414 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6986414 : Nat := 118140960795 + 6986414 * 2 ^ 59
def prefixEnd_6986414 : Nat := 4983230072969 + 3 ^ 40 * 6986414 * 2
def baseEnd_6986414 : Nat := 3587388433300733856795073

theorem tailTrace_6986414 : CollatzResearch.WordTrace tailWord_6986414 prefixEnd_6986414 3587388433300733856795073 := by
  unfold tailWord_6986414
  simp only [CollatzResearch.WordTrace]
  refine ⟨31851931563927842170254787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169876968340948491574692197 31851931563927842170254787)
  ·
    refine ⟨47777897345891763255382181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31851931563927842170254787 47777897345891763255382181)
    ·
      refine ⟨8958355752354705610384159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47777897345891763255382181 8958355752354705610384159)
      ·
        refine ⟨13437533628532058415576239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8958355752354705610384159 13437533628532058415576239)
        ·
          refine ⟨20156300442798087623364359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13437533628532058415576239 20156300442798087623364359)
          ·
            refine ⟨30234450664197131435046539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20156300442798087623364359 30234450664197131435046539)
            ·
              refine ⟨45351675996295697152569809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30234450664197131435046539 45351675996295697152569809)
              ·
                refine ⟨34013756997221772864427357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45351675996295697152569809 34013756997221772864427357)
                ·
                  refine ⟨12755158873958164824160259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34013756997221772864427357 12755158873958164824160259)
                  ·
                    refine ⟨19132738310937247236240389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12755158873958164824160259 19132738310937247236240389)
                    ·
                      refine ⟨3587388433300733856795073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19132738310937247236240389 3587388433300733856795073)
                      ·
                        rfl

theorem cell23_6986414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6986414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986414 prefixEnd_6986414 := by exact prefixLift 6986414
  have htrace : WordTrace (prefixWord ++ tailWord_6986414) baseStart_6986414 baseEnd_6986414 := by
    simpa [prefixWord, tailWord_6986414, baseEnd_6986414] using wordTrace_append hprefix tailTrace_6986414
  have hstable : (prefixWord ++ tailWord_6986414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986414).length < 2 ^ (prefixWord ++ tailWord_6986414).sum := by decide
  have hdescent : baseEnd_6986414 < baseStart_6986414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986445 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6986445 : Nat := 118140960795 + 6986445 * 2 ^ 59
def prefixEnd_6986445 : Nat := 4983230072969 + 3 ^ 40 * 6986445 * 2
def baseEnd_6986445 : Nat := 1195801450400341078502477

theorem tailTrace_6986445 : CollatzResearch.WordTrace tailWord_6986445 prefixEnd_6986445 1195801450400341078502477 := by
  unfold tailWord_6986445
  simp only [CollatzResearch.WordTrace]
  refine ⟨254816583174310429656416789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169877722116206953104277859 254816583174310429656416789)
  ·
    refine ⟨11944527336295801390144537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 254816583174310429656416789 11944527336295801390144537)
    ·
      refine ⟨8958395502221851042608403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11944527336295801390144537 8958395502221851042608403)
      ·
        refine ⟨13437593253332776563912605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8958395502221851042608403 13437593253332776563912605)
        ·
          refine ⟨5039097469999791211467227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13437593253332776563912605 5039097469999791211467227)
          ·
            refine ⟨7558646204999686817200841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039097469999791211467227 7558646204999686817200841)
            ·
              refine ⟨5668984653749765112900631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7558646204999686817200841 5668984653749765112900631)
              ·
                refine ⟨8503476980624647669350947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5668984653749765112900631 8503476980624647669350947)
                ·
                  refine ⟨12755215470936971504026421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8503476980624647669350947 12755215470936971504026421)
                  ·
                    refine ⟨1195801450400341078502477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12755215470936971504026421 1195801450400341078502477)
                    ·
                      rfl

theorem cell23_6986445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6986445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986445 prefixEnd_6986445 := by exact prefixLift 6986445
  have htrace : WordTrace (prefixWord ++ tailWord_6986445) baseStart_6986445 baseEnd_6986445 := by
    simpa [prefixWord, tailWord_6986445, baseEnd_6986445] using wordTrace_append hprefix tailTrace_6986445
  have hstable : (prefixWord ++ tailWord_6986445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986445).length < 2 ^ (prefixWord ++ tailWord_6986445).sum := by decide
  have hdescent : baseEnd_6986445 < baseStart_6986445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986480 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 2, 6]
def baseStart_6986480 : Nat := 118140960795 + 6986480 * 2 ^ 59
def prefixEnd_6986480 : Nat := 4983230072969 + 3 ^ 40 * 6986480 * 2
def baseEnd_6986480 : Nat := 1195807441007976866189923

theorem tailTrace_6986480 : CollatzResearch.WordTrace tailWord_6986480 prefixEnd_6986480 1195807441007976866189923 := by
  unfold tailWord_6986480
  simp only [CollatzResearch.WordTrace]
  refine ⟨127408929864591815316970447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169878573152789087089293929 127408929864591815316970447)
  ·
    refine ⟨191113394796887722975455671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127408929864591815316970447 191113394796887722975455671)
    ·
      refine ⟨286670092195331584463183507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191113394796887722975455671 286670092195331584463183507)
      ·
        refine ⟨430005138292997376694775261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286670092195331584463183507 430005138292997376694775261)
        ·
          refine ⟨161251926859874016260540723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430005138292997376694775261 161251926859874016260540723)
          ·
            refine ⟨241877890289811024390811085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161251926859874016260540723 241877890289811024390811085)
            ·
              refine ⟨90704208858679134146554157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241877890289811024390811085 90704208858679134146554157)
              ·
                refine ⟨34014078322004675304957809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90704208858679134146554157 34014078322004675304957809)
                ·
                  refine ⟨25510558741503506478718357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34014078322004675304957809 25510558741503506478718357)
                  ·
                    refine ⟨1195807441007976866189923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25510558741503506478718357 1195807441007976866189923)
                    ·
                      rfl

theorem cell23_6986480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_6986480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986480 prefixEnd_6986480 := by exact prefixLift 6986480
  have htrace : WordTrace (prefixWord ++ tailWord_6986480) baseStart_6986480 baseEnd_6986480 := by
    simpa [prefixWord, tailWord_6986480, baseEnd_6986480] using wordTrace_append hprefix tailTrace_6986480
  have hstable : (prefixWord ++ tailWord_6986480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986480).length < 2 ^ (prefixWord ++ tailWord_6986480).sum := by decide
  have hdescent : baseEnd_6986480 < baseStart_6986480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986481 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 2, 1, 3]
def baseStart_6986481 : Nat := 118140960795 + 6986481 * 2 ^ 59
def prefixEnd_6986481 : Nat := 4983230072969 + 3 ^ 40 * 6986481 * 2
def baseEnd_6986481 : Nat := 3587422836504585094657265

theorem tailTrace_6986481 : CollatzResearch.WordTrace tailWord_6986481 prefixEnd_6986481 3587422836504585094657265 := by
  unfold tailWord_6986481
  simp only [CollatzResearch.WordTrace]
  refine ⟨254817896202180007804727297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169878597468120005203151531 254817896202180007804727297)
  ·
    refine ⟨191113422151635005853545473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254817896202180007804727297 191113422151635005853545473)
    ·
      refine ⟨143335066613726254390159105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191113422151635005853545473 143335066613726254390159105)
      ·
        refine ⟨107501299960294690792619329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143335066613726254390159105 107501299960294690792619329)
        ·
          refine ⟨80625974970221018094464497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107501299960294690792619329 80625974970221018094464497)
          ·
            refine ⟨60469481227665763570848373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80625974970221018094464497 60469481227665763570848373)
            ·
              refine ⟨5669013865093665334767035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60469481227665763570848373 5669013865093665334767035)
              ·
                refine ⟨8503520797640498002150553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669013865093665334767035 8503520797640498002150553)
                ·
                  refine ⟨6377640598230373501612915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8503520797640498002150553 6377640598230373501612915)
                  ·
                    refine ⟨9566460897345560252419373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6377640598230373501612915 9566460897345560252419373)
                    ·
                      refine ⟨3587422836504585094657265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9566460897345560252419373 3587422836504585094657265)
                      ·
                        rfl

theorem cell23_6986481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_6986481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986481 prefixEnd_6986481 := by exact prefixLift 6986481
  have htrace : WordTrace (prefixWord ++ tailWord_6986481) baseStart_6986481 baseEnd_6986481 := by
    simpa [prefixWord, tailWord_6986481, baseEnd_6986481] using wordTrace_append hprefix tailTrace_6986481
  have hstable : (prefixWord ++ tailWord_6986481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986481).length < 2 ^ (prefixWord ++ tailWord_6986481).sum := by decide
  have hdescent : baseEnd_6986481 < baseStart_6986481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986485 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6986485 : Nat := 118140960795 + 6986485 * 2 ^ 59
def prefixEnd_6986485 : Nat := 4983230072969 + 3 ^ 40 * 6986485 * 2
def baseEnd_6986485 : Nat := 3587424890427203079007247

theorem tailTrace_6986485 : CollatzResearch.WordTrace tailWord_6986485 prefixEnd_6986485 3587424890427203079007247 := by
  unfold tailWord_6986485
  simp only [CollatzResearch.WordTrace]
  refine ⟨254818042094165516487872909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169878694729443677658581939 254818042094165516487872909)
  ·
    refine ⟨95556765785312068682952341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254818042094165516487872909 95556765785312068682952341)
    ·
      refine ⟨4479223396186503219513391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95556765785312068682952341 4479223396186503219513391)
      ·
        refine ⟨6718835094279754829270087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4479223396186503219513391 6718835094279754829270087)
        ·
          refine ⟨10078252641419632243905131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6718835094279754829270087 10078252641419632243905131)
          ·
            refine ⟨15117378962129448365857697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10078252641419632243905131 15117378962129448365857697)
            ·
              refine ⟨11338034221597086274393273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15117378962129448365857697 11338034221597086274393273)
              ·
                refine ⟨8503525666197814705794955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11338034221597086274393273 8503525666197814705794955)
                ·
                  refine ⟨12755288499296722058692433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8503525666197814705794955 12755288499296722058692433)
                  ·
                    refine ⟨9566466374472541544019325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12755288499296722058692433 9566466374472541544019325)
                    ·
                      refine ⟨3587424890427203079007247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9566466374472541544019325 3587424890427203079007247)
                      ·
                        rfl

theorem cell23_6986485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6986485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986485 prefixEnd_6986485 := by exact prefixLift 6986485
  have htrace : WordTrace (prefixWord ++ tailWord_6986485) baseStart_6986485 baseEnd_6986485 := by
    simpa [prefixWord, tailWord_6986485, baseEnd_6986485] using wordTrace_append hprefix tailTrace_6986485
  have hstable : (prefixWord ++ tailWord_6986485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986485).length < 2 ^ (prefixWord ++ tailWord_6986485).sum := by decide
  have hdescent : baseEnd_6986485 < baseStart_6986485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986520 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_6986520 : Nat := 118140960795 + 6986520 * 2 ^ 59
def prefixEnd_6986520 : Nat := 4983230072969 + 3 ^ 40 * 6986520 * 2
def baseEnd_6986520 : Nat := 3587442862250110442069585

theorem tailTrace_6986520 : CollatzResearch.WordTrace tailWord_6986520 prefixEnd_6986520 3587442862250110442069585 := by
  unfold tailWord_6986520
  simp only [CollatzResearch.WordTrace]
  refine ⟨127409659324519358732698507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169879545766025811643598009 127409659324519358732698507)
  ·
    refine ⟨191114488986779038099047761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127409659324519358732698507 191114488986779038099047761)
    ·
      refine ⟨143335866740084278574285821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191114488986779038099047761 143335866740084278574285821)
      ·
        refine ⟨53750950027531604465357183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143335866740084278574285821 53750950027531604465357183)
        ·
          refine ⟨80626425041297406698035775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53750950027531604465357183 80626425041297406698035775)
          ·
            refine ⟨120939637561946110047053663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80626425041297406698035775 120939637561946110047053663)
            ·
              refine ⟨181409456342919165070580495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120939637561946110047053663 181409456342919165070580495)
              ·
                refine ⟨272114184514378747605870743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181409456342919165070580495 272114184514378747605870743)
                ·
                  refine ⟨408171276771568121408806115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272114184514378747605870743 408171276771568121408806115)
                  ·
                    refine ⟨612256915157352182113209173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 408171276771568121408806115 612256915157352182113209173)
                    ·
                      refine ⟨3587442862250110442069585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 612256915157352182113209173 3587442862250110442069585)
                      ·
                        rfl

theorem cell23_6986520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_6986520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986520 prefixEnd_6986520 := by exact prefixLift 6986520
  have htrace : WordTrace (prefixWord ++ tailWord_6986520) baseStart_6986520 baseEnd_6986520 := by
    simpa [prefixWord, tailWord_6986520, baseEnd_6986520] using wordTrace_append hprefix tailTrace_6986520
  have hstable : (prefixWord ++ tailWord_6986520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986520).length < 2 ^ (prefixWord ++ tailWord_6986520).sum := by decide
  have hdescent : baseEnd_6986520 < baseStart_6986520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986527 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 7]
def baseStart_6986527 : Nat := 118140960795 + 6986527 * 2 ^ 59
def prefixEnd_6986527 : Nat := 4983230072969 + 3 ^ 40 * 6986527 * 2
def baseEnd_6986527 : Nat := 398605161846076879409117

theorem tailTrace_6986527 : CollatzResearch.WordTrace tailWord_6986527 prefixEnd_6986527 398605161846076879409117 := by
  unfold tailWord_6986527
  simp only [CollatzResearch.WordTrace]
  refine ⟨254819573960013357660901835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169879715973342238440601223 254819573960013357660901835)
  ·
    refine ⟨382229360940020036491352753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254819573960013357660901835 382229360940020036491352753)
    ·
      refine ⟨286672020705015027368514565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382229360940020036491352753 286672020705015027368514565)
      ·
        refine ⟨53751003882190317631596481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286672020705015027368514565 53751003882190317631596481)
        ·
          refine ⟨40313252911642738223697361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53751003882190317631596481 40313252911642738223697361)
          ·
            refine ⟨30234939683732053667773021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40313252911642738223697361 30234939683732053667773021)
            ·
              refine ⟨11338102381399520125414883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30234939683732053667773021 11338102381399520125414883)
              ·
                refine ⟨17007153572099280188122325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11338102381399520125414883 17007153572099280188122325)
                ·
                  refine ⟨398605161846076879409117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17007153572099280188122325 398605161846076879409117)
                  ·
                    rfl

theorem cell23_6986527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 7].length) (baseStart_6986527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986527 prefixEnd_6986527 := by exact prefixLift 6986527
  have htrace : WordTrace (prefixWord ++ tailWord_6986527) baseStart_6986527 baseEnd_6986527 := by
    simpa [prefixWord, tailWord_6986527, baseEnd_6986527] using wordTrace_append hprefix tailTrace_6986527
  have hstable : (prefixWord ++ tailWord_6986527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986527).length < 2 ^ (prefixWord ++ tailWord_6986527).sum := by decide
  have hdescent : baseEnd_6986527 < baseStart_6986527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986604 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_6986604 : Nat := 118140960795 + 6986604 * 2 ^ 59
def prefixEnd_6986604 : Nat := 4983230072969 + 3 ^ 40 * 6986604 * 2
def baseEnd_6986604 : Nat := 1195828664875029371139733

theorem tailTrace_6986604 : CollatzResearch.WordTrace tailWord_6986604 prefixEnd_6986604 1195828664875029371139733 := by
  unfold tailWord_6986604
  simp only [CollatzResearch.WordTrace]
  refine ⟨127411191190367199905727433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169881588253822933207636577 127411191190367199905727433)
  ·
    refine ⟨95558393392775399929295575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127411191190367199905727433 95558393392775399929295575)
    ·
      refine ⟨143337590089163099893943363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95558393392775399929295575 143337590089163099893943363)
      ·
        refine ⟨215006385133744649840915045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143337590089163099893943363 215006385133744649840915045)
        ·
          refine ⟨40313697212577121845171571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215006385133744649840915045 40313697212577121845171571)
          ·
            refine ⟨60470545818865682767757357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40313697212577121845171571 60470545818865682767757357)
            ·
              refine ⟨22676454682074631037909009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60470545818865682767757357 22676454682074631037909009)
              ·
                refine ⟨17007341011555973278431757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22676454682074631037909009 17007341011555973278431757)
                ·
                  refine ⟨6377752879333489979411909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17007341011555973278431757 6377752879333489979411909)
                  ·
                    refine ⟨1195828664875029371139733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6377752879333489979411909 1195828664875029371139733)
                    ·
                      rfl

theorem cell23_6986604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_6986604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986604 prefixEnd_6986604 := by exact prefixLift 6986604
  have htrace : WordTrace (prefixWord ++ tailWord_6986604) baseStart_6986604 baseEnd_6986604 := by
    simpa [prefixWord, tailWord_6986604, baseEnd_6986604] using wordTrace_append hprefix tailTrace_6986604
  have hstable : (prefixWord ++ tailWord_6986604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986604).length < 2 ^ (prefixWord ++ tailWord_6986604).sum := by decide
  have hdescent : baseEnd_6986604 < baseStart_6986604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986621 : List Nat := [1, 4, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_6986621 : Nat := 118140960795 + 6986621 * 2 ^ 59
def prefixEnd_6986621 : Nat := 4983230072969 + 3 ^ 40 * 6986621 * 2
def baseEnd_6986621 : Nat := 1195831574598738182302207

theorem tailTrace_6986621 : CollatzResearch.WordTrace tailWord_6986621 prefixEnd_6986621 1195831574598738182302207 := by
  unfold tailWord_6986621
  simp only [CollatzResearch.WordTrace]
  refine ⟨254823002421672811714823717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169882001614448541143215811 254823002421672811714823717)
  ·
    refine ⟨47779312954063652196529447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254823002421672811714823717 47779312954063652196529447)
    ·
      refine ⟨71668969431095478294794171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47779312954063652196529447 71668969431095478294794171)
      ·
        refine ⟨107503454146643217442191257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71668969431095478294794171 107503454146643217442191257)
        ·
          refine ⟨80627590609982413081643443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107503454146643217442191257 80627590609982413081643443)
          ·
            refine ⟨120941385914973619622465165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80627590609982413081643443 120941385914973619622465165)
            ·
              refine ⟨45353019718115107358424437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120941385914973619622465165 45353019718115107358424437)
              ·
                refine ⟨4251845598573291314852291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45353019718115107358424437 4251845598573291314852291)
                ·
                  refine ⟨6377768397859936972278437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251845598573291314852291 6377768397859936972278437)
                  ·
                    refine ⟨1195831574598738182302207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6377768397859936972278437 1195831574598738182302207)
                    ·
                      rfl

theorem cell23_6986621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_6986621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986621 prefixEnd_6986621 := by exact prefixLift 6986621
  have htrace : WordTrace (prefixWord ++ tailWord_6986621) baseStart_6986621 baseEnd_6986621 := by
    simpa [prefixWord, tailWord_6986621, baseEnd_6986621] using wordTrace_append hprefix tailTrace_6986621
  have hstable : (prefixWord ++ tailWord_6986621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986621).length < 2 ^ (prefixWord ++ tailWord_6986621).sum := by decide
  have hdescent : baseEnd_6986621 < baseStart_6986621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986634 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 8]
def baseStart_6986634 : Nat := 118140960795 + 6986634 * 2 ^ 59
def prefixEnd_6986634 : Nat := 4983230072969 + 3 ^ 40 * 6986634 * 2
def baseEnd_6986634 : Nat := 398611266560524777338229

theorem tailTrace_6986634 : CollatzResearch.WordTrace tailWord_6986634 prefixEnd_6986634 398611266560524777338229 := by
  unfold tailWord_6986634
  simp only [CollatzResearch.WordTrace]
  refine ⟨63705869142656428733761739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169882317713750476623364637 63705869142656428733761739)
  ·
    refine ⟨95558803713984643100642609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63705869142656428733761739 95558803713984643100642609)
    ·
      refine ⟨71669102785488482325481957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95558803713984643100642609 71669102785488482325481957)
      ·
        refine ⟨13437956772279090436027867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71669102785488482325481957 13437956772279090436027867)
        ·
          refine ⟨20156935158418635654041801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13437956772279090436027867 20156935158418635654041801)
          ·
            refine ⟨15117701368813976740531351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20156935158418635654041801 15117701368813976740531351)
            ·
              refine ⟨22676552053220965110797027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15117701368813976740531351 22676552053220965110797027)
              ·
                refine ⟨34014828079831447666195541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22676552053220965110797027 34014828079831447666195541)
                ·
                  refine ⟨398611266560524777338229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34014828079831447666195541 398611266560524777338229)
                  ·
                    rfl

theorem cell23_6986634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_6986634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986634 prefixEnd_6986634 := by exact prefixLift 6986634
  have htrace : WordTrace (prefixWord ++ tailWord_6986634) baseStart_6986634 baseEnd_6986634 := by
    simpa [prefixWord, tailWord_6986634, baseEnd_6986634] using wordTrace_append hprefix tailTrace_6986634
  have hstable : (prefixWord ++ tailWord_6986634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986634).length < 2 ^ (prefixWord ++ tailWord_6986634).sum := by decide
  have hdescent : baseEnd_6986634 < baseStart_6986634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986697 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_6986697 : Nat := 118140960795 + 6986697 * 2 ^ 59
def prefixEnd_6986697 : Nat := 4983230072969 + 3 ^ 40 * 6986697 * 2
def baseEnd_6986697 : Nat := 3587533748325956249556271

theorem tailTrace_6986697 : CollatzResearch.WordTrace tailWord_6986697 prefixEnd_6986697 3587533748325956249556271 := by
  unfold tailWord_6986697
  simp only [CollatzResearch.WordTrace]
  refine ⟨254825774369397476694590345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169883849579598317796393563 254825774369397476694590345)
  ·
    refine ⟨191119330777048107520942759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254825774369397476694590345 191119330777048107520942759)
    ·
      refine ⟨286678996165572161281414139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191119330777048107520942759 286678996165572161281414139)
      ·
        refine ⟨430018494248358241922121209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286678996165572161281414139 430018494248358241922121209)
        ·
          refine ⟨322513870686268681441590907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430018494248358241922121209 322513870686268681441590907)
          ·
            refine ⟨483770806029403022162386361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322513870686268681441590907 483770806029403022162386361)
            ·
              refine ⟨362828104522052266621789771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483770806029403022162386361 362828104522052266621789771)
              ·
                refine ⟨544242156783078399932684657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362828104522052266621789771 544242156783078399932684657)
                ·
                  refine ⟨408181617587308799949513493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544242156783078399932684657 408181617587308799949513493)
                  ·
                    refine ⟨19133513324405099997633445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 408181617587308799949513493 19133513324405099997633445)
                    ·
                      refine ⟨3587533748325956249556271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19133513324405099997633445 3587533748325956249556271)
                      ·
                        rfl

theorem cell23_6986697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_6986697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986697 prefixEnd_6986697 := by exact prefixLift 6986697
  have htrace : WordTrace (prefixWord ++ tailWord_6986697) baseStart_6986697 baseEnd_6986697 := by
    simpa [prefixWord, tailWord_6986697, baseEnd_6986697] using wordTrace_append hprefix tailTrace_6986697
  have hstable : (prefixWord ++ tailWord_6986697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986697).length < 2 ^ (prefixWord ++ tailWord_6986697).sum := by decide
  have hdescent : baseEnd_6986697 < baseStart_6986697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986704 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 3]
def baseStart_6986704 : Nat := 118140960795 + 6986704 * 2 ^ 59
def prefixEnd_6986704 : Nat := 4983230072969 + 3 ^ 40 * 6986704 * 2
def baseEnd_6986704 : Nat := 3587537342690537722168739

theorem tailTrace_6986704 : CollatzResearch.WordTrace tailWord_6986704 prefixEnd_6986704 3587537342690537722168739 := by
  unfold tailWord_6986704
  simp only [CollatzResearch.WordTrace]
  refine ⟨127413014840186058445047583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169884019786914744593396777 127413014840186058445047583)
  ·
    refine ⟨191119522260279087667571375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127413014840186058445047583 191119522260279087667571375)
    ·
      refine ⟨286679283390418631501357063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191119522260279087667571375 286679283390418631501357063)
      ·
        refine ⟨430018925085627947252035595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286679283390418631501357063 430018925085627947252035595)
        ·
          refine ⟨645028387628441920878053393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430018925085627947252035595 645028387628441920878053393)
          ·
            refine ⟨483771290721331440658540045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645028387628441920878053393 483771290721331440658540045)
            ·
              refine ⟨181414234020499290246952517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483771290721331440658540045 181414234020499290246952517)
              ·
                refine ⟨34015168878843616921303597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181414234020499290246952517 34015168878843616921303597)
                ·
                  refine ⟨12755688329566356345488849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34015168878843616921303597 12755688329566356345488849)
                  ·
                    refine ⟨9566766247174767259116637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12755688329566356345488849 9566766247174767259116637)
                    ·
                      refine ⟨3587537342690537722168739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9566766247174767259116637 3587537342690537722168739)
                      ·
                        rfl

theorem cell23_6986704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_6986704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986704 prefixEnd_6986704 := by exact prefixLift 6986704
  have htrace : WordTrace (prefixWord ++ tailWord_6986704) baseStart_6986704 baseEnd_6986704 := by
    simpa [prefixWord, tailWord_6986704, baseEnd_6986704] using wordTrace_append hprefix tailTrace_6986704
  have hstable : (prefixWord ++ tailWord_6986704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986704).length < 2 ^ (prefixWord ++ tailWord_6986704).sum := by decide
  have hdescent : baseEnd_6986704 < baseStart_6986704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986714 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_6986714 : Nat := 118140960795 + 6986714 * 2 ^ 59
def prefixEnd_6986714 : Nat := 4983230072969 + 3 ^ 40 * 6986714 * 2
def baseEnd_6986714 : Nat := 3587542477497082683043693

theorem tailTrace_6986714 : CollatzResearch.WordTrace tailWord_6986714 prefixEnd_6986714 3587542477497082683043693 := by
  unfold tailWord_6986714
  simp only [CollatzResearch.WordTrace]
  refine ⟨63706598602583972149489799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169884262940223925731972797 63706598602583972149489799)
  ·
    refine ⟨95559897903875958224234699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63706598602583972149489799 95559897903875958224234699)
    ·
      refine ⟨143339846855813937336352049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95559897903875958224234699 143339846855813937336352049)
      ·
        refine ⟨107504885141860453002264037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143339846855813937336352049 107504885141860453002264037)
        ·
          refine ⟨20157165964098834937924507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107504885141860453002264037 20157165964098834937924507)
          ·
            refine ⟨30235748946148252406886761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20157165964098834937924507 30235748946148252406886761)
            ·
              refine ⟨22676811709611189305165071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30235748946148252406886761 22676811709611189305165071)
              ·
                refine ⟨34015217564416783957747607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22676811709611189305165071 34015217564416783957747607)
                ·
                  refine ⟨51022826346625175936621411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34015217564416783957747607 51022826346625175936621411)
                  ·
                    refine ⟨76534239519937763904932117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51022826346625175936621411 76534239519937763904932117)
                    ·
                      refine ⟨3587542477497082683043693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76534239519937763904932117 3587542477497082683043693)
                      ·
                        rfl

theorem cell23_6986714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_6986714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986714 prefixEnd_6986714 := by exact prefixLift 6986714
  have htrace : WordTrace (prefixWord ++ tailWord_6986714) baseStart_6986714 baseEnd_6986714 := by
    simpa [prefixWord, tailWord_6986714, baseEnd_6986714] using wordTrace_append hprefix tailTrace_6986714
  have hstable : (prefixWord ++ tailWord_6986714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986714).length < 2 ^ (prefixWord ++ tailWord_6986714).sum := by decide
  have hdescent : baseEnd_6986714 < baseStart_6986714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986741 : List Nat := [1, 3, 5, 2, 1, 11]
def baseStart_6986741 : Nat := 118140960795 + 6986741 * 2 ^ 59
def prefixEnd_6986741 : Nat := 4983230072969 + 3 ^ 40 * 6986741 * 2
def baseEnd_6986741 : Nat := 14763606343517506491383

theorem tailTrace_6986741 : CollatzResearch.WordTrace tailWord_6986741 prefixEnd_6986741 14763606343517506491383 := by
  unfold tailWord_6986741
  simp only [CollatzResearch.WordTrace]
  refine ⟨254827379181238072209192077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169884919454158714806128051 254827379181238072209192077)
  ·
    refine ⟨95560267192964277078447029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254827379181238072209192077 95560267192964277078447029)
    ·
      refine ⟨8958775049340400976104409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95560267192964277078447029 8958775049340400976104409)
      ·
        refine ⟨6719081287005300732078307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8958775049340400976104409 6719081287005300732078307)
        ·
          refine ⟨10078621930507951098117461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6719081287005300732078307 10078621930507951098117461)
          ·
            refine ⟨14763606343517506491383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10078621930507951098117461 14763606343517506491383)
            ·
              rfl

theorem cell23_6986741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 11].length) (baseStart_6986741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986741 prefixEnd_6986741 := by exact prefixLift 6986741
  have htrace : WordTrace (prefixWord ++ tailWord_6986741) baseStart_6986741 baseEnd_6986741 := by
    simpa [prefixWord, tailWord_6986741, baseEnd_6986741] using wordTrace_append hprefix tailTrace_6986741
  have hstable : (prefixWord ++ tailWord_6986741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986741).length < 2 ^ (prefixWord ++ tailWord_6986741).sum := by decide
  have hdescent : baseEnd_6986741 < baseStart_6986741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986778 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2]
def baseStart_6986778 : Nat := 118140960795 + 6986778 * 2 ^ 59
def prefixEnd_6986778 : Nat := 4983230072969 + 3 ^ 40 * 6986778 * 2
def baseEnd_6986778 : Nat := 3587575340258970432643399

theorem tailTrace_6986778 : CollatzResearch.WordTrace tailWord_6986778 prefixEnd_6986778 3587575340258970432643399 := by
  unfold tailWord_6986778
  simp only [CollatzResearch.WordTrace]
  refine ⟨63707182170526006882072247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169885819121402685018859325 63707182170526006882072247)
  ·
    refine ⟨95560773255789010323108371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63707182170526006882072247 95560773255789010323108371)
    ·
      refine ⟨143341159883683515484662557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95560773255789010323108371 143341159883683515484662557)
      ·
        refine ⟨53752934956381318306748459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143341159883683515484662557 53752934956381318306748459)
        ·
          refine ⟨80629402434571977460122689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53752934956381318306748459 80629402434571977460122689)
          ·
            refine ⟨60472051825928983095092017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80629402434571977460122689 60472051825928983095092017)
            ·
              refine ⟨45354038869446737321319013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60472051825928983095092017 45354038869446737321319013)
              ·
                refine ⟨8503882288021263247747315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45354038869446737321319013 8503882288021263247747315)
                ·
                  refine ⟨12755823432031894871620973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8503882288021263247747315 12755823432031894871620973)
                  ·
                    refine ⟨4783433787011960576857865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12755823432031894871620973 4783433787011960576857865)
                    ·
                      refine ⟨3587575340258970432643399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4783433787011960576857865 3587575340258970432643399)
                      ·
                        rfl

theorem cell23_6986778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_6986778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986778 prefixEnd_6986778 := by exact prefixLift 6986778
  have htrace : WordTrace (prefixWord ++ tailWord_6986778) baseStart_6986778 baseEnd_6986778 := by
    simpa [prefixWord, tailWord_6986778, baseEnd_6986778] using wordTrace_append hprefix tailTrace_6986778
  have hstable : (prefixWord ++ tailWord_6986778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986778).length < 2 ^ (prefixWord ++ tailWord_6986778).sum := by decide
  have hdescent : baseEnd_6986778 < baseStart_6986778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986851 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 1, 7, 2]
def baseStart_6986851 : Nat := 118140960795 + 6986851 * 2 ^ 59
def prefixEnd_6986851 : Nat := 4983230072969 + 3 ^ 40 * 6986851 * 2
def baseEnd_6986851 : Nat := 3587612824346748647030563

theorem tailTrace_6986851 : CollatzResearch.WordTrace tailWord_6986851 prefixEnd_6986851 3587612824346748647030563 := by
  unfold tailWord_6986851
  simp only [CollatzResearch.WordTrace]
  refine ⟨254831391210839560995696407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169887594140559707330464271 254831391210839560995696407)
  ·
    refine ⟨382247086816259341493544611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254831391210839560995696407 382247086816259341493544611)
    ·
      refine ⟨573370630224389012240316917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382247086816259341493544611 573370630224389012240316917)
      ·
        refine ⟨53753496583536469897529711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 573370630224389012240316917 53753496583536469897529711)
        ·
          refine ⟨80630244875304704846294567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53753496583536469897529711 80630244875304704846294567)
          ·
            refine ⟨120945367312957057269441851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80630244875304704846294567 120945367312957057269441851)
            ·
              refine ⟨181418050969435585904162777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120945367312957057269441851 181418050969435585904162777)
              ·
                refine ⟨136063538227076689428122083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181418050969435585904162777 136063538227076689428122083)
                ·
                  refine ⟨204095307340615034142183125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136063538227076689428122083 204095307340615034142183125)
                  ·
                    refine ⟨4783483765795664862707417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 204095307340615034142183125 4783483765795664862707417)
                    ·
                      refine ⟨3587612824346748647030563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4783483765795664862707417 3587612824346748647030563)
                      ·
                        rfl

theorem cell23_6986851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_6986851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986851 prefixEnd_6986851 := by exact prefixLift 6986851
  have htrace : WordTrace (prefixWord ++ tailWord_6986851) baseStart_6986851 baseEnd_6986851 := by
    simpa [prefixWord, tailWord_6986851, baseEnd_6986851] using wordTrace_append hprefix tailTrace_6986851
  have hstable : (prefixWord ++ tailWord_6986851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986851).length < 2 ^ (prefixWord ++ tailWord_6986851).sum := by decide
  have hdescent : baseEnd_6986851 < baseStart_6986851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986861 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_6986861 : Nat := 118140960795 + 6986861 * 2 ^ 59
def prefixEnd_6986861 : Nat := 4983230072969 + 3 ^ 40 * 6986861 * 2
def baseEnd_6986861 : Nat := 1195872653051097869301839

theorem tailTrace_6986861 : CollatzResearch.WordTrace tailWord_6986861 prefixEnd_6986861 1195872653051097869301839 := by
  unfold tailWord_6986861
  simp only [CollatzResearch.WordTrace]
  refine ⟨254831755940803332703560437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169887837293868888469040291 254831755940803332703560437)
  ·
    refine ⟨23890477119450312440958791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254831755940803332703560437 23890477119450312440958791)
    ·
      refine ⟨35835715679175468661438187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23890477119450312440958791 35835715679175468661438187)
      ·
        refine ⟨53753573518763202992157281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35835715679175468661438187 53753573518763202992157281)
        ·
          refine ⟨40315180139072402244117961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53753573518763202992157281 40315180139072402244117961)
          ·
            refine ⟨30236385104304301683088471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40315180139072402244117961 30236385104304301683088471)
            ·
              refine ⟨45354577656456452524632707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30236385104304301683088471 45354577656456452524632707)
              ·
                refine ⟨68031866484684678786949061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45354577656456452524632707 68031866484684678786949061)
                ·
                  refine ⟨12755974965878377272552949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68031866484684678786949061 12755974965878377272552949)
                  ·
                    refine ⟨1195872653051097869301839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12755974965878377272552949 1195872653051097869301839)
                    ·
                      rfl

theorem cell23_6986861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_6986861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986861 prefixEnd_6986861 := by exact prefixLift 6986861
  have htrace : WordTrace (prefixWord ++ tailWord_6986861) baseStart_6986861 baseEnd_6986861 := by
    simpa [prefixWord, tailWord_6986861, baseEnd_6986861] using wordTrace_append hprefix tailTrace_6986861
  have hstable : (prefixWord ++ tailWord_6986861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986861).length < 2 ^ (prefixWord ++ tailWord_6986861).sum := by decide
  have hdescent : baseEnd_6986861 < baseStart_6986861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986891 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 3, 4]
def baseStart_6986891 : Nat := 118140960795 + 6986891 * 2 ^ 59
def prefixEnd_6986891 : Nat := 4983230072969 + 3 ^ 40 * 6986891 * 2
def baseEnd_6986891 : Nat := 1195877787857642830176793

theorem tailTrace_6986891 : CollatzResearch.WordTrace tailWord_6986891 prefixEnd_6986891 1195877787857642830176793 := by
  unfold tailWord_6986891
  simp only [CollatzResearch.WordTrace]
  refine ⟨254832850130694647827152527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169888566753796431884768351 254832850130694647827152527)
  ·
    refine ⟨382249275196041971740728791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254832850130694647827152527 382249275196041971740728791)
    ·
      refine ⟨573373912794062957611093187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382249275196041971740728791 573373912794062957611093187)
      ·
        refine ⟨860060869191094436416639781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573373912794062957611093187 860060869191094436416639781)
        ·
          refine ⟨161261412973330206828119959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 860060869191094436416639781 161261412973330206828119959)
          ·
            refine ⟨241892119459995310242179939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161261412973330206828119959 241892119459995310242179939)
            ·
              refine ⟨362838179189992965363269909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241892119459995310242179939 362838179189992965363269909)
              ·
                refine ⟨17008039649530920251403277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 362838179189992965363269909 17008039649530920251403277)
                ·
                  refine ⟨6378014868574095094276229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17008039649530920251403277 6378014868574095094276229)
                  ·
                    refine ⟨1195877787857642830176793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6378014868574095094276229 1195877787857642830176793)
                    ·
                      rfl

theorem cell23_6986891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 4].length) (baseStart_6986891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986891 prefixEnd_6986891 := by exact prefixLift 6986891
  have htrace : WordTrace (prefixWord ++ tailWord_6986891) baseStart_6986891 baseEnd_6986891 := by
    simpa [prefixWord, tailWord_6986891, baseEnd_6986891] using wordTrace_append hprefix tailTrace_6986891
  have hstable : (prefixWord ++ tailWord_6986891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986891).length < 2 ^ (prefixWord ++ tailWord_6986891).sum := by decide
  have hdescent : baseEnd_6986891 < baseStart_6986891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6986898 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6986898 : Nat := 118140960795 + 6986898 * 2 ^ 59
def prefixEnd_6986898 : Nat := 4983230072969 + 3 ^ 40 * 6986898 * 2
def baseEnd_6986898 : Nat := 3587636957937509963142847

theorem tailTrace_6986898 : CollatzResearch.WordTrace tailWord_6986898 prefixEnd_6986898 3587636957937509963142847 := by
  unfold tailWord_6986898
  simp only [CollatzResearch.WordTrace]
  refine ⟨63708276360417322005664337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169888736961112858681771565 63708276360417322005664337)
  ·
    refine ⟨47781207270312991504248253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63708276360417322005664337 47781207270312991504248253)
    ·
      refine ⟨17917952726367371814093095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47781207270312991504248253 17917952726367371814093095)
      ·
        refine ⟨26876929089551057721139643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17917952726367371814093095 26876929089551057721139643)
        ·
          refine ⟨40315393634326586581709465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26876929089551057721139643 40315393634326586581709465)
          ·
            refine ⟨30236545225744939936282099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40315393634326586581709465 30236545225744939936282099)
            ·
              refine ⟨45354817838617409904423149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30236545225744939936282099 45354817838617409904423149)
              ·
                refine ⟨17008056689481528714158681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45354817838617409904423149 17008056689481528714158681)
                ·
                  refine ⟨12756042517111146535619011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17008056689481528714158681 12756042517111146535619011)
                  ·
                    refine ⟨19134063775666719803428517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12756042517111146535619011 19134063775666719803428517)
                    ·
                      refine ⟨3587636957937509963142847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19134063775666719803428517 3587636957937509963142847)
                      ·
                        rfl

theorem cell23_6986898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6986898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6986898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6986898 prefixEnd_6986898 := by exact prefixLift 6986898
  have htrace : WordTrace (prefixWord ++ tailWord_6986898) baseStart_6986898 baseEnd_6986898 := by
    simpa [prefixWord, tailWord_6986898, baseEnd_6986898] using wordTrace_append hprefix tailTrace_6986898
  have hstable : (prefixWord ++ tailWord_6986898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6986898).length < 2 ^ (prefixWord ++ tailWord_6986898).sum := by decide
  have hdescent : baseEnd_6986898 < baseStart_6986898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6986898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987001 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_6987001 : Nat := 118140960795 + 6987001 * 2 ^ 59
def prefixEnd_6987001 : Nat := 4983230072969 + 3 ^ 40 * 6987001 * 2
def baseEnd_6987001 : Nat := 3587689846444923060154873

theorem tailTrace_6987001 : CollatzResearch.WordTrace tailWord_6987001 prefixEnd_6987001 3587689846444923060154873 := by
  unfold tailWord_6987001
  simp only [CollatzResearch.WordTrace]
  refine ⟨254836862160296136613656857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169891241440197424409104571 254836862160296136613656857)
  ·
    refine ⟨191127646620222102460242643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254836862160296136613656857 191127646620222102460242643)
    ·
      refine ⟨286691469930333153690363965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191127646620222102460242643 286691469930333153690363965)
      ·
        refine ⟨107509301223874932633886487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286691469930333153690363965 107509301223874932633886487)
        ·
          refine ⟨161263951835812398950829731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107509301223874932633886487 161263951835812398950829731)
          ·
            refine ⟨241895927753718598426244597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161263951835812398950829731 241895927753718598426244597)
            ·
              refine ⟨22677743226911118602460431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241895927753718598426244597 22677743226911118602460431)
              ·
                refine ⟨34016614840366677903690647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22677743226911118602460431 34016614840366677903690647)
                ·
                  refine ⟨51024922260550016855535971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34016614840366677903690647 51024922260550016855535971)
                  ·
                    refine ⟨76537383390825025283303957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51024922260550016855535971 76537383390825025283303957)
                    ·
                      refine ⟨3587689846444923060154873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76537383390825025283303957 3587689846444923060154873)
                      ·
                        rfl

theorem cell23_6987001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_6987001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987001 prefixEnd_6987001 := by exact prefixLift 6987001
  have htrace : WordTrace (prefixWord ++ tailWord_6987001) baseStart_6987001 baseEnd_6987001 := by
    simpa [prefixWord, tailWord_6987001, baseEnd_6987001] using wordTrace_append hprefix tailTrace_6987001
  have hstable : (prefixWord ++ tailWord_6987001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987001).length < 2 ^ (prefixWord ++ tailWord_6987001).sum := by decide
  have hdescent : baseEnd_6987001 < baseStart_6987001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987011 : List Nat := [1, 1, 1, 3, 2, 5, 1, 9]
def baseStart_6987011 : Nat := 118140960795 + 6987011 * 2 ^ 59
def prefixEnd_6987011 : Nat := 4983230072969 + 3 ^ 40 * 6987011 * 2
def baseEnd_6987011 : Nat := 132877591898202519297401

theorem tailTrace_6987011 : CollatzResearch.WordTrace tailWord_6987011 prefixEnd_6987011 132877591898202519297401 := by
  unfold tailWord_6987011
  simp only [CollatzResearch.WordTrace]
  refine ⟨254837226890259908321520887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169891484593506605547680591 254837226890259908321520887)
  ·
    refine ⟨382255840335389862482281331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254837226890259908321520887 382255840335389862482281331)
    ·
      refine ⟨573383760503084793723421997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382255840335389862482281331 573383760503084793723421997)
      ·
        refine ⟨215018910188656797646283249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 573383760503084793723421997 215018910188656797646283249)
        ·
          refine ⟨161264182641492598234712437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215018910188656797646283249 161264182641492598234712437)
          ·
            refine ⟨15118517122639931084504291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161264182641492598234712437 15118517122639931084504291)
            ·
              refine ⟨22677775683959896626756437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15118517122639931084504291 22677775683959896626756437)
              ·
                refine ⟨132877591898202519297401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22677775683959896626756437 132877591898202519297401)
                ·
                  rfl

theorem cell23_6987011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 9].length) (baseStart_6987011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987011 prefixEnd_6987011 := by exact prefixLift 6987011
  have htrace : WordTrace (prefixWord ++ tailWord_6987011) baseStart_6987011 baseEnd_6987011 := by
    simpa [prefixWord, tailWord_6987011, baseEnd_6987011] using wordTrace_append hprefix tailTrace_6987011
  have hstable : (prefixWord ++ tailWord_6987011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987011).length < 2 ^ (prefixWord ++ tailWord_6987011).sum := by decide
  have hdescent : baseEnd_6987011 < baseStart_6987011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987016 : List Nat := [2, 1, 3, 2, 5, 1, 1, 3, 1, 1, 3]
def baseStart_6987016 : Nat := 118140960795 + 6987016 * 2 ^ 59
def prefixEnd_6987016 : Nat := 4983230072969 + 3 ^ 40 * 6987016 * 2
def baseEnd_6987016 : Nat := 3587697548654740501467305

theorem tailTrace_6987016 : CollatzResearch.WordTrace tailWord_6987016 prefixEnd_6987016 3587697548654740501467305 := by
  unfold tailWord_6987016
  simp only [CollatzResearch.WordTrace]
  refine ⟨127418704627620897087726451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169891606170161196116968601 127418704627620897087726451)
  ·
    refine ⟨191128056941431345631589677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127418704627620897087726451 191128056941431345631589677)
    ·
      refine ⟨71673021353036754611846129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191128056941431345631589677 71673021353036754611846129)
      ·
        refine ⟨53754766014777565958884597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71673021353036754611846129 53754766014777565958884597)
        ·
          refine ⟨5039509313885396808645431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53754766014777565958884597 5039509313885396808645431)
          ·
            refine ⟨7559263970828095212968147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5039509313885396808645431 7559263970828095212968147)
            ·
              refine ⟨11338895956242142819452221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7559263970828095212968147 11338895956242142819452221)
              ·
                refine ⟨4252085983590803557294583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11338895956242142819452221 4252085983590803557294583)
                ·
                  refine ⟨6378128975386205335941875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4252085983590803557294583 6378128975386205335941875)
                  ·
                    refine ⟨9567193463079308003912813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6378128975386205335941875 9567193463079308003912813)
                    ·
                      refine ⟨3587697548654740501467305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9567193463079308003912813 3587697548654740501467305)
                      ·
                        rfl

theorem cell23_6987016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_6987016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987016 prefixEnd_6987016 := by exact prefixLift 6987016
  have htrace : WordTrace (prefixWord ++ tailWord_6987016) baseStart_6987016 baseEnd_6987016 := by
    simpa [prefixWord, tailWord_6987016, baseEnd_6987016] using wordTrace_append hprefix tailTrace_6987016
  have hstable : (prefixWord ++ tailWord_6987016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987016).length < 2 ^ (prefixWord ++ tailWord_6987016).sum := by decide
  have hdescent : baseEnd_6987016 < baseStart_6987016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987039 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 3, 2, 2]
def baseStart_6987039 : Nat := 118140960795 + 6987039 * 2 ^ 59
def prefixEnd_6987039 : Nat := 4983230072969 + 3 ^ 40 * 6987039 * 2
def baseEnd_6987039 : Nat := 3587709358709793911479699

theorem tailTrace_6987039 : CollatzResearch.WordTrace tailWord_6987039 prefixEnd_6987039 3587709358709793911479699 := by
  unfold tailWord_6987039
  simp only [CollatzResearch.WordTrace]
  refine ⟨254838248134158469103540171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169892165422772312735693447 254838248134158469103540171)
  ·
    refine ⟨382257372201237703655310257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254838248134158469103540171 382257372201237703655310257)
    ·
      refine ⟨286693029150928277741482693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382257372201237703655310257 286693029150928277741482693)
      ·
        refine ⟨53754942965799052076528005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286693029150928277741482693 53754942965799052076528005)
        ·
          refine ⟨10079051806087322264349001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53754942965799052076528005 10079051806087322264349001)
          ·
            refine ⟨7559288854565491698261751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10079051806087322264349001 7559288854565491698261751)
            ·
              refine ⟨11338933281848237547392627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7559288854565491698261751 11338933281848237547392627)
              ·
                refine ⟨17008399922772356321088941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11338933281848237547392627 17008399922772356321088941)
                ·
                  refine ⟨6378149971039633620408353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17008399922772356321088941 6378149971039633620408353)
                  ·
                    refine ⟨4783612478279725215306265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6378149971039633620408353 4783612478279725215306265)
                    ·
                      refine ⟨3587709358709793911479699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4783612478279725215306265 3587709358709793911479699)
                      ·
                        rfl

theorem cell23_6987039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_6987039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987039 prefixEnd_6987039 := by exact prefixLift 6987039
  have htrace : WordTrace (prefixWord ++ tailWord_6987039) baseStart_6987039 baseEnd_6987039 := by
    simpa [prefixWord, tailWord_6987039, baseEnd_6987039] using wordTrace_append hprefix tailTrace_6987039
  have hstable : (prefixWord ++ tailWord_6987039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987039).length < 2 ^ (prefixWord ++ tailWord_6987039).sum := by decide
  have hdescent : baseEnd_6987039 < baseStart_6987039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987041 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 2, 7]
def baseStart_6987041 : Nat := 118140960795 + 6987041 * 2 ^ 59
def prefixEnd_6987041 : Nat := 4983230072969 + 3 ^ 40 * 6987041 * 2
def baseEnd_6987041 : Nat := 1195903461890367634551563

theorem tailTrace_6987041 : CollatzResearch.WordTrace tailWord_6987041 prefixEnd_6987041 1195903461890367634551563 := by
  unfold tailWord_6987041
  simp only [CollatzResearch.WordTrace]
  refine ⟨254838321080151223445112977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169892214053434148963408651 254838321080151223445112977)
  ·
    refine ⟨191128740810113417583834733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254838321080151223445112977 191128740810113417583834733)
    ·
      refine ⟨71673277803792531593938025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191128740810113417583834733 71673277803792531593938025)
      ·
        refine ⟨53754958352844398695453519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71673277803792531593938025 53754958352844398695453519)
        ·
          refine ⟨80632437529266598043180279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53754958352844398695453519 80632437529266598043180279)
          ·
            refine ⟨120948656293899897064770419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80632437529266598043180279 120948656293899897064770419)
            ·
              refine ⟨181422984440849845597155629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120948656293899897064770419 181422984440849845597155629)
              ·
                refine ⟨68033619165318692098933361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181422984440849845597155629 68033619165318692098933361)
                ·
                  refine ⟨51025214373989019074200021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68033619165318692098933361 51025214373989019074200021)
                  ·
                    refine ⟨1195903461890367634551563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51025214373989019074200021 1195903461890367634551563)
                    ·
                      rfl

theorem cell23_6987041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_6987041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987041 prefixEnd_6987041 := by exact prefixLift 6987041
  have htrace : WordTrace (prefixWord ++ tailWord_6987041) baseStart_6987041 baseEnd_6987041 := by
    simpa [prefixWord, tailWord_6987041, baseEnd_6987041] using wordTrace_append hprefix tailTrace_6987041
  have hstable : (prefixWord ++ tailWord_6987041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987041).length < 2 ^ (prefixWord ++ tailWord_6987041).sum := by decide
  have hdescent : baseEnd_6987041 < baseStart_6987041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987098 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_6987098 : Nat := 118140960795 + 6987098 * 2 ^ 59
def prefixEnd_6987098 : Nat := 4983230072969 + 3 ^ 40 * 6987098 * 2
def baseEnd_6987098 : Nat := 3587739654068409180641927

theorem tailTrace_6987098 : CollatzResearch.WordTrace tailWord_6987098 prefixEnd_6987098 3587739654068409180641927 := by
  unfold tailWord_6987098
  simp only [CollatzResearch.WordTrace]
  refine ⟨63710100010236180544984487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169893600027296481453291965 63710100010236180544984487)
  ·
    refine ⟨95565150015354270817476731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63710100010236180544984487 95565150015354270817476731)
    ·
      refine ⟨143347725023031406226215097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95565150015354270817476731 143347725023031406226215097)
      ·
        refine ⟨107510793767273554669661323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143347725023031406226215097 107510793767273554669661323)
        ·
          refine ⟨161266190650910332004491985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107510793767273554669661323 161266190650910332004491985)
          ·
            refine ⟨120949642988182749003368989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161266190650910332004491985 120949642988182749003368989)
            ·
              refine ⟨45356116120568530876263371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120949642988182749003368989 45356116120568530876263371)
              ·
                refine ⟨68034174180852796314395057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45356116120568530876263371 68034174180852796314395057)
                ·
                  refine ⟨51025630635639597235796293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68034174180852796314395057 51025630635639597235796293)
                  ·
                    refine ⟨9567305744182424481711805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51025630635639597235796293 9567305744182424481711805)
                    ·
                      refine ⟨3587739654068409180641927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9567305744182424481711805 3587739654068409180641927)
                      ·
                        rfl

theorem cell23_6987098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_6987098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987098 prefixEnd_6987098 := by exact prefixLift 6987098
  have htrace : WordTrace (prefixWord ++ tailWord_6987098) baseStart_6987098 baseEnd_6987098 := by
    simpa [prefixWord, tailWord_6987098, baseEnd_6987098] using wordTrace_append hprefix tailTrace_6987098
  have hstable : (prefixWord ++ tailWord_6987098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987098).length < 2 ^ (prefixWord ++ tailWord_6987098).sum := by decide
  have hdescent : baseEnd_6987098 < baseStart_6987098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987108 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_6987108 : Nat := 118140960795 + 6987108 * 2 ^ 59
def prefixEnd_6987108 : Nat := 4983230072969 + 3 ^ 40 * 6987108 * 2
def baseEnd_6987108 : Nat := 3587744788874954141516881

theorem tailTrace_6987108 : CollatzResearch.WordTrace tailWord_6987108 prefixEnd_6987108 3587744788874954141516881 := by
  unfold tailWord_6987108
  simp only [CollatzResearch.WordTrace]
  refine ⟨127420382385454246943900989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169893843180605662591867985 127420382385454246943900989)
  ·
    refine ⟨47782643394545342603962871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127420382385454246943900989 47782643394545342603962871)
    ·
      refine ⟨71673965091818013905944307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47782643394545342603962871 71673965091818013905944307)
      ·
        refine ⟨107510947637727020858916461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71673965091818013905944307 107510947637727020858916461)
        ·
          refine ⟨40316605364147632822093673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107510947637727020858916461 40316605364147632822093673)
          ·
            refine ⟨30237454023110724616570255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40316605364147632822093673 30237454023110724616570255)
            ·
              refine ⟨45356181034666086924855383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30237454023110724616570255 45356181034666086924855383)
              ·
                refine ⟨68034271551999130387283075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45356181034666086924855383 68034271551999130387283075)
                ·
                  refine ⟨102051407327998695580924613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68034271551999130387283075 102051407327998695580924613)
                  ·
                    refine ⟨19134638873999755421423365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102051407327998695580924613 19134638873999755421423365)
                    ·
                      refine ⟨3587744788874954141516881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19134638873999755421423365 3587744788874954141516881)
                      ·
                        rfl

theorem cell23_6987108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_6987108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987108 prefixEnd_6987108 := by exact prefixLift 6987108
  have htrace : WordTrace (prefixWord ++ tailWord_6987108) baseStart_6987108 baseEnd_6987108 := by
    simpa [prefixWord, tailWord_6987108, baseEnd_6987108] using wordTrace_append hprefix tailTrace_6987108
  have hstable : (prefixWord ++ tailWord_6987108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987108).length < 2 ^ (prefixWord ++ tailWord_6987108).sum := by decide
  have hdescent : baseEnd_6987108 < baseStart_6987108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987148 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_6987148 : Nat := 118140960795 + 6987148 * 2 ^ 59
def prefixEnd_6987148 : Nat := 4983230072969 + 3 ^ 40 * 6987148 * 2
def baseEnd_6987148 : Nat := 1195921776033711328338899

theorem tailTrace_6987148 : CollatzResearch.WordTrace tailWord_6987148 prefixEnd_6987148 1195921776033711328338899 := by
  unfold tailWord_6987148
  simp only [CollatzResearch.WordTrace]
  refine ⟨127421111845381790359629049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169894815793842387146172065 127421111845381790359629049)
  ·
    refine ⟨95565833884036342769721787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127421111845381790359629049 95565833884036342769721787)
    ·
      refine ⟨143348750826054514154582681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95565833884036342769721787 143348750826054514154582681)
      ·
        refine ⟨107511563119540885615937011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143348750826054514154582681 107511563119540885615937011)
        ·
          refine ⟨161267344679311328423905517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107511563119540885615937011 161267344679311328423905517)
          ·
            refine ⟨60475254254741748158964569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161267344679311328423905517 60475254254741748158964569)
            ·
              refine ⟨45356440691056311119223427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60475254254741748158964569 45356440691056311119223427)
              ·
                refine ⟨68034661036584466678835141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45356440691056311119223427 68034661036584466678835141)
                ·
                  refine ⟨12756498944359587502281589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68034661036584466678835141 12756498944359587502281589)
                  ·
                    refine ⟨1195921776033711328338899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12756498944359587502281589 1195921776033711328338899)
                    ·
                      rfl

theorem cell23_6987148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_6987148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987148 prefixEnd_6987148 := by exact prefixLift 6987148
  have htrace : WordTrace (prefixWord ++ tailWord_6987148) baseStart_6987148 baseEnd_6987148 := by
    simpa [prefixWord, tailWord_6987148, baseEnd_6987148] using wordTrace_append hprefix tailTrace_6987148
  have hstable : (prefixWord ++ tailWord_6987148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987148).length < 2 ^ (prefixWord ++ tailWord_6987148).sum := by decide
  have hdescent : baseEnd_6987148 < baseStart_6987148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987168 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_6987168 : Nat := 118140960795 + 6987168 * 2 ^ 59
def prefixEnd_6987168 : Nat := 4983230072969 + 3 ^ 40 * 6987168 * 2
def baseEnd_6987168 : Nat := 3587775597714223906766605

theorem tailTrace_6987168 : CollatzResearch.WordTrace tailWord_6987168 prefixEnd_6987168 3587775597714223906766605 := by
  unfold tailWord_6987168
  simp only [CollatzResearch.WordTrace]
  refine ⟨127421476575345562067493079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169895302100460749423324105 127421476575345562067493079)
  ·
    refine ⟨191132214863018343101239619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127421476575345562067493079 191132214863018343101239619)
    ·
      refine ⟨286698322294527514651859429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191132214863018343101239619 286698322294527514651859429)
      ·
        refine ⟨53755935430223908997223643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286698322294527514651859429 53755935430223908997223643)
        ·
          refine ⟨80633903145335863495835465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53755935430223908997223643 80633903145335863495835465)
          ·
            refine ⟨60475427359001897621876599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80633903145335863495835465 60475427359001897621876599)
            ·
              refine ⟨90713141038502846432814899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60475427359001897621876599 90713141038502846432814899)
              ·
                refine ⟨136069711557754269649222349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90713141038502846432814899 136069711557754269649222349)
                ·
                  refine ⟨51026141834157851118458381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136069711557754269649222349 51026141834157851118458381)
                  ·
                    refine ⟨19134803187809194169421893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51026141834157851118458381 19134803187809194169421893)
                    ·
                      refine ⟨3587775597714223906766605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19134803187809194169421893 3587775597714223906766605)
                      ·
                        rfl

theorem cell23_6987168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_6987168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987168 prefixEnd_6987168 := by exact prefixLift 6987168
  have htrace : WordTrace (prefixWord ++ tailWord_6987168) baseStart_6987168 baseEnd_6987168 := by
    simpa [prefixWord, tailWord_6987168, baseEnd_6987168] using wordTrace_append hprefix tailTrace_6987168
  have hstable : (prefixWord ++ tailWord_6987168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987168).length < 2 ^ (prefixWord ++ tailWord_6987168).sum := by decide
  have hdescent : baseEnd_6987168 < baseStart_6987168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987185 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_6987185 : Nat := 118140960795 + 6987185 * 2 ^ 59
def prefixEnd_6987185 : Nat := 4983230072969 + 3 ^ 40 * 6987185 * 2
def baseEnd_6987185 : Nat := 3587784326885350340254027

theorem tailTrace_6987185 : CollatzResearch.WordTrace tailWord_6987185 prefixEnd_6987185 3587784326885350340254027 := by
  unfold tailWord_6987185
  simp only [CollatzResearch.WordTrace]
  refine ⟨254843573191629536038355009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169895715461086357358903339 254843573191629536038355009)
  ·
    refine ⟨191132679893722152028766257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254843573191629536038355009 191132679893722152028766257)
    ·
      refine ⟨143349509920291614021574693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191132679893722152028766257 143349509920291614021574693)
      ·
        refine ⟨26878033110054677629045255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143349509920291614021574693 26878033110054677629045255)
        ·
          refine ⟨40317049665082016443567883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26878033110054677629045255 40317049665082016443567883)
          ·
            refine ⟨60475574497623024665351825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40317049665082016443567883 60475574497623024665351825)
            ·
              refine ⟨45356680873217268499013869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60475574497623024665351825 45356680873217268499013869)
              ·
                refine ⟨17008755327456475687130201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45356680873217268499013869 17008755327456475687130201)
                ·
                  refine ⟨12756566495592356765347651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17008755327456475687130201 12756566495592356765347651)
                  ·
                    refine ⟨19134849743388535148021477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12756566495592356765347651 19134849743388535148021477)
                    ·
                      refine ⟨3587784326885350340254027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19134849743388535148021477 3587784326885350340254027)
                      ·
                        rfl

theorem cell23_6987185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_6987185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987185 prefixEnd_6987185 := by exact prefixLift 6987185
  have htrace : WordTrace (prefixWord ++ tailWord_6987185) baseStart_6987185 baseEnd_6987185 := by
    simpa [prefixWord, tailWord_6987185, baseEnd_6987185] using wordTrace_append hprefix tailTrace_6987185
  have hstable : (prefixWord ++ tailWord_6987185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987185).length < 2 ^ (prefixWord ++ tailWord_6987185).sum := by decide
  have hdescent : baseEnd_6987185 < baseStart_6987185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987208 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 8]
def baseStart_6987208 : Nat := 118140960795 + 6987208 * 2 ^ 59
def prefixEnd_6987208 : Nat := 4983230072969 + 3 ^ 40 * 6987208 * 2
def baseEnd_6987208 : Nat := 398644015215600416696269

theorem tailTrace_6987208 : CollatzResearch.WordTrace tailWord_6987208 prefixEnd_6987208 398644015215600416696269 := by
  unfold tailWord_6987208
  simp only [CollatzResearch.WordTrace]
  refine ⟨127422206035273105483221139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169896274713697473977628185 127422206035273105483221139)
  ·
    refine ⟨191133309052909658224831709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127422206035273105483221139 191133309052909658224831709)
    ·
      refine ⟨71674990894841121834311891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191133309052909658224831709 71674990894841121834311891)
      ·
        refine ⟨107512486342261682751467837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71674990894841121834311891 107512486342261682751467837)
        ·
          refine ⟨40317182378348131031800439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107512486342261682751467837 40317182378348131031800439)
          ·
            refine ⟨60475773567522196547700659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40317182378348131031800439 60475773567522196547700659)
            ·
              refine ⟨90713660351283294821550989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60475773567522196547700659 90713660351283294821550989)
              ·
                refine ⟨34017622631731235558081621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90713660351283294821550989 34017622631731235558081621)
                ·
                  refine ⟨398644015215600416696269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34017622631731235558081621 398644015215600416696269)
                  ·
                    rfl

theorem cell23_6987208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 8].length) (baseStart_6987208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987208 prefixEnd_6987208 := by exact prefixLift 6987208
  have htrace : WordTrace (prefixWord ++ tailWord_6987208) baseStart_6987208 baseEnd_6987208 := by
    simpa [prefixWord, tailWord_6987208, baseEnd_6987208] using wordTrace_append hprefix tailTrace_6987208
  have hstable : (prefixWord ++ tailWord_6987208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987208).length < 2 ^ (prefixWord ++ tailWord_6987208).sum := by decide
  have hdescent : baseEnd_6987208 < baseStart_6987208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987212 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_6987212 : Nat := 118140960795 + 6987212 * 2 ^ 59
def prefixEnd_6987212 : Nat := 4983230072969 + 3 ^ 40 * 6987212 * 2
def baseEnd_6987212 : Nat := 1195932730287673911538801

theorem tailTrace_6987212 : CollatzResearch.WordTrace tailWord_6987212 prefixEnd_6987212 1195932730287673911538801 := by
  unfold tailWord_6987212
  simp only [CollatzResearch.WordTrace]
  refine ⟨127422278981265859824793945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169896371975021146433058593 127422278981265859824793945)
  ·
    refine ⟨95566709235949394868595459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127422278981265859824793945 95566709235949394868595459)
    ·
      refine ⟨143350063853924092302893189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95566709235949394868595459 143350063853924092302893189)
      ·
        refine ⟨26878136972610767306792473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143350063853924092302893189 26878136972610767306792473)
        ·
          refine ⟨20158602729458075480094355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26878136972610767306792473 20158602729458075480094355)
          ·
            refine ⟨30237904094187113220141533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20158602729458075480094355 30237904094187113220141533)
            ·
              refine ⟨11339214035320167457553075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30237904094187113220141533 11339214035320167457553075)
              ·
                refine ⟨17008821052980251186329613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11339214035320167457553075 17008821052980251186329613)
                ·
                  refine ⟨6378307894867594194873605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17008821052980251186329613 6378307894867594194873605)
                  ·
                    refine ⟨1195932730287673911538801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6378307894867594194873605 1195932730287673911538801)
                    ·
                      rfl

theorem cell23_6987212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_6987212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987212 prefixEnd_6987212 := by exact prefixLift 6987212
  have htrace : WordTrace (prefixWord ++ tailWord_6987212) baseStart_6987212 baseEnd_6987212 := by
    simpa [prefixWord, tailWord_6987212, baseEnd_6987212] using wordTrace_append hprefix tailTrace_6987212
  have hstable : (prefixWord ++ tailWord_6987212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987212).length < 2 ^ (prefixWord ++ tailWord_6987212).sum := by decide
  have hdescent : baseEnd_6987212 < baseStart_6987212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987225 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 6]
def baseStart_6987225 : Nat := 118140960795 + 6987225 * 2 ^ 59
def prefixEnd_6987225 : Nat := 4983230072969 + 3 ^ 40 * 6987225 * 2
def baseEnd_6987225 : Nat := 398644985123503353750427

theorem tailTrace_6987225 : CollatzResearch.WordTrace tailWord_6987225 prefixEnd_6987225 398644985123503353750427 := by
  unfold tailWord_6987225
  simp only [CollatzResearch.WordTrace]
  refine ⟨254845032111484622869811129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169896688074323081913207419 254845032111484622869811129)
  ·
    refine ⟨191133774083613467152358347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254845032111484622869811129 191133774083613467152358347)
    ·
      refine ⟨286700661125420200728537521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191133774083613467152358347 286700661125420200728537521)
      ·
        refine ⟨215025495844065150546403141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286700661125420200728537521 215025495844065150546403141)
        ·
          refine ⟨40317280470762215727450589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215025495844065150546403141 40317280470762215727450589)
          ·
            refine ⟨15118980176535830897793971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40317280470762215727450589 15118980176535830897793971)
            ·
              refine ⟨22678470264803746346690957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15118980176535830897793971 22678470264803746346690957)
              ·
                refine ⟨8504426349301404880009109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22678470264803746346690957 8504426349301404880009109)
                ·
                  refine ⟨398644985123503353750427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8504426349301404880009109 398644985123503353750427)
                  ·
                    rfl

theorem cell23_6987225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 6].length) (baseStart_6987225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987225 prefixEnd_6987225 := by exact prefixLift 6987225
  have htrace : WordTrace (prefixWord ++ tailWord_6987225) baseStart_6987225 baseEnd_6987225 := by
    simpa [prefixWord, tailWord_6987225, baseEnd_6987225] using wordTrace_append hprefix tailTrace_6987225
  have hstable : (prefixWord ++ tailWord_6987225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987225).length < 2 ^ (prefixWord ++ tailWord_6987225).sum := by decide
  have hdescent : baseEnd_6987225 < baseStart_6987225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987285 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_6987285 : Nat := 118140960795 + 6987285 * 2 ^ 59
def prefixEnd_6987285 : Nat := 4983230072969 + 3 ^ 40 * 6987285 * 2
def baseEnd_6987285 : Nat := 1195945224983599983001189

theorem tailTrace_6987285 : CollatzResearch.WordTrace tailWord_6987285 prefixEnd_6987285 1195945224983599983001189 := by
  unfold tailWord_6987285
  simp only [CollatzResearch.WordTrace]
  refine ⟨254847220491267253116995309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169898146994178168744663539 254847220491267253116995309)
  ·
    refine ⟨95567707684225219918873241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254847220491267253116995309 95567707684225219918873241)
    ·
      refine ⟨71675780763168914939154931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95567707684225219918873241 71675780763168914939154931)
      ·
        refine ⟨107513671144753372408732397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71675780763168914939154931 107513671144753372408732397)
        ·
          refine ⟨40317626679282514653274649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107513671144753372408732397 40317626679282514653274649)
          ·
            refine ⟨30238220009461885989955987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40317626679282514653274649 30238220009461885989955987)
            ·
              refine ⟨45357330014192828984933981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30238220009461885989955987 45357330014192828984933981)
              ·
                refine ⟨17008998755322310869350243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45357330014192828984933981 17008998755322310869350243)
                ·
                  refine ⟨25513498132983466304025365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17008998755322310869350243 25513498132983466304025365)
                  ·
                    refine ⟨1195945224983599983001189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25513498132983466304025365 1195945224983599983001189)
                    ·
                      rfl

theorem cell23_6987285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_6987285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987285 prefixEnd_6987285 := by exact prefixLift 6987285
  have htrace : WordTrace (prefixWord ++ tailWord_6987285) baseStart_6987285 baseEnd_6987285 := by
    simpa [prefixWord, tailWord_6987285, baseEnd_6987285] using wordTrace_append hprefix tailTrace_6987285
  have hstable : (prefixWord ++ tailWord_6987285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987285).length < 2 ^ (prefixWord ++ tailWord_6987285).sum := by decide
  have hdescent : baseEnd_6987285 < baseStart_6987285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987292 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_6987292 : Nat := 118140960795 + 6987292 * 2 ^ 59
def prefixEnd_6987292 : Nat := 4983230072969 + 3 ^ 40 * 6987292 * 2
def baseEnd_6987292 : Nat := 3587839269315381421616035

theorem tailTrace_6987292 : CollatzResearch.WordTrace tailWord_6987292 prefixEnd_6987292 3587839269315381421616035 := by
  unfold tailWord_6987292
  simp only [CollatzResearch.WordTrace]
  refine ⟨127423737901120946656250065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169898317201494595541666753 127423737901120946656250065)
  ·
    refine ⟨95567803425840709992187549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127423737901120946656250065 95567803425840709992187549)
    ·
      refine ⟨35837926284690266247070331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95567803425840709992187549 35837926284690266247070331)
      ·
        refine ⟨53756889427035399370605497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35837926284690266247070331 53756889427035399370605497)
        ·
          refine ⟨40317667070276549527954123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53756889427035399370605497 40317667070276549527954123)
          ·
            refine ⟨60476500605414824291931185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40317667070276549527954123 60476500605414824291931185)
            ·
              refine ⟨45357375454061118218948389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60476500605414824291931185 45357375454061118218948389)
              ·
                refine ⟨8504507897636459666052823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45357375454061118218948389 8504507897636459666052823)
                ·
                  refine ⟨12756761846454689499079235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8504507897636459666052823 12756761846454689499079235)
                  ·
                    refine ⟨19135142769682034248618853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12756761846454689499079235 19135142769682034248618853)
                    ·
                      refine ⟨3587839269315381421616035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19135142769682034248618853 3587839269315381421616035)
                      ·
                        rfl

theorem cell23_6987292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_6987292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987292 prefixEnd_6987292 := by exact prefixLift 6987292
  have htrace : WordTrace (prefixWord ++ tailWord_6987292) baseStart_6987292 baseEnd_6987292 := by
    simpa [prefixWord, tailWord_6987292, baseEnd_6987292] using wordTrace_append hprefix tailTrace_6987292
  have hstable : (prefixWord ++ tailWord_6987292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987292).length < 2 ^ (prefixWord ++ tailWord_6987292).sum := by decide
  have hdescent : baseEnd_6987292 < baseStart_6987292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987296 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6987296 : Nat := 118140960795 + 6987296 * 2 ^ 59
def prefixEnd_6987296 : Nat := 4983230072969 + 3 ^ 40 * 6987296 * 2
def baseEnd_6987296 : Nat := 3587841323237999405966017

theorem tailTrace_6987296 : CollatzResearch.WordTrace tailWord_6987296 prefixEnd_6987296 3587841323237999405966017 := by
  unfold tailWord_6987296
  simp only [CollatzResearch.WordTrace]
  refine ⟨127423810847113700997822871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169898414462818267997097161 127423810847113700997822871)
  ·
    refine ⟨191135716270670551496734307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127423810847113700997822871 191135716270670551496734307)
    ·
      refine ⟨286703574406005827245101461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191135716270670551496734307 286703574406005827245101461)
      ·
        refine ⟨13439230050281523152114131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 286703574406005827245101461 13439230050281523152114131)
        ·
          refine ⟨20158845075422284728171197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13439230050281523152114131 20158845075422284728171197)
          ·
            refine ⟨7559566903283356773064199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20158845075422284728171197 7559566903283356773064199)
            ·
              refine ⟨11339350354925035159596299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7559566903283356773064199 11339350354925035159596299)
              ·
                refine ⟨17009025532387552739394449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11339350354925035159596299 17009025532387552739394449)
                ·
                  refine ⟨12756769149290664554545837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17009025532387552739394449 12756769149290664554545837)
                  ·
                    refine ⟨4783788430983999207954689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12756769149290664554545837 4783788430983999207954689)
                    ·
                      refine ⟨3587841323237999405966017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4783788430983999207954689 3587841323237999405966017)
                      ·
                        rfl

theorem cell23_6987296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6987296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987296 prefixEnd_6987296 := by exact prefixLift 6987296
  have htrace : WordTrace (prefixWord ++ tailWord_6987296) baseStart_6987296 baseEnd_6987296 := by
    simpa [prefixWord, tailWord_6987296, baseEnd_6987296] using wordTrace_append hprefix tailTrace_6987296
  have hstable : (prefixWord ++ tailWord_6987296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987296).length < 2 ^ (prefixWord ++ tailWord_6987296).sum := by decide
  have hdescent : baseEnd_6987296 < baseStart_6987296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987319 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 2, 4]
def baseStart_6987319 : Nat := 118140960795 + 6987319 * 2 ^ 59
def prefixEnd_6987319 : Nat := 4983230072969 + 3 ^ 40 * 6987319 * 2
def baseEnd_6987319 : Nat := 1195951044431017605326137

theorem tailTrace_6987319 : CollatzResearch.WordTrace tailWord_6987319 prefixEnd_6987319 1195951044431017605326137 := by
  unfold tailWord_6987319
  simp only [CollatzResearch.WordTrace]
  refine ⟨254848460573144076923733011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169898973715429384615822007 254848460573144076923733011)
  ·
    refine ⟨382272690859716115385599517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254848460573144076923733011 382272690859716115385599517)
    ·
      refine ⟨143352259072393543269599819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382272690859716115385599517 143352259072393543269599819)
      ·
        refine ⟨215028388608590314904399729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143352259072393543269599819 215028388608590314904399729)
        ·
          refine ⟨161271291456442736178299797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215028388608590314904399729 161271291456442736178299797)
          ·
            refine ⟨7559591787020753258357803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161271291456442736178299797 7559591787020753258357803)
            ·
              refine ⟨11339387680531129887536705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7559591787020753258357803 11339387680531129887536705)
              ·
                refine ⟨8504540760398347415652529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11339387680531129887536705 8504540760398347415652529)
                ·
                  refine ⟨6378405570298760561739397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8504540760398347415652529 6378405570298760561739397)
                  ·
                    refine ⟨1195951044431017605326137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6378405570298760561739397 1195951044431017605326137)
                    ·
                      rfl

theorem cell23_6987319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_6987319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987319 prefixEnd_6987319 := by exact prefixLift 6987319
  have htrace : WordTrace (prefixWord ++ tailWord_6987319) baseStart_6987319 baseEnd_6987319 := by
    simpa [prefixWord, tailWord_6987319, baseEnd_6987319] using wordTrace_append hprefix tailTrace_6987319
  have hstable : (prefixWord ++ tailWord_6987319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987319).length < 2 ^ (prefixWord ++ tailWord_6987319).sum := by decide
  have hdescent : baseEnd_6987319 < baseStart_6987319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987369 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 1, 3, 2]
def baseStart_6987369 : Nat := 118140960795 + 6987369 * 2 ^ 59
def prefixEnd_6987369 : Nat := 4983230072969 + 3 ^ 40 * 6987369 * 2
def baseEnd_6987369 : Nat := 3587878807325777620353181

theorem tailTrace_6987369 : CollatzResearch.WordTrace tailWord_6987369 prefixEnd_6987369 3587878807325777620353181 := by
  unfold tailWord_6987369
  simp only [CollatzResearch.WordTrace]
  refine ⟨254850284222962935463053161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169900189481975290308702107 254850284222962935463053161)
  ·
    refine ⟨191137713167222201597289871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254850284222962935463053161 191137713167222201597289871)
    ·
      refine ⟨286706569750833302395934807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191137713167222201597289871 286706569750833302395934807)
      ·
        refine ⟨430059854626249953593902211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286706569750833302395934807 430059854626249953593902211)
        ·
          refine ⟨645089781939374930390853317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430059854626249953593902211 645089781939374930390853317)
          ·
            refine ⟨120954334113632799448284997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 645089781939374930390853317 120954334113632799448284997)
            ·
              refine ⟨22678937646306149896553437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120954334113632799448284997 22678937646306149896553437)
              ·
                refine ⟨8504601617364806211207539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22678937646306149896553437 8504601617364806211207539)
                ·
                  refine ⟨12756902426047209316811309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8504601617364806211207539 12756902426047209316811309)
                  ·
                    refine ⟨4783838409767703493804241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12756902426047209316811309 4783838409767703493804241)
                    ·
                      refine ⟨3587878807325777620353181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4783838409767703493804241 3587878807325777620353181)
                      ·
                        rfl

theorem cell23_6987369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 3, 2].length) (baseStart_6987369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987369 prefixEnd_6987369 := by exact prefixLift 6987369
  have htrace : WordTrace (prefixWord ++ tailWord_6987369) baseStart_6987369 baseEnd_6987369 := by
    simpa [prefixWord, tailWord_6987369, baseEnd_6987369] using wordTrace_append hprefix tailTrace_6987369
  have hstable : (prefixWord ++ tailWord_6987369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987369).length < 2 ^ (prefixWord ++ tailWord_6987369).sum := by decide
  have hdescent : baseEnd_6987369 < baseStart_6987369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987385 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_6987385 : Nat := 118140960795 + 6987385 * 2 ^ 59
def prefixEnd_6987385 : Nat := 4983230072969 + 3 ^ 40 * 6987385 * 2
def baseEnd_6987385 : Nat := 3587887023016249557753107

theorem tailTrace_6987385 : CollatzResearch.WordTrace tailWord_6987385 prefixEnd_6987385 3587887023016249557753107 := by
  unfold tailWord_6987385
  simp only [CollatzResearch.WordTrace]
  refine ⟨254850867790904970195635609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169900578527269980130423739 254850867790904970195635609)
  ·
    refine ⟨191138150843178727646726707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254850867790904970195635609 191138150843178727646726707)
    ·
      refine ⟨286707226264768091470090061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191138150843178727646726707 286707226264768091470090061)
      ·
        refine ⟨107515209849288034301283773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286707226264768091470090061 107515209849288034301283773)
        ·
          refine ⟨40318203693483012862981415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107515209849288034301283773 40318203693483012862981415)
          ·
            refine ⟨60477305540224519294472123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40318203693483012862981415 60477305540224519294472123)
            ·
              refine ⟨90715958310336778941708185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60477305540224519294472123 90715958310336778941708185)
              ·
                refine ⟨68036968732752584206281139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90715958310336778941708185 68036968732752584206281139)
                ·
                  refine ⟨102055453099128876309421709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68036968732752584206281139 102055453099128876309421709)
                  ·
                    refine ⟨38270794912173328616033141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102055453099128876309421709 38270794912173328616033141)
                    ·
                      refine ⟨3587887023016249557753107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38270794912173328616033141 3587887023016249557753107)
                      ·
                        rfl

theorem cell23_6987385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_6987385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987385 prefixEnd_6987385 := by exact prefixLift 6987385
  have htrace : WordTrace (prefixWord ++ tailWord_6987385) baseStart_6987385 baseEnd_6987385 := by
    simpa [prefixWord, tailWord_6987385, baseEnd_6987385] using wordTrace_append hprefix tailTrace_6987385
  have hstable : (prefixWord ++ tailWord_6987385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987385).length < 2 ^ (prefixWord ++ tailWord_6987385).sum := by decide
  have hdescent : baseEnd_6987385 < baseStart_6987385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987393 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_6987393 : Nat := 118140960795 + 6987393 * 2 ^ 59
def prefixEnd_6987393 : Nat := 4983230072969 + 3 ^ 40 * 6987393 * 2
def baseEnd_6987393 : Nat := 3587891130861485526453071

theorem tailTrace_6987393 : CollatzResearch.WordTrace tailWord_6987393 prefixEnd_6987393 3587891130861485526453071 := by
  unfold tailWord_6987393
  simp only [CollatzResearch.WordTrace]
  refine ⟨254851159574875987561926833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169900773049917325041284555 254851159574875987561926833)
  ·
    refine ⟨191138369681156990671445125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254851159574875987561926833 191138369681156990671445125)
    ·
      refine ⟨35838444315216935750895961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191138369681156990671445125 35838444315216935750895961)
      ·
        refine ⟨26878833236412701813171971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35838444315216935750895961 26878833236412701813171971)
        ·
          refine ⟨40318249854619052719757957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26878833236412701813171971 40318249854619052719757957)
          ·
            refine ⟨7559671847741072384954617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40318249854619052719757957 7559671847741072384954617)
            ·
              refine ⟨5669753885805804288715963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7559671847741072384954617 5669753885805804288715963)
              ·
                refine ⟨8504630828708706433073945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669753885805804288715963 8504630828708706433073945)
                ·
                  refine ⟨6378473121531529824805459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8504630828708706433073945 6378473121531529824805459)
                  ·
                    refine ⟨9567709682297294737208189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6378473121531529824805459 9567709682297294737208189)
                    ·
                      refine ⟨3587891130861485526453071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9567709682297294737208189 3587891130861485526453071)
                      ·
                        rfl

theorem cell23_6987393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_6987393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987393 prefixEnd_6987393 := by exact prefixLift 6987393
  have htrace : WordTrace (prefixWord ++ tailWord_6987393) baseStart_6987393 baseEnd_6987393 := by
    simpa [prefixWord, tailWord_6987393, baseEnd_6987393] using wordTrace_append hprefix tailTrace_6987393
  have hstable : (prefixWord ++ tailWord_6987393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987393).length < 2 ^ (prefixWord ++ tailWord_6987393).sum := by decide
  have hdescent : baseEnd_6987393 < baseStart_6987393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987395 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 4]
def baseStart_6987395 : Nat := 118140960795 + 6987395 * 2 ^ 59
def prefixEnd_6987395 : Nat := 4983230072969 + 3 ^ 40 * 6987395 * 2
def baseEnd_6987395 : Nat := 3587892157822794518628061

theorem tailTrace_6987395 : CollatzResearch.WordTrace tailWord_6987395 prefixEnd_6987395 3587892157822794518628061 := by
  unfold tailWord_6987395
  simp only [CollatzResearch.WordTrace]
  refine ⟨254851232520868741903499639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169900821680579161268999759 254851232520868741903499639)
  ·
    refine ⟨382276848781303112855249459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254851232520868741903499639 382276848781303112855249459)
    ·
      refine ⟨573415273171954669282874189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382276848781303112855249459 573415273171954669282874189)
      ·
        refine ⟨215030727439483000981077821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 573415273171954669282874189 215030727439483000981077821)
        ·
          refine ⟨80636522789806125367904183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215030727439483000981077821 80636522789806125367904183)
          ·
            refine ⟨120954784184709188051856275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80636522789806125367904183 120954784184709188051856275)
            ·
              refine ⟨181432176277063782077784413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120954784184709188051856275 181432176277063782077784413)
              ·
                refine ⟨68037066103898918279169155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181432176277063782077784413 68037066103898918279169155)
                ·
                  refine ⟨102055599155848377418753733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68037066103898918279169155 102055599155848377418753733)
                  ·
                    refine ⟨19135424841721570766016325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102055599155848377418753733 19135424841721570766016325)
                    ·
                      refine ⟨3587892157822794518628061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19135424841721570766016325 3587892157822794518628061)
                      ·
                        rfl

theorem cell23_6987395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_6987395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987395 prefixEnd_6987395 := by exact prefixLift 6987395
  have htrace : WordTrace (prefixWord ++ tailWord_6987395) baseStart_6987395 baseEnd_6987395 := by
    simpa [prefixWord, tailWord_6987395, baseEnd_6987395] using wordTrace_append hprefix tailTrace_6987395
  have hstable : (prefixWord ++ tailWord_6987395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987395).length < 2 ^ (prefixWord ++ tailWord_6987395).sum := by decide
  have hdescent : baseEnd_6987395 < baseStart_6987395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987402 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_6987402 : Nat := 118140960795 + 6987402 * 2 ^ 59
def prefixEnd_6987402 : Nat := 4983230072969 + 3 ^ 40 * 6987402 * 2
def baseEnd_6987402 : Nat := 3587895752187375991240529

theorem tailTrace_6987402 : CollatzResearch.WordTrace tailWord_6987402 prefixEnd_6987402 3587895752187375991240529 := by
  unfold tailWord_6987402
  simp only [CollatzResearch.WordTrace]
  refine ⟨63712871957960845524751115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169900991887895588066002973 63712871957960845524751115)
  ·
    refine ⟨95569307936941268287126673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63712871957960845524751115 95569307936941268287126673)
    ·
      refine ⟨71676980952705951215345005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95569307936941268287126673 71676980952705951215345005)
      ·
        refine ⟨26878867857264731705754377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71676980952705951215345005 26878867857264731705754377)
        ·
          refine ⟨20159150892948548779315783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26878867857264731705754377 20159150892948548779315783)
          ·
            refine ⟨30238726339422823168973675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20159150892948548779315783 30238726339422823168973675)
            ·
              refine ⟨45358089509134234753460513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30238726339422823168973675 45358089509134234753460513)
              ·
                refine ⟨34018567131850676065095385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45358089509134234753460513 34018567131850676065095385)
                ·
                  refine ⟨25513925348888007048821539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34018567131850676065095385 25513925348888007048821539)
                  ·
                    refine ⟨38270888023332010573232309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25513925348888007048821539 38270888023332010573232309)
                    ·
                      refine ⟨3587895752187375991240529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38270888023332010573232309 3587895752187375991240529)
                      ·
                        rfl

theorem cell23_6987402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_6987402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987402 prefixEnd_6987402 := by exact prefixLift 6987402
  have htrace : WordTrace (prefixWord ++ tailWord_6987402) baseStart_6987402 baseEnd_6987402 := by
    simpa [prefixWord, tailWord_6987402, baseEnd_6987402] using wordTrace_append hprefix tailTrace_6987402
  have hstable : (prefixWord ++ tailWord_6987402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987402).length < 2 ^ (prefixWord ++ tailWord_6987402).sum := by decide
  have hdescent : baseEnd_6987402 < baseStart_6987402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987446 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6987446 : Nat := 118140960795 + 6987446 * 2 ^ 59
def prefixEnd_6987446 : Nat := 4983230072969 + 3 ^ 40 * 6987446 * 2
def baseEnd_6987446 : Nat := 3587918345336173819090327

theorem tailTrace_6987446 : CollatzResearch.WordTrace tailWord_6987446 prefixEnd_6987446 3587918345336173819090327 := by
  unfold tailWord_6987446
  simp only [CollatzResearch.WordTrace]
  refine ⟨15928318290230248600850387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169902061762455985075737461 15928318290230248600850387)
  ·
    refine ⟨23892477435345372901275581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15928318290230248600850387 23892477435345372901275581)
    ·
      refine ⟨8959679038254514837978343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23892477435345372901275581 8959679038254514837978343)
      ·
        refine ⟨13439518557381772256967515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8959679038254514837978343 13439518557381772256967515)
        ·
          refine ⟨20159277836072658385451273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13439518557381772256967515 20159277836072658385451273)
          ·
            refine ⟨15119458377054493789088455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20159277836072658385451273 15119458377054493789088455)
            ·
              refine ⟨22679187565581740683632683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15119458377054493789088455 22679187565581740683632683)
              ·
                refine ⟨34018781348372611025449025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22679187565581740683632683 34018781348372611025449025)
                ·
                  refine ⟨25514086011279458269086769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34018781348372611025449025 25514086011279458269086769)
                  ·
                    refine ⟨19135564508459593701815077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25514086011279458269086769 19135564508459593701815077)
                    ·
                      refine ⟨3587918345336173819090327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19135564508459593701815077 3587918345336173819090327)
                      ·
                        rfl

theorem cell23_6987446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6987446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987446 prefixEnd_6987446 := by exact prefixLift 6987446
  have htrace : WordTrace (prefixWord ++ tailWord_6987446) baseStart_6987446 baseEnd_6987446 := by
    simpa [prefixWord, tailWord_6987446, baseEnd_6987446] using wordTrace_append hprefix tailTrace_6987446
  have hstable : (prefixWord ++ tailWord_6987446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987446).length < 2 ^ (prefixWord ++ tailWord_6987446).sum := by decide
  have hdescent : baseEnd_6987446 < baseStart_6987446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987472 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_6987472 : Nat := 118140960795 + 6987472 * 2 ^ 59
def prefixEnd_6987472 : Nat := 4983230072969 + 3 ^ 40 * 6987472 * 2
def baseEnd_6987472 : Nat := 3587931695833190717365207

theorem tailTrace_6987472 : CollatzResearch.WordTrace tailWord_6987472 prefixEnd_6987472 3587931695833190717365207 := by
  unfold tailWord_6987472
  simp only [CollatzResearch.WordTrace]
  refine ⟨127427020470794892027026335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169902693961059856036035113 127427020470794892027026335)
  ·
    refine ⟨191140530706192338040539503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127427020470794892027026335 191140530706192338040539503)
    ·
      refine ⟨286710796059288507060809255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191140530706192338040539503 286710796059288507060809255)
      ·
        refine ⟨430066194088932760591213883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286710796059288507060809255 430066194088932760591213883)
        ·
          refine ⟨645099291133399140886820825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430066194088932760591213883 645099291133399140886820825)
          ·
            refine ⟨483824468350049355665115619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645099291133399140886820825 483824468350049355665115619)
            ·
              refine ⟨725736702525074033497673429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483824468350049355665115619 725736702525074033497673429)
              ·
                refine ⟨17009453965431422660101721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 725736702525074033497673429 17009453965431422660101721)
                ·
                  refine ⟨12757090474073566995076291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17009453965431422660101721 12757090474073566995076291)
                  ·
                    refine ⟨19135635711110350492614437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12757090474073566995076291 19135635711110350492614437)
                    ·
                      refine ⟨3587931695833190717365207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19135635711110350492614437 3587931695833190717365207)
                      ·
                        rfl

theorem cell23_6987472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_6987472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987472 prefixEnd_6987472 := by exact prefixLift 6987472
  have htrace : WordTrace (prefixWord ++ tailWord_6987472) baseStart_6987472 baseEnd_6987472 := by
    simpa [prefixWord, tailWord_6987472, baseEnd_6987472] using wordTrace_append hprefix tailTrace_6987472
  have hstable : (prefixWord ++ tailWord_6987472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987472).length < 2 ^ (prefixWord ++ tailWord_6987472).sum := by decide
  have hdescent : baseEnd_6987472 < baseStart_6987472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987475 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 5]
def baseStart_6987475 : Nat := 118140960795 + 6987475 * 2 ^ 59
def prefixEnd_6987475 : Nat := 4983230072969 + 3 ^ 40 * 6987475 * 2
def baseEnd_6987475 : Nat := 3587933236275154205627693

theorem tailTrace_6987475 : CollatzResearch.WordTrace tailWord_6987475 prefixEnd_6987475 3587933236275154205627693 := by
  unfold tailWord_6987475
  simp only [CollatzResearch.WordTrace]
  refine ⟨254854150360578915566411879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169902766907052610377607919 254854150360578915566411879)
  ·
    refine ⟨382281225540868373349617819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254854150360578915566411879 382281225540868373349617819)
    ·
      refine ⟨573421838311302560024426729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382281225540868373349617819 573421838311302560024426729)
      ·
        refine ⟨430066378733476920018320047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573421838311302560024426729 430066378733476920018320047)
        ·
          refine ⟨645099568100215380027480071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430066378733476920018320047 645099568100215380027480071)
          ·
            refine ⟨967649352150323070041220107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645099568100215380027480071 967649352150323070041220107)
            ·
              refine ⟨1451474028225484605061830161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967649352150323070041220107 1451474028225484605061830161)
              ·
                refine ⟨1088605521169113453796372621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451474028225484605061830161 1088605521169113453796372621)
                ·
                  refine ⟨408227070438417545173639733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088605521169113453796372621 408227070438417545173639733)
                  ·
                    refine ⟨38271287853601644860028725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 408227070438417545173639733 38271287853601644860028725)
                    ·
                      refine ⟨3587933236275154205627693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38271287853601644860028725 3587933236275154205627693)
                      ·
                        rfl

theorem cell23_6987475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_6987475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987475 prefixEnd_6987475 := by exact prefixLift 6987475
  have htrace : WordTrace (prefixWord ++ tailWord_6987475) baseStart_6987475 baseEnd_6987475 := by
    simpa [prefixWord, tailWord_6987475, baseEnd_6987475] using wordTrace_append hprefix tailTrace_6987475
  have hstable : (prefixWord ++ tailWord_6987475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987475).length < 2 ^ (prefixWord ++ tailWord_6987475).sum := by decide
  have hdescent : baseEnd_6987475 < baseStart_6987475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987502 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_6987502 : Nat := 118140960795 + 6987502 * 2 ^ 59
def prefixEnd_6987502 : Nat := 4983230072969 + 3 ^ 40 * 6987502 * 2
def baseEnd_6987502 : Nat := 3587947100252825599990069

theorem tailTrace_6987502 : CollatzResearch.WordTrace tailWord_6987502 prefixEnd_6987502 3587947100252825599990069 := by
  unfold tailWord_6987502
  simp only [CollatzResearch.WordTrace]
  refine ⟨31856891891435137397205595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169903423420987399451763173 31856891891435137397205595)
  ·
    refine ⟨47785337837152706095808393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31856891891435137397205595 47785337837152706095808393)
    ·
      refine ⟨35839003377864529571856295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47785337837152706095808393 35839003377864529571856295)
      ·
        refine ⟨53758505066796794357784443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35839003377864529571856295 53758505066796794357784443)
        ·
          refine ⟨80637757600195191536676665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53758505066796794357784443 80637757600195191536676665)
          ·
            refine ⟨60478318200146393652507499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80637757600195191536676665 60478318200146393652507499)
            ·
              refine ⟨90717477300219590478761249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60478318200146393652507499 90717477300219590478761249)
              ·
                refine ⟨68038107975164692859070937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90717477300219590478761249 68038107975164692859070937)
                ·
                  refine ⟨51028580981373519644303203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68038107975164692859070937 51028580981373519644303203)
                  ·
                    refine ⟨76542871472060279466454805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51028580981373519644303203 76542871472060279466454805)
                    ·
                      refine ⟨3587947100252825599990069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76542871472060279466454805 3587947100252825599990069)
                      ·
                        rfl

theorem cell23_6987502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_6987502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987502 prefixEnd_6987502 := by exact prefixLift 6987502
  have htrace : WordTrace (prefixWord ++ tailWord_6987502) baseStart_6987502 baseEnd_6987502 := by
    simpa [prefixWord, tailWord_6987502, baseEnd_6987502] using wordTrace_append hprefix tailTrace_6987502
  have hstable : (prefixWord ++ tailWord_6987502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987502).length < 2 ^ (prefixWord ++ tailWord_6987502).sum := by decide
  have hdescent : baseEnd_6987502 < baseStart_6987502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987540 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6987540 : Nat := 118140960795 + 6987540 * 2 ^ 59
def prefixEnd_6987540 : Nat := 4983230072969 + 3 ^ 40 * 6987540 * 2
def baseEnd_6987540 : Nat := 3587966612517696451314895

theorem tailTrace_6987540 : CollatzResearch.WordTrace tailWord_6987540 prefixEnd_6987540 3587966612517696451314895 := by
  unfold tailWord_6987540
  simp only [CollatzResearch.WordTrace]
  refine ⟨127428260552671715833764037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169904347403562287778352049 127428260552671715833764037)
  ·
    refine ⟨23892798853625946718830757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127428260552671715833764037 23892798853625946718830757)
    ·
      refine ⟨4479899785054865009780767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23892798853625946718830757 4479899785054865009780767)
      ·
        refine ⟨6719849677582297514671151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4479899785054865009780767 6719849677582297514671151)
        ·
          refine ⟨10079774516373446272006727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6719849677582297514671151 10079774516373446272006727)
          ·
            refine ⟨15119661774560169408010091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10079774516373446272006727 15119661774560169408010091)
            ·
              refine ⟨22679492661840254112015137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15119661774560169408010091 22679492661840254112015137)
              ·
                refine ⟨17009619496380190584011353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22679492661840254112015137 17009619496380190584011353)
                ·
                  refine ⟨12757214622285142938008515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17009619496380190584011353 12757214622285142938008515)
                  ·
                    refine ⟨19135821933427714407012773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12757214622285142938008515 19135821933427714407012773)
                    ·
                      refine ⟨3587966612517696451314895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19135821933427714407012773 3587966612517696451314895)
                      ·
                        rfl

theorem cell23_6987540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6987540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987540 prefixEnd_6987540 := by exact prefixLift 6987540
  have htrace : WordTrace (prefixWord ++ tailWord_6987540) baseStart_6987540 baseEnd_6987540 := by
    simpa [prefixWord, tailWord_6987540, baseEnd_6987540] using wordTrace_append hprefix tailTrace_6987540
  have hstable : (prefixWord ++ tailWord_6987540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987540).length < 2 ^ (prefixWord ++ tailWord_6987540).sum := by decide
  have hdescent : baseEnd_6987540 < baseStart_6987540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987576 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 1, 5]
def baseStart_6987576 : Nat := 118140960795 + 6987576 * 2 ^ 59
def prefixEnd_6987576 : Nat := 4983230072969 + 3 ^ 40 * 6987576 * 2
def baseEnd_6987576 : Nat := 1195995032607086103488243

theorem tailTrace_6987576 : CollatzResearch.WordTrace tailWord_6987576 prefixEnd_6987576 1195995032607086103488243 := by
  unfold tailWord_6987576
  simp only [CollatzResearch.WordTrace]
  refine ⟨127428917066606504907919291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169905222755475339877225721 127428917066606504907919291)
  ·
    refine ⟨191143375599909757361878937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127428917066606504907919291 191143375599909757361878937)
    ·
      refine ⟨143357531699932318021409203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191143375599909757361878937 143357531699932318021409203)
      ·
        refine ⟨215036297549898477032113805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143357531699932318021409203 215036297549898477032113805)
        ·
          refine ⟨80638611581211928887042677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215036297549898477032113805 80638611581211928887042677)
          ·
            refine ⟨7559869835738618333160251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80638611581211928887042677 7559869835738618333160251)
            ·
              refine ⟨11339804753607927499740377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7559869835738618333160251 11339804753607927499740377)
              ·
                refine ⟨8504853565205945624805283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11339804753607927499740377 8504853565205945624805283)
                ·
                  refine ⟨12757280347808918437207925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8504853565205945624805283 12757280347808918437207925)
                  ·
                    refine ⟨1195995032607086103488243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12757280347808918437207925 1195995032607086103488243)
                    ·
                      rfl

theorem cell23_6987576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_6987576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987576 prefixEnd_6987576 := by exact prefixLift 6987576
  have htrace : WordTrace (prefixWord ++ tailWord_6987576) baseStart_6987576 baseEnd_6987576 := by
    simpa [prefixWord, tailWord_6987576, baseEnd_6987576] using wordTrace_append hprefix tailTrace_6987576
  have hstable : (prefixWord ++ tailWord_6987576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987576).length < 2 ^ (prefixWord ++ tailWord_6987576).sum := by decide
  have hdescent : baseEnd_6987576 < baseStart_6987576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987583 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 2, 3, 2]
def baseStart_6987583 : Nat := 118140960795 + 6987583 * 2 ^ 59
def prefixEnd_6987583 : Nat := 4983230072969 + 3 ^ 40 * 6987583 * 2
def baseEnd_6987583 : Nat := 3587988692185839783077197

theorem tailTrace_6987583 : CollatzResearch.WordTrace tailWord_6987583 prefixEnd_6987583 3587988692185839783077197 := by
  unfold tailWord_6987583
  simp only [CollatzResearch.WordTrace]
  refine ⟨254858089444187650011343403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169905392962791766674228935 254858089444187650011343403)
  ·
    refine ⟨382287134166281475017015105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254858089444187650011343403 382287134166281475017015105)
    ·
      refine ⟨286715350624711106262761329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382287134166281475017015105 286715350624711106262761329)
      ·
        refine ⟨215036512968533329697070997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286715350624711106262761329 215036512968533329697070997)
        ·
          refine ⟨10079836545399999829550203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 215036512968533329697070997 10079836545399999829550203)
          ·
            refine ⟨15119754818099999744325305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10079836545399999829550203 15119754818099999744325305)
            ·
              refine ⟨11339816113574999808243979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15119754818099999744325305 11339816113574999808243979)
              ·
                refine ⟨17009724170362499712365969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11339816113574999808243979 17009724170362499712365969)
                ·
                  refine ⟨12757293127771874784274477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17009724170362499712365969 12757293127771874784274477)
                  ·
                    refine ⟨4783984922914453044102929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12757293127771874784274477 4783984922914453044102929)
                    ·
                      refine ⟨3587988692185839783077197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4783984922914453044102929 3587988692185839783077197)
                      ·
                        rfl

theorem cell23_6987583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_6987583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987583 prefixEnd_6987583 := by exact prefixLift 6987583
  have htrace : WordTrace (prefixWord ++ tailWord_6987583) baseStart_6987583 baseEnd_6987583 := by
    simpa [prefixWord, tailWord_6987583, baseEnd_6987583] using wordTrace_append hprefix tailTrace_6987583
  have hstable : (prefixWord ++ tailWord_6987583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987583).length < 2 ^ (prefixWord ++ tailWord_6987583).sum := by decide
  have hdescent : baseEnd_6987583 < baseStart_6987583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987602 : List Nat := [3, 2, 2, 1, 1, 14]
def baseStart_6987602 : Nat := 118140960795 + 6987602 * 2 ^ 59
def prefixEnd_6987602 : Nat := 4983230072969 + 3 ^ 40 * 6987602 * 2
def baseEnd_6987602 : Nat := 14765425713243930900163

theorem tailTrace_6987602 : CollatzResearch.WordTrace tailWord_6987602 prefixEnd_6987602 14765425713243930900163 := by
  unfold tailWord_6987602
  simp only [CollatzResearch.WordTrace]
  refine ⟨63714695607779704064071265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169905854954079210837523373 63714695607779704064071265)
  ·
    refine ⟨47786021705834778048053449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63714695607779704064071265 47786021705834778048053449)
    ·
      refine ⟨35839516279376083536040087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47786021705834778048053449 35839516279376083536040087)
      ·
        refine ⟨53759274419064125304060131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35839516279376083536040087 53759274419064125304060131)
        ·
          refine ⟨80638911628596187956090197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53759274419064125304060131 80638911628596187956090197)
          ·
            refine ⟨14765425713243930900163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 80638911628596187956090197 14765425713243930900163)
            ·
              rfl

theorem cell23_6987602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 14].length) (baseStart_6987602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987602 prefixEnd_6987602 := by exact prefixLift 6987602
  have htrace : WordTrace (prefixWord ++ tailWord_6987602) baseStart_6987602 baseEnd_6987602 := by
    simpa [prefixWord, tailWord_6987602, baseEnd_6987602] using wordTrace_append hprefix tailTrace_6987602
  have hstable : (prefixWord ++ tailWord_6987602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987602).length < 2 ^ (prefixWord ++ tailWord_6987602).sum := by decide
  have hdescent : baseEnd_6987602 < baseStart_6987602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987607 : List Nat := [1, 1, 3, 2, 5, 2, 2, 2, 1, 1, 3]
def baseStart_6987607 : Nat := 118140960795 + 6987607 * 2 ^ 59
def prefixEnd_6987607 : Nat := 4983230072969 + 3 ^ 40 * 6987607 * 2
def baseEnd_6987607 : Nat := 3588001015721547689177087

theorem tailTrace_6987607 : CollatzResearch.WordTrace tailWord_6987607 prefixEnd_6987607 3588001015721547689177087 := by
  unfold tailWord_6987607
  simp only [CollatzResearch.WordTrace]
  refine ⟨254858964796100702110217075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169905976530733801406811383 254858964796100702110217075)
  ·
    refine ⟨382288447194151053165325613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254858964796100702110217075 382288447194151053165325613)
    ·
      refine ⟨143358167697806644936997105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382288447194151053165325613 143358167697806644936997105)
      ·
        refine ⟨107518625773354983702747829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143358167697806644936997105 107518625773354983702747829)
        ·
          refine ⟨10079871166252029722132609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107518625773354983702747829 10079871166252029722132609)
          ·
            refine ⟨7559903374689022291599457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10079871166252029722132609 7559903374689022291599457)
            ·
              refine ⟨5669927531016766718699593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7559903374689022291599457 5669927531016766718699593)
              ·
                refine ⟨4252445648262575039024695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5669927531016766718699593 4252445648262575039024695)
                ·
                  refine ⟨6378668472393862558537043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4252445648262575039024695 6378668472393862558537043)
                  ·
                    refine ⟨9568002708590793837805565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6378668472393862558537043 9568002708590793837805565)
                    ·
                      refine ⟨3588001015721547689177087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9568002708590793837805565 3588001015721547689177087)
                      ·
                        rfl

theorem cell23_6987607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_6987607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987607 prefixEnd_6987607 := by exact prefixLift 6987607
  have htrace : WordTrace (prefixWord ++ tailWord_6987607) baseStart_6987607 baseEnd_6987607 := by
    simpa [prefixWord, tailWord_6987607, baseEnd_6987607] using wordTrace_append hprefix tailTrace_6987607
  have hstable : (prefixWord ++ tailWord_6987607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987607).length < 2 ^ (prefixWord ++ tailWord_6987607).sum := by decide
  have hdescent : baseEnd_6987607 < baseStart_6987607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987630 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_6987630 : Nat := 118140960795 + 6987630 * 2 ^ 59
def prefixEnd_6987630 : Nat := 4983230072969 + 3 ^ 40 * 6987630 * 2
def baseEnd_6987630 : Nat := 3588012825776601099189481

theorem tailTrace_6987630 : CollatzResearch.WordTrace tailWord_6987630 prefixEnd_6987630 3588012825776601099189481 := by
  unfold tailWord_6987630
  simp only [CollatzResearch.WordTrace]
  refine ⟨31857475459377172129788043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169906535783344918025536229 31857475459377172129788043)
  ·
    refine ⟨47786213189065758194682065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31857475459377172129788043 47786213189065758194682065)
    ·
      refine ⟨35839659891799318646011549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47786213189065758194682065 35839659891799318646011549)
      ·
        refine ⟨13439872459424744492254331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35839659891799318646011549 13439872459424744492254331)
        ·
          refine ⟨20159808689137116738381497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13439872459424744492254331 20159808689137116738381497)
          ·
            refine ⟨15119856516852837553786123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20159808689137116738381497 15119856516852837553786123)
            ·
              refine ⟨22679784775279256330679185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15119856516852837553786123 22679784775279256330679185)
              ·
                refine ⟨17009838581459442248009389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22679784775279256330679185 17009838581459442248009389)
                ·
                  refine ⟨6378689468047290843003521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17009838581459442248009389 6378689468047290843003521)
                  ·
                    refine ⟨4784017101035468132252641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6378689468047290843003521 4784017101035468132252641)
                    ·
                      refine ⟨3588012825776601099189481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4784017101035468132252641 3588012825776601099189481)
                      ·
                        rfl

theorem cell23_6987630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_6987630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987630 prefixEnd_6987630 := by exact prefixLift 6987630
  have htrace : WordTrace (prefixWord ++ tailWord_6987630) baseStart_6987630 baseEnd_6987630 := by
    simpa [prefixWord, tailWord_6987630, baseEnd_6987630] using wordTrace_append hprefix tailTrace_6987630
  have hstable : (prefixWord ++ tailWord_6987630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987630).length < 2 ^ (prefixWord ++ tailWord_6987630).sum := by decide
  have hdescent : baseEnd_6987630 < baseStart_6987630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987632 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 4, 7]
def baseStart_6987632 : Nat := 118140960795 + 6987632 * 2 ^ 59
def prefixEnd_6987632 : Nat := 4983230072969 + 3 ^ 40 * 6987632 * 2
def baseEnd_6987632 : Nat := 1196004617579303363788157

theorem tailTrace_6987632 : CollatzResearch.WordTrace tailWord_6987632 prefixEnd_6987632 1196004617579303363788157 := by
  unfold tailWord_6987632
  simp only [CollatzResearch.WordTrace]
  refine ⟨127429938310505065689938575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169906584414006754253251433 127429938310505065689938575)
  ·
    refine ⟨191144907465757598534907863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127429938310505065689938575 191144907465757598534907863)
    ·
      refine ⟨286717361198636397802361795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191144907465757598534907863 286717361198636397802361795)
      ·
        refine ⟨430076041797954596703542693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286717361198636397802361795 430076041797954596703542693)
        ·
          refine ⟨80639257837116486881914255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430076041797954596703542693 80639257837116486881914255)
          ·
            refine ⟨120958886755674730322871383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80639257837116486881914255 120958886755674730322871383)
            ·
              refine ⟨181438330133512095484307075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120958886755674730322871383 181438330133512095484307075)
              ·
                refine ⟨272157495200268143226460613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181438330133512095484307075 272157495200268143226460613)
                ·
                  refine ⟨51029530350050276854961365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272157495200268143226460613 51029530350050276854961365)
                  ·
                    refine ⟨1196004617579303363788157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51029530350050276854961365 1196004617579303363788157)
                    ·
                      rfl

theorem cell23_6987632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_6987632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987632 prefixEnd_6987632 := by exact prefixLift 6987632
  have htrace : WordTrace (prefixWord ++ tailWord_6987632) baseStart_6987632 baseEnd_6987632 := by
    simpa [prefixWord, tailWord_6987632, baseEnd_6987632] using wordTrace_append hprefix tailTrace_6987632
  have hstable : (prefixWord ++ tailWord_6987632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987632).length < 2 ^ (prefixWord ++ tailWord_6987632).sum := by decide
  have hdescent : baseEnd_6987632 < baseStart_6987632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987813 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_6987813 : Nat := 118140960795 + 6987813 * 2 ^ 59
def prefixEnd_6987813 : Nat := 4983230072969 + 3 ^ 40 * 6987813 * 2
def baseEnd_6987813 : Nat := 3588106792736373883201139

theorem tailTrace_6987813 : CollatzResearch.WordTrace tailWord_6987813 prefixEnd_6987813 3588106792736373883201139 := by
  unfold tailWord_6987813
  simp only [CollatzResearch.WordTrace]
  refine ⟨254866478233354399292216093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169910985488902932861477395 254866478233354399292216093)
  ·
    refine ⟨95574929337507899734581035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254866478233354399292216093 95574929337507899734581035)
    ·
      refine ⟨143362394006261849601871553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95574929337507899734581035 143362394006261849601871553)
      ·
        refine ⟨107521795504696387201403665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143362394006261849601871553 107521795504696387201403665)
        ·
          refine ⟨80641346628522290401052749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107521795504696387201403665 80641346628522290401052749)
          ·
            refine ⟨30240504985695858900394781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80641346628522290401052749 30240504985695858900394781)
            ·
              refine ⟨11340189369635947087648043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30240504985695858900394781 11340189369635947087648043)
              ·
                refine ⟨17010284054453920631472065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11340189369635947087648043 17010284054453920631472065)
                ·
                  refine ⟨12757713040840440473604049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17010284054453920631472065 12757713040840440473604049)
                  ·
                    refine ⟨9568284780630330355203037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12757713040840440473604049 9568284780630330355203037)
                    ·
                      refine ⟨3588106792736373883201139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9568284780630330355203037 3588106792736373883201139)
                      ·
                        rfl

theorem cell23_6987813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_6987813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987813 prefixEnd_6987813 := by exact prefixLift 6987813
  have htrace : WordTrace (prefixWord ++ tailWord_6987813) baseStart_6987813 baseEnd_6987813 := by
    simpa [prefixWord, tailWord_6987813, baseEnd_6987813] using wordTrace_append hprefix tailTrace_6987813
  have hstable : (prefixWord ++ tailWord_6987813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987813).length < 2 ^ (prefixWord ++ tailWord_6987813).sum := by decide
  have hdescent : baseEnd_6987813 < baseStart_6987813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987876 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_6987876 : Nat := 118140960795 + 6987876 * 2 ^ 59
def prefixEnd_6987876 : Nat := 4983230072969 + 3 ^ 40 * 6987876 * 2
def baseEnd_6987876 : Nat := 1196046380672535712237783

theorem tailTrace_6987876 : CollatzResearch.WordTrace tailWord_6987876 prefixEnd_6987876 1196046380672535712237783 := by
  unfold tailWord_6987876
  simp only [CollatzResearch.WordTrace]
  refine ⟨127434388016063080525879741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169912517354750774034506321 127434388016063080525879741)
  ·
    refine ⟨47787895506023655197204903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127434388016063080525879741 47787895506023655197204903)
    ·
      refine ⟨71681843259035482795807355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47787895506023655197204903 71681843259035482795807355)
      ·
        refine ⟨107522764888553224193711033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71681843259035482795807355 107522764888553224193711033)
        ·
          refine ⟨80642073666414918145283275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107522764888553224193711033 80642073666414918145283275)
          ·
            refine ⟨120963110499622377217924913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80642073666414918145283275 120963110499622377217924913)
            ·
              refine ⟨90722332874716782913443685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120963110499622377217924913 90722332874716782913443685)
              ·
                refine ⟨17010437414009396796270691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90722332874716782913443685 17010437414009396796270691)
                ·
                  refine ⟨25515656121014095194406037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17010437414009396796270691 25515656121014095194406037)
                  ·
                    refine ⟨1196046380672535712237783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25515656121014095194406037 1196046380672535712237783)
                    ·
                      rfl

theorem cell23_6987876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_6987876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987876 prefixEnd_6987876 := by exact prefixLift 6987876
  have htrace : WordTrace (prefixWord ++ tailWord_6987876) baseStart_6987876 baseEnd_6987876 := by
    simpa [prefixWord, tailWord_6987876, baseEnd_6987876] using wordTrace_append hprefix tailTrace_6987876
  have hstable : (prefixWord ++ tailWord_6987876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987876).length < 2 ^ (prefixWord ++ tailWord_6987876).sum := by decide
  have hdescent : baseEnd_6987876 < baseStart_6987876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987877 : List Nat := [1, 3, 1, 3, 2, 2, 3, 3, 1, 1, 3]
def baseStart_6987877 : Nat := 118140960795 + 6987877 * 2 ^ 59
def prefixEnd_6987877 : Nat := 4983230072969 + 3 ^ 40 * 6987877 * 2
def baseEnd_6987877 : Nat := 3588139655498261632800845

theorem tailTrace_6987877 : CollatzResearch.WordTrace tailWord_6987877 prefixEnd_6987877 3588139655498261632800845 := by
  unfold tailWord_6987877
  simp only [CollatzResearch.WordTrace]
  refine ⟨254868812505122538222545885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169912541670081692148363923 254868812505122538222545885)
  ·
    refine ⟨95575804689420951833454707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254868812505122538222545885 95575804689420951833454707)
    ·
      refine ⟨143363707034131427750182061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95575804689420951833454707 143363707034131427750182061)
      ·
        refine ⟨53761390137799285406318273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143363707034131427750182061 53761390137799285406318273)
        ·
          refine ⟨40321042603349464054738705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53761390137799285406318273 40321042603349464054738705)
          ·
            refine ⟨30240781952512098041054029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40321042603349464054738705 30240781952512098041054029)
            ·
              refine ⟨11340293232192036765395261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30240781952512098041054029 11340293232192036765395261)
              ·
                refine ⟨4252609962072013787023223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11340293232192036765395261 4252609962072013787023223)
                ·
                  refine ⟨6378914943108020680534835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4252609962072013787023223 6378914943108020680534835)
                  ·
                    refine ⟨9568372414662031020802253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6378914943108020680534835 9568372414662031020802253)
                    ·
                      refine ⟨3588139655498261632800845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9568372414662031020802253 3588139655498261632800845)
                      ·
                        rfl

theorem cell23_6987877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_6987877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987877 prefixEnd_6987877 := by exact prefixLift 6987877
  have htrace : WordTrace (prefixWord ++ tailWord_6987877) baseStart_6987877 baseEnd_6987877 := by
    simpa [prefixWord, tailWord_6987877, baseEnd_6987877] using wordTrace_append hprefix tailTrace_6987877
  have hstable : (prefixWord ++ tailWord_6987877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987877).length < 2 ^ (prefixWord ++ tailWord_6987877).sum := by decide
  have hdescent : baseEnd_6987877 < baseStart_6987877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987930 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_6987930 : Nat := 118140960795 + 6987930 * 2 ^ 59
def prefixEnd_6987930 : Nat := 4983230072969 + 3 ^ 40 * 6987930 * 2
def baseEnd_6987930 : Nat := 3588166869972949925438101

theorem tailTrace_6987930 : CollatzResearch.WordTrace tailWord_6987930 prefixEnd_6987930 3588166869972949925438101 := by
  unfold tailWord_6987930
  simp only [CollatzResearch.WordTrace]
  refine ⟨63717686393482632068556311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169913830382620352182816829 63717686393482632068556311)
  ·
    refine ⟨95576529590223948102834467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63717686393482632068556311 95576529590223948102834467)
    ·
      refine ⟨143364794385335922154251701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95576529590223948102834467 143364794385335922154251701)
      ·
        refine ⟨13440449473625242701961097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143364794385335922154251701 13440449473625242701961097)
        ·
          refine ⟨10080337105218932026470823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13440449473625242701961097 10080337105218932026470823)
          ·
            refine ⟨15120505657828398039706235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10080337105218932026470823 15120505657828398039706235)
            ·
              refine ⟨22680758486742597059559353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15120505657828398039706235 22680758486742597059559353)
              ·
                refine ⟨17010568865056947794669515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22680758486742597059559353 17010568865056947794669515)
                ·
                  refine ⟨25515853297585421692004273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17010568865056947794669515 25515853297585421692004273)
                  ·
                    refine ⟨19136889973189066269003205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25515853297585421692004273 19136889973189066269003205)
                    ·
                      refine ⟨3588166869972949925438101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19136889973189066269003205 3588166869972949925438101)
                      ·
                        rfl

theorem cell23_6987930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_6987930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987930 prefixEnd_6987930 := by exact prefixLift 6987930
  have htrace : WordTrace (prefixWord ++ tailWord_6987930) baseStart_6987930 baseEnd_6987930 := by
    simpa [prefixWord, tailWord_6987930, baseEnd_6987930] using wordTrace_append hprefix tailTrace_6987930
  have hstable : (prefixWord ++ tailWord_6987930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987930).length < 2 ^ (prefixWord ++ tailWord_6987930).sum := by decide
  have hdescent : baseEnd_6987930 < baseStart_6987930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987933 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_6987933 : Nat := 118140960795 + 6987933 * 2 ^ 59
def prefixEnd_6987933 : Nat := 4983230072969 + 3 ^ 40 * 6987933 * 2
def baseEnd_6987933 : Nat := 3588168410414913413700587

theorem tailTrace_6987933 : CollatzResearch.WordTrace tailWord_6987933 prefixEnd_6987933 3588168410414913413700587 := by
  unfold tailWord_6987933
  simp only [CollatzResearch.WordTrace]
  refine ⟨254870854992919659786584453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169913903328613106524389635 254870854992919659786584453)
  ·
    refine ⟨47788285311172436209984585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254870854992919659786584453 47788285311172436209984585)
    ·
      refine ⟨35841213983379327157488439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47788285311172436209984585 35841213983379327157488439)
      ·
        refine ⟨53761820975068990736232659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35841213983379327157488439 53761820975068990736232659)
        ·
          refine ⟨80642731462603486104348989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53761820975068990736232659 80642731462603486104348989)
          ·
            refine ⟨30241024298476307289130871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80642731462603486104348989 30241024298476307289130871)
            ·
              refine ⟨45361536447714460933696307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30241024298476307289130871 45361536447714460933696307)
              ·
                refine ⟨68042304671571691400544461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45361536447714460933696307 68042304671571691400544461)
                ·
                  refine ⟨25515864251839384275204173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68042304671571691400544461 25515864251839384275204173)
                  ·
                    refine ⟨9568449094439769103201565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25515864251839384275204173 9568449094439769103201565)
                    ·
                      refine ⟨3588168410414913413700587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9568449094439769103201565 3588168410414913413700587)
                      ·
                        rfl

theorem cell23_6987933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_6987933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987933 prefixEnd_6987933 := by exact prefixLift 6987933
  have htrace : WordTrace (prefixWord ++ tailWord_6987933) baseStart_6987933 baseEnd_6987933 := by
    simpa [prefixWord, tailWord_6987933, baseEnd_6987933] using wordTrace_append hprefix tailTrace_6987933
  have hstable : (prefixWord ++ tailWord_6987933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987933).length < 2 ^ (prefixWord ++ tailWord_6987933).sum := by decide
  have hdescent : baseEnd_6987933 < baseStart_6987933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987934 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_6987934 : Nat := 118140960795 + 6987934 * 2 ^ 59
def prefixEnd_6987934 : Nat := 4983230072969 + 3 ^ 40 * 6987934 * 2
def baseEnd_6987934 : Nat := 3588168923895567909788083

theorem tailTrace_6987934 : CollatzResearch.WordTrace tailWord_6987934 prefixEnd_6987934 3588168923895567909788083 := by
  unfold tailWord_6987934
  simp only [CollatzResearch.WordTrace]
  refine ⟨31858861433239504619671357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169913927643944024638247237 31858861433239504619671357)
  ·
    refine ⟨11947073037464814232376759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31858861433239504619671357 11947073037464814232376759)
    ·
      refine ⟨17920609556197221348565139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11947073037464814232376759 17920609556197221348565139)
      ·
        refine ⟨26880914334295832022847709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17920609556197221348565139 26880914334295832022847709)
        ·
          refine ⟨10080342875360937008567891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26880914334295832022847709 10080342875360937008567891)
          ·
            refine ⟨15120514313041405512851837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10080342875360937008567891 15120514313041405512851837)
            ·
              refine ⟨5670192867390527067319439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15120514313041405512851837 5670192867390527067319439)
              ·
                refine ⟨8505289301085790600979159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5670192867390527067319439 8505289301085790600979159)
                ·
                  refine ⟨12757933951628685901468739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8505289301085790600979159 12757933951628685901468739)
                  ·
                    refine ⟨19136900927443028852203109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12757933951628685901468739 19136900927443028852203109)
                    ·
                      refine ⟨3588168923895567909788083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19136900927443028852203109 3588168923895567909788083)
                      ·
                        rfl

theorem cell23_6987934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_6987934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987934 prefixEnd_6987934 := by exact prefixLift 6987934
  have htrace : WordTrace (prefixWord ++ tailWord_6987934) baseStart_6987934 baseEnd_6987934 := by
    simpa [prefixWord, tailWord_6987934, baseEnd_6987934] using wordTrace_append hprefix tailTrace_6987934
  have hstable : (prefixWord ++ tailWord_6987934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987934).length < 2 ^ (prefixWord ++ tailWord_6987934).sum := by decide
  have hdescent : baseEnd_6987934 < baseStart_6987934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987937 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_6987937 : Nat := 118140960795 + 6987937 * 2 ^ 59
def prefixEnd_6987937 : Nat := 4983230072969 + 3 ^ 40 * 6987937 * 2
def baseEnd_6987937 : Nat := 3588170464337531398050569

theorem tailTrace_6987937 : CollatzResearch.WordTrace tailWord_6987937 prefixEnd_6987937 3588170464337531398050569 := by
  unfold tailWord_6987937
  simp only [CollatzResearch.WordTrace]
  refine ⟨254871000884905168469730065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169914000589936778979820043 254871000884905168469730065)
  ·
    refine ⟨191153250663678876352297549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254871000884905168469730065 191153250663678876352297549)
    ·
      refine ⟨71682468998879578632111581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191153250663678876352297549 71682468998879578632111581)
      ·
        refine ⟨26880925874579841987041843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71682468998879578632111581 26880925874579841987041843)
        ·
          refine ⟨40321388811869762980562765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26880925874579841987041843 40321388811869762980562765)
          ·
            refine ⟨15120520804451161117711037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40321388811869762980562765 15120520804451161117711037)
            ·
              refine ⟨5670195301669185419141639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15120520804451161117711037 5670195301669185419141639)
              ·
                refine ⟨8505292952503778128712459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5670195301669185419141639 8505292952503778128712459)
                ·
                  refine ⟨12757939428755667193068689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8505292952503778128712459 12757939428755667193068689)
                  ·
                    refine ⟨9568454571566750394801517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12757939428755667193068689 9568454571566750394801517)
                    ·
                      refine ⟨3588170464337531398050569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9568454571566750394801517 3588170464337531398050569)
                      ·
                        rfl

theorem cell23_6987937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_6987937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987937 prefixEnd_6987937 := by exact prefixLift 6987937
  have htrace : WordTrace (prefixWord ++ tailWord_6987937) baseStart_6987937 baseEnd_6987937 := by
    simpa [prefixWord, tailWord_6987937, baseEnd_6987937] using wordTrace_append hprefix tailTrace_6987937
  have hstable : (prefixWord ++ tailWord_6987937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987937).length < 2 ^ (prefixWord ++ tailWord_6987937).sum := by decide
  have hdescent : baseEnd_6987937 < baseStart_6987937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6987957 : List Nat := [1, 3, 3, 4, 2, 1, 1, 8]
def baseStart_6987957 : Nat := 118140960795 + 6987957 * 2 ^ 59
def prefixEnd_6987957 : Nat := 4983230072969 + 3 ^ 40 * 6987957 * 2
def baseEnd_6987957 : Nat := 132895582738911900733351

theorem tailTrace_6987957 : CollatzResearch.WordTrace tailWord_6987957 prefixEnd_6987957 132895582738911900733351 := by
  unfold tailWord_6987957
  simp only [CollatzResearch.WordTrace]
  refine ⟨254871730344832711885458125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169914486896555141256972083 254871730344832711885458125)
  ·
    refine ⟨95576898879312266957046797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254871730344832711885458125 95576898879312266957046797)
    ·
      refine ⟨35841337079742100108892549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95576898879312266957046797 35841337079742100108892549)
      ·
        refine ⟨6720250702451643770417353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35841337079742100108892549 6720250702451643770417353)
        ·
          refine ⟨5040188026838732827813015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6720250702451643770417353 5040188026838732827813015)
          ·
            refine ⟨7560282040258099241719523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040188026838732827813015 7560282040258099241719523)
            ·
              refine ⟨11340423060387148862579285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7560282040258099241719523 11340423060387148862579285)
              ·
                refine ⟨132895582738911900733351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11340423060387148862579285 132895582738911900733351)
                ·
                  rfl

theorem cell23_6987957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 8].length) (baseStart_6987957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6987957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6987957 prefixEnd_6987957 := by exact prefixLift 6987957
  have htrace : WordTrace (prefixWord ++ tailWord_6987957) baseStart_6987957 baseEnd_6987957 := by
    simpa [prefixWord, tailWord_6987957, baseEnd_6987957] using wordTrace_append hprefix tailTrace_6987957
  have hstable : (prefixWord ++ tailWord_6987957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6987957).length < 2 ^ (prefixWord ++ tailWord_6987957).sum := by decide
  have hdescent : baseEnd_6987957 < baseStart_6987957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6987957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988043 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 2, 5]
def baseStart_6988043 : Nat := 118140960795 + 6988043 * 2 ^ 59
def prefixEnd_6988043 : Nat := 4983230072969 + 3 ^ 40 * 6988043 * 2
def baseEnd_6988043 : Nat := 1196074964428969327775027

theorem tailTrace_6988043 : CollatzResearch.WordTrace tailWord_6988043 prefixEnd_6988043 1196074964428969327775027 := by
  unfold tailWord_6988043
  simp only [CollatzResearch.WordTrace]
  refine ⟨254874867022521148573088783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169916578015014099048725855 254874867022521148573088783)
  ·
    refine ⟨382312300533781722859633175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254874867022521148573088783 382312300533781722859633175)
    ·
      refine ⟨573468450800672584289449763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382312300533781722859633175 573468450800672584289449763)
      ·
        refine ⟨860202676201008876434174645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573468450800672584289449763 860202676201008876434174645)
        ·
          refine ⟨80644000893844582165703873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 860202676201008876434174645 80644000893844582165703873)
          ·
            refine ⟨60483000670383436624277905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80644000893844582165703873 60483000670383436624277905)
            ·
              refine ⟨45362250502787577468208429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60483000670383436624277905 45362250502787577468208429)
              ·
                refine ⟨17010843938545341550578161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45362250502787577468208429 17010843938545341550578161)
                ·
                  refine ⟨12758132953909006162933621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17010843938545341550578161 12758132953909006162933621)
                  ·
                    refine ⟨1196074964428969327775027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12758132953909006162933621 1196074964428969327775027)
                    ·
                      rfl

theorem cell23_6988043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 5].length) (baseStart_6988043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988043 prefixEnd_6988043 := by exact prefixLift 6988043
  have htrace : WordTrace (prefixWord ++ tailWord_6988043) baseStart_6988043 baseEnd_6988043 := by
    simpa [prefixWord, tailWord_6988043, baseEnd_6988043] using wordTrace_append hprefix tailTrace_6988043
  have hstable : (prefixWord ++ tailWord_6988043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988043).length < 2 ^ (prefixWord ++ tailWord_6988043).sum := by decide
  have hdescent : baseEnd_6988043 < baseStart_6988043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988157 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_6988157 : Nat := 118140960795 + 6988157 * 2 ^ 59
def prefixEnd_6988157 : Nat := 4983230072969 + 3 ^ 40 * 6988157 * 2
def baseEnd_6988157 : Nat := 3588283430081520537299557

theorem tailTrace_6988157 : CollatzResearch.WordTrace tailWord_6988157 prefixEnd_6988157 3588283430081520537299557 := by
  unfold tailWord_6988157
  simp only [CollatzResearch.WordTrace]
  refine ⟨254879024944108146042738725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169919349962738764028492483 254879024944108146042738725)
  ·
    refine ⟨47789817177020277383013511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254879024944108146042738725 47789817177020277383013511)
    ·
      refine ⟨71684725765530416074520267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47789817177020277383013511 71684725765530416074520267)
      ·
        refine ⟨107527088648295624111780401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71684725765530416074520267 107527088648295624111780401)
        ·
          refine ⟨80645316486221718083835301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107527088648295624111780401 80645316486221718083835301)
          ·
            refine ⟨15120996841166572140719119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80645316486221718083835301 15120996841166572140719119)
            ·
              refine ⟨22681495261749858211078679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15120996841166572140719119 22681495261749858211078679)
              ·
                refine ⟨34022242892624787316618019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22681495261749858211078679 34022242892624787316618019)
                ·
                  refine ⟨51033364338937180974927029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34022242892624787316618019 51033364338937180974927029)
                  ·
                    refine ⟨4784377906775360716399409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51033364338937180974927029 4784377906775360716399409)
                    ·
                      refine ⟨3588283430081520537299557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4784377906775360716399409 3588283430081520537299557)
                      ·
                        rfl

theorem cell23_6988157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_6988157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988157 prefixEnd_6988157 := by exact prefixLift 6988157
  have htrace : WordTrace (prefixWord ++ tailWord_6988157) baseStart_6988157 baseEnd_6988157 := by
    simpa [prefixWord, tailWord_6988157, baseEnd_6988157] using wordTrace_append hprefix tailTrace_6988157
  have hstable : (prefixWord ++ tailWord_6988157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988157).length < 2 ^ (prefixWord ++ tailWord_6988157).sum := by decide
  have hdescent : baseEnd_6988157 < baseStart_6988157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988223 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 3, 9]
def baseStart_6988223 : Nat := 118140960795 + 6988223 * 2 ^ 59
def prefixEnd_6988223 : Nat := 4983230072969 + 3 ^ 40 * 6988223 * 2
def baseEnd_6988223 : Nat := 1196105773268239093024751

theorem tailTrace_6988223 : CollatzResearch.WordTrace tailWord_6988223 prefixEnd_6988223 1196105773268239093024751 := by
  unfold tailWord_6988223
  simp only [CollatzResearch.WordTrace]
  refine ⟨254881432161869039314641323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169920954774579359543094215 254881432161869039314641323)
  ·
    refine ⟨382322148242803558971961985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254881432161869039314641323 382322148242803558971961985)
    ·
      refine ⟨286741611182102669228971489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382322148242803558971961985 286741611182102669228971489)
      ·
        refine ⟨215056208386577001921728617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286741611182102669228971489 215056208386577001921728617)
        ·
          refine ⟨161292156289932751441296463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215056208386577001921728617 161292156289932751441296463)
          ·
            refine ⟨241938234434899127161944695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161292156289932751441296463 241938234434899127161944695)
            ·
              refine ⟨362907351652348690742917043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241938234434899127161944695 362907351652348690742917043)
              ·
                refine ⟨544361027478523036114375565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362907351652348690742917043 544361027478523036114375565)
                ·
                  refine ⟨204135385304446138542890837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544361027478523036114375565 204135385304446138542890837)
                  ·
                    refine ⟨1196105773268239093024751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 204135385304446138542890837 1196105773268239093024751)
                    ·
                      rfl

theorem cell23_6988223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_6988223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988223 prefixEnd_6988223 := by exact prefixLift 6988223
  have htrace : WordTrace (prefixWord ++ tailWord_6988223) baseStart_6988223 baseEnd_6988223 := by
    simpa [prefixWord, tailWord_6988223, baseEnd_6988223] using wordTrace_append hprefix tailTrace_6988223
  have hstable : (prefixWord ++ tailWord_6988223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988223).length < 2 ^ (prefixWord ++ tailWord_6988223).sum := by decide
  have hdescent : baseEnd_6988223 < baseStart_6988223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988243 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 10]
def baseStart_6988243 : Nat := 118140960795 + 6988243 * 2 ^ 59
def prefixEnd_6988243 : Nat := 4983230072969 + 3 ^ 40 * 6988243 * 2
def baseEnd_6988243 : Nat := 3588327589417807200824161

theorem tailTrace_6988243 : CollatzResearch.WordTrace tailWord_6988243 prefixEnd_6988243 3588327589417807200824161 := by
  unfold tailWord_6988243
  simp only [CollatzResearch.WordTrace]
  refine ⟨254882161621796582730369383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169921441081197721820246255 254882161621796582730369383)
  ·
    refine ⟨382323242432694874095554075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254882161621796582730369383 382323242432694874095554075)
    ·
      refine ⟨573484863649042311143331113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382323242432694874095554075 573484863649042311143331113)
      ·
        refine ⟨430113647736781733357498335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573484863649042311143331113 430113647736781733357498335)
        ·
          refine ⟨645170471605172600036247503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430113647736781733357498335 645170471605172600036247503)
          ·
            refine ⟨967755707407758900054371255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645170471605172600036247503 967755707407758900054371255)
            ·
              refine ⟨1451633561111638350081556883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967755707407758900054371255 1451633561111638350081556883)
              ·
                refine ⟨2177450341667457525122335325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451633561111638350081556883 2177450341667457525122335325)
                ·
                  refine ⟨816543878125296571920875747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2177450341667457525122335325 816543878125296571920875747)
                  ·
                    refine ⟨1224815817187944857881313621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 816543878125296571920875747 1224815817187944857881313621)
                    ·
                      refine ⟨3588327589417807200824161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1224815817187944857881313621 3588327589417807200824161)
                      ·
                        rfl

theorem cell23_6988243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_6988243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988243 prefixEnd_6988243 := by exact prefixLift 6988243
  have htrace : WordTrace (prefixWord ++ tailWord_6988243) baseStart_6988243 baseEnd_6988243 := by
    simpa [prefixWord, tailWord_6988243, baseEnd_6988243] using wordTrace_append hprefix tailTrace_6988243
  have hstable : (prefixWord ++ tailWord_6988243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988243).length < 2 ^ (prefixWord ++ tailWord_6988243).sum := by decide
  have hdescent : baseEnd_6988243 < baseStart_6988243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988264 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_6988264 : Nat := 118140960795 + 6988264 * 2 ^ 59
def prefixEnd_6988264 : Nat := 4983230072969 + 3 ^ 40 * 6988264 * 2
def baseEnd_6988264 : Nat := 3588338372511551618661565

theorem tailTrace_6988264 : CollatzResearch.WordTrace tailWord_6988264 prefixEnd_6988264 3588338372511551618661565 := by
  unfold tailWord_6988264
  simp only [CollatzResearch.WordTrace]
  refine ⟨127441463777360251658441923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169921951703147002211255897 127441463777360251658441923)
  ·
    refine ⟨191162195666040377487662885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127441463777360251658441923 191162195666040377487662885)
    ·
      refine ⟨35842911687382570778936791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191162195666040377487662885 35842911687382570778936791)
      ·
        refine ⟨53764367531073856168405187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35842911687382570778936791 53764367531073856168405187)
        ·
          refine ⟨80646551296610784252607781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53764367531073856168405187 80646551296610784252607781)
          ·
            refine ⟨15121228368114522047363959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80646551296610784252607781 15121228368114522047363959)
            ·
              refine ⟨22681842552171783071045939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15121228368114522047363959 22681842552171783071045939)
              ·
                refine ⟨34022763828257674606568909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22681842552171783071045939 34022763828257674606568909)
                ·
                  refine ⟨12758536435596627977463341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34022763828257674606568909 12758536435596627977463341)
                  ·
                    refine ⟨4784451163348735491548753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12758536435596627977463341 4784451163348735491548753)
                    ·
                      refine ⟨3588338372511551618661565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4784451163348735491548753 3588338372511551618661565)
                      ·
                        rfl

theorem cell23_6988264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_6988264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988264 prefixEnd_6988264 := by exact prefixLift 6988264
  have htrace : WordTrace (prefixWord ++ tailWord_6988264) baseStart_6988264 baseEnd_6988264 := by
    simpa [prefixWord, tailWord_6988264, baseEnd_6988264] using wordTrace_append hprefix tailTrace_6988264
  have hstable : (prefixWord ++ tailWord_6988264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988264).length < 2 ^ (prefixWord ++ tailWord_6988264).sum := by decide
  have hdescent : baseEnd_6988264 < baseStart_6988264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988280 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_6988280 : Nat := 118140960795 + 6988280 * 2 ^ 59
def prefixEnd_6988280 : Nat := 4983230072969 + 3 ^ 40 * 6988280 * 2
def baseEnd_6988280 : Nat := 3588346588202023556061491

theorem tailTrace_6988280 : CollatzResearch.WordTrace tailWord_6988280 prefixEnd_6988280 3588346588202023556061491 := by
  unfold tailWord_6988280
  simp only [CollatzResearch.WordTrace]
  refine ⟨127441755561331269024733147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169922340748441692032977529 127441755561331269024733147)
  ·
    refine ⟨191162633341996903537099721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127441755561331269024733147 191162633341996903537099721)
    ·
      refine ⟨143371975006497677652824791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191162633341996903537099721 143371975006497677652824791)
      ·
        refine ⟨215057962509746516479237187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143371975006497677652824791 215057962509746516479237187)
        ·
          refine ⟨322586943764619774718855781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215057962509746516479237187 322586943764619774718855781)
          ·
            refine ⟨60485051955866207759785459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322586943764619774718855781 60485051955866207759785459)
            ·
              refine ⟨90727577933799311639678189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60485051955866207759785459 90727577933799311639678189)
              ·
                refine ⟨34022841725174741864879321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90727577933799311639678189 34022841725174741864879321)
                ·
                  refine ⟨25517131293881056398659491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34022841725174741864879321 25517131293881056398659491)
                  ·
                    refine ⟨38275696940821584597989237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25517131293881056398659491 38275696940821584597989237)
                    ·
                      refine ⟨3588346588202023556061491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38275696940821584597989237 3588346588202023556061491)
                      ·
                        rfl

theorem cell23_6988280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_6988280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988280 prefixEnd_6988280 := by exact prefixLift 6988280
  have htrace : WordTrace (prefixWord ++ tailWord_6988280) baseStart_6988280 baseEnd_6988280 := by
    simpa [prefixWord, tailWord_6988280, baseEnd_6988280] using wordTrace_append hprefix tailTrace_6988280
  have hstable : (prefixWord ++ tailWord_6988280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988280).length < 2 ^ (prefixWord ++ tailWord_6988280).sum := by decide
  have hdescent : baseEnd_6988280 < baseStart_6988280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988317 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 7]
def baseStart_6988317 : Nat := 118140960795 + 6988317 * 2 ^ 59
def prefixEnd_6988317 : Nat := 4983230072969 + 3 ^ 40 * 6988317 * 2
def baseEnd_6988317 : Nat := 398707287442915545699869

theorem tailTrace_6988317 : CollatzResearch.WordTrace tailWord_6988317 prefixEnd_6988317 398707287442915545699869 := by
  unfold tailWord_6988317
  simp only [CollatzResearch.WordTrace]
  refine ⟨254884860623528493368563205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169923240415685662245708803 254884860623528493368563205)
  ·
    refine ⟨47790911366911592506605601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254884860623528493368563205 47790911366911592506605601)
    ·
      refine ⟨35843183525183694379954201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47790911366911592506605601 35843183525183694379954201)
      ·
        refine ⟨26882387643887770784965651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35843183525183694379954201 26882387643887770784965651)
        ·
          refine ⟨40323581465831656177448477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26882387643887770784965651 40323581465831656177448477)
          ·
            refine ⟨15121343049686871066543179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40323581465831656177448477 15121343049686871066543179)
            ·
              refine ⟨22682014574530306599814769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15121343049686871066543179 22682014574530306599814769)
              ·
                refine ⟨17011510930897729949861077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22682014574530306599814769 17011510930897729949861077)
                ·
                  refine ⟨398707287442915545699869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17011510930897729949861077 398707287442915545699869)
                  ·
                    rfl

theorem cell23_6988317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_6988317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988317 prefixEnd_6988317 := by exact prefixLift 6988317
  have htrace : WordTrace (prefixWord ++ tailWord_6988317) baseStart_6988317 baseEnd_6988317 := by
    simpa [prefixWord, tailWord_6988317, baseEnd_6988317] using wordTrace_append hprefix tailTrace_6988317
  have hstable : (prefixWord ++ tailWord_6988317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988317).length < 2 ^ (prefixWord ++ tailWord_6988317).sum := by decide
  have hdescent : baseEnd_6988317 < baseStart_6988317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988387 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 3]
def baseStart_6988387 : Nat := 118140960795 + 6988387 * 2 ^ 59
def prefixEnd_6988387 : Nat := 4983230072969 + 3 ^ 40 * 6988387 * 2
def baseEnd_6988387 : Nat := 3588401530632054637423499

theorem tailTrace_6988387 : CollatzResearch.WordTrace tailWord_6988387 prefixEnd_6988387 3588401530632054637423499 := by
  unfold tailWord_6988387
  simp only [CollatzResearch.WordTrace]
  refine ⟨254887413733274895323611415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169924942488849930215740943 254887413733274895323611415)
  ·
    refine ⟨382331120599912342985417123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254887413733274895323611415 382331120599912342985417123)
    ·
      refine ⟨573496680899868514478125685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382331120599912342985417123 573496680899868514478125685)
      ·
        refine ⟨53765313834362673232324283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 573496680899868514478125685 53765313834362673232324283)
        ·
          refine ⟨80647970751544009848486425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53765313834362673232324283 80647970751544009848486425)
          ·
            refine ⟨60485978063658007386364819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80647970751544009848486425 60485978063658007386364819)
            ·
              refine ⟨90728967095487011079547229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60485978063658007386364819 90728967095487011079547229)
              ·
                refine ⟨34023362660807629154830211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90728967095487011079547229 34023362660807629154830211)
                ·
                  refine ⟨51035043991211443732245317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34023362660807629154830211 51035043991211443732245317)
                  ·
                    refine ⟨9569070748352145699795997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51035043991211443732245317 9569070748352145699795997)
                    ·
                      refine ⟨3588401530632054637423499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9569070748352145699795997 3588401530632054637423499)
                      ·
                        rfl

theorem cell23_6988387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_6988387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988387 prefixEnd_6988387 := by exact prefixLift 6988387
  have htrace : WordTrace (prefixWord ++ tailWord_6988387) baseStart_6988387 baseEnd_6988387 := by
    simpa [prefixWord, tailWord_6988387, baseEnd_6988387] using wordTrace_append hprefix tailTrace_6988387
  have hstable : (prefixWord ++ tailWord_6988387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988387).length < 2 ^ (prefixWord ++ tailWord_6988387).sum := by decide
  have hdescent : baseEnd_6988387 < baseStart_6988387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988457 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_6988457 : Nat := 118140960795 + 6988457 * 2 ^ 59
def prefixEnd_6988457 : Nat := 4983230072969 + 3 ^ 40 * 6988457 * 2
def baseEnd_6988457 : Nat := 3588437474277869363548177

theorem tailTrace_6988457 : CollatzResearch.WordTrace tailWord_6988457 prefixEnd_6988457 3588437474277869363548177 := by
  unfold tailWord_6988457
  simp only [CollatzResearch.WordTrace]
  refine ⟨254889966843021297278659625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169926644562014198185773083 254889966843021297278659625)
  ·
    refine ⟨191167475132265972958994719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254889966843021297278659625 191167475132265972958994719)
    ·
      refine ⟨286751212698398959438492079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191167475132265972958994719 286751212698398959438492079)
      ·
        refine ⟨430126819047598439157738119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286751212698398959438492079 430126819047598439157738119)
        ·
          refine ⟨645190228571397658736607179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430126819047598439157738119 645190228571397658736607179)
          ·
            refine ⟨967785342857096488104910769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645190228571397658736607179 967785342857096488104910769)
            ·
              refine ⟨725839007142822366078683077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967785342857096488104910769 725839007142822366078683077)
              ·
                refine ⟨136094813839279193639753077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 725839007142822366078683077 136094813839279193639753077)
                ·
                  refine ⟨12758888797432424403726851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136094813839279193639753077 12758888797432424403726851)
                  ·
                    refine ⟨19138333196148636605590277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12758888797432424403726851 19138333196148636605590277)
                    ·
                      refine ⟨3588437474277869363548177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19138333196148636605590277 3588437474277869363548177)
                      ·
                        rfl

theorem cell23_6988457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_6988457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988457 prefixEnd_6988457 := by exact prefixLift 6988457
  have htrace : WordTrace (prefixWord ++ tailWord_6988457) baseStart_6988457 baseEnd_6988457 := by
    simpa [prefixWord, tailWord_6988457, baseEnd_6988457] using wordTrace_append hprefix tailTrace_6988457
  have hstable : (prefixWord ++ tailWord_6988457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988457).length < 2 ^ (prefixWord ++ tailWord_6988457).sum := by decide
  have hdescent : baseEnd_6988457 < baseStart_6988457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988458 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 6]
def baseStart_6988458 : Nat := 118140960795 + 6988458 * 2 ^ 59
def prefixEnd_6988458 : Nat := 4983230072969 + 3 ^ 40 * 6988458 * 2
def baseEnd_6988458 : Nat := 398715331973169317737297

theorem tailTrace_6988458 : CollatzResearch.WordTrace tailWord_6988458 prefixEnd_6988458 398715331973169317737297 := by
  unfold tailWord_6988458
  simp only [CollatzResearch.WordTrace]
  refine ⟨63722500829004418612361507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169926668877345116299630685 63722500829004418612361507)
  ·
    refine ⟨95583751243506627918542261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63722500829004418612361507 95583751243506627918542261)
    ·
      refine ⟨8960976679078746367363337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95583751243506627918542261 8960976679078746367363337)
      ·
        refine ⟨6720732509309059775522503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8960976679078746367363337 6720732509309059775522503)
        ·
          refine ⟨10081098763963589663283755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6720732509309059775522503 10081098763963589663283755)
          ·
            refine ⟨15121648145945384494925633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081098763963589663283755 15121648145945384494925633)
            ·
              refine ⟨11341236109459038371194225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15121648145945384494925633 11341236109459038371194225)
              ·
                refine ⟨8505927082094278778395669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11341236109459038371194225 8505927082094278778395669)
                ·
                  refine ⟨398715331973169317737297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8505927082094278778395669 398715331973169317737297)
                  ·
                    rfl

theorem cell23_6988458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_6988458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988458 prefixEnd_6988458 := by exact prefixLift 6988458
  have htrace : WordTrace (prefixWord ++ tailWord_6988458) baseStart_6988458 baseEnd_6988458 := by
    simpa [prefixWord, tailWord_6988458, baseEnd_6988458] using wordTrace_append hprefix tailTrace_6988458
  have hstable : (prefixWord ++ tailWord_6988458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988458).length < 2 ^ (prefixWord ++ tailWord_6988458).sum := by decide
  have hdescent : baseEnd_6988458 < baseStart_6988458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988462 : List Nat := [4, 1, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_6988462 : Nat := 118140960795 + 6988462 * 2 ^ 59
def prefixEnd_6988462 : Nat := 4983230072969 + 3 ^ 40 * 6988462 * 2
def baseEnd_6988462 : Nat := 1196146680560380614661885

theorem tailTrace_6988462 : CollatzResearch.WordTrace tailWord_6988462 prefixEnd_6988462 1196146680560380614661885 := by
  unfold tailWord_6988462
  simp only [CollatzResearch.WordTrace]
  refine ⟨31861268651000397891573955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169926766138668788755061093 31861268651000397891573955)
  ·
    refine ⟨47791902976500596837360933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31861268651000397891573955 47791902976500596837360933)
    ·
      refine ⟨8960981808093861907005175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47791902976500596837360933 8960981808093861907005175)
      ·
        refine ⟨13441472712140792860507763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8960981808093861907005175 13441472712140792860507763)
        ·
          refine ⟨20162209068211189290761645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13441472712140792860507763 20162209068211189290761645)
          ·
            refine ⟨7560828400579195984035617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20162209068211189290761645 7560828400579195984035617)
            ·
              refine ⟨5670621300434396988026713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7560828400579195984035617 5670621300434396988026713)
              ·
                refine ⟨4252965975325797741020035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5670621300434396988026713 4252965975325797741020035)
                ·
                  refine ⟨6379448962988696611530053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4252965975325797741020035 6379448962988696611530053)
                  ·
                    refine ⟨1196146680560380614661885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6379448962988696611530053 1196146680560380614661885)
                    ·
                      rfl

theorem cell23_6988462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_6988462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988462 prefixEnd_6988462 := by exact prefixLift 6988462
  have htrace : WordTrace (prefixWord ++ tailWord_6988462) baseStart_6988462 baseEnd_6988462 := by
    simpa [prefixWord, tailWord_6988462, baseEnd_6988462] using wordTrace_append hprefix tailTrace_6988462
  have hstable : (prefixWord ++ tailWord_6988462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988462).length < 2 ^ (prefixWord ++ tailWord_6988462).sum := by decide
  have hdescent : baseEnd_6988462 < baseStart_6988462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988484 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6988484 : Nat := 118140960795 + 6988484 * 2 ^ 59
def prefixEnd_6988484 : Nat := 4983230072969 + 3 ^ 40 * 6988484 * 2
def baseEnd_6988484 : Nat := 1196150446085180252636851

theorem tailTrace_6988484 : CollatzResearch.WordTrace tailWord_6988484 prefixEnd_6988484 1196150446085180252636851 := by
  unfold tailWord_6988484
  simp only [CollatzResearch.WordTrace]
  refine ⟨127445475806961740444946253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169927301075948987259928337 127445475806961740444946253)
  ·
    refine ⟨47792053427610652666854845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127445475806961740444946253 47792053427610652666854845)
    ·
      refine ⟨17922020035353994750070567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47792053427610652666854845 17922020035353994750070567)
      ·
        refine ⟨26883030053030992125105851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17922020035353994750070567 26883030053030992125105851)
        ·
          refine ⟨40324545079546488187658777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26883030053030992125105851 40324545079546488187658777)
          ·
            refine ⟨30243408809659866140744083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40324545079546488187658777 30243408809659866140744083)
            ·
              refine ⟨45365113214489799211116125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30243408809659866140744083 45365113214489799211116125)
              ·
                refine ⟨17011917455433674704168547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45365113214489799211116125 17011917455433674704168547)
                ·
                  refine ⟨25517876183150512056252821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17011917455433674704168547 25517876183150512056252821)
                  ·
                    refine ⟨1196150446085180252636851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25517876183150512056252821 1196150446085180252636851)
                    ·
                      rfl

theorem cell23_6988484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6988484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988484 prefixEnd_6988484 := by exact prefixLift 6988484
  have htrace : WordTrace (prefixWord ++ tailWord_6988484) baseStart_6988484 baseEnd_6988484 := by
    simpa [prefixWord, tailWord_6988484, baseEnd_6988484] using wordTrace_append hprefix tailTrace_6988484
  have hstable : (prefixWord ++ tailWord_6988484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988484).length < 2 ^ (prefixWord ++ tailWord_6988484).sum := by decide
  have hdescent : baseEnd_6988484 < baseStart_6988484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988504 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_6988504 : Nat := 118140960795 + 6988504 * 2 ^ 59
def prefixEnd_6988504 : Nat := 4983230072969 + 3 ^ 40 * 6988504 * 2
def baseEnd_6988504 : Nat := 3588461607868630679660461

theorem tailTrace_6988504 : CollatzResearch.WordTrace tailWord_6988504 prefixEnd_6988504 3588461607868630679660461 := by
  unfold tailWord_6988504
  simp only [CollatzResearch.WordTrace]
  refine ⟨127445840536925512152810283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169927787382567349537080377 127445840536925512152810283)
  ·
    refine ⟨191168760805388268229215425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127445840536925512152810283 191168760805388268229215425)
    ·
      refine ⟨143376570604041201171911569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191168760805388268229215425 143376570604041201171911569)
      ·
        refine ⟨107532427953030900878933677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143376570604041201171911569 107532427953030900878933677)
        ·
          refine ⟨40324660482386587829600129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107532427953030900878933677 40324660482386587829600129)
          ·
            refine ⟨30243495361789940872200097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40324660482386587829600129 30243495361789940872200097)
            ·
              refine ⟨22682621521342455654150073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30243495361789940872200097 22682621521342455654150073)
              ·
                refine ⟨17011966141006841740612555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22682621521342455654150073 17011966141006841740612555)
                ·
                  refine ⟨25517949211510262610918833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17011966141006841740612555 25517949211510262610918833)
                  ·
                    refine ⟨19138461908632696958189125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25517949211510262610918833 19138461908632696958189125)
                    ·
                      refine ⟨3588461607868630679660461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19138461908632696958189125 3588461607868630679660461)
                      ·
                        rfl

theorem cell23_6988504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_6988504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988504 prefixEnd_6988504 := by exact prefixLift 6988504
  have htrace : WordTrace (prefixWord ++ tailWord_6988504) baseStart_6988504 baseEnd_6988504 := by
    simpa [prefixWord, tailWord_6988504, baseEnd_6988504] using wordTrace_append hprefix tailTrace_6988504
  have hstable : (prefixWord ++ tailWord_6988504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988504).length < 2 ^ (prefixWord ++ tailWord_6988504).sum := by decide
  have hdescent : baseEnd_6988504 < baseStart_6988504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988508 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6988508 : Nat := 118140960795 + 6988508 * 2 ^ 59
def prefixEnd_6988508 : Nat := 4983230072969 + 3 ^ 40 * 6988508 * 2
def baseEnd_6988508 : Nat := 3588463661791248664010443

theorem tailTrace_6988508 : CollatzResearch.WordTrace tailWord_6988508 prefixEnd_6988508 3588463661791248664010443 := by
  unfold tailWord_6988508
  simp only [CollatzResearch.WordTrace]
  refine ⟨127445913482918266494383089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169927884643891021992510785 127445913482918266494383089)
  ·
    refine ⟨95584435112188699870787317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127445913482918266494383089 95584435112188699870787317)
    ·
      refine ⟨8961040791767690612886311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95584435112188699870787317 8961040791767690612886311)
      ·
        refine ⟨13441561187651535919329467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8961040791767690612886311 13441561187651535919329467)
        ·
          refine ⟨20162341781477303878994201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13441561187651535919329467 20162341781477303878994201)
          ·
            refine ⟨15121756336107977909245651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20162341781477303878994201 15121756336107977909245651)
            ·
              refine ⟨22682634504161966863868477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15121756336107977909245651 22682634504161966863868477)
              ·
                refine ⟨8505987939060737573950679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22682634504161966863868477 8505987939060737573950679)
                ·
                  refine ⟨12758981908591106360926019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8505987939060737573950679 12758981908591106360926019)
                  ·
                    refine ⟨19138472862886659541389029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12758981908591106360926019 19138472862886659541389029)
                    ·
                      refine ⟨3588463661791248664010443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19138472862886659541389029 3588463661791248664010443)
                      ·
                        rfl

theorem cell23_6988508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6988508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988508 prefixEnd_6988508 := by exact prefixLift 6988508
  have htrace : WordTrace (prefixWord ++ tailWord_6988508) baseStart_6988508 baseEnd_6988508 := by
    simpa [prefixWord, tailWord_6988508, baseEnd_6988508] using wordTrace_append hprefix tailTrace_6988508
  have hstable : (prefixWord ++ tailWord_6988508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988508).length < 2 ^ (prefixWord ++ tailWord_6988508).sum := by decide
  have hdescent : baseEnd_6988508 < baseStart_6988508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988511 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 3]
def baseStart_6988511 : Nat := 118140960795 + 6988511 * 2 ^ 59
def prefixEnd_6988511 : Nat := 4983230072969 + 3 ^ 40 * 6988511 * 2
def baseEnd_6988511 : Nat := 3588465202233212152272929

theorem tailTrace_6988511 : CollatzResearch.WordTrace tailWord_6988511 prefixEnd_6988511 3588465202233212152272929 := by
  unfold tailWord_6988511
  simp only [CollatzResearch.WordTrace]
  refine ⟨254891936384825664501125387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169927957589883776334083591 254891936384825664501125387)
  ·
    refine ⟨382337904577238496751688081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254891936384825664501125387 382337904577238496751688081)
    ·
      refine ⟨286753428432928872563766061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382337904577238496751688081 286753428432928872563766061)
      ·
        refine ⟨107532535662348327211412273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286753428432928872563766061 107532535662348327211412273)
        ·
          refine ⟨80649401746761245408559205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107532535662348327211412273 80649401746761245408559205)
          ·
            refine ⟨15121762827517733514104851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80649401746761245408559205 15121762827517733514104851)
            ·
              refine ⟨22682644241276600271157277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15121762827517733514104851 22682644241276600271157277)
              ·
                refine ⟨8505991590478725101683979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22682644241276600271157277 8505991590478725101683979)
                ·
                  refine ⟨12758987385718087652525969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8505991590478725101683979 12758987385718087652525969)
                  ·
                    refine ⟨9569240539288565739394477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12758987385718087652525969 9569240539288565739394477)
                    ·
                      refine ⟨3588465202233212152272929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9569240539288565739394477 3588465202233212152272929)
                      ·
                        rfl

theorem cell23_6988511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_6988511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988511 prefixEnd_6988511 := by exact prefixLift 6988511
  have htrace : WordTrace (prefixWord ++ tailWord_6988511) baseStart_6988511 baseEnd_6988511 := by
    simpa [prefixWord, tailWord_6988511, baseEnd_6988511] using wordTrace_append hprefix tailTrace_6988511
  have hstable : (prefixWord ++ tailWord_6988511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988511).length < 2 ^ (prefixWord ++ tailWord_6988511).sum := by decide
  have hdescent : baseEnd_6988511 < baseStart_6988511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988525 : List Nat := [1, 5, 1, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_6988525 : Nat := 118140960795 + 6988525 * 2 ^ 59
def prefixEnd_6988525 : Nat := 4983230072969 + 3 ^ 40 * 6988525 * 2
def baseEnd_6988525 : Nat := 3588472390962375097497865

theorem tailTrace_6988525 : CollatzResearch.WordTrace tailWord_6988525 prefixEnd_6988525 3588472390962375097497865 := by
  unfold tailWord_6988525
  simp only [CollatzResearch.WordTrace]
  refine ⟨254892447006774944892135029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169928298004516629928090019 254892447006774944892135029)
  ·
    refine ⟨23896166906885151083637659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254892447006774944892135029 23896166906885151083637659)
    ·
      refine ⟨35844250360327726625456489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23896166906885151083637659 35844250360327726625456489)
      ·
        refine ⟨26883187770245794969092367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35844250360327726625456489 26883187770245794969092367)
        ·
          refine ⟨40324781655368692453638551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26883187770245794969092367 40324781655368692453638551)
          ·
            refine ⟨60487172483053038680457827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40324781655368692453638551 60487172483053038680457827)
            ·
              refine ⟨90730758724579558020686741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60487172483053038680457827 90730758724579558020686741)
              ·
                refine ⟨4253004315214666782219691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90730758724579558020686741 4253004315214666782219691)
                ·
                  refine ⟨6379506472822000173329537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253004315214666782219691 6379506472822000173329537)
                  ·
                    refine ⟨4784629854616500129997153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6379506472822000173329537 4784629854616500129997153)
                    ·
                      refine ⟨3588472390962375097497865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4784629854616500129997153 3588472390962375097497865)
                      ·
                        rfl

theorem cell23_6988525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_6988525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988525 prefixEnd_6988525 := by exact prefixLift 6988525
  have htrace : WordTrace (prefixWord ++ tailWord_6988525) baseStart_6988525 baseEnd_6988525 := by
    simpa [prefixWord, tailWord_6988525, baseEnd_6988525] using wordTrace_append hprefix tailTrace_6988525
  have hstable : (prefixWord ++ tailWord_6988525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988525).length < 2 ^ (prefixWord ++ tailWord_6988525).sum := by decide
  have hdescent : baseEnd_6988525 < baseStart_6988525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988537 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_6988537 : Nat := 118140960795 + 6988537 * 2 ^ 59
def prefixEnd_6988537 : Nat := 4983230072969 + 3 ^ 40 * 6988537 * 2
def baseEnd_6988537 : Nat := 3588478552730229050547809

theorem tailTrace_6988537 : CollatzResearch.WordTrace tailWord_6988537 prefixEnd_6988537 3588478552730229050547809 := by
  unfold tailWord_6988537
  simp only [CollatzResearch.WordTrace]
  refine ⟨254892884682731470941571865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169928589788487647294381243 254892884682731470941571865)
  ·
    refine ⟨191169663512048603206178899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254892884682731470941571865 191169663512048603206178899)
    ·
      refine ⟨286754495268072904809268349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191169663512048603206178899 286754495268072904809268349)
      ·
        refine ⟨107532935725527339303475631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286754495268072904809268349 107532935725527339303475631)
        ·
          refine ⟨161299403588291008955213447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107532935725527339303475631 161299403588291008955213447)
          ·
            refine ⟨241949105382436513432820171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161299403588291008955213447 241949105382436513432820171)
            ·
              refine ⟨362923658073654770149230257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241949105382436513432820171 362923658073654770149230257)
              ·
                refine ⟨272192743555241077611922693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362923658073654770149230257 272192743555241077611922693)
                ·
                  refine ⟨51036139416607702052235505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272192743555241077611922693 51036139416607702052235505)
                  ·
                    refine ⟨38277104562455776539176629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51036139416607702052235505 38277104562455776539176629)
                    ·
                      refine ⟨3588478552730229050547809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38277104562455776539176629 3588478552730229050547809)
                      ·
                        rfl

theorem cell23_6988537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_6988537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988537 prefixEnd_6988537 := by exact prefixLift 6988537
  have htrace : WordTrace (prefixWord ++ tailWord_6988537) baseStart_6988537 baseEnd_6988537 := by
    simpa [prefixWord, tailWord_6988537, baseEnd_6988537] using wordTrace_append hprefix tailTrace_6988537
  have hstable : (prefixWord ++ tailWord_6988537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988537).length < 2 ^ (prefixWord ++ tailWord_6988537).sum := by decide
  have hdescent : baseEnd_6988537 < baseStart_6988537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988584 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_6988584 : Nat := 118140960795 + 6988584 * 2 ^ 59
def prefixEnd_6988584 : Nat := 4983230072969 + 3 ^ 40 * 6988584 * 2
def baseEnd_6988584 : Nat := 3588502686320990366660093

theorem tailTrace_6988584 : CollatzResearch.WordTrace tailWord_6988584 prefixEnd_6988584 3588502686320990366660093 := by
  unfold tailWord_6988584
  simp only [CollatzResearch.WordTrace]
  refine ⟨127447299456780598984266403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169929732609040798645688537 127447299456780598984266403)
  ·
    refine ⟨191170949185170898476399605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127447299456780598984266403 191170949185170898476399605)
    ·
      refine ⟨17922276486109771732162463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191170949185170898476399605 17922276486109771732162463)
      ·
        refine ⟨26883414729164657598243695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17922276486109771732162463 26883414729164657598243695)
        ·
          refine ⟨40325122093746986397365543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26883414729164657598243695 40325122093746986397365543)
          ·
            refine ⟨60487683140620479596048315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40325122093746986397365543 60487683140620479596048315)
            ·
              refine ⟨90731524710930719394072473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60487683140620479596048315 90731524710930719394072473)
              ·
                refine ⟨68048643533198039545554355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90731524710930719394072473 68048643533198039545554355)
                ·
                  refine ⟨102072965299797059318331533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68048643533198039545554355 102072965299797059318331533)
                  ·
                    refine ⟨38277361987423897244374325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102072965299797059318331533 38277361987423897244374325)
                    ·
                      refine ⟨3588502686320990366660093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38277361987423897244374325 3588502686320990366660093)
                      ·
                        rfl

theorem cell23_6988584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_6988584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988584 prefixEnd_6988584 := by exact prefixLift 6988584
  have htrace : WordTrace (prefixWord ++ tailWord_6988584) baseStart_6988584 baseEnd_6988584 := by
    simpa [prefixWord, tailWord_6988584, baseEnd_6988584] using wordTrace_append hprefix tailTrace_6988584
  have hstable : (prefixWord ++ tailWord_6988584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988584).length < 2 ^ (prefixWord ++ tailWord_6988584).sum := by decide
  have hdescent : baseEnd_6988584 < baseStart_6988584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988594 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_6988594 : Nat := 118140960795 + 6988594 * 2 ^ 59
def prefixEnd_6988594 : Nat := 4983230072969 + 3 ^ 40 * 6988594 * 2
def baseEnd_6988594 : Nat := 3588507821127535327535047

theorem tailTrace_6988594 : CollatzResearch.WordTrace tailWord_6988594 prefixEnd_6988594 3588507821127535327535047 := by
  unfold tailWord_6988594
  simp only [CollatzResearch.WordTrace]
  refine ⟨63723740910881242419099209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169929975762349979784264557 63723740910881242419099209)
  ·
    refine ⟨47792805683160931814324407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63723740910881242419099209 47792805683160931814324407)
    ·
      refine ⟨71689208524741397721486611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47792805683160931814324407 71689208524741397721486611)
      ·
        refine ⟨107533812787112096582229917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71689208524741397721486611 107533812787112096582229917)
        ·
          refine ⟨40325179795167036218336219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107533812787112096582229917 40325179795167036218336219)
          ·
            refine ⟨60487769692750554327504329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40325179795167036218336219 60487769692750554327504329)
            ·
              refine ⟨45365827269562915745628247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60487769692750554327504329 45365827269562915745628247)
              ·
                refine ⟨68048740904344373618442371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45365827269562915745628247 68048740904344373618442371)
                ·
                  refine ⟨102073111356516560427663557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68048740904344373618442371 102073111356516560427663557)
                  ·
                    refine ⟨19138708379346855080186917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102073111356516560427663557 19138708379346855080186917)
                    ·
                      refine ⟨3588507821127535327535047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19138708379346855080186917 3588507821127535327535047)
                      ·
                        rfl

theorem cell23_6988594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_6988594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988594 prefixEnd_6988594 := by exact prefixLift 6988594
  have htrace : WordTrace (prefixWord ++ tailWord_6988594) baseStart_6988594 baseEnd_6988594 := by
    simpa [prefixWord, tailWord_6988594, baseEnd_6988594] using wordTrace_append hprefix tailTrace_6988594
  have hstable : (prefixWord ++ tailWord_6988594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988594).length < 2 ^ (prefixWord ++ tailWord_6988594).sum := by decide
  have hdescent : baseEnd_6988594 < baseStart_6988594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988602 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2]
def baseStart_6988602 : Nat := 118140960795 + 6988602 * 2 ^ 59
def prefixEnd_6988602 : Nat := 4983230072969 + 3 ^ 40 * 6988602 * 2
def baseEnd_6988602 : Nat := 3588511928972771296235011

theorem tailTrace_6988602 : CollatzResearch.WordTrace tailWord_6988602 prefixEnd_6988602 3588511928972771296235011 := by
  unfold tailWord_6988602
  simp only [CollatzResearch.WordTrace]
  refine ⟨63723813856873996760672015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169930170284997324695125373 63723813856873996760672015)
  ·
    refine ⟨95585720785310995141008023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63723813856873996760672015 95585720785310995141008023)
    ·
      refine ⟨143378581177966492711512035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95585720785310995141008023 143378581177966492711512035)
      ·
        refine ⟨215067871766949739067268053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143378581177966492711512035 215067871766949739067268053)
        ·
          refine ⟨5040653244537884509389095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 215067871766949739067268053 5040653244537884509389095)
          ·
            refine ⟨7560979866806826764083643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5040653244537884509389095 7560979866806826764083643)
            ·
              refine ⟨11341469800210240146125465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7560979866806826764083643 11341469800210240146125465)
              ·
                refine ⟨8506102350157680109594099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11341469800210240146125465 8506102350157680109594099)
                ·
                  refine ⟨12759153525236520164391149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8506102350157680109594099 12759153525236520164391149)
                  ·
                    refine ⟨4784682571963695061646681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12759153525236520164391149 4784682571963695061646681)
                    ·
                      refine ⟨3588511928972771296235011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4784682571963695061646681 3588511928972771296235011)
                      ·
                        rfl

theorem cell23_6988602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_6988602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988602 prefixEnd_6988602 := by exact prefixLift 6988602
  have htrace : WordTrace (prefixWord ++ tailWord_6988602) baseStart_6988602 baseEnd_6988602 := by
    simpa [prefixWord, tailWord_6988602, baseEnd_6988602] using wordTrace_append hprefix tailTrace_6988602
  have hstable : (prefixWord ++ tailWord_6988602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988602).length < 2 ^ (prefixWord ++ tailWord_6988602).sum := by decide
  have hdescent : baseEnd_6988602 < baseStart_6988602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988671 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 4]
def baseStart_6988671 : Nat := 118140960795 + 6988671 * 2 ^ 59
def prefixEnd_6988671 : Nat := 4983230072969 + 3 ^ 40 * 6988671 * 2
def baseEnd_6988671 : Nat := 3588547359137931526272193

theorem tailTrace_6988671 : CollatzResearch.WordTrace tailWord_6988671 prefixEnd_6988671 3588547359137931526272193 := by
  unfold tailWord_6988671
  simp only [CollatzResearch.WordTrace]
  refine ⟨254897772064246011826949867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169931848042830674551299911 254897772064246011826949867)
  ·
    refine ⟨382346658096369017740424801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254897772064246011826949867 382346658096369017740424801)
    ·
      refine ⟨286759993572276763305318601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382346658096369017740424801 286759993572276763305318601)
      ·
        refine ⟨215069995179207572478988951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286759993572276763305318601 215069995179207572478988951)
        ·
          refine ⟨322604992768811358718483427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215069995179207572478988951 322604992768811358718483427)
          ·
            refine ⟨483907489153217038077725141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322604992768811358718483427 483907489153217038077725141)
            ·
              refine ⟨11341581777028524329946683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 483907489153217038077725141 11341581777028524329946683)
              ·
                refine ⟨17012372665542786494920025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11341581777028524329946683 17012372665542786494920025)
                ·
                  refine ⟨12759279499157089871190019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17012372665542786494920025 12759279499157089871190019)
                  ·
                    refine ⟨19138919248735634806785029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12759279499157089871190019 19138919248735634806785029)
                    ·
                      refine ⟨3588547359137931526272193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19138919248735634806785029 3588547359137931526272193)
                      ·
                        rfl

theorem cell23_6988671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_6988671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988671 prefixEnd_6988671 := by exact prefixLift 6988671
  have htrace : WordTrace (prefixWord ++ tailWord_6988671) baseStart_6988671 baseEnd_6988671 := by
    simpa [prefixWord, tailWord_6988671, baseEnd_6988671] using wordTrace_append hprefix tailTrace_6988671
  have hstable : (prefixWord ++ tailWord_6988671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988671).length < 2 ^ (prefixWord ++ tailWord_6988671).sum := by decide
  have hdescent : baseEnd_6988671 < baseStart_6988671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988684 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_6988684 : Nat := 118140960795 + 6988684 * 2 ^ 59
def prefixEnd_6988684 : Nat := 4983230072969 + 3 ^ 40 * 6988684 * 2
def baseEnd_6988684 : Nat := 3588554034386439975409633

theorem tailTrace_6988684 : CollatzResearch.WordTrace tailWord_6988684 prefixEnd_6988684 3588554034386439975409633 := by
  unfold tailWord_6988684
  simp only [CollatzResearch.WordTrace]
  refine ⟨127449123106599457523586553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169932164142132610031448737 127449123106599457523586553)
  ·
    refine ⟨95586842329949593142689915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127449123106599457523586553 95586842329949593142689915)
    ·
      refine ⟨143380263494924389714034873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95586842329949593142689915 143380263494924389714034873)
      ·
        refine ⟨107535197621193292285526155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143380263494924389714034873 107535197621193292285526155)
        ·
          refine ⟨161302796431789938428289233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107535197621193292285526155 161302796431789938428289233)
          ·
            refine ⟨120977097323842453821216925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161302796431789938428289233 120977097323842453821216925)
            ·
              refine ⟨45366411496440920182956347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120977097323842453821216925 45366411496440920182956347)
              ·
                refine ⟨68049617244661380274434521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45366411496440920182956347 68049617244661380274434521)
                ·
                  refine ⟨51037212933496035205825891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68049617244661380274434521 51037212933496035205825891)
                  ·
                    refine ⟨76555819400244052808738837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51037212933496035205825891 76555819400244052808738837)
                    ·
                      refine ⟨3588554034386439975409633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76555819400244052808738837 3588554034386439975409633)
                      ·
                        rfl

theorem cell23_6988684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_6988684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988684 prefixEnd_6988684 := by exact prefixLift 6988684
  have htrace : WordTrace (prefixWord ++ tailWord_6988684) baseStart_6988684 baseEnd_6988684 := by
    simpa [prefixWord, tailWord_6988684, baseEnd_6988684] using wordTrace_append hprefix tailTrace_6988684
  have hstable : (prefixWord ++ tailWord_6988684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988684).length < 2 ^ (prefixWord ++ tailWord_6988684).sum := by decide
  have hdescent : baseEnd_6988684 < baseStart_6988684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988731 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 5, 5, 2]
def baseStart_6988731 : Nat := 118140960795 + 6988731 * 2 ^ 59
def prefixEnd_6988731 : Nat := 4983230072969 + 3 ^ 40 * 6988731 * 2
def baseEnd_6988731 : Nat := 3588578167977201291521917

theorem tailTrace_6988731 : CollatzResearch.WordTrace tailWord_6988731 prefixEnd_6988731 3588578167977201291521917 := by
  unfold tailWord_6988731
  simp only [CollatzResearch.WordTrace]
  refine ⟨254899960444028642074134047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169933306962685761382756031 254899960444028642074134047)
  ·
    refine ⟨382349940666042963111201071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254899960444028642074134047 382349940666042963111201071)
    ·
      refine ⟨573524910999064444666801607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382349940666042963111201071 573524910999064444666801607)
      ·
        refine ⟨860287366498596667000202411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573524910999064444666801607 860287366498596667000202411)
        ·
          refine ⟨1290431049747895000500303617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860287366498596667000202411 1290431049747895000500303617)
          ·
            refine ⟨967823287310921250375227713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290431049747895000500303617 967823287310921250375227713)
            ·
              refine ⟨725867465483190937781420785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967823287310921250375227713 725867465483190937781420785)
              ·
                refine ⟨544400599112393203336065589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725867465483190937781420785 544400599112393203336065589)
                ·
                  refine ⟨51037556166786862812756149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 544400599112393203336065589 51037556166786862812756149)
                  ·
                    refine ⟨4784770890636268388695889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51037556166786862812756149 4784770890636268388695889)
                    ·
                      refine ⟨3588578167977201291521917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4784770890636268388695889 3588578167977201291521917)
                      ·
                        rfl

theorem cell23_6988731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 5, 2].length) (baseStart_6988731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988731 prefixEnd_6988731 := by exact prefixLift 6988731
  have htrace : WordTrace (prefixWord ++ tailWord_6988731) baseStart_6988731 baseEnd_6988731 := by
    simpa [prefixWord, tailWord_6988731, baseEnd_6988731] using wordTrace_append hprefix tailTrace_6988731
  have hstable : (prefixWord ++ tailWord_6988731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988731).length < 2 ^ (prefixWord ++ tailWord_6988731).sum := by decide
  have hdescent : baseEnd_6988731 < baseStart_6988731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988771 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 1, 6]
def baseStart_6988771 : Nat := 118140960795 + 6988771 * 2 ^ 59
def prefixEnd_6988771 : Nat := 4983230072969 + 3 ^ 40 * 6988771 * 2
def baseEnd_6988771 : Nat := 1196199569067793711673911

theorem tailTrace_6988771 : CollatzResearch.WordTrace tailWord_6988771 prefixEnd_6988771 1196199569067793711673911 := by
  unfold tailWord_6988771
  simp only [CollatzResearch.WordTrace]
  refine ⟨254901419363883728905590167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169934279575922485937060111 254901419363883728905590167)
  ·
    refine ⟨382352129045825593358385251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254901419363883728905590167 382352129045825593358385251)
    ·
      refine ⟨573528193568738390037577877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382352129045825593358385251 573528193568738390037577877)
      ·
        refine ⟨26884134073534612033011463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 573528193568738390037577877 26884134073534612033011463)
        ·
          refine ⟨40326201110301918049517195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26884134073534612033011463 40326201110301918049517195)
          ·
            refine ⟨60489301665452877074275793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40326201110301918049517195 60489301665452877074275793)
            ·
              refine ⟨45366976249089657805706845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60489301665452877074275793 45366976249089657805706845)
              ·
                refine ⟨17012616093408621677140067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45366976249089657805706845 17012616093408621677140067)
                ·
                  refine ⟨25518924140112932515710101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17012616093408621677140067 25518924140112932515710101)
                  ·
                    refine ⟨1196199569067793711673911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25518924140112932515710101 1196199569067793711673911)
                    ·
                      rfl

theorem cell23_6988771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 6].length) (baseStart_6988771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988771 prefixEnd_6988771 := by exact prefixLift 6988771
  have htrace : WordTrace (prefixWord ++ tailWord_6988771) baseStart_6988771 baseEnd_6988771 := by
    simpa [prefixWord, tailWord_6988771, baseEnd_6988771] using wordTrace_append hprefix tailTrace_6988771
  have hstable : (prefixWord ++ tailWord_6988771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988771).length < 2 ^ (prefixWord ++ tailWord_6988771).sum := by decide
  have hdescent : baseEnd_6988771 < baseStart_6988771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988775 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 1, 5]
def baseStart_6988775 : Nat := 118140960795 + 6988775 * 2 ^ 59
def prefixEnd_6988775 : Nat := 4983230072969 + 3 ^ 40 * 6988775 * 2
def baseEnd_6988775 : Nat := 1196200253708666373123905

theorem tailTrace_6988775 : CollatzResearch.WordTrace tailWord_6988775 prefixEnd_6988775 1196200253708666373123905 := by
  unfold tailWord_6988775
  simp only [CollatzResearch.WordTrace]
  refine ⟨254901565255869237588735779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169934376837246158392490519 254901565255869237588735779)
  ·
    refine ⟨382352347883803856383103669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254901565255869237588735779 382352347883803856383103669)
    ·
      refine ⟨35845532614106611535915969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 382352347883803856383103669 35845532614106611535915969)
      ·
        refine ⟨26884149460579958651936977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35845532614106611535915969 26884149460579958651936977)
        ·
          refine ⟨20163112095434968988952733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26884149460579958651936977 20163112095434968988952733)
          ·
            refine ⟨7561167035788113370857275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20163112095434968988952733 7561167035788113370857275)
            ·
              refine ⟨11341750553682170056285913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7561167035788113370857275 11341750553682170056285913)
              ·
                refine ⟨8506312915261627542214435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11341750553682170056285913 8506312915261627542214435)
                ·
                  refine ⟨12759469372892441313321653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8506312915261627542214435 12759469372892441313321653)
                  ·
                    refine ⟨1196200253708666373123905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12759469372892441313321653 1196200253708666373123905)
                    ·
                      rfl

theorem cell23_6988775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_6988775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988775 prefixEnd_6988775 := by exact prefixLift 6988775
  have htrace : WordTrace (prefixWord ++ tailWord_6988775) baseStart_6988775 baseEnd_6988775 := by
    simpa [prefixWord, tailWord_6988775, baseEnd_6988775] using wordTrace_append hprefix tailTrace_6988775
  have hstable : (prefixWord ++ tailWord_6988775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988775).length < 2 ^ (prefixWord ++ tailWord_6988775).sum := by decide
  have hdescent : baseEnd_6988775 < baseStart_6988775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988778 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_6988778 : Nat := 118140960795 + 6988778 * 2 ^ 59
def prefixEnd_6988778 : Nat := 4983230072969 + 3 ^ 40 * 6988778 * 2
def baseEnd_6988778 : Nat := 3588602301567962607634201

theorem tailTrace_6988778 : CollatzResearch.WordTrace tailWord_6988778 prefixEnd_6988778 3588602301567962607634201 := by
  unfold tailWord_6988778
  simp only [CollatzResearch.WordTrace]
  refine ⟨63725418668714592275273747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169934449783238912734063325 63725418668714592275273747)
  ·
    refine ⟨95588128003071888412910621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63725418668714592275273747 95588128003071888412910621)
    ·
      refine ⟨35845548001151958154841483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95588128003071888412910621 35845548001151958154841483)
      ·
        refine ⟨53768322001727937232262225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35845548001151958154841483 53768322001727937232262225)
        ·
          refine ⟨40326241501295952924196669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53768322001727937232262225 40326241501295952924196669)
          ·
            refine ⟨15122340562985982346573751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40326241501295952924196669 15122340562985982346573751)
            ·
              refine ⟨22683510844478973519860627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15122340562985982346573751 22683510844478973519860627)
              ·
                refine ⟨34025266266718460279790941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22683510844478973519860627 34025266266718460279790941)
                ·
                  refine ⟨12759474850019422604921603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34025266266718460279790941 12759474850019422604921603)
                  ·
                    refine ⟨19139212275029133907382405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12759474850019422604921603 19139212275029133907382405)
                    ·
                      refine ⟨3588602301567962607634201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19139212275029133907382405 3588602301567962607634201)
                      ·
                        rfl

theorem cell23_6988778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_6988778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988778 prefixEnd_6988778 := by exact prefixLift 6988778
  have htrace : WordTrace (prefixWord ++ tailWord_6988778) baseStart_6988778 baseEnd_6988778 := by
    simpa [prefixWord, tailWord_6988778, baseEnd_6988778] using wordTrace_append hprefix tailTrace_6988778
  have hstable : (prefixWord ++ tailWord_6988778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988778).length < 2 ^ (prefixWord ++ tailWord_6988778).sum := by decide
  have hdescent : baseEnd_6988778 < baseStart_6988778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988782 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_6988782 : Nat := 118140960795 + 6988782 * 2 ^ 59
def prefixEnd_6988782 : Nat := 4983230072969 + 3 ^ 40 * 6988782 * 2
def baseEnd_6988782 : Nat := 3588604355490580591984183

theorem tailTrace_6988782 : CollatzResearch.WordTrace tailWord_6988782 prefixEnd_6988782 3588604355490580591984183 := by
  unfold tailWord_6988782
  simp only [CollatzResearch.WordTrace]
  refine ⟨31862727570855484723030075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169934547044562585189493733 31862727570855484723030075)
  ·
    refine ⟨47794091356283227084545113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31862727570855484723030075 47794091356283227084545113)
    ·
      refine ⟨35845568517212420313408835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47794091356283227084545113 35845568517212420313408835)
      ·
        refine ⟨53768352775818630470113253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35845568517212420313408835 53768352775818630470113253)
        ·
          refine ⟨10081566145465993213146235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53768352775818630470113253 10081566145465993213146235)
          ·
            refine ⟨15122349218198989819719353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081566145465993213146235 15122349218198989819719353)
            ·
              refine ⟨11341761913649242364789515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15122349218198989819719353 11341761913649242364789515)
              ·
                refine ⟨17012642870473863547184273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11341761913649242364789515 17012642870473863547184273)
                ·
                  refine ⟨12759482152855397660388205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17012642870473863547184273 12759482152855397660388205)
                  ·
                    refine ⟨4784805807320774122645577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12759482152855397660388205 4784805807320774122645577)
                    ·
                      refine ⟨3588604355490580591984183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4784805807320774122645577 3588604355490580591984183)
                      ·
                        rfl

theorem cell23_6988782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_6988782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988782 prefixEnd_6988782 := by exact prefixLift 6988782
  have htrace : WordTrace (prefixWord ++ tailWord_6988782) baseStart_6988782 baseEnd_6988782 := by
    simpa [prefixWord, tailWord_6988782, baseEnd_6988782] using wordTrace_append hprefix tailTrace_6988782
  have hstable : (prefixWord ++ tailWord_6988782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988782).length < 2 ^ (prefixWord ++ tailWord_6988782).sum := by decide
  have hdescent : baseEnd_6988782 < baseStart_6988782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988862 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_6988862 : Nat := 118140960795 + 6988862 * 2 ^ 59
def prefixEnd_6988862 : Nat := 4983230072969 + 3 ^ 40 * 6988862 * 2
def baseEnd_6988862 : Nat := 3588645433942940278983815

theorem tailTrace_6988862 : CollatzResearch.WordTrace tailWord_6988862 prefixEnd_6988862 3588645433942940278983815 := by
  unfold tailWord_6988862
  simp only [CollatzResearch.WordTrace]
  refine ⟨31863092300819256430894105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169936492271036034298101893 31863092300819256430894105)
  ·
    refine ⟨23897319225614442323170579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31863092300819256430894105 23897319225614442323170579)
    ·
      refine ⟨35845978838421663484755869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23897319225614442323170579 35845978838421663484755869)
      ·
        refine ⟨13442242064408123806783451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35845978838421663484755869 13442242064408123806783451)
        ·
          refine ⟨20163363096612185710175177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13442242064408123806783451 20163363096612185710175177)
          ·
            refine ⟨15122522322459139282631383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20163363096612185710175177 15122522322459139282631383)
            ·
              refine ⟨22683783483688708923947075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15122522322459139282631383 22683783483688708923947075)
              ·
                refine ⟨34025675225533063385920613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22683783483688708923947075 34025675225533063385920613)
                ·
                  refine ⟨6379814104787449384860115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34025675225533063385920613 6379814104787449384860115)
                  ·
                    refine ⟨9569721157181174077290173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6379814104787449384860115 9569721157181174077290173)
                    ·
                      refine ⟨3588645433942940278983815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9569721157181174077290173 3588645433942940278983815)
                      ·
                        rfl

theorem cell23_6988862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_6988862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988862 prefixEnd_6988862 := by exact prefixLift 6988862
  have htrace : WordTrace (prefixWord ++ tailWord_6988862) baseStart_6988862 baseEnd_6988862 := by
    simpa [prefixWord, tailWord_6988862, baseEnd_6988862] using wordTrace_append hprefix tailTrace_6988862
  have hstable : (prefixWord ++ tailWord_6988862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988862).length < 2 ^ (prefixWord ++ tailWord_6988862).sum := by decide
  have hdescent : baseEnd_6988862 < baseStart_6988862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988918 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6988918 : Nat := 118140960795 + 6988918 * 2 ^ 59
def prefixEnd_6988918 : Nat := 4983230072969 + 3 ^ 40 * 6988918 * 2
def baseEnd_6988918 : Nat := 3588674188859592059883557

theorem tailTrace_6988918 : CollatzResearch.WordTrace tailWord_6988918 prefixEnd_6988918 3588674188859592059883557 := by
  unfold tailWord_6988918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931673805896948313199463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169937853929567448674127605 15931673805896948313199463)
  ·
    refine ⟨23897510708845422469799195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15931673805896948313199463 23897510708845422469799195)
    ·
      refine ⟨35846266063268133704698793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23897510708845422469799195 35846266063268133704698793)
      ·
        refine ⟨26884699547451100278524095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35846266063268133704698793 26884699547451100278524095)
        ·
          refine ⟨40327049321176650417786143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26884699547451100278524095 40327049321176650417786143)
          ·
            refine ⟨60490573981764975626679215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40327049321176650417786143 60490573981764975626679215)
            ·
              refine ⟨90735860972647463440018823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60490573981764975626679215 90735860972647463440018823)
              ·
                refine ⟨136103791458971195160028235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90735860972647463440018823 136103791458971195160028235)
                ·
                  refine ⟨204155687188456792740042353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136103791458971195160028235 204155687188456792740042353)
                  ·
                    refine ⟨153116765391342594555031765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204155687188456792740042353 153116765391342594555031765)
                    ·
                      refine ⟨3588674188859592059883557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153116765391342594555031765 3588674188859592059883557)
                      ·
                        rfl

theorem cell23_6988918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6988918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988918 prefixEnd_6988918 := by exact prefixLift 6988918
  have htrace : WordTrace (prefixWord ++ tailWord_6988918) baseStart_6988918 baseEnd_6988918 := by
    simpa [prefixWord, tailWord_6988918, baseEnd_6988918] using wordTrace_append hprefix tailTrace_6988918
  have hstable : (prefixWord ++ tailWord_6988918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988918).length < 2 ^ (prefixWord ++ tailWord_6988918).sum := by decide
  have hdescent : baseEnd_6988918 < baseStart_6988918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988938 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_6988938 : Nat := 118140960795 + 6988938 * 2 ^ 59
def prefixEnd_6988938 : Nat := 4983230072969 + 3 ^ 40 * 6988938 * 2
def baseEnd_6988938 : Nat := 1196228152824227327211155

theorem tailTrace_6988938 : CollatzResearch.WordTrace tailWord_6988938 prefixEnd_6988938 1196228152824227327211155 := by
  unfold tailWord_6988938
  simp only [CollatzResearch.WordTrace]
  refine ⟨63726877588569679106729867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169938340236185810951279645 63726877588569679106729867)
  ·
    refine ⟨95590316382854518660094801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63726877588569679106729867 95590316382854518660094801)
    ·
      refine ⟨71692737287140888995071101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95590316382854518660094801 71692737287140888995071101)
      ·
        refine ⟨26884776482677833373151663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71692737287140888995071101 26884776482677833373151663)
        ·
          refine ⟨40327164724016750059727495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26884776482677833373151663 40327164724016750059727495)
          ·
            refine ⟨60490747086025125089591243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40327164724016750059727495 60490747086025125089591243)
            ·
              refine ⟨90736120629037687634386865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60490747086025125089591243 90736120629037687634386865)
              ·
                refine ⟨68052090471778265725790149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90736120629037687634386865 68052090471778265725790149)
                ·
                  refine ⟨12759766963458424823585653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68052090471778265725790149 12759766963458424823585653)
                  ·
                    refine ⟨1196228152824227327211155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12759766963458424823585653 1196228152824227327211155)
                    ·
                      rfl

theorem cell23_6988938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_6988938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988938 prefixEnd_6988938 := by exact prefixLift 6988938
  have htrace : WordTrace (prefixWord ++ tailWord_6988938) baseStart_6988938 baseEnd_6988938 := by
    simpa [prefixWord, tailWord_6988938, baseEnd_6988938] using wordTrace_append hprefix tailTrace_6988938
  have hstable : (prefixWord ++ tailWord_6988938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988938).length < 2 ^ (prefixWord ++ tailWord_6988938).sum := by decide
  have hdescent : baseEnd_6988938 < baseStart_6988938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6988992 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 2, 4, 2]
def baseStart_6988992 : Nat := 118140960795 + 6988992 * 2 ^ 59
def prefixEnd_6988992 : Nat := 4983230072969 + 3 ^ 40 * 6988992 * 2
def baseEnd_6988992 : Nat := 3588712186428024770358217

theorem tailTrace_6988992 : CollatzResearch.WordTrace tailWord_6988992 prefixEnd_6988992 3588712186428024770358217 := by
  unfold tailWord_6988992
  simp only [CollatzResearch.WordTrace]
  refine ⟨127454739948041541824692615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169939653264055389099590153 127454739948041541824692615)
  ·
    refine ⟨191182109922062312737038923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127454739948041541824692615 191182109922062312737038923)
    ·
      refine ⟨286773164883093469105558385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191182109922062312737038923 286773164883093469105558385)
      ·
        refine ⟨215079873662320101829168789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286773164883093469105558385 215079873662320101829168789)
        ·
          refine ⟨10081869077921254773242287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 215079873662320101829168789 10081869077921254773242287)
          ·
            refine ⟨15122803616881882159863431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081869077921254773242287 15122803616881882159863431)
            ·
              refine ⟨22684205425322823239795147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15122803616881882159863431 22684205425322823239795147)
              ·
                refine ⟨34026308137984234859692721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22684205425322823239795147 34026308137984234859692721)
                ·
                  refine ⟨25519731103488176144769541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34026308137984234859692721 25519731103488176144769541)
                  ·
                    refine ⟨4784949581904033027144289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25519731103488176144769541 4784949581904033027144289)
                    ·
                      refine ⟨3588712186428024770358217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4784949581904033027144289 3588712186428024770358217)
                      ·
                        rfl

theorem cell23_6988992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_6988992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6988992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6988992 prefixEnd_6988992 := by exact prefixLift 6988992
  have htrace : WordTrace (prefixWord ++ tailWord_6988992) baseStart_6988992 baseEnd_6988992 := by
    simpa [prefixWord, tailWord_6988992, baseEnd_6988992] using wordTrace_append hprefix tailTrace_6988992
  have hstable : (prefixWord ++ tailWord_6988992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6988992).length < 2 ^ (prefixWord ++ tailWord_6988992).sum := by decide
  have hdescent : baseEnd_6988992 < baseStart_6988992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6988992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989065 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 2, 6, 2]
def baseStart_6989065 : Nat := 118140960795 + 6989065 * 2 ^ 59
def prefixEnd_6989065 : Nat := 4983230072969 + 3 ^ 40 * 6989065 * 2
def baseEnd_6989065 : Nat := 3588749670515802984745381

theorem tailTrace_6989065 : CollatzResearch.WordTrace tailWord_6989065 prefixEnd_6989065 3588749670515802984745381 := by
  unfold tailWord_6989065
  simp only [CollatzResearch.WordTrace]
  refine ⟨254912142424818617116792649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169941428283212411411195099 254912142424818617116792649)
  ·
    refine ⟨191184106818613962837594487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254912142424818617116792649 191184106818613962837594487)
    ·
      refine ⟨286776160227920944256391731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191184106818613962837594487 286776160227920944256391731)
      ·
        refine ⟨430164240341881416384587597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286776160227920944256391731 430164240341881416384587597)
        ·
          refine ⟨161311590128205531144220349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430164240341881416384587597 161311590128205531144220349)
          ·
            refine ⟨60491846298077074179082631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161311590128205531144220349 60491846298077074179082631)
            ·
              refine ⟨90737769447115611268623947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60491846298077074179082631 90737769447115611268623947)
              ·
                refine ⟨136106654170673416902935921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90737769447115611268623947 136106654170673416902935921)
                ·
                  refine ⟨102079990628005062677201941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136106654170673416902935921 102079990628005062677201941)
                  ·
                    refine ⟨4784999560687737312993841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102079990628005062677201941 4784999560687737312993841)
                    ·
                      refine ⟨3588749670515802984745381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4784999560687737312993841 3588749670515802984745381)
                      ·
                        rfl

theorem cell23_6989065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 6, 2].length) (baseStart_6989065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989065 prefixEnd_6989065 := by exact prefixLift 6989065
  have htrace : WordTrace (prefixWord ++ tailWord_6989065) baseStart_6989065 baseEnd_6989065 := by
    simpa [prefixWord, tailWord_6989065, baseEnd_6989065] using wordTrace_append hprefix tailTrace_6989065
  have hstable : (prefixWord ++ tailWord_6989065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989065).length < 2 ^ (prefixWord ++ tailWord_6989065).sum := by decide
  have hdescent : baseEnd_6989065 < baseStart_6989065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989082 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4]
def baseStart_6989082 : Nat := 118140960795 + 6989082 * 2 ^ 59
def prefixEnd_6989082 : Nat := 4983230072969 + 3 ^ 40 * 6989082 * 2
def baseEnd_6989082 : Nat := 3588758399686929418232803

theorem tailTrace_6989082 : CollatzResearch.WordTrace tailWord_6989082 prefixEnd_6989082 3588758399686929418232803 := by
  unfold tailWord_6989082
  simp only [CollatzResearch.WordTrace]
  refine ⟨63728190616439257255040375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169941841643838019346774333 63728190616439257255040375)
  ·
    refine ⟨95592285924658885882560563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63728190616439257255040375 95592285924658885882560563)
    ·
      refine ⟨143388428886988328823840845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95592285924658885882560563 143388428886988328823840845)
      ·
        refine ⟨53770660832620623308940317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143388428886988328823840845 53770660832620623308940317)
        ·
          refine ⟨20163997812232733740852619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53770660832620623308940317 20163997812232733740852619)
          ·
            refine ⟨30245996718349100611278929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20163997812232733740852619 30245996718349100611278929)
            ·
              refine ⟨22684497538761825458459197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30245996718349100611278929 22684497538761825458459197)
              ·
                refine ⟨8506686577035684546922199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22684497538761825458459197 8506686577035684546922199)
                ·
                  refine ⟨12760029865553526820383299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8506686577035684546922199 12760029865553526820383299)
                  ·
                    refine ⟨19140044798330290230574949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12760029865553526820383299 19140044798330290230574949)
                    ·
                      refine ⟨3588758399686929418232803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19140044798330290230574949 3588758399686929418232803)
                      ·
                        rfl

theorem cell23_6989082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_6989082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989082 prefixEnd_6989082 := by exact prefixLift 6989082
  have htrace : WordTrace (prefixWord ++ tailWord_6989082) baseStart_6989082 baseEnd_6989082 := by
    simpa [prefixWord, tailWord_6989082, baseEnd_6989082] using wordTrace_append hprefix tailTrace_6989082
  have hstable : (prefixWord ++ tailWord_6989082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989082).length < 2 ^ (prefixWord ++ tailWord_6989082).sum := by decide
  have hdescent : baseEnd_6989082 < baseStart_6989082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989092 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_6989092 : Nat := 118140960795 + 6989092 * 2 ^ 59
def prefixEnd_6989092 : Nat := 4983230072969 + 3 ^ 40 * 6989092 * 2
def baseEnd_6989092 : Nat := 1196254511497824793035919

theorem tailTrace_6989092 : CollatzResearch.WordTrace tailWord_6989092 prefixEnd_6989092 1196254511497824793035919 := by
  unfold tailWord_6989092
  simp only [CollatzResearch.WordTrace]
  refine ⟨127456563597860400364012765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169942084797147200485350353 127456563597860400364012765)
  ·
    refine ⟨47796211349197650136504787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127456563597860400364012765 47796211349197650136504787)
    ·
      refine ⟨71694317023796475204757181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47796211349197650136504787 71694317023796475204757181)
      ·
        refine ⟨26885368883923678201783943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71694317023796475204757181 26885368883923678201783943)
        ·
          refine ⟨40328053325885517302675915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26885368883923678201783943 40328053325885517302675915)
          ·
            refine ⟨60492079988828275954013873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40328053325885517302675915 60492079988828275954013873)
            ·
              refine ⟨45369059991621206965510405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60492079988828275954013873 45369059991621206965510405)
              ·
                refine ⟨8506698748428976306033201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45369059991621206965510405 8506698748428976306033201)
                ·
                  refine ⟨6380024061321732229524901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8506698748428976306033201 6380024061321732229524901)
                  ·
                    refine ⟨1196254511497824793035919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6380024061321732229524901 1196254511497824793035919)
                    ·
                      rfl

theorem cell23_6989092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_6989092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989092 prefixEnd_6989092 := by exact prefixLift 6989092
  have htrace : WordTrace (prefixWord ++ tailWord_6989092) baseStart_6989092 baseEnd_6989092 := by
    simpa [prefixWord, tailWord_6989092, baseEnd_6989092] using wordTrace_append hprefix tailTrace_6989092
  have hstable : (prefixWord ++ tailWord_6989092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989092).length < 2 ^ (prefixWord ++ tailWord_6989092).sum := by decide
  have hdescent : baseEnd_6989092 < baseStart_6989092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989105 : List Nat := [1, 2, 2, 3, 3, 2, 2, 8]
def baseStart_6989105 : Nat := 118140960795 + 6989105 * 2 ^ 59
def prefixEnd_6989105 : Nat := 4983230072969 + 3 ^ 40 * 6989105 * 2
def baseEnd_6989105 : Nat := 132917415175628993638711

theorem tailTrace_6989105 : CollatzResearch.WordTrace tailWord_6989105 prefixEnd_6989105 132917415175628993638711 := by
  unfold tailWord_6989105
  simp only [CollatzResearch.WordTrace]
  refine ⟨254913601344673703948248769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169942400896449135965499179 254913601344673703948248769)
  ·
    refine ⟨191185201008505277961186577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254913601344673703948248769 191185201008505277961186577)
    ·
      refine ⟨143388900756378958470889933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191185201008505277961186577 143388900756378958470889933)
      ·
        refine ⟨53770837783642109426583725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143388900756378958470889933 53770837783642109426583725)
        ·
          refine ⟨20164064168865791034968897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53770837783642109426583725 20164064168865791034968897)
          ·
            refine ⟨15123048126649343276226673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20164064168865791034968897 15123048126649343276226673)
            ·
              refine ⟨11342286094987007457170005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15123048126649343276226673 11342286094987007457170005)
              ·
                refine ⟨132917415175628993638711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11342286094987007457170005 132917415175628993638711)
                ·
                  rfl

theorem cell23_6989105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 8].length) (baseStart_6989105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989105 prefixEnd_6989105 := by exact prefixLift 6989105
  have htrace : WordTrace (prefixWord ++ tailWord_6989105) baseStart_6989105 baseEnd_6989105 := by
    simpa [prefixWord, tailWord_6989105, baseEnd_6989105] using wordTrace_append hprefix tailTrace_6989105
  have hstable : (prefixWord ++ tailWord_6989105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989105).length < 2 ^ (prefixWord ++ tailWord_6989105).sum := by decide
  have hdescent : baseEnd_6989105 < baseStart_6989105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989109 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_6989109 : Nat := 118140960795 + 6989109 * 2 ^ 59
def prefixEnd_6989109 : Nat := 4983230072969 + 3 ^ 40 * 6989109 * 2
def baseEnd_6989109 : Nat := 1196257421221533604198393

theorem tailTrace_6989109 : CollatzResearch.WordTrace tailWord_6989109 prefixEnd_6989109 1196257421221533604198393 := by
  unfold tailWord_6989109
  simp only [CollatzResearch.WordTrace]
  refine ⟨254913747236659212631394381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169942498157772808420929587 254913747236659212631394381)
  ·
    refine ⟨95592655213747204736772893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254913747236659212631394381 95592655213747204736772893)
    ·
      refine ⟨35847245705155201776289835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95592655213747204736772893 35847245705155201776289835)
      ·
        refine ⟨53770868557732802664434753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35847245705155201776289835 53770868557732802664434753)
        ·
          refine ⟨40328151418299601998326065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53770868557732802664434753 40328151418299601998326065)
          ·
            refine ⟨30246113563724701498744549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40328151418299601998326065 30246113563724701498744549)
            ·
              refine ⟨5671146293198381531014603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30246113563724701498744549 5671146293198381531014603)
              ·
                refine ⟨8506719439797572296521905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671146293198381531014603 8506719439797572296521905)
                ·
                  refine ⟨6380039579848179222391429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8506719439797572296521905 6380039579848179222391429)
                  ·
                    refine ⟨1196257421221533604198393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6380039579848179222391429 1196257421221533604198393)
                    ·
                      rfl

theorem cell23_6989109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_6989109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989109 prefixEnd_6989109 := by exact prefixLift 6989109
  have htrace : WordTrace (prefixWord ++ tailWord_6989109) baseStart_6989109 baseEnd_6989109 := by
    simpa [prefixWord, tailWord_6989109, baseEnd_6989109] using wordTrace_append hprefix tailTrace_6989109
  have hstable : (prefixWord ++ tailWord_6989109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989109).length < 2 ^ (prefixWord ++ tailWord_6989109).sum := by decide
  have hdescent : baseEnd_6989109 < baseStart_6989109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989119 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 3]
def baseStart_6989119 : Nat := 118140960795 + 6989119 * 2 ^ 59
def prefixEnd_6989119 : Nat := 4983230072969 + 3 ^ 40 * 6989119 * 2
def baseEnd_6989119 : Nat := 3588777398471145773470133

theorem tailTrace_6989119 : CollatzResearch.WordTrace tailWord_6989119 prefixEnd_6989119 3588777398471145773470133 := by
  unfold tailWord_6989119
  simp only [CollatzResearch.WordTrace]
  refine ⟨254914111966622984339258411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169942741311081989559505607 254914111966622984339258411)
  ·
    refine ⟨382371167949934476508887617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254914111966622984339258411 382371167949934476508887617)
    ·
      refine ⟨286778375962450857381665713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382371167949934476508887617 286778375962450857381665713)
      ·
        refine ⟨215083781971838143036249285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286778375962450857381665713 215083781971838143036249285)
        ·
          refine ⟨40328209119719651819296741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215083781971838143036249285 40328209119719651819296741)
          ·
            refine ⟨7561539209947434716118139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40328209119719651819296741 7561539209947434716118139)
            ·
              refine ⟨11342308814921152074177209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7561539209947434716118139 11342308814921152074177209)
              ·
                refine ⟨8506731611190864055632907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11342308814921152074177209 8506731611190864055632907)
                ·
                  refine ⟨12760097416786296083449361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8506731611190864055632907 12760097416786296083449361)
                  ·
                    refine ⟨9570073062589722062587021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12760097416786296083449361 9570073062589722062587021)
                    ·
                      refine ⟨3588777398471145773470133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9570073062589722062587021 3588777398471145773470133)
                      ·
                        rfl

theorem cell23_6989119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_6989119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989119 prefixEnd_6989119 := by exact prefixLift 6989119
  have htrace : WordTrace (prefixWord ++ tailWord_6989119) baseStart_6989119 baseEnd_6989119 := by
    simpa [prefixWord, tailWord_6989119, baseEnd_6989119] using wordTrace_append hprefix tailTrace_6989119
  have hstable : (prefixWord ++ tailWord_6989119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989119).length < 2 ^ (prefixWord ++ tailWord_6989119).sum := by decide
  have hdescent : baseEnd_6989119 < baseStart_6989119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989126 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_6989126 : Nat := 118140960795 + 6989126 * 2 ^ 59
def prefixEnd_6989126 : Nat := 4983230072969 + 3 ^ 40 * 6989126 * 2
def baseEnd_6989126 : Nat := 1196260330945242415360867

theorem tailTrace_6989126 : CollatzResearch.WordTrace tailWord_6989126 prefixEnd_6989126 1196260330945242415360867 := by
  unfold tailWord_6989126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7966073977424925766711351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169942911518398416356508821 7966073977424925766711351)
  ·
    refine ⟨11949110966137388650067027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7966073977424925766711351 11949110966137388650067027)
    ·
      refine ⟨17923666449206082975100541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11949110966137388650067027 17923666449206082975100541)
      ·
        refine ⟨6721374918452281115662703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17923666449206082975100541 6721374918452281115662703)
        ·
          refine ⟨10082062377678421673494055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721374918452281115662703 10082062377678421673494055)
          ·
            refine ⟨15123093566517632510241083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10082062377678421673494055 15123093566517632510241083)
            ·
              refine ⟨22684640349776448765361625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15123093566517632510241083 22684640349776448765361625)
              ·
                refine ⟨17013480262332336574021219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22684640349776448765361625 17013480262332336574021219)
                ·
                  refine ⟨25520220393498504861031829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17013480262332336574021219 25520220393498504861031829)
                  ·
                    refine ⟨1196260330945242415360867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25520220393498504861031829 1196260330945242415360867)
                    ·
                      rfl

theorem cell23_6989126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_6989126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989126 prefixEnd_6989126 := by exact prefixLift 6989126
  have htrace : WordTrace (prefixWord ++ tailWord_6989126) baseStart_6989126 baseEnd_6989126 := by
    simpa [prefixWord, tailWord_6989126, baseEnd_6989126] using wordTrace_append hprefix tailTrace_6989126
  have hstable : (prefixWord ++ tailWord_6989126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989126).length < 2 ^ (prefixWord ++ tailWord_6989126).sum := by decide
  have hdescent : baseEnd_6989126 < baseStart_6989126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989132 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_6989132 : Nat := 118140960795 + 6989132 * 2 ^ 59
def prefixEnd_6989132 : Nat := 4983230072969 + 3 ^ 40 * 6989132 * 2
def baseEnd_6989132 : Nat := 3588784073719654222607573

theorem tailTrace_6989132 : CollatzResearch.WordTrace tailWord_6989132 prefixEnd_6989132 3588784073719654222607573 := by
  unfold tailWord_6989132
  simp only [CollatzResearch.WordTrace]
  refine ⟨127457293057787943779740825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169943057410383925039654433 127457293057787943779740825)
  ·
    refine ⟨95592969793340957834805619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127457293057787943779740825 95592969793340957834805619)
    ·
      refine ⟨143389454690011436752208429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95592969793340957834805619 143389454690011436752208429)
      ·
        refine ⟨53771045508754288782078161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143389454690011436752208429 53771045508754288782078161)
        ·
          refine ⟨40328284131565716586558621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53771045508754288782078161 40328284131565716586558621)
          ·
            refine ⟨15123106549337143719959483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40328284131565716586558621 15123106549337143719959483)
            ·
              refine ⟨22684659824005715579939225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15123106549337143719959483 22684659824005715579939225)
              ·
                refine ⟨17013494868004286684954419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22684659824005715579939225 17013494868004286684954419)
                ·
                  refine ⟨25520242302006430027431629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17013494868004286684954419 25520242302006430027431629)
                  ·
                    refine ⟨9570090863252411260286861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25520242302006430027431629 9570090863252411260286861)
                    ·
                      refine ⟨3588784073719654222607573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9570090863252411260286861 3588784073719654222607573)
                      ·
                        rfl

theorem cell23_6989132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_6989132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989132 prefixEnd_6989132 := by exact prefixLift 6989132
  have htrace : WordTrace (prefixWord ++ tailWord_6989132) baseStart_6989132 baseEnd_6989132 := by
    simpa [prefixWord, tailWord_6989132, baseEnd_6989132] using wordTrace_append hprefix tailTrace_6989132
  have hstable : (prefixWord ++ tailWord_6989132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989132).length < 2 ^ (prefixWord ++ tailWord_6989132).sum := by decide
  have hdescent : baseEnd_6989132 < baseStart_6989132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989133 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6989133 : Nat := 118140960795 + 6989133 * 2 ^ 59
def prefixEnd_6989133 : Nat := 4983230072969 + 3 ^ 40 * 6989133 * 2
def baseEnd_6989133 : Nat := 3588784587200308718695069

theorem tailTrace_6989133 : CollatzResearch.WordTrace tailWord_6989133 prefixEnd_6989133 3588784587200308718695069 := by
  unfold tailWord_6989133
  simp only [CollatzResearch.WordTrace]
  refine ⟨254914622588572264730268053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169943081725714843153512035 254914622588572264730268053)
  ·
    refine ⟨11949122933839324909231315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 254914622588572264730268053 11949122933839324909231315)
    ·
      refine ⟨17923684400758987363846973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11949122933839324909231315 17923684400758987363846973)
      ·
        refine ⟨6721381650284620261442615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17923684400758987363846973 6721381650284620261442615)
        ·
          refine ⟨10082072475426930392163923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721381650284620261442615 10082072475426930392163923)
          ·
            refine ⟨15123108713140395588245885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10082072475426930392163923 15123108713140395588245885)
            ·
              refine ⟨5671165767427648345592207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15123108713140395588245885 5671165767427648345592207)
              ·
                refine ⟨8506748651141472518388311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671165767427648345592207 8506748651141472518388311)
                ·
                  refine ⟨12760122976712208777582467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8506748651141472518388311 12760122976712208777582467)
                  ·
                    refine ⟨19140184465068313166373701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12760122976712208777582467 19140184465068313166373701)
                    ·
                      refine ⟨3588784587200308718695069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19140184465068313166373701 3588784587200308718695069)
                      ·
                        rfl

theorem cell23_6989133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6989133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989133 prefixEnd_6989133 := by exact prefixLift 6989133
  have htrace : WordTrace (prefixWord ++ tailWord_6989133) baseStart_6989133 baseEnd_6989133 := by
    simpa [prefixWord, tailWord_6989133, baseEnd_6989133] using wordTrace_append hprefix tailTrace_6989133
  have hstable : (prefixWord ++ tailWord_6989133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989133).length < 2 ^ (prefixWord ++ tailWord_6989133).sum := by decide
  have hdescent : baseEnd_6989133 < baseStart_6989133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989155 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6989155 : Nat := 118140960795 + 6989155 * 2 ^ 59
def prefixEnd_6989155 : Nat := 4983230072969 + 3 ^ 40 * 6989155 * 2
def baseEnd_6989155 : Nat := 3588795883774707632619967

theorem tailTrace_6989155 : CollatzResearch.WordTrace tailWord_6989155 prefixEnd_6989155 3588795883774707632619967 := by
  unfold tailWord_6989155
  simp only [CollatzResearch.WordTrace]
  refine ⟨254915424994492562487568919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169943616662995041658379279 254915424994492562487568919)
  ·
    refine ⟨382373137491738843731353379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254915424994492562487568919 382373137491738843731353379)
    ·
      refine ⟨573559706237608265597030069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382373137491738843731353379 573559706237608265597030069)
      ·
        refine ⟨53771222459775774899721569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 573559706237608265597030069 53771222459775774899721569)
        ·
          refine ⟨40328416844831831174791177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53771222459775774899721569 40328416844831831174791177)
          ·
            refine ⟨30246312633623873381093383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40328416844831831174791177 30246312633623873381093383)
            ·
              refine ⟨45369468950435810071640075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30246312633623873381093383 45369468950435810071640075)
              ·
                refine ⟨68054203425653715107460113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45369468950435810071640075 68054203425653715107460113)
                ·
                  refine ⟨51040652569240286330595085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68054203425653715107460113 51040652569240286330595085)
                  ·
                    refine ⟨19140244713465107373973157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51040652569240286330595085 19140244713465107373973157)
                    ·
                      refine ⟨3588795883774707632619967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19140244713465107373973157 3588795883774707632619967)
                      ·
                        rfl

theorem cell23_6989155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6989155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989155 prefixEnd_6989155 := by exact prefixLift 6989155
  have htrace : WordTrace (prefixWord ++ tailWord_6989155) baseStart_6989155 baseEnd_6989155 := by
    simpa [prefixWord, tailWord_6989155, baseEnd_6989155] using wordTrace_append hprefix tailTrace_6989155
  have hstable : (prefixWord ++ tailWord_6989155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989155).length < 2 ^ (prefixWord ++ tailWord_6989155).sum := by decide
  have hdescent : baseEnd_6989155 < baseStart_6989155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989165 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_6989165 : Nat := 118140960795 + 6989165 * 2 ^ 59
def prefixEnd_6989165 : Nat := 4983230072969 + 3 ^ 40 * 6989165 * 2
def baseEnd_6989165 : Nat := 1196267006193750864498307

theorem tailTrace_6989165 : CollatzResearch.WordTrace tailWord_6989165 prefixEnd_6989165 1196267006193750864498307 := by
  unfold tailWord_6989165
  simp only [CollatzResearch.WordTrace]
  refine ⟨254915789724456334195432949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169943859816304222796955299 254915789724456334195432949)
  ·
    refine ⟨23898355286667781330821839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254915789724456334195432949 23898355286667781330821839)
    ·
      refine ⟨35847532930001671996232759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23898355286667781330821839 35847532930001671996232759)
      ·
        refine ⟨53771299395002507994349139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35847532930001671996232759 53771299395002507994349139)
        ·
          refine ⟨80656949092503761991523709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53771299395002507994349139 80656949092503761991523709)
          ·
            refine ⟨30246355909688910746821391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80656949092503761991523709 30246355909688910746821391)
            ·
              refine ⟨45369533864533366120232087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30246355909688910746821391 45369533864533366120232087)
              ·
                refine ⟨68054300796800049180348131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45369533864533366120232087 68054300796800049180348131)
                ·
                  refine ⟨102081451195200073770522197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68054300796800049180348131 102081451195200073770522197)
                  ·
                    refine ⟨1196267006193750864498307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102081451195200073770522197 1196267006193750864498307)
                    ·
                      rfl

theorem cell23_6989165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_6989165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989165 prefixEnd_6989165 := by exact prefixLift 6989165
  have htrace : WordTrace (prefixWord ++ tailWord_6989165) baseStart_6989165 baseEnd_6989165 := by
    simpa [prefixWord, tailWord_6989165, baseEnd_6989165] using wordTrace_append hprefix tailTrace_6989165
  have hstable : (prefixWord ++ tailWord_6989165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989165).length < 2 ^ (prefixWord ++ tailWord_6989165).sum := by decide
  have hdescent : baseEnd_6989165 < baseStart_6989165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989166 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6989166 : Nat := 118140960795 + 6989166 * 2 ^ 59
def prefixEnd_6989166 : Nat := 4983230072969 + 3 ^ 40 * 6989166 * 2
def baseEnd_6989166 : Nat := 3588801532061907089582417

theorem tailTrace_6989166 : CollatzResearch.WordTrace tailWord_6989166 prefixEnd_6989166 3588801532061907089582417 := by
  unfold tailWord_6989166
  simp only [CollatzResearch.WordTrace]
  refine ⟨31864478274681588920777419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169943884131635140910812901 31864478274681588920777419)
  ·
    refine ⟨47796717412022383381166129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31864478274681588920777419 47796717412022383381166129)
    ·
      refine ⟨35847538059016787535874597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47796717412022383381166129 35847538059016787535874597)
      ·
        refine ⟨6721413386065647662976487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35847538059016787535874597 6721413386065647662976487)
        ·
          refine ⟨10082120079098471494464731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721413386065647662976487 10082120079098471494464731)
          ·
            refine ⟨15123180118647707241697097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10082120079098471494464731 15123180118647707241697097)
            ·
              refine ⟨11342385088985780431272823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15123180118647707241697097 11342385088985780431272823)
              ·
                refine ⟨17013577633478670646909235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11342385088985780431272823 17013577633478670646909235)
                ·
                  refine ⟨25520366450218005970363853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17013577633478670646909235 25520366450218005970363853)
                  ·
                    refine ⟨9570137418831752238886445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25520366450218005970363853 9570137418831752238886445)
                    ·
                      refine ⟨3588801532061907089582417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9570137418831752238886445 3588801532061907089582417)
                      ·
                        rfl

theorem cell23_6989166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6989166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989166 prefixEnd_6989166 := by exact prefixLift 6989166
  have htrace : WordTrace (prefixWord ++ tailWord_6989166) baseStart_6989166 baseEnd_6989166 := by
    simpa [prefixWord, tailWord_6989166, baseEnd_6989166] using wordTrace_append hprefix tailTrace_6989166
  have hstable : (prefixWord ++ tailWord_6989166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989166).length < 2 ^ (prefixWord ++ tailWord_6989166).sum := by decide
  have hdescent : baseEnd_6989166 < baseStart_6989166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989175 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_6989175 : Nat := 118140960795 + 6989175 * 2 ^ 59
def prefixEnd_6989175 : Nat := 4983230072969 + 3 ^ 40 * 6989175 * 2
def baseEnd_6989175 : Nat := 3588806153387797554369875

theorem tailTrace_6989175 : CollatzResearch.WordTrace tailWord_6989175 prefixEnd_6989175 3588806153387797554369875 := by
  unfold tailWord_6989175
  simp only [CollatzResearch.WordTrace]
  refine ⟨254916154454420105903296979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169944102969613403935531319 254916154454420105903296979)
  ·
    refine ⟨382374231681630158854945469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254916154454420105903296979 382374231681630158854945469)
    ·
      refine ⟨143390336880611309570604551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382374231681630158854945469 143390336880611309570604551)
      ·
        refine ⟨215085505320916964355906827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143390336880611309570604551 215085505320916964355906827)
        ·
          refine ⟨322628257981375446533860241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215085505320916964355906827 322628257981375446533860241)
          ·
            refine ⟨241971193486031584900395181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322628257981375446533860241 241971193486031584900395181)
            ·
              refine ⟨90739197557261844337648193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241971193486031584900395181 90739197557261844337648193)
              ·
                refine ⟨68054398167946383253236145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90739197557261844337648193 68054398167946383253236145)
                ·
                  refine ⟨51040798625959787439927109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68054398167946383253236145 51040798625959787439927109)
                  ·
                    refine ⟨9570149742367460144986333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51040798625959787439927109 9570149742367460144986333)
                    ·
                      refine ⟨3588806153387797554369875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9570149742367460144986333 3588806153387797554369875)
                      ·
                        rfl

theorem cell23_6989175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_6989175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989175 prefixEnd_6989175 := by exact prefixLift 6989175
  have htrace : WordTrace (prefixWord ++ tailWord_6989175) baseStart_6989175 baseEnd_6989175 := by
    simpa [prefixWord, tailWord_6989175, baseEnd_6989175] using wordTrace_append hprefix tailTrace_6989175
  have hstable : (prefixWord ++ tailWord_6989175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989175).length < 2 ^ (prefixWord ++ tailWord_6989175).sum := by decide
  have hdescent : baseEnd_6989175 < baseStart_6989175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989193 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 1, 3, 2]
def baseStart_6989193 : Nat := 118140960795 + 6989193 * 2 ^ 59
def prefixEnd_6989193 : Nat := 4983230072969 + 3 ^ 40 * 6989193 * 2
def baseEnd_6989193 : Nat := 3588815396039578483944793

theorem tailTrace_6989193 : CollatzResearch.WordTrace tailWord_6989193 prefixEnd_6989193 3588815396039578483944793 := by
  unfold tailWord_6989193
  simp only [CollatzResearch.WordTrace]
  refine ⟨254916810968354894977452233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169944540645569929984968155 254916810968354894977452233)
  ·
    refine ⟨191187608226266171233089175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254916810968354894977452233 191187608226266171233089175)
    ·
      refine ⟨286781412339399256849633763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191187608226266171233089175 286781412339399256849633763)
      ·
        refine ⟨430172118509098885274450645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286781412339399256849633763 430172118509098885274450645)
        ·
          refine ⟨10082159027557005123619937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 430172118509098885274450645 10082159027557005123619937)
          ·
            refine ⟨7561619270667753842714953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10082159027557005123619937 7561619270667753842714953)
            ·
              refine ⟨5671214453000815382036215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7561619270667753842714953 5671214453000815382036215)
              ·
                refine ⟨8506821679501223073054323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671214453000815382036215 8506821679501223073054323)
                ·
                  refine ⟨12760232519251834609581485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8506821679501223073054323 12760232519251834609581485)
                  ·
                    refine ⟨4785087194719437978593057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12760232519251834609581485 4785087194719437978593057)
                    ·
                      refine ⟨3588815396039578483944793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785087194719437978593057 3588815396039578483944793)
                      ·
                        rfl

theorem cell23_6989193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 3, 2].length) (baseStart_6989193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989193 prefixEnd_6989193 := by exact prefixLift 6989193
  have htrace : WordTrace (prefixWord ++ tailWord_6989193) baseStart_6989193 baseEnd_6989193 := by
    simpa [prefixWord, tailWord_6989193, baseEnd_6989193] using wordTrace_append hprefix tailTrace_6989193
  have hstable : (prefixWord ++ tailWord_6989193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989193).length < 2 ^ (prefixWord ++ tailWord_6989193).sum := by decide
  have hdescent : baseEnd_6989193 < baseStart_6989193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989223 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_6989223 : Nat := 118140960795 + 6989223 * 2 ^ 59
def prefixEnd_6989223 : Nat := 4983230072969 + 3 ^ 40 * 6989223 * 2
def baseEnd_6989223 : Nat := 3588830800459213366569655

theorem tailTrace_6989223 : CollatzResearch.WordTrace tailWord_6989223 prefixEnd_6989223 3588830800459213366569655 := by
  unfold tailWord_6989223
  simp only [CollatzResearch.WordTrace]
  refine ⟨254917905158246210101044323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169945270105497473400696215 254917905158246210101044323)
  ·
    refine ⟨382376857737369315151566485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254917905158246210101044323 382376857737369315151566485)
    ·
      refine ⟨17923915206439186647729679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 382376857737369315151566485 17923915206439186647729679)
      ·
        refine ⟨26885872809658779971594519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17923915206439186647729679 26885872809658779971594519)
        ·
          refine ⟨40328809214488169957391779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26885872809658779971594519 40328809214488169957391779)
          ·
            refine ⟨60493213821732254936087669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40328809214488169957391779 60493213821732254936087669)
            ·
              refine ⟨5671238795787398900258219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60493213821732254936087669 5671238795787398900258219)
              ·
                refine ⟨8506858193681098350387329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671238795787398900258219 8506858193681098350387329)
                ·
                  refine ⟨6380143645260823762790497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8506858193681098350387329 6380143645260823762790497)
                  ·
                    refine ⟨4785107733945617822092873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6380143645260823762790497 4785107733945617822092873)
                    ·
                      refine ⟨3588830800459213366569655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785107733945617822092873 3588830800459213366569655)
                      ·
                        rfl

theorem cell23_6989223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_6989223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989223 prefixEnd_6989223 := by exact prefixLift 6989223
  have htrace : WordTrace (prefixWord ++ tailWord_6989223) baseStart_6989223 baseEnd_6989223 := by
    simpa [prefixWord, tailWord_6989223, baseEnd_6989223] using wordTrace_append hprefix tailTrace_6989223
  have hstable : (prefixWord ++ tailWord_6989223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989223).length < 2 ^ (prefixWord ++ tailWord_6989223).sum := by decide
  have hdescent : baseEnd_6989223 < baseStart_6989223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989262 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_6989262 : Nat := 118140960795 + 6989262 * 2 ^ 59
def prefixEnd_6989262 : Nat := 4983230072969 + 3 ^ 40 * 6989262 * 2
def baseEnd_6989262 : Nat := 3588850826204738713981975

theorem tailTrace_6989262 : CollatzResearch.WordTrace tailWord_6989262 prefixEnd_6989262 3588850826204738713981975 := by
  unfold tailWord_6989262
  simp only [CollatzResearch.WordTrace]
  refine ⟨31864915950638114970214255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169946218403403279841142693 31864915950638114970214255)
  ·
    refine ⟨47797373925957172455321383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31864915950638114970214255 47797373925957172455321383)
    ·
      refine ⟨71696060888935758682982075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47797373925957172455321383 71696060888935758682982075)
      ·
        refine ⟨107544091333403638024473113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71696060888935758682982075 107544091333403638024473113)
        ·
          refine ⟨80658068500052728518354835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107544091333403638024473113 80658068500052728518354835)
          ·
            refine ⟨120987102750079092777532253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80658068500052728518354835 120987102750079092777532253)
            ·
              refine ⟨45370163531279659791574595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120987102750079092777532253 45370163531279659791574595)
              ·
                refine ⟨68055245296919489687361893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45370163531279659791574595 68055245296919489687361893)
                ·
                  refine ⟨12760358493172404316380355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68055245296919489687361893 12760358493172404316380355)
                  ·
                    refine ⟨19140537739758606474570533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12760358493172404316380355 19140537739758606474570533)
                    ·
                      refine ⟨3588850826204738713981975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19140537739758606474570533 3588850826204738713981975)
                      ·
                        rfl

theorem cell23_6989262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_6989262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989262 prefixEnd_6989262 := by exact prefixLift 6989262
  have htrace : WordTrace (prefixWord ++ tailWord_6989262) baseStart_6989262 baseEnd_6989262 := by
    simpa [prefixWord, tailWord_6989262, baseEnd_6989262] using wordTrace_append hprefix tailTrace_6989262
  have hstable : (prefixWord ++ tailWord_6989262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989262).length < 2 ^ (prefixWord ++ tailWord_6989262).sum := by decide
  have hdescent : baseEnd_6989262 < baseStart_6989262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989305 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_6989305 : Nat := 118140960795 + 6989305 * 2 ^ 59
def prefixEnd_6989305 : Nat := 4983230072969 + 3 ^ 40 * 6989305 * 2
def baseEnd_6989305 : Nat := 3588872905872882045744277

theorem tailTrace_6989305 : CollatzResearch.WordTrace tailWord_6989305 prefixEnd_6989305 3588872905872882045744277 := by
  unfold tailWord_6989305
  simp only [CollatzResearch.WordTrace]
  refine ⟨254920895943949138105529369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169947263962632758737019579 254920895943949138105529369)
  ·
    refine ⟨191190671957961853579147027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254920895943949138105529369 191190671957961853579147027)
    ·
      refine ⟨286786007936942780368720541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191190671957961853579147027 286786007936942780368720541)
      ·
        refine ⟨107544752976353542638270203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286786007936942780368720541 107544752976353542638270203)
        ·
          refine ⟨161317129464530313957405305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107544752976353542638270203 161317129464530313957405305)
          ·
            refine ⟨120987847098397735468053979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161317129464530313957405305 120987847098397735468053979)
            ·
              refine ⟨181481770647596603202080969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120987847098397735468053979 181481770647596603202080969)
              ·
                refine ⟨136111327985697452401560727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181481770647596603202080969 136111327985697452401560727)
                ·
                  refine ⟨204166991978546178602341091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136111327985697452401560727 204166991978546178602341091)
                  ·
                    refine ⟨306250487967819267903511637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204166991978546178602341091 306250487967819267903511637)
                    ·
                      refine ⟨3588872905872882045744277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 306250487967819267903511637 3588872905872882045744277)
                      ·
                        rfl

theorem cell23_6989305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_6989305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989305 prefixEnd_6989305 := by exact prefixLift 6989305
  have htrace : WordTrace (prefixWord ++ tailWord_6989305) baseStart_6989305 baseEnd_6989305 := by
    simpa [prefixWord, tailWord_6989305, baseEnd_6989305] using wordTrace_append hprefix tailTrace_6989305
  have hstable : (prefixWord ++ tailWord_6989305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989305).length < 2 ^ (prefixWord ++ tailWord_6989305).sum := by decide
  have hdescent : baseEnd_6989305 < baseStart_6989305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989319 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 6]
def baseStart_6989319 : Nat := 118140960795 + 6989319 * 2 ^ 59
def prefixEnd_6989319 : Nat := 4983230072969 + 3 ^ 40 * 6989319 * 2
def baseEnd_6989319 : Nat := 398764454955782776774357

theorem tailTrace_6989319 : CollatzResearch.WordTrace tailWord_6989319 prefixEnd_6989319 398764454955782776774357 := by
  unfold tailWord_6989319
  simp only [CollatzResearch.WordTrace]
  refine ⟨254921406565898418496539011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169947604377265612331026007 254921406565898418496539011)
  ·
    refine ⟨382382109848847627744808517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254921406565898418496539011 382382109848847627744808517)
    ·
      refine ⟨71696645596658930202151597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382382109848847627744808517 71696645596658930202151597)
      ·
        refine ⟨26886242098747098825806849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71696645596658930202151597 26886242098747098825806849)
        ·
          refine ⟨20164681574060324119355137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26886242098747098825806849 20164681574060324119355137)
          ·
            refine ⟨15123511180545243089516353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20164681574060324119355137 15123511180545243089516353)
            ·
              refine ⟨11342633385408932317137265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15123511180545243089516353 11342633385408932317137265)
              ·
                refine ⟨8506975039056699237852949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11342633385408932317137265 8506975039056699237852949)
                ·
                  refine ⟨398764454955782776774357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8506975039056699237852949 398764454955782776774357)
                  ·
                    rfl

theorem cell23_6989319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 6].length) (baseStart_6989319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989319 prefixEnd_6989319 := by exact prefixLift 6989319
  have htrace : WordTrace (prefixWord ++ tailWord_6989319) baseStart_6989319 baseEnd_6989319 := by
    simpa [prefixWord, tailWord_6989319, baseEnd_6989319] using wordTrace_append hprefix tailTrace_6989319
  have hstable : (prefixWord ++ tailWord_6989319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989319).length < 2 ^ (prefixWord ++ tailWord_6989319).sum := by decide
  have hdescent : baseEnd_6989319 < baseStart_6989319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989329 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 3]
def baseStart_6989329 : Nat := 118140960795 + 6989329 * 2 ^ 59
def prefixEnd_6989329 : Nat := 4983230072969 + 3 ^ 40 * 6989329 * 2
def baseEnd_6989329 : Nat := 3588885229408589951844167

theorem tailTrace_6989329 : CollatzResearch.WordTrace tailWord_6989329 prefixEnd_6989329 3588885229408589951844167 := by
  unfold tailWord_6989329
  simp only [CollatzResearch.WordTrace]
  refine ⟨254921771295862190204403041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169947847530574793469602027 254921771295862190204403041)
  ·
    refine ⟨191191328471896642653302281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254921771295862190204403041 191191328471896642653302281)
    ·
      refine ⟨143393496353922481989976711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191191328471896642653302281 143393496353922481989976711)
      ·
        refine ⟨215090244530883722984965067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143393496353922481989976711 215090244530883722984965067)
        ·
          refine ⟨322635366796325584477447601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215090244530883722984965067 322635366796325584477447601)
          ·
            refine ⟨241976525097244188358085701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322635366796325584477447601 241976525097244188358085701)
            ·
              refine ⟨45370598455733285317141069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241976525097244188358085701 45370598455733285317141069)
              ·
                refine ⟨17013974420899981993927901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45370598455733285317141069 17013974420899981993927901)
                ·
                  refine ⟨6380240407837493247722963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17013974420899981993927901 6380240407837493247722963)
                  ·
                    refine ⟨9570360611756239871584445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6380240407837493247722963 9570360611756239871584445)
                    ·
                      refine ⟨3588885229408589951844167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9570360611756239871584445 3588885229408589951844167)
                      ·
                        rfl

theorem cell23_6989329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_6989329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989329 prefixEnd_6989329 := by exact prefixLift 6989329
  have htrace : WordTrace (prefixWord ++ tailWord_6989329) baseStart_6989329 baseEnd_6989329 := by
    simpa [prefixWord, tailWord_6989329, baseEnd_6989329] using wordTrace_append hprefix tailTrace_6989329
  have hstable : (prefixWord ++ tailWord_6989329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989329).length < 2 ^ (prefixWord ++ tailWord_6989329).sum := by decide
  have hdescent : baseEnd_6989329 < baseStart_6989329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989363 : List Nat := [1, 1, 1, 2, 4, 4, 2, 3, 1, 1, 3]
def baseStart_6989363 : Nat := 118140960795 + 6989363 * 2 ^ 59
def prefixEnd_6989363 : Nat := 4983230072969 + 3 ^ 40 * 6989363 * 2
def baseEnd_6989363 : Nat := 3588902687750842818819011

theorem tailTrace_6989363 : CollatzResearch.WordTrace tailWord_6989363 prefixEnd_6989363 3588902687750842818819011 := by
  unfold tailWord_6989363
  simp only [CollatzResearch.WordTrace]
  refine ⟨254923011377739014011140743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169948674251826009340760495 254923011377739014011140743)
  ·
    refine ⟨382384517066608521016711115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254923011377739014011140743 382384517066608521016711115)
    ·
      refine ⟨573576775599912781525066673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382384517066608521016711115 573576775599912781525066673)
      ·
        refine ⟨430182581699934586143800005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573576775599912781525066673 430182581699934586143800005)
        ·
          refine ⟨80659234068737734901962501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430182581699934586143800005 80659234068737734901962501)
          ·
            refine ⟨15123606387888325294117969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80659234068737734901962501 15123606387888325294117969)
            ·
              refine ⟨11342704790916243970588477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15123606387888325294117969 11342704790916243970588477)
              ·
                refine ⟨4253514296593591488970679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11342704790916243970588477 4253514296593591488970679)
                ·
                  refine ⟨6380271444890387233456019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253514296593591488970679 6380271444890387233456019)
                  ·
                    refine ⟨9570407167335580850184029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6380271444890387233456019 9570407167335580850184029)
                    ·
                      refine ⟨3588902687750842818819011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9570407167335580850184029 3588902687750842818819011)
                      ·
                        rfl

theorem cell23_6989363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 1, 3].length) (baseStart_6989363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989363 prefixEnd_6989363 := by exact prefixLift 6989363
  have htrace : WordTrace (prefixWord ++ tailWord_6989363) baseStart_6989363 baseEnd_6989363 := by
    simpa [prefixWord, tailWord_6989363, baseEnd_6989363] using wordTrace_append hprefix tailTrace_6989363
  have hstable : (prefixWord ++ tailWord_6989363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989363).length < 2 ^ (prefixWord ++ tailWord_6989363).sum := by decide
  have hdescent : baseEnd_6989363 < baseStart_6989363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989399 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_6989399 : Nat := 118140960795 + 6989399 * 2 ^ 59
def prefixEnd_6989399 : Nat := 4983230072969 + 3 ^ 40 * 6989399 * 2
def baseEnd_6989399 : Nat := 3588921173054404677968845

theorem tailTrace_6989399 : CollatzResearch.WordTrace tailWord_6989399 prefixEnd_6989399 3588921173054404677968845 := by
  unfold tailWord_6989399
  simp only [CollatzResearch.WordTrace]
  refine ⟨254924324405608592159451251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169949549603739061439634167 254924324405608592159451251)
  ·
    refine ⟨382386486608412888239176877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254924324405608592159451251 382386486608412888239176877)
    ·
      refine ⟨143394932478154833089691329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382386486608412888239176877 143394932478154833089691329)
      ·
        refine ⟨107546199358616124817268497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143394932478154833089691329 107546199358616124817268497)
        ·
          refine ⟨80659649518962093612951373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107546199358616124817268497 80659649518962093612951373)
          ·
            refine ⟨30247368569610785104856765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80659649518962093612951373 30247368569610785104856765)
            ·
              refine ⟨11342763213604044414321287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30247368569610785104856765 11342763213604044414321287)
              ·
                refine ⟨17014144820406066621481931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11342763213604044414321287 17014144820406066621481931)
                ·
                  refine ⟨25521217230609099932222897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17014144820406066621481931 25521217230609099932222897)
                  ·
                    refine ⟨19140912922956824949167173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25521217230609099932222897 19140912922956824949167173)
                    ·
                      refine ⟨3588921173054404677968845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19140912922956824949167173 3588921173054404677968845)
                      ·
                        rfl

theorem cell23_6989399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_6989399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989399 prefixEnd_6989399 := by exact prefixLift 6989399
  have htrace : WordTrace (prefixWord ++ tailWord_6989399) baseStart_6989399 baseEnd_6989399 := by
    simpa [prefixWord, tailWord_6989399, baseEnd_6989399] using wordTrace_append hprefix tailTrace_6989399
  have hstable : (prefixWord ++ tailWord_6989399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989399).length < 2 ^ (prefixWord ++ tailWord_6989399).sum := by decide
  have hdescent : baseEnd_6989399 < baseStart_6989399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989436 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_6989436 : Nat := 118140960795 + 6989436 * 2 ^ 59
def prefixEnd_6989436 : Nat := 4983230072969 + 3 ^ 40 * 6989436 * 2
def baseEnd_6989436 : Nat := 3588940171838621033206175

theorem tailTrace_6989436 : CollatzResearch.WordTrace tailWord_6989436 prefixEnd_6989436 3588940171838621033206175 := by
  unfold tailWord_6989436
  simp only [CollatzResearch.WordTrace]
  refine ⟨127462836953237273739274081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169950449270983031652365441 127462836953237273739274081)
  ·
    refine ⟨95597127714927955304455561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127462836953237273739274081 95597127714927955304455561)
    ·
      refine ⟨71697845786195966478341671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95597127714927955304455561 71697845786195966478341671)
      ·
        refine ⟨107546768679293949717512507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71697845786195966478341671 107546768679293949717512507)
        ·
          refine ⟨161320153018940924576268761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107546768679293949717512507 161320153018940924576268761)
          ·
            refine ⟨120990114764205693432201571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161320153018940924576268761 120990114764205693432201571)
            ·
              refine ⟨181485172146308540148302357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120990114764205693432201571 181485172146308540148302357)
              ·
                refine ⟨8507117444358212819451673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181485172146308540148302357 8507117444358212819451673)
                ·
                  refine ⟨6380338083268659614588755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8507117444358212819451673 6380338083268659614588755)
                  ·
                    refine ⟨9570507124902989421883133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6380338083268659614588755 9570507124902989421883133)
                    ·
                      refine ⟨3588940171838621033206175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9570507124902989421883133 3588940171838621033206175)
                      ·
                        rfl

theorem cell23_6989436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_6989436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989436 prefixEnd_6989436 := by exact prefixLift 6989436
  have htrace : WordTrace (prefixWord ++ tailWord_6989436) baseStart_6989436 baseEnd_6989436 := by
    simpa [prefixWord, tailWord_6989436, baseEnd_6989436] using wordTrace_append hprefix tailTrace_6989436
  have hstable : (prefixWord ++ tailWord_6989436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989436).length < 2 ^ (prefixWord ++ tailWord_6989436).sum := by decide
  have hdescent : baseEnd_6989436 < baseStart_6989436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989437 : List Nat := [1, 4, 1, 1, 4, 2, 3, 2, 1, 2, 2]
def baseStart_6989437 : Nat := 118140960795 + 6989437 * 2 ^ 59
def prefixEnd_6989437 : Nat := 4983230072969 + 3 ^ 40 * 6989437 * 2
def baseEnd_6989437 : Nat := 3588940685319275529293671

theorem tailTrace_6989437 : CollatzResearch.WordTrace tailWord_6989437 prefixEnd_6989437 3588940685319275529293671 := by
  unfold tailWord_6989437
  simp only [CollatzResearch.WordTrace]
  refine ⟨254925710379470924649334565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169950473586313949766223043 254925710379470924649334565)
  ·
    refine ⟨47798570696150798371750231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254925710379470924649334565 47798570696150798371750231)
    ·
      refine ⟨71697856044226197557625347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47798570696150798371750231 71697856044226197557625347)
      ·
        refine ⟨107546784066339296336438021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71697856044226197557625347 107546784066339296336438021)
        ·
          refine ⟨20165022012438618063082129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107546784066339296336438021 20165022012438618063082129)
          ·
            refine ⟨15123766509328963547311597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20165022012438618063082129 15123766509328963547311597)
            ·
              refine ⟨5671412440998361330241849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15123766509328963547311597 5671412440998361330241849)
              ·
                refine ⟨4253559330748770997681387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5671412440998361330241849 4253559330748770997681387)
                ·
                  refine ⟨6380338996123156496522081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253559330748770997681387 6380338996123156496522081)
                  ·
                    refine ⟨4785254247092367372391561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6380338996123156496522081 4785254247092367372391561)
                    ·
                      refine ⟨3588940685319275529293671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785254247092367372391561 3588940685319275529293671)
                      ·
                        rfl

theorem cell23_6989437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_6989437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989437 prefixEnd_6989437 := by exact prefixLift 6989437
  have htrace : WordTrace (prefixWord ++ tailWord_6989437) baseStart_6989437 baseEnd_6989437 := by
    simpa [prefixWord, tailWord_6989437, baseEnd_6989437] using wordTrace_append hprefix tailTrace_6989437
  have hstable : (prefixWord ++ tailWord_6989437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989437).length < 2 ^ (prefixWord ++ tailWord_6989437).sum := by decide
  have hdescent : baseEnd_6989437 < baseStart_6989437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989452 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_6989452 : Nat := 118140960795 + 6989452 * 2 ^ 59
def prefixEnd_6989452 : Nat := 4983230072969 + 3 ^ 40 * 6989452 * 2
def baseEnd_6989452 : Nat := 1196316129176364323535367

theorem tailTrace_6989452 : CollatzResearch.WordTrace tailWord_6989452 prefixEnd_6989452 1196316129176364323535367 := by
  unfold tailWord_6989452
  simp only [CollatzResearch.WordTrace]
  refine ⟨127463128737208291105565305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169950838316277721474087073 127463128737208291105565305)
  ·
    refine ⟨95597346552906218329173979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127463128737208291105565305 95597346552906218329173979)
    ·
      refine ⟨143396019829359327493760969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95597346552906218329173979 143396019829359327493760969)
      ·
        refine ⟨107547014872019495620320727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143396019829359327493760969 107547014872019495620320727)
        ·
          refine ⟨161320522308029243430481091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107547014872019495620320727 161320522308029243430481091)
          ·
            refine ⟨241980783462043865145721637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161320522308029243430481091 241980783462043865145721637)
            ·
              refine ⟨45371396899133224714822807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241980783462043865145721637 45371396899133224714822807)
              ·
                refine ⟨68057095348699837072234211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45371396899133224714822807 68057095348699837072234211)
                ·
                  refine ⟨102085643023049755608351317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68057095348699837072234211 102085643023049755608351317)
                  ·
                    refine ⟨1196316129176364323535367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102085643023049755608351317 1196316129176364323535367)
                    ·
                      rfl

theorem cell23_6989452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_6989452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989452 prefixEnd_6989452 := by exact prefixLift 6989452
  have htrace : WordTrace (prefixWord ++ tailWord_6989452) baseStart_6989452 baseEnd_6989452 := by
    simpa [prefixWord, tailWord_6989452, baseEnd_6989452] using wordTrace_append hprefix tailTrace_6989452
  have hstable : (prefixWord ++ tailWord_6989452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989452).length < 2 ^ (prefixWord ++ tailWord_6989452).sum := by decide
  have hdescent : baseEnd_6989452 < baseStart_6989452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989463 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 1, 3, 2]
def baseStart_6989463 : Nat := 118140960795 + 6989463 * 2 ^ 59
def prefixEnd_6989463 : Nat := 4983230072969 + 3 ^ 40 * 6989463 * 2
def baseEnd_6989463 : Nat := 3588954035816292427568551

theorem tailTrace_6989463 : CollatzResearch.WordTrace tailWord_6989463 prefixEnd_6989463 3588954035816292427568551 := by
  unfold tailWord_6989463
  simp only [CollatzResearch.WordTrace]
  refine ⟨254926658677376731089781043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169951105784917820726520695 254926658677376731089781043)
  ·
    refine ⟨382389988016065096634671565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254926658677376731089781043 382389988016065096634671565)
    ·
      refine ⟨143396245506024411238001837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382389988016065096634671565 143396245506024411238001837)
      ·
        refine ⟨53773592064759154214250689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143396245506024411238001837 53773592064759154214250689)
        ·
          refine ⟨40330194048569365660688017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53773592064759154214250689 40330194048569365660688017)
          ·
            refine ⟨30247645536427024245516013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40330194048569365660688017 30247645536427024245516013)
            ·
              refine ⟨11342867076160134092068505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30247645536427024245516013 11342867076160134092068505)
              ·
                refine ⟨8507150307120100569051379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11342867076160134092068505 8507150307120100569051379)
                ·
                  refine ⟨12760725460680150853577069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8507150307120100569051379 12760725460680150853577069)
                  ·
                    refine ⟨4785272047755056570091401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12760725460680150853577069 4785272047755056570091401)
                    ·
                      refine ⟨3588954035816292427568551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785272047755056570091401 3588954035816292427568551)
                      ·
                        rfl

theorem cell23_6989463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_6989463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989463 prefixEnd_6989463 := by exact prefixLift 6989463
  have htrace : WordTrace (prefixWord ++ tailWord_6989463) baseStart_6989463 baseEnd_6989463 := by
    simpa [prefixWord, tailWord_6989463, baseEnd_6989463] using wordTrace_append hprefix tailTrace_6989463
  have hstable : (prefixWord ++ tailWord_6989463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989463).length < 2 ^ (prefixWord ++ tailWord_6989463).sum := by decide
  have hdescent : baseEnd_6989463 < baseStart_6989463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989476 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_6989476 : Nat := 118140960795 + 6989476 * 2 ^ 59
def prefixEnd_6989476 : Nat := 4983230072969 + 3 ^ 40 * 6989476 * 2
def baseEnd_6989476 : Nat := 3588960711064800876705991

theorem tailTrace_6989476 : CollatzResearch.WordTrace tailWord_6989476 prefixEnd_6989476 3588960711064800876705991 := by
  unfold tailWord_6989476
  simp only [CollatzResearch.WordTrace]
  refine ⟨127463566413164817155002141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169951421884219756206669521 127463566413164817155002141)
  ·
    refine ⟨47798837404936806433125803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127463566413164817155002141 47798837404936806433125803)
    ·
      refine ⟨71698256107405209649688705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47798837404936806433125803 71698256107405209649688705)
      ·
        refine ⟨53773692080553907237266529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71698256107405209649688705 53773692080553907237266529)
        ·
          refine ⟨40330269060415430427949897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53773692080553907237266529 40330269060415430427949897)
          ·
            refine ⟨30247701795311572820962423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40330269060415430427949897 30247701795311572820962423)
            ·
              refine ⟨45371552692967359231443635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30247701795311572820962423 45371552692967359231443635)
              ·
                refine ⟨68057329039451038847165453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45371552692967359231443635 68057329039451038847165453)
                ·
                  refine ⟨25521498389794139567687045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68057329039451038847165453 25521498389794139567687045)
                  ·
                    refine ⟨4785280948086401168941321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25521498389794139567687045 4785280948086401168941321)
                    ·
                      refine ⟨3588960711064800876705991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785280948086401168941321 3588960711064800876705991)
                      ·
                        rfl

theorem cell23_6989476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_6989476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989476 prefixEnd_6989476 := by exact prefixLift 6989476
  have htrace : WordTrace (prefixWord ++ tailWord_6989476) baseStart_6989476 baseEnd_6989476 := by
    simpa [prefixWord, tailWord_6989476, baseEnd_6989476] using wordTrace_append hprefix tailTrace_6989476
  have hstable : (prefixWord ++ tailWord_6989476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989476).length < 2 ^ (prefixWord ++ tailWord_6989476).sum := by decide
  have hdescent : baseEnd_6989476 < baseStart_6989476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989509 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_6989509 : Nat := 118140960795 + 6989509 * 2 ^ 59
def prefixEnd_6989509 : Nat := 4983230072969 + 3 ^ 40 * 6989509 * 2
def baseEnd_6989509 : Nat := 3588977655926399247593339

theorem tailTrace_6989509 : CollatzResearch.WordTrace tailWord_6989509 prefixEnd_6989509 3588977655926399247593339 := by
  unfold tailWord_6989509
  simp only [CollatzResearch.WordTrace]
  refine ⟨254928336435210080945955581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169952224290140053963970387 254928336435210080945955581)
  ·
    refine ⟨95598126163203780354733343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254928336435210080945955581 95598126163203780354733343)
    ·
      refine ⟨143397189244805670532100015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95598126163203780354733343 143397189244805670532100015)
      ·
        refine ⟨215095783867208505798150023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143397189244805670532100015 215095783867208505798150023)
        ·
          refine ⟨322643675800812758697225035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215095783867208505798150023 322643675800812758697225035)
          ·
            refine ⟨483965513701219138045837553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322643675800812758697225035 483965513701219138045837553)
            ·
              refine ⟨362974135275914353534378165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483965513701219138045837553 362974135275914353534378165)
              ·
                refine ⟨34028825182116970643847953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 362974135275914353534378165 34028825182116970643847953)
                ·
                  refine ⟨25521618886587727982885965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34028825182116970643847953 25521618886587727982885965)
                  ·
                    refine ⟨9570607082470397993582237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25521618886587727982885965 9570607082470397993582237)
                    ·
                      refine ⟨3588977655926399247593339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9570607082470397993582237 3588977655926399247593339)
                      ·
                        rfl

theorem cell23_6989509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_6989509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989509 prefixEnd_6989509 := by exact prefixLift 6989509
  have htrace : WordTrace (prefixWord ++ tailWord_6989509) baseStart_6989509 baseEnd_6989509 := by
    simpa [prefixWord, tailWord_6989509, baseEnd_6989509] using wordTrace_append hprefix tailTrace_6989509
  have hstable : (prefixWord ++ tailWord_6989509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989509).length < 2 ^ (prefixWord ++ tailWord_6989509).sum := by decide
  have hdescent : baseEnd_6989509 < baseStart_6989509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989516 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 7]
def baseStart_6989516 : Nat := 118140960795 + 6989516 * 2 ^ 59
def prefixEnd_6989516 : Nat := 4983230072969 + 3 ^ 40 * 6989516 * 2
def baseEnd_6989516 : Nat := 398775694476775635578423

theorem tailTrace_6989516 : CollatzResearch.WordTrace tailWord_6989516 prefixEnd_6989516 398775694476775635578423 := by
  unfold tailWord_6989516
  simp only [CollatzResearch.WordTrace]
  refine ⟨127464295873092360570730201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169952394497456480760973601 127464295873092360570730201)
  ·
    refine ⟨95598221904819270428047651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127464295873092360570730201 95598221904819270428047651)
    ·
      refine ⟨143397332857228905642071477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95598221904819270428047651 143397332857228905642071477)
      ·
        refine ⟨13443499955365209903944201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143397332857228905642071477 13443499955365209903944201)
        ·
          refine ⟨10082624966523907427958151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13443499955365209903944201 10082624966523907427958151)
          ·
            refine ⟨15123937449785861141937227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10082624966523907427958151 15123937449785861141937227)
            ·
              refine ⟨22685906174678791712905841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15123937449785861141937227 22685906174678791712905841)
              ·
                refine ⟨17014429631009093784679381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22685906174678791712905841 17014429631009093784679381)
                ·
                  refine ⟨398775694476775635578423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17014429631009093784679381 398775694476775635578423)
                  ·
                    rfl

theorem cell23_6989516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_6989516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989516 prefixEnd_6989516 := by exact prefixLift 6989516
  have htrace : WordTrace (prefixWord ++ tailWord_6989516) baseStart_6989516 baseEnd_6989516 := by
    simpa [prefixWord, tailWord_6989516, baseEnd_6989516] using wordTrace_append hprefix tailTrace_6989516
  have hstable : (prefixWord ++ tailWord_6989516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989516).length < 2 ^ (prefixWord ++ tailWord_6989516).sum := by decide
  have hdescent : baseEnd_6989516 < baseStart_6989516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989529 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 1, 7]
def baseStart_6989529 : Nat := 118140960795 + 6989529 * 2 ^ 59
def prefixEnd_6989529 : Nat := 4983230072969 + 3 ^ 40 * 6989529 * 2
def baseEnd_6989529 : Nat := 1196329308513163056447749

theorem tailTrace_6989529 : CollatzResearch.WordTrace tailWord_6989529 prefixEnd_6989529 1196329308513163056447749 := by
  unfold tailWord_6989529
  simp only [CollatzResearch.WordTrace]
  refine ⟨254929065895137624361683641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169952710596758416241122427 254929065895137624361683641)
  ·
    refine ⟨191196799421353218271262731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254929065895137624361683641 191196799421353218271262731)
    ·
      refine ⟨286795199132029827406894097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191196799421353218271262731 286795199132029827406894097)
      ·
        refine ⟨215096399349022370555170573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286795199132029827406894097 215096399349022370555170573)
        ·
          refine ⟨80661149755883388958188965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215096399349022370555170573 80661149755883388958188965)
          ·
            refine ⟨15123965579228135429660431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80661149755883388958188965 15123965579228135429660431)
            ·
              refine ⟨22685948368842203144490647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15123965579228135429660431 22685948368842203144490647)
              ·
                refine ⟨34028922553263304716735971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22685948368842203144490647 34028922553263304716735971)
                ·
                  refine ⟨51043383829894957075103957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34028922553263304716735971 51043383829894957075103957)
                  ·
                    refine ⟨1196329308513163056447749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51043383829894957075103957 1196329308513163056447749)
                    ·
                      rfl

theorem cell23_6989529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_6989529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989529 prefixEnd_6989529 := by exact prefixLift 6989529
  have htrace : WordTrace (prefixWord ++ tailWord_6989529) baseStart_6989529 baseEnd_6989529 := by
    simpa [prefixWord, tailWord_6989529, baseEnd_6989529] using wordTrace_append hprefix tailTrace_6989529
  have hstable : (prefixWord ++ tailWord_6989529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989529).length < 2 ^ (prefixWord ++ tailWord_6989529).sum := by decide
  have hdescent : baseEnd_6989529 < baseStart_6989529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989576 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 3, 4]
def baseStart_6989576 : Nat := 118140960795 + 6989576 * 2 ^ 59
def prefixEnd_6989576 : Nat := 4983230072969 + 3 ^ 40 * 6989576 * 2
def baseEnd_6989576 : Nat := 1196337353043416828485177

theorem tailTrace_6989576 : CollatzResearch.WordTrace tailWord_6989576 prefixEnd_6989576 1196337353043416828485177 := by
  unfold tailWord_6989576
  simp only [CollatzResearch.WordTrace]
  refine ⟨127465390062983675694322291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169953853417311567592429721 127465390062983675694322291)
  ·
    refine ⟨191198085094475513541483437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127465390062983675694322291 191198085094475513541483437)
    ·
      refine ⟨71699281910428317578056289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191198085094475513541483437 71699281910428317578056289)
      ·
        refine ⟨53774461432821238183542217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71699281910428317578056289 53774461432821238183542217)
        ·
          refine ⟨40330846074615928637656663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53774461432821238183542217 40330846074615928637656663)
          ·
            refine ⟨60496269111923892956484995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40330846074615928637656663 60496269111923892956484995)
            ·
              refine ⟨90744403667885839434727493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60496269111923892956484995 90744403667885839434727493)
              ·
                refine ⟨17014575687728594894011405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90744403667885839434727493 17014575687728594894011405)
                ·
                  refine ⟨6380465882898223085254277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17014575687728594894011405 6380465882898223085254277)
                  ·
                    refine ⟨1196337353043416828485177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6380465882898223085254277 1196337353043416828485177)
                    ·
                      rfl

theorem cell23_6989576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_6989576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989576 prefixEnd_6989576 := by exact prefixLift 6989576
  have htrace : WordTrace (prefixWord ++ tailWord_6989576) baseStart_6989576 baseEnd_6989576 := by
    simpa [prefixWord, tailWord_6989576, baseEnd_6989576] using wordTrace_append hprefix tailTrace_6989576
  have hstable : (prefixWord ++ tailWord_6989576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989576).length < 2 ^ (prefixWord ++ tailWord_6989576).sum := by decide
  have hdescent : baseEnd_6989576 < baseStart_6989576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989589 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 8]
def baseStart_6989589 : Nat := 118140960795 + 6989589 * 2 ^ 59
def prefixEnd_6989589 : Nat := 4983230072969 + 3 ^ 40 * 6989589 * 2
def baseEnd_6989589 : Nat := 398779859375417659399219

theorem tailTrace_6989589 : CollatzResearch.WordTrace tailWord_6989589 prefixEnd_6989589 398779859375417659399219 := by
  unfold tailWord_6989589
  simp only [CollatzResearch.WordTrace]
  refine ⟨254931254274920254608867821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169954169516613503072578547 254931254274920254608867821)
  ·
    refine ⟨95599220353095095478325433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254931254274920254608867821 95599220353095095478325433)
    ·
      refine ⟨71699415264821321608744075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95599220353095095478325433 71699415264821321608744075)
      ·
        refine ⟨107549122897231982413116113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71699415264821321608744075 107549122897231982413116113)
        ·
          refine ⟨80661842172923986809837085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107549122897231982413116113 80661842172923986809837085)
          ·
            refine ⟨30248190814846495053688907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80661842172923986809837085 30248190814846495053688907)
            ·
              refine ⟨45372286222269742580533361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30248190814846495053688907 45372286222269742580533361)
              ·
                refine ⟨34029214666702306935400021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45372286222269742580533361 34029214666702306935400021)
                ·
                  refine ⟨398779859375417659399219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34029214666702306935400021 398779859375417659399219)
                  ·
                    rfl

theorem cell23_6989589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_6989589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989589 prefixEnd_6989589 := by exact prefixLift 6989589
  have htrace : WordTrace (prefixWord ++ tailWord_6989589) baseStart_6989589 baseEnd_6989589 := by
    simpa [prefixWord, tailWord_6989589, baseEnd_6989589] using wordTrace_append hprefix tailTrace_6989589
  have hstable : (prefixWord ++ tailWord_6989589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989589).length < 2 ^ (prefixWord ++ tailWord_6989589).sum := by decide
  have hdescent : baseEnd_6989589 < baseStart_6989589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989667 : List Nat := [1, 1, 1, 5, 4, 1, 1, 4, 1, 1, 3]
def baseStart_6989667 : Nat := 118140960795 + 6989667 * 2 ^ 59
def prefixEnd_6989667 : Nat := 4983230072969 + 3 ^ 40 * 6989667 * 2
def baseEnd_6989667 : Nat := 3589058785869809629417613

theorem tailTrace_6989667 : CollatzResearch.WordTrace tailWord_6989667 prefixEnd_6989667 3589058785869809629417613 := by
  unfold tailWord_6989667
  simp only [CollatzResearch.WordTrace]
  refine ⟨254934099168637673930207255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169956066112425115953471503 254934099168637673930207255)
  ·
    refine ⟨382401148752956510895310883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254934099168637673930207255 382401148752956510895310883)
    ·
      refine ⟨573601723129434766342966325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382401148752956510895310883 573601723129434766342966325)
      ·
        refine ⟨53775161543384509344653093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 573601723129434766342966325 53775161543384509344653093)
        ·
          refine ⟨10082842789384595502122455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53775161543384509344653093 10082842789384595502122455)
          ·
            refine ⟨15124264184076893253183683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10082842789384595502122455 15124264184076893253183683)
            ·
              refine ⟨22686396276115339879775525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15124264184076893253183683 22686396276115339879775525)
              ·
                refine ⟨4253699301771626227457911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22686396276115339879775525 4253699301771626227457911)
                ·
                  refine ⟨6380548952657439341186867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253699301771626227457911 6380548952657439341186867)
                  ·
                    refine ⟨9570823428986159011780301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6380548952657439341186867 9570823428986159011780301)
                    ·
                      refine ⟨3589058785869809629417613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9570823428986159011780301 3589058785869809629417613)
                      ·
                        rfl

theorem cell23_6989667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_6989667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989667 prefixEnd_6989667 := by exact prefixLift 6989667
  have htrace : WordTrace (prefixWord ++ tailWord_6989667) baseStart_6989667 baseEnd_6989667 := by
    simpa [prefixWord, tailWord_6989667, baseEnd_6989667] using wordTrace_append hprefix tailTrace_6989667
  have hstable : (prefixWord ++ tailWord_6989667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989667).length < 2 ^ (prefixWord ++ tailWord_6989667).sum := by decide
  have hdescent : baseEnd_6989667 < baseStart_6989667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989673 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 7, 2, 2]
def baseStart_6989673 : Nat := 118140960795 + 6989673 * 2 ^ 59
def prefixEnd_6989673 : Nat := 4983230072969 + 3 ^ 40 * 6989673 * 2
def baseEnd_6989673 : Nat := 3589061866753736605942585

theorem tailTrace_6989673 : CollatzResearch.WordTrace tailWord_6989673 prefixEnd_6989673 3589061866753736605942585 := by
  unfold tailWord_6989673
  simp only [CollatzResearch.WordTrace]
  refine ⟨254934318006615936954925673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169956212004410624636617115 254934318006615936954925673)
  ·
    refine ⟨191200738504961952716194255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254934318006615936954925673 191200738504961952716194255)
    ·
      refine ⟨286801107757442929074291383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191200738504961952716194255 286801107757442929074291383)
      ·
        refine ⟨430201661636164393611437075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286801107757442929074291383 430201661636164393611437075)
        ·
          refine ⟨645302492454246590417155613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430201661636164393611437075 645302492454246590417155613)
          ·
            refine ⟨241988434670342471406433355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645302492454246590417155613 241988434670342471406433355)
            ·
              refine ⟨362982652005513707109650033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241988434670342471406433355 362982652005513707109650033)
              ·
                refine ⟨272236989004135280332237525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362982652005513707109650033 272236989004135280332237525)
                ·
                  refine ⟨6380554429784420632786817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 272236989004135280332237525 6380554429784420632786817)
                  ·
                    refine ⟨4785415822338315474590113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6380554429784420632786817 4785415822338315474590113)
                    ·
                      refine ⟨3589061866753736605942585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785415822338315474590113 3589061866753736605942585)
                      ·
                        rfl

theorem cell23_6989673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 2, 2].length) (baseStart_6989673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989673 prefixEnd_6989673 := by exact prefixLift 6989673
  have htrace : WordTrace (prefixWord ++ tailWord_6989673) baseStart_6989673 baseEnd_6989673 := by
    simpa [prefixWord, tailWord_6989673, baseEnd_6989673] using wordTrace_append hprefix tailTrace_6989673
  have hstable : (prefixWord ++ tailWord_6989673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989673).length < 2 ^ (prefixWord ++ tailWord_6989673).sum := by decide
  have hdescent : baseEnd_6989673 < baseStart_6989673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989693 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_6989693 : Nat := 118140960795 + 6989693 * 2 ^ 59
def prefixEnd_6989693 : Nat := 4983230072969 + 3 ^ 40 * 6989693 * 2
def baseEnd_6989693 : Nat := 3589072136366826527692493

theorem tailTrace_6989693 : CollatzResearch.WordTrace tailWord_6989693 prefixEnd_6989693 3589072136366826527692493 := by
  unfold tailWord_6989693
  simp only [CollatzResearch.WordTrace]
  refine ⟨254935047466543480370653733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169956698311028986913769155 254935047466543480370653733)
  ·
    refine ⟨47800321399976902569497575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254935047466543480370653733 47800321399976902569497575)
    ·
      refine ⟨71700482099965353854246363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47800321399976902569497575 71700482099965353854246363)
      ·
        refine ⟨107550723149948030781369545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71700482099965353854246363 107550723149948030781369545)
        ·
          refine ⟨80663042362461023086027159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107550723149948030781369545 80663042362461023086027159)
          ·
            refine ⟨120994563543691534629040739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80663042362461023086027159 120994563543691534629040739)
            ·
              refine ⟨181491845315537301943561109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120994563543691534629040739 181491845315537301943561109)
              ·
                refine ⟨8507430249165811028604427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181491845315537301943561109 8507430249165811028604427)
                ·
                  refine ⟨12761145373748716542906641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8507430249165811028604427 12761145373748716542906641)
                  ·
                    refine ⟨9570859030311537407179981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12761145373748716542906641 9570859030311537407179981)
                    ·
                      refine ⟨3589072136366826527692493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9570859030311537407179981 3589072136366826527692493)
                      ·
                        rfl

theorem cell23_6989693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_6989693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989693 prefixEnd_6989693 := by exact prefixLift 6989693
  have htrace : WordTrace (prefixWord ++ tailWord_6989693) baseStart_6989693 baseEnd_6989693 := by
    simpa [prefixWord, tailWord_6989693, baseEnd_6989693] using wordTrace_append hprefix tailTrace_6989693
  have hstable : (prefixWord ++ tailWord_6989693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989693).length < 2 ^ (prefixWord ++ tailWord_6989693).sum := by decide
  have hdescent : baseEnd_6989693 < baseStart_6989693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989694 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6989694 : Nat := 118140960795 + 6989694 * 2 ^ 59
def prefixEnd_6989694 : Nat := 4983230072969 + 3 ^ 40 * 6989694 * 2
def baseEnd_6989694 : Nat := 3589072649847481023779989

theorem tailTrace_6989694 : CollatzResearch.WordTrace tailWord_6989694 prefixEnd_6989694 3589072649847481023779989 := by
  unfold tailWord_6989694
  simp only [CollatzResearch.WordTrace]
  refine ⟨31866885492442482192680017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169956722626359905027626757 31866885492442482192680017)
  ·
    refine ⟨23900164119331861644510013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31866885492442482192680017 23900164119331861644510013)
    ·
      refine ⟨8962561544749448116691255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23900164119331861644510013 8962561544749448116691255)
      ·
        refine ⟨13443842317124172175036883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8962561544749448116691255 13443842317124172175036883)
        ·
          refine ⟨20165763475686258262555325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13443842317124172175036883 20165763475686258262555325)
          ·
            refine ⟨7562161303382346848458247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20165763475686258262555325 7562161303382346848458247)
            ·
              refine ⟨11343241955073520272687371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7562161303382346848458247 11343241955073520272687371)
              ·
                refine ⟨17014862932610280409031057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11343241955073520272687371 17014862932610280409031057)
                ·
                  refine ⟨12761147199457710306773293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17014862932610280409031057 12761147199457710306773293)
                  ·
                    refine ⟨4785430199796641365039985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12761147199457710306773293 4785430199796641365039985)
                    ·
                      refine ⟨3589072649847481023779989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785430199796641365039985 3589072649847481023779989)
                      ·
                        rfl

theorem cell23_6989694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6989694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989694 prefixEnd_6989694 := by exact prefixLift 6989694
  have htrace : WordTrace (prefixWord ++ tailWord_6989694) baseStart_6989694 baseEnd_6989694 := by
    simpa [prefixWord, tailWord_6989694, baseEnd_6989694] using wordTrace_append hprefix tailTrace_6989694
  have hstable : (prefixWord ++ tailWord_6989694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989694).length < 2 ^ (prefixWord ++ tailWord_6989694).sum := by decide
  have hdescent : baseEnd_6989694 < baseStart_6989694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989696 : List Nat := [2, 1, 1, 2, 1, 2, 7, 7]
def baseStart_6989696 : Nat := 118140960795 + 6989696 * 2 ^ 59
def prefixEnd_6989696 : Nat := 4983230072969 + 3 ^ 40 * 6989696 * 2
def baseEnd_6989696 : Nat := 132928654696621852442777

theorem tailTrace_6989696 : CollatzResearch.WordTrace tailWord_6989696 prefixEnd_6989696 132928654696621852442777 := by
  unfold tailWord_6989696
  simp only [CollatzResearch.WordTrace]
  refine ⟨127467578442766305941506471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169956771257021741255341961 127467578442766305941506471)
  ·
    refine ⟨191201367664149458912259707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127467578442766305941506471 191201367664149458912259707)
    ·
      refine ⟨286802051496224188368389561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191201367664149458912259707 286802051496224188368389561)
      ·
        refine ⟨215101538622168141276292171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286802051496224188368389561 215101538622168141276292171)
        ·
          refine ⟨322652307933252211914438257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215101538622168141276292171 322652307933252211914438257)
          ·
            refine ⟨241989230949939158935828693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322652307933252211914438257 241989230949939158935828693)
            ·
              refine ⟨5671622600389199037558485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 241989230949939158935828693 5671622600389199037558485)
              ·
                refine ⟨132928654696621852442777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5671622600389199037558485 132928654696621852442777)
                ·
                  rfl

theorem cell23_6989696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 7].length) (baseStart_6989696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989696 prefixEnd_6989696 := by exact prefixLift 6989696
  have htrace : WordTrace (prefixWord ++ tailWord_6989696) baseStart_6989696 baseEnd_6989696 := by
    simpa [prefixWord, tailWord_6989696, baseEnd_6989696] using wordTrace_append hprefix tailTrace_6989696
  have hstable : (prefixWord ++ tailWord_6989696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989696).length < 2 ^ (prefixWord ++ tailWord_6989696).sum := by decide
  have hdescent : baseEnd_6989696 < baseStart_6989696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989724 : List Nat := [2, 2, 3, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6989724 : Nat := 118140960795 + 6989724 * 2 ^ 59
def prefixEnd_6989724 : Nat := 4983230072969 + 3 ^ 40 * 6989724 * 2
def baseEnd_6989724 : Nat := 3589088054267115906404851

theorem tailTrace_6989724 : CollatzResearch.WordTrace tailWord_6989724 prefixEnd_6989724 3589088054267115906404851 := by
  unfold tailWord_6989724
  simp only [CollatzResearch.WordTrace]
  refine ⟨127468089064715586332516113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169957452086287448443354817 127468089064715586332516113)
  ·
    refine ⟨95601066798536689749387085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127468089064715586332516113 95601066798536689749387085)
    ·
      refine ⟨35850400049451258656020157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95601066798536689749387085 35850400049451258656020157)
      ·
        refine ⟨13443900018544221996007559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35850400049451258656020157 13443900018544221996007559)
        ·
          refine ⟨20165850027816332994011339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13443900018544221996007559 20165850027816332994011339)
          ·
            refine ⟨30248775041724499491017009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20165850027816332994011339 30248775041724499491017009)
            ·
              refine ⟨22686581281293374618262757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30248775041724499491017009 22686581281293374618262757)
              ·
                refine ⟨4253733990242507740924267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22686581281293374618262757 4253733990242507740924267)
                ·
                  refine ⟨6380600985363761611386401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253733990242507740924267 6380600985363761611386401)
                  ·
                    refine ⟨4785450739022821208539801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6380600985363761611386401 4785450739022821208539801)
                    ·
                      refine ⟨3589088054267115906404851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785450739022821208539801 3589088054267115906404851)
                      ·
                        rfl

theorem cell23_6989724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6989724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989724 prefixEnd_6989724 := by exact prefixLift 6989724
  have htrace : WordTrace (prefixWord ++ tailWord_6989724) baseStart_6989724 baseEnd_6989724 := by
    simpa [prefixWord, tailWord_6989724, baseEnd_6989724] using wordTrace_append hprefix tailTrace_6989724
  have hstable : (prefixWord ++ tailWord_6989724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989724).length < 2 ^ (prefixWord ++ tailWord_6989724).sum := by decide
  have hdescent : baseEnd_6989724 < baseStart_6989724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989733 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 5, 3, 2]
def baseStart_6989733 : Nat := 118140960795 + 6989733 * 2 ^ 59
def prefixEnd_6989733 : Nat := 4983230072969 + 3 ^ 40 * 6989733 * 2
def baseEnd_6989733 : Nat := 3589092675593006371192309

theorem tailTrace_6989733 : CollatzResearch.WordTrace tailWord_6989733 prefixEnd_6989733 3589092675593006371192309 := by
  unfold tailWord_6989733
  simp only [CollatzResearch.WordTrace]
  refine ⟨254936506386398567202109853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169957670924265711468073235 254936506386398567202109853)
  ·
    refine ⟨95601189894899462700791195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254936506386398567202109853 95601189894899462700791195)
    ·
      refine ⟨143401784842349194051186793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95601189894899462700791195 143401784842349194051186793)
      ·
        refine ⟨107551338631761895538390095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143401784842349194051186793 107551338631761895538390095)
        ·
          refine ⟨161327007947642843307585143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107551338631761895538390095 161327007947642843307585143)
          ·
            refine ⟨241990511921464264961377715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161327007947642843307585143 241990511921464264961377715)
            ·
              refine ⟨362985767882196397442066573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241990511921464264961377715 362985767882196397442066573)
              ·
                refine ⟨136119662955823649040774965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362985767882196397442066573 136119662955823649040774965)
                ·
                  refine ⟨12761218402108467097572653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136119662955823649040774965 12761218402108467097572653)
                  ·
                    refine ⟨4785456900790675161589745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12761218402108467097572653 4785456900790675161589745)
                    ·
                      refine ⟨3589092675593006371192309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785456900790675161589745 3589092675593006371192309)
                      ·
                        rfl

theorem cell23_6989733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_6989733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989733 prefixEnd_6989733 := by exact prefixLift 6989733
  have htrace : WordTrace (prefixWord ++ tailWord_6989733) baseStart_6989733 baseEnd_6989733 := by
    simpa [prefixWord, tailWord_6989733, baseEnd_6989733] using wordTrace_append hprefix tailTrace_6989733
  have hstable : (prefixWord ++ tailWord_6989733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989733).length < 2 ^ (prefixWord ++ tailWord_6989733).sum := by decide
  have hdescent : baseEnd_6989733 < baseStart_6989733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989746 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_6989746 : Nat := 118140960795 + 6989746 * 2 ^ 59
def prefixEnd_6989746 : Nat := 4983230072969 + 3 ^ 40 * 6989746 * 2
def baseEnd_6989746 : Nat := 3589099350841514820329749

theorem tailTrace_6989746 : CollatzResearch.WordTrace tailWord_6989746 prefixEnd_6989746 3589099350841514820329749 := by
  unfold tailWord_6989746
  simp only [CollatzResearch.WordTrace]
  refine ⟨63734245133837867605583273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169957987023567646948222061 63734245133837867605583273)
  ·
    refine ⟨47800683850378400704187455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63734245133837867605583273 47800683850378400704187455)
    ·
      refine ⟨71701025775567601056281183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47800683850378400704187455 71701025775567601056281183)
      ·
        refine ⟨107551538663351401584421775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71701025775567601056281183 107551538663351401584421775)
        ·
          refine ⟨161327307995027102376632663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107551538663351401584421775 161327307995027102376632663)
          ·
            refine ⟨241990961992540653564948995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161327307995027102376632663 241990961992540653564948995)
            ·
              refine ⟨362986442988810980347423493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241990961992540653564948995 362986442988810980347423493)
              ·
                refine ⟨68059958060402058815141905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 362986442988810980347423493 68059958060402058815141905)
                ·
                  refine ⟨51044968545301544111356429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68059958060402058815141905 51044968545301544111356429)
                  ·
                    refine ⟨19141863204488079041758661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51044968545301544111356429 19141863204488079041758661)
                    ·
                      refine ⟨3589099350841514820329749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19141863204488079041758661 3589099350841514820329749)
                      ·
                        rfl

theorem cell23_6989746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_6989746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989746 prefixEnd_6989746 := by exact prefixLift 6989746
  have htrace : WordTrace (prefixWord ++ tailWord_6989746) baseStart_6989746 baseEnd_6989746 := by
    simpa [prefixWord, tailWord_6989746, baseEnd_6989746] using wordTrace_append hprefix tailTrace_6989746
  have hstable : (prefixWord ++ tailWord_6989746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989746).length < 2 ^ (prefixWord ++ tailWord_6989746).sum := by decide
  have hdescent : baseEnd_6989746 < baseStart_6989746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989776 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_6989776 : Nat := 118140960795 + 6989776 * 2 ^ 59
def prefixEnd_6989776 : Nat := 4983230072969 + 3 ^ 40 * 6989776 * 2
def baseEnd_6989776 : Nat := 3589114755261149702954611

theorem tailTrace_6989776 : CollatzResearch.WordTrace tailWord_6989776 prefixEnd_6989776 3589114755261149702954611 := by
  unfold tailWord_6989776
  simp only [CollatzResearch.WordTrace]
  refine ⟨127469037362621392772962591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169958716483495190363950121 127469037362621392772962591)
  ·
    refine ⟨191203556043932089159443887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127469037362621392772962591 191203556043932089159443887)
    ·
      refine ⟨286805334065898133739165831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191203556043932089159443887 286805334065898133739165831)
      ·
        refine ⟨430208001098847200608748747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286805334065898133739165831 430208001098847200608748747)
        ·
          refine ⟨645312001648270800913123121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430208001098847200608748747 645312001648270800913123121)
          ·
            refine ⟨483984001236203100684842341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645312001648270800913123121 483984001236203100684842341)
            ·
              refine ⟨90747000231788081378407939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 483984001236203100684842341 90747000231788081378407939)
              ·
                refine ⟨136120500347682122067611909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90747000231788081378407939 136120500347682122067611909)
                ·
                  refine ⟨25522593815190397887677233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136120500347682122067611909 25522593815190397887677233)
                  ·
                    refine ⟨19141945361392798415757925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25522593815190397887677233 19141945361392798415757925)
                    ·
                      refine ⟨3589114755261149702954611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19141945361392798415757925 3589114755261149702954611)
                      ·
                        rfl

theorem cell23_6989776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_6989776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989776 prefixEnd_6989776 := by exact prefixLift 6989776
  have htrace : WordTrace (prefixWord ++ tailWord_6989776) baseStart_6989776 baseEnd_6989776 := by
    simpa [prefixWord, tailWord_6989776, baseEnd_6989776] using wordTrace_append hprefix tailTrace_6989776
  have hstable : (prefixWord ++ tailWord_6989776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989776).length < 2 ^ (prefixWord ++ tailWord_6989776).sum := by decide
  have hdescent : baseEnd_6989776 < baseStart_6989776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989816 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 1, 7]
def baseStart_6989816 : Nat := 118140960795 + 6989816 * 2 ^ 59
def prefixEnd_6989816 : Nat := 4983230072969 + 3 ^ 40 * 6989816 * 2
def baseEnd_6989816 : Nat := 1196378431495776515484809

theorem tailTrace_6989816 : CollatzResearch.WordTrace tailWord_6989816 prefixEnd_6989816 1196378431495776515484809 := by
  unfold tailWord_6989816
  simp only [CollatzResearch.WordTrace]
  refine ⟨127469766822548936188690651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169959689096731914918254201 127469766822548936188690651)
  ·
    refine ⟨191204650233823404283035977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127469766822548936188690651 191204650233823404283035977)
    ·
      refine ⟨143403487675367553212276983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191204650233823404283035977 143403487675367553212276983)
      ·
        refine ⟨215105231513051329818415475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143403487675367553212276983 215105231513051329818415475)
        ·
          refine ⟨322657847269576994727623213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215105231513051329818415475 322657847269576994727623213)
          ·
            refine ⟨120996692726091373022858705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322657847269576994727623213 120996692726091373022858705)
            ·
              refine ⟨90747519544568529767144029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120996692726091373022858705 90747519544568529767144029)
              ·
                refine ⟨34030319829213198662679011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90747519544568529767144029 34030319829213198662679011)
                ·
                  refine ⟨51045479743819797994018517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34030319829213198662679011 51045479743819797994018517)
                  ·
                    refine ⟨1196378431495776515484809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51045479743819797994018517 1196378431495776515484809)
                    ·
                      rfl

theorem cell23_6989816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_6989816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989816 prefixEnd_6989816 := by exact prefixLift 6989816
  have htrace : WordTrace (prefixWord ++ tailWord_6989816) baseStart_6989816 baseEnd_6989816 := by
    simpa [prefixWord, tailWord_6989816, baseEnd_6989816] using wordTrace_append hprefix tailTrace_6989816
  have hstable : (prefixWord ++ tailWord_6989816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989816).length < 2 ^ (prefixWord ++ tailWord_6989816).sum := by decide
  have hdescent : baseEnd_6989816 < baseStart_6989816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989823 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 4, 5, 2]
def baseStart_6989823 : Nat := 118140960795 + 6989823 * 2 ^ 59
def prefixEnd_6989823 : Nat := 4983230072969 + 3 ^ 40 * 6989823 * 2
def baseEnd_6989823 : Nat := 3589138888851911019066895

theorem tailTrace_6989823 : CollatzResearch.WordTrace tailWord_6989823 prefixEnd_6989823 3589138888851911019066895 := by
  unfold tailWord_6989823
  simp only [CollatzResearch.WordTrace]
  refine ⟨254939788956072512572886123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169959859304048341715257415 254939788956072512572886123)
  ·
    refine ⟨382409683434108768859329185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254939788956072512572886123 382409683434108768859329185)
    ·
      refine ⟨286807262575581576644496889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382409683434108768859329185 286807262575581576644496889)
      ·
        refine ⟨215105446931686182483372667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286807262575581576644496889 215105446931686182483372667)
        ·
          refine ⟨322658170397529273725059001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215105446931686182483372667 322658170397529273725059001)
          ·
            refine ⟨241993627798146955293794251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322658170397529273725059001 241993627798146955293794251)
            ·
              refine ⟨362990441697220432940691377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241993627798146955293794251 362990441697220432940691377)
              ·
                refine ⟨272242831272915324705518533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362990441697220432940691377 272242831272915324705518533)
                ·
                  refine ⟨51045530863671623382284725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272242831272915324705518533 51045530863671623382284725)
                  ·
                    refine ⟨4785518518469214692089193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51045530863671623382284725 4785518518469214692089193)
                    ·
                      refine ⟨3589138888851911019066895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785518518469214692089193 3589138888851911019066895)
                      ·
                        rfl

theorem cell23_6989823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_6989823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989823 prefixEnd_6989823 := by exact prefixLift 6989823
  have htrace : WordTrace (prefixWord ++ tailWord_6989823) baseStart_6989823 baseEnd_6989823 := by
    simpa [prefixWord, tailWord_6989823, baseEnd_6989823] using wordTrace_append hprefix tailTrace_6989823
  have hstable : (prefixWord ++ tailWord_6989823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989823).length < 2 ^ (prefixWord ++ tailWord_6989823).sum := by decide
  have hdescent : baseEnd_6989823 < baseStart_6989823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989870 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_6989870 : Nat := 118140960795 + 6989870 * 2 ^ 59
def prefixEnd_6989870 : Nat := 4983230072969 + 3 ^ 40 * 6989870 * 2
def baseEnd_6989870 : Nat := 3589163022442672335179179

theorem tailTrace_6989870 : CollatzResearch.WordTrace tailWord_6989870 prefixEnd_6989870 3589163022442672335179179 := by
  unfold tailWord_6989870
  simp only [CollatzResearch.WordTrace]
  refine ⟨31867687898362779949980883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169961002124601493066564709 31867687898362779949980883)
  ·
    refine ⟨47801531847544169924971325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31867687898362779949980883 47801531847544169924971325)
    ·
      refine ⟨17925574442829063721864247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47801531847544169924971325 17925574442829063721864247)
      ·
        refine ⟨26888361664243595582796371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17925574442829063721864247 26888361664243595582796371)
        ·
          refine ⟨40332542496365393374194557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26888361664243595582796371 40332542496365393374194557)
          ·
            refine ⟨15124703436137022515322959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40332542496365393374194557 15124703436137022515322959)
            ·
              refine ⟨22687055154205533772984439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15124703436137022515322959 22687055154205533772984439)
              ·
                refine ⟨34030582731308300659476659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22687055154205533772984439 34030582731308300659476659)
                ·
                  refine ⟨51045874096962450989214989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34030582731308300659476659 51045874096962450989214989)
                  ·
                    refine ⟨19142202786360919120955621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51045874096962450989214989 19142202786360919120955621)
                    ·
                      refine ⟨3589163022442672335179179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19142202786360919120955621 3589163022442672335179179)
                      ·
                        rfl

theorem cell23_6989870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_6989870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989870 prefixEnd_6989870 := by exact prefixLift 6989870
  have htrace : WordTrace (prefixWord ++ tailWord_6989870) baseStart_6989870 baseEnd_6989870 := by
    simpa [prefixWord, tailWord_6989870, baseEnd_6989870] using wordTrace_append hprefix tailTrace_6989870
  have hstable : (prefixWord ++ tailWord_6989870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989870).length < 2 ^ (prefixWord ++ tailWord_6989870).sum := by decide
  have hdescent : baseEnd_6989870 < baseStart_6989870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989923 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 3, 5]
def baseStart_6989923 : Nat := 118140960795 + 6989923 * 2 ^ 59
def prefixEnd_6989923 : Nat := 4983230072969 + 3 ^ 40 * 6989923 * 2
def baseEnd_6989923 : Nat := 1196396745639120209272145

theorem tailTrace_6989923 : CollatzResearch.WordTrace tailWord_6989923 prefixEnd_6989923 1196396745639120209272145 := by
  unfold tailWord_6989923
  simp only [CollatzResearch.WordTrace]
  refine ⟨254943436255710229651526423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169962290837140153101017615 254943436255710229651526423)
  ·
    refine ⟨382415154383565344477289635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254943436255710229651526423 382415154383565344477289635)
    ·
      refine ⟨573622731575348016715934453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382415154383565344477289635 573622731575348016715934453)
      ·
        refine ⟨53777131085188876567118855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 573622731575348016715934453 53777131085188876567118855)
        ·
          refine ⟨80665696627783314850678283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53777131085188876567118855 80665696627783314850678283)
          ·
            refine ⟨120998544941674972276017425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80665696627783314850678283 120998544941674972276017425)
            ·
              refine ⟨90748908706256229207013069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120998544941674972276017425 90748908706256229207013069)
              ·
                refine ⟨34030840764846085952629901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90748908706256229207013069 34030840764846085952629901)
                ·
                  refine ⟨12761565286817282232236213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34030840764846085952629901 12761565286817282232236213)
                  ·
                    refine ⟨1196396745639120209272145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12761565286817282232236213 1196396745639120209272145)
                    ·
                      rfl

theorem cell23_6989923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 5].length) (baseStart_6989923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989923 prefixEnd_6989923 := by exact prefixLift 6989923
  have htrace : WordTrace (prefixWord ++ tailWord_6989923) baseStart_6989923 baseEnd_6989923 := by
    simpa [prefixWord, tailWord_6989923, baseEnd_6989923] using wordTrace_append hprefix tailTrace_6989923
  have hstable : (prefixWord ++ tailWord_6989923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989923).length < 2 ^ (prefixWord ++ tailWord_6989923).sum := by decide
  have hdescent : baseEnd_6989923 < baseStart_6989923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989963 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 3]
def baseStart_6989963 : Nat := 118140960795 + 6989963 * 2 ^ 59
def prefixEnd_6989963 : Nat := 4983230072969 + 3 ^ 40 * 6989963 * 2
def baseEnd_6989963 : Nat := 3589210776143540471316251

theorem tailTrace_6989963 : CollatzResearch.WordTrace tailWord_6989963 prefixEnd_6989963 3589210776143540471316251 := by
  unfold tailWord_6989963
  simp only [CollatzResearch.WordTrace]
  refine ⟨254944895175565316482982543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169963263450376877655321695 254944895175565316482982543)
  ·
    refine ⟨382417342763347974724473815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254944895175565316482982543 382417342763347974724473815)
    ·
      refine ⟨573626014145021962086710723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382417342763347974724473815 573626014145021962086710723)
      ·
        refine ⟨860439021217532943130066085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573626014145021962086710723 860439021217532943130066085)
        ·
          refine ⟨161332316478287426836887391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 860439021217532943130066085 161332316478287426836887391)
          ·
            refine ⟨241998474717431140255331087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161332316478287426836887391 241998474717431140255331087)
            ·
              refine ⟨362997712076146710382996631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241998474717431140255331087 362997712076146710382996631)
              ·
                refine ⟨544496568114220065574494947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362997712076146710382996631 544496568114220065574494947)
                ·
                  refine ⟨816744852171330098361742421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544496568114220065574494947 816744852171330098361742421)
                  ·
                    refine ⟨9571228736382774590176669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 816744852171330098361742421 9571228736382774590176669)
                    ·
                      refine ⟨3589210776143540471316251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9571228736382774590176669 3589210776143540471316251)
                      ·
                        rfl

theorem cell23_6989963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 3].length) (baseStart_6989963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989963 prefixEnd_6989963 := by exact prefixLift 6989963
  have htrace : WordTrace (prefixWord ++ tailWord_6989963) baseStart_6989963 baseEnd_6989963 := by
    simpa [prefixWord, tailWord_6989963, baseEnd_6989963] using wordTrace_append hprefix tailTrace_6989963
  have hstable : (prefixWord ++ tailWord_6989963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989963).length < 2 ^ (prefixWord ++ tailWord_6989963).sum := by decide
  have hdescent : baseEnd_6989963 < baseStart_6989963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989970 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_6989970 : Nat := 118140960795 + 6989970 * 2 ^ 59
def prefixEnd_6989970 : Nat := 4983230072969 + 3 ^ 40 * 6989970 * 2
def baseEnd_6989970 : Nat := 1196404790169373981309573

theorem tailTrace_6989970 : CollatzResearch.WordTrace tailWord_6989970 prefixEnd_6989970 1196404790169373981309573 := by
  unfold tailWord_6989970
  simp only [CollatzResearch.WordTrace]
  refine ⟨63736287621634989169621841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169963433657693304452324909 63736287621634989169621841)
  ·
    refine ⟨47802215716226241877216381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63736287621634989169621841 47802215716226241877216381)
    ·
      refine ⟨17925830893584840703956143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47802215716226241877216381 17925830893584840703956143)
      ·
        refine ⟨26888746340377261055934215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17925830893584840703956143 26888746340377261055934215)
        ·
          refine ⟨40333119510565891583901323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26888746340377261055934215 40333119510565891583901323)
          ·
            refine ⟨60499679265848837375851985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40333119510565891583901323 60499679265848837375851985)
            ·
              refine ⟨45374759449386628031888989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60499679265848837375851985 45374759449386628031888989)
              ·
                refine ⟨17015534793519985511958371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45374759449386628031888989 17015534793519985511958371)
                ·
                  refine ⟨25523302190279978267937557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17015534793519985511958371 25523302190279978267937557)
                  ·
                    refine ⟨1196404790169373981309573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25523302190279978267937557 1196404790169373981309573)
                    ·
                      rfl

theorem cell23_6989970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_6989970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989970 prefixEnd_6989970 := by exact prefixLift 6989970
  have htrace : WordTrace (prefixWord ++ tailWord_6989970) baseStart_6989970 baseEnd_6989970 := by
    simpa [prefixWord, tailWord_6989970, baseEnd_6989970] using wordTrace_append hprefix tailTrace_6989970
  have hstable : (prefixWord ++ tailWord_6989970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989970).length < 2 ^ (prefixWord ++ tailWord_6989970).sum := by decide
  have hdescent : baseEnd_6989970 < baseStart_6989970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989973 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_6989973 : Nat := 118140960795 + 6989973 * 2 ^ 59
def prefixEnd_6989973 : Nat := 4983230072969 + 3 ^ 40 * 6989973 * 2
def baseEnd_6989973 : Nat := 3589215910950085432191205

theorem tailTrace_6989973 : CollatzResearch.WordTrace tailWord_6989973 prefixEnd_6989973 3589215910950085432191205 := by
  unfold tailWord_6989973
  simp only [CollatzResearch.WordTrace]
  refine ⟨254945259905529088190846573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169963506603686058793897715 254945259905529088190846573)
  ·
    refine ⟨95604472464573408071567465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254945259905529088190846573 95604472464573408071567465)
    ·
      refine ⟨71703354348430056053675599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95604472464573408071567465 71703354348430056053675599)
      ·
        refine ⟨107555031522645084080513399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71703354348430056053675599 107555031522645084080513399)
        ·
          refine ⟨161332547283967626120770099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107555031522645084080513399 161332547283967626120770099)
          ·
            refine ⟨241998820925951439181155149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161332547283967626120770099 241998820925951439181155149)
            ·
              refine ⟨90749557847231789692933181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241998820925951439181155149 90749557847231789692933181)
              ·
                refine ⟨34031084192711921134849943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90749557847231789692933181 34031084192711921134849943)
                ·
                  refine ⟨51046626289067881702274915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34031084192711921134849943 51046626289067881702274915)
                  ·
                    refine ⟨76569939433601822553412373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51046626289067881702274915 76569939433601822553412373)
                    ·
                      refine ⟨3589215910950085432191205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76569939433601822553412373 3589215910950085432191205)
                      ·
                        rfl

theorem cell23_6989973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_6989973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989973 prefixEnd_6989973 := by exact prefixLift 6989973
  have htrace : WordTrace (prefixWord ++ tailWord_6989973) baseStart_6989973 baseEnd_6989973 := by
    simpa [prefixWord, tailWord_6989973, baseEnd_6989973] using wordTrace_append hprefix tailTrace_6989973
  have hstable : (prefixWord ++ tailWord_6989973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989973).length < 2 ^ (prefixWord ++ tailWord_6989973).sum := by decide
  have hdescent : baseEnd_6989973 < baseStart_6989973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989977 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 3, 2, 2]
def baseStart_6989977 : Nat := 118140960795 + 6989977 * 2 ^ 59
def prefixEnd_6989977 : Nat := 4983230072969 + 3 ^ 40 * 6989977 * 2
def baseEnd_6989977 : Nat := 3589217964872703416541187

theorem tailTrace_6989977 : CollatzResearch.WordTrace tailWord_6989977 prefixEnd_6989977 3589217964872703416541187 := by
  unfold tailWord_6989977
  simp only [CollatzResearch.WordTrace]
  refine ⟨254945405797514596873992185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169963603865009731249328123 254945405797514596873992185)
  ·
    refine ⟨191209054348135947655494139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254945405797514596873992185 191209054348135947655494139)
    ·
      refine ⟨286813581522203921483241209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191209054348135947655494139 286813581522203921483241209)
      ·
        refine ⟨215110186141652941112430907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286813581522203921483241209 215110186141652941112430907)
        ·
          refine ⟨322665279212479411668646361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215110186141652941112430907 322665279212479411668646361)
          ·
            refine ⟨241998959409359558751484771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322665279212479411668646361 241998959409359558751484771)
            ·
              refine ⟨362998439114039338127227157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241998959409359558751484771 362998439114039338127227157)
              ·
                refine ⟨17015551833470593974713773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 362998439114039338127227157 17015551833470593974713773)
                ·
                  refine ⟨6380831937551472740517665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17015551833470593974713773 6380831937551472740517665)
                  ·
                    refine ⟨4785623953163604555388249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6380831937551472740517665 4785623953163604555388249)
                    ·
                      refine ⟨3589217964872703416541187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785623953163604555388249 3589217964872703416541187)
                      ·
                        rfl

theorem cell23_6989977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_6989977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989977 prefixEnd_6989977 := by exact prefixLift 6989977
  have htrace : WordTrace (prefixWord ++ tailWord_6989977) baseStart_6989977 baseEnd_6989977 := by
    simpa [prefixWord, tailWord_6989977, baseEnd_6989977] using wordTrace_append hprefix tailTrace_6989977
  have hstable : (prefixWord ++ tailWord_6989977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989977).length < 2 ^ (prefixWord ++ tailWord_6989977).sum := by decide
  have hdescent : baseEnd_6989977 < baseStart_6989977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989997 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_6989997 : Nat := 118140960795 + 6989997 * 2 ^ 59
def prefixEnd_6989997 : Nat := 4983230072969 + 3 ^ 40 * 6989997 * 2
def baseEnd_6989997 : Nat := 3589228234485793338291095

theorem tailTrace_6989997 : CollatzResearch.WordTrace tailWord_6989997 prefixEnd_6989997 3589228234485793338291095 := by
  unfold tailWord_6989997
  simp only [CollatzResearch.WordTrace]
  refine ⟨254946135257442140289720245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169964090171628093526480163 254946135257442140289720245)
  ·
    refine ⟨23901200180385200652161273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254946135257442140289720245 23901200180385200652161273)
    ·
      refine ⟨17925900135288900489120955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23901200180385200652161273 17925900135288900489120955)
      ·
        refine ⟨26888850202933350733681433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17925900135288900489120955 26888850202933350733681433)
        ·
          refine ⟨20166637652200013050261075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26888850202933350733681433 20166637652200013050261075)
          ·
            refine ⟨30249956478300019575391613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20166637652200013050261075 30249956478300019575391613)
            ·
              refine ⟨11343733679362507340771855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30249956478300019575391613 11343733679362507340771855)
              ·
                refine ⟨17015600519043761011157783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11343733679362507340771855 17015600519043761011157783)
                ·
                  refine ⟨25523400778565641516736675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17015600519043761011157783 25523400778565641516736675)
                  ·
                    refine ⟨38285101167848462275105013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25523400778565641516736675 38285101167848462275105013)
                    ·
                      refine ⟨3589228234485793338291095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38285101167848462275105013 3589228234485793338291095)
                      ·
                        rfl

theorem cell23_6989997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_6989997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6989997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6989997 prefixEnd_6989997 := by exact prefixLift 6989997
  have htrace : WordTrace (prefixWord ++ tailWord_6989997) baseStart_6989997 baseEnd_6989997 := by
    simpa [prefixWord, tailWord_6989997, baseEnd_6989997] using wordTrace_append hprefix tailTrace_6989997
  have hstable : (prefixWord ++ tailWord_6989997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989997).length < 2 ^ (prefixWord ++ tailWord_6989997).sum := by decide
  have hdescent : baseEnd_6989997 < baseStart_6989997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990005 : List Nat := [1, 3, 3, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6990005 : Nat := 118140960795 + 6990005 * 2 ^ 59
def prefixEnd_6990005 : Nat := 4983230072969 + 3 ^ 40 * 6990005 * 2
def baseEnd_6990005 : Nat := 3589232342331029306991059

theorem tailTrace_6990005 : CollatzResearch.WordTrace tailWord_6990005 prefixEnd_6990005 3589232342331029306991059 := by
  unfold tailWord_6990005
  simp only [CollatzResearch.WordTrace]
  refine ⟨254946427041413157656011469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169964284694275438437340979 254946427041413157656011469)
  ·
    refine ⟨95604910140529934121004301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254946427041413157656011469 95604910140529934121004301)
    ·
      refine ⟨35851841302698725295376613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95604910140529934121004301 35851841302698725295376613)
      ·
        refine ⟨6722220244256010992883115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35851841302698725295376613 6722220244256010992883115)
        ·
          refine ⟨10083330366384016489324673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6722220244256010992883115 10083330366384016489324673)
          ·
            refine ⟨7562497774788012366993505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10083330366384016489324673 7562497774788012366993505)
            ·
              refine ⟨5671873331091009275245129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7562497774788012366993505 5671873331091009275245129)
              ·
                refine ⟨4253904998318256956433847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5671873331091009275245129 4253904998318256956433847)
                ·
                  refine ⟨6380857497477385434650771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253904998318256956433847 6380857497477385434650771)
                  ·
                    refine ⟨9571286246216078151976157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6380857497477385434650771 9571286246216078151976157)
                    ·
                      refine ⟨3589232342331029306991059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9571286246216078151976157 3589232342331029306991059)
                      ·
                        rfl

theorem cell23_6990005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6990005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990005 prefixEnd_6990005 := by exact prefixLift 6990005
  have htrace : WordTrace (prefixWord ++ tailWord_6990005) baseStart_6990005 baseEnd_6990005 := by
    simpa [prefixWord, tailWord_6990005, baseEnd_6990005] using wordTrace_append hprefix tailTrace_6990005
  have hstable : (prefixWord ++ tailWord_6990005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990005).length < 2 ^ (prefixWord ++ tailWord_6990005).sum := by decide
  have hdescent : baseEnd_6990005 < baseStart_6990005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990023 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_6990023 : Nat := 118140960795 + 6990023 * 2 ^ 59
def prefixEnd_6990023 : Nat := 4983230072969 + 3 ^ 40 * 6990023 * 2
def baseEnd_6990023 : Nat := 3589241584982810236565975

theorem tailTrace_6990023 : CollatzResearch.WordTrace tailWord_6990023 prefixEnd_6990023 3589241584982810236565975 := by
  unfold tailWord_6990023
  simp only [CollatzResearch.WordTrace]
  refine ⟨254947083555347946730166723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169964722370231964486777815 254947083555347946730166723)
  ·
    refine ⟨382420625333021920095250085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254947083555347946730166723 382420625333021920095250085)
    ·
      refine ⟨71703867249941610017859391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382420625333021920095250085 71703867249941610017859391)
      ·
        refine ⟨107555800874912415026789087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71703867249941610017859391 107555800874912415026789087)
        ·
          refine ⟨161333701312368622540183631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107555800874912415026789087 161333701312368622540183631)
          ·
            refine ⟨242000551968552933810275447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161333701312368622540183631 242000551968552933810275447)
            ·
              refine ⟨363000827952829400715413171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242000551968552933810275447 363000827952829400715413171)
              ·
                refine ⟨544501241929244101073119757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363000827952829400715413171 544501241929244101073119757)
                ·
                  refine ⟨204187965723466537902419909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544501241929244101073119757 204187965723466537902419909)
                  ·
                    refine ⟨38285243573149975856703733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204187965723466537902419909 38285243573149975856703733)
                    ·
                      refine ⟨3589241584982810236565975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38285243573149975856703733 3589241584982810236565975)
                      ·
                        rfl

theorem cell23_6990023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_6990023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990023 prefixEnd_6990023 := by exact prefixLift 6990023
  have htrace : WordTrace (prefixWord ++ tailWord_6990023) baseStart_6990023 baseEnd_6990023 := by
    simpa [prefixWord, tailWord_6990023, baseEnd_6990023] using wordTrace_append hprefix tailTrace_6990023
  have hstable : (prefixWord ++ tailWord_6990023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990023).length < 2 ^ (prefixWord ++ tailWord_6990023).sum := by decide
  have hdescent : baseEnd_6990023 < baseStart_6990023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990027 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 3]
def baseStart_6990027 : Nat := 118140960795 + 6990027 * 2 ^ 59
def prefixEnd_6990027 : Nat := 4983230072969 + 3 ^ 40 * 6990027 * 2
def baseEnd_6990027 : Nat := 3589243638905428220915957

theorem tailTrace_6990027 : CollatzResearch.WordTrace tailWord_6990027 prefixEnd_6990027 3589243638905428220915957 := by
  unfold tailWord_6990027
  simp only [CollatzResearch.WordTrace]
  refine ⟨254947229447333455413312335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169964819631555636942208223 254947229447333455413312335)
  ·
    refine ⟨382420844171000183119968503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254947229447333455413312335 382420844171000183119968503)
    ·
      refine ⟨573631266256500274679952755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382420844171000183119968503 573631266256500274679952755)
      ·
        refine ⟨860446899384750412019929133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573631266256500274679952755 860446899384750412019929133)
        ·
          refine ⟨322667587269281404507473425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 860446899384750412019929133 322667587269281404507473425)
          ·
            refine ⟨242000690451961053380605069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322667587269281404507473425 242000690451961053380605069)
            ·
              refine ⟨90750258919485395017726901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242000690451961053380605069 90750258919485395017726901)
              ·
                refine ⟨8507836773701755782911897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90750258919485395017726901 8507836773701755782911897)
                ·
                  refine ⟨6380877580276316837183923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8507836773701755782911897 6380877580276316837183923)
                  ·
                    refine ⟨9571316370414475255775885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6380877580276316837183923 9571316370414475255775885)
                    ·
                      refine ⟨3589243638905428220915957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9571316370414475255775885 3589243638905428220915957)
                      ·
                        rfl

theorem cell23_6990027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 3].length) (baseStart_6990027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990027 prefixEnd_6990027 := by exact prefixLift 6990027
  have htrace : WordTrace (prefixWord ++ tailWord_6990027) baseStart_6990027 baseEnd_6990027 := by
    simpa [prefixWord, tailWord_6990027, baseEnd_6990027] using wordTrace_append hprefix tailTrace_6990027
  have hstable : (prefixWord ++ tailWord_6990027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990027).length < 2 ^ (prefixWord ++ tailWord_6990027).sum := by decide
  have hdescent : baseEnd_6990027 < baseStart_6990027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990043 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 4, 6]
def baseStart_6990043 : Nat := 118140960795 + 6990043 * 2 ^ 59
def prefixEnd_6990043 : Nat := 4983230072969 + 3 ^ 40 * 6990043 * 2
def baseEnd_6990043 : Nat := 1196417284865300052771961

theorem tailTrace_6990043 : CollatzResearch.WordTrace tailWord_6990043 prefixEnd_6990043 1196417284865300052771961 := by
  unfold tailWord_6990043
  simp only [CollatzResearch.WordTrace]
  refine ⟨254947813015275490145894783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169965208676850326763929855 254947813015275490145894783)
  ·
    refine ⟨382421719522913235218842175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254947813015275490145894783 382421719522913235218842175)
    ·
      refine ⟨573632579284369852828263263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382421719522913235218842175 573632579284369852828263263)
      ·
        refine ⟨860448868926554779242394895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573632579284369852828263263 860448868926554779242394895)
        ·
          refine ⟨1290673303389832168863592343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860448868926554779242394895 1290673303389832168863592343)
          ·
            refine ⟨1936009955084748253295388515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290673303389832168863592343 1936009955084748253295388515)
            ·
              refine ⟨2904014932627122379943082773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936009955084748253295388515 2904014932627122379943082773)
              ·
                refine ⟨136125699966896361559832005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2904014932627122379943082773 136125699966896361559832005)
                ·
                  refine ⟨25523568743793067792468501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136125699966896361559832005 25523568743793067792468501)
                  ·
                    refine ⟨1196417284865300052771961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25523568743793067792468501 1196417284865300052771961)
                    ·
                      rfl

theorem cell23_6990043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 6].length) (baseStart_6990043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990043 prefixEnd_6990043 := by exact prefixLift 6990043
  have htrace : WordTrace (prefixWord ++ tailWord_6990043) baseStart_6990043 baseEnd_6990043 := by
    simpa [prefixWord, tailWord_6990043, baseEnd_6990043] using wordTrace_append hprefix tailTrace_6990043
  have hstable : (prefixWord ++ tailWord_6990043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990043).length < 2 ^ (prefixWord ++ tailWord_6990043).sum := by decide
  have hdescent : baseEnd_6990043 < baseStart_6990043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990080 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_6990080 : Nat := 118140960795 + 6990080 * 2 ^ 59
def prefixEnd_6990080 : Nat := 4983230072969 + 3 ^ 40 * 6990080 * 2
def baseEnd_6990080 : Nat := 3589270853380116513553213

theorem tailTrace_6990080 : CollatzResearch.WordTrace tailWord_6990080 prefixEnd_6990080 3589270853380116513553213 := by
  unfold tailWord_6990080
  simp only [CollatzResearch.WordTrace]
  refine ⟨127474581258070722732495847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169966108344094296976661129 127474581258070722732495847)
  ·
    refine ⟨191211871887106084098743771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127474581258070722732495847 191211871887106084098743771)
    ·
      refine ⟨286817807830659126148115657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191211871887106084098743771 286817807830659126148115657)
      ·
        refine ⟨215113355872994344611086743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286817807830659126148115657 215113355872994344611086743)
        ·
          refine ⟨322670033809491516916630115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215113355872994344611086743 322670033809491516916630115)
          ·
            refine ⟨484005050714237275374945173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322670033809491516916630115 484005050714237275374945173)
            ·
              refine ⟨22687736752229872283200555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 484005050714237275374945173 22687736752229872283200555)
              ·
                refine ⟨34031605128344808424800833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22687736752229872283200555 34031605128344808424800833)
                ·
                  refine ⟨25523703846258606318600625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34031605128344808424800833 25523703846258606318600625)
                  ·
                    refine ⟨19142777884693954738950469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25523703846258606318600625 19142777884693954738950469)
                    ·
                      refine ⟨3589270853380116513553213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19142777884693954738950469 3589270853380116513553213)
                      ·
                        rfl

theorem cell23_6990080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_6990080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990080 prefixEnd_6990080 := by exact prefixLift 6990080
  have htrace : WordTrace (prefixWord ++ tailWord_6990080) baseStart_6990080 baseEnd_6990080 := by
    simpa [prefixWord, tailWord_6990080, baseEnd_6990080] using wordTrace_append hprefix tailTrace_6990080
  have hstable : (prefixWord ++ tailWord_6990080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990080).length < 2 ^ (prefixWord ++ tailWord_6990080).sum := by decide
  have hdescent : baseEnd_6990080 < baseStart_6990080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990090 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 7]
def baseStart_6990090 : Nat := 118140960795 + 6990090 * 2 ^ 59
def prefixEnd_6990090 : Nat := 4983230072969 + 3 ^ 40 * 6990090 * 2
def baseEnd_6990090 : Nat := 398808443131851274936463

theorem tailTrace_6990090 : CollatzResearch.WordTrace tailWord_6990090 prefixEnd_6990090 398808443131851274936463 := by
  unfold tailWord_6990090
  simp only [CollatzResearch.WordTrace]
  refine ⟨63737381811526304293213931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169966351497403478115237149 63737381811526304293213931)
  ·
    refine ⟨95606072717289456439820897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63737381811526304293213931 95606072717289456439820897)
    ·
      refine ⟨71704554537967092329865673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95606072717289456439820897 71704554537967092329865673)
      ·
        refine ⟨53778415903475319247399255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71704554537967092329865673 53778415903475319247399255)
        ·
          refine ⟨80667623855212978871098883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53778415903475319247399255 80667623855212978871098883)
          ·
            refine ⟨121001435782819468306648325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80667623855212978871098883 121001435782819468306648325)
            ·
              refine ⟨22687769209278650307496561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121001435782819468306648325 22687769209278650307496561)
              ·
                refine ⟨17015826906958987730622421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22687769209278650307496561 17015826906958987730622421)
                ·
                  refine ⟨398808443131851274936463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17015826906958987730622421 398808443131851274936463)
                  ·
                    rfl

theorem cell23_6990090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_6990090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990090 prefixEnd_6990090 := by exact prefixLift 6990090
  have htrace : WordTrace (prefixWord ++ tailWord_6990090) baseStart_6990090 baseEnd_6990090 := by
    simpa [prefixWord, tailWord_6990090, baseEnd_6990090] using wordTrace_append hprefix tailTrace_6990090
  have hstable : (prefixWord ++ tailWord_6990090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990090).length < 2 ^ (prefixWord ++ tailWord_6990090).sum := by decide
  have hdescent : baseEnd_6990090 < baseStart_6990090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990107 : List Nat := [1, 1, 1, 1, 1, 1, 9, 3, 5]
def baseStart_6990107 : Nat := 118140960795 + 6990107 * 2 ^ 59
def prefixEnd_6990107 : Nat := 4983230072969 + 3 ^ 40 * 6990107 * 2
def baseEnd_6990107 : Nat := 398809413039754211990621

theorem tailTrace_6990107 : CollatzResearch.WordTrace tailWord_6990107 prefixEnd_6990107 398809413039754211990621 := by
  unfold tailWord_6990107
  simp only [CollatzResearch.WordTrace]
  refine ⟨254950147287043629076224575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169966764858029086050816383 254950147287043629076224575)
  ·
    refine ⟨382425220930565443614336863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254950147287043629076224575 382425220930565443614336863)
    ·
      refine ⟨573637831395848165421505295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382425220930565443614336863 573637831395848165421505295)
      ·
        refine ⟨860456747093772248132257943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573637831395848165421505295 860456747093772248132257943)
        ·
          refine ⟨1290685120640658372198386915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860456747093772248132257943 1290685120640658372198386915)
          ·
            refine ⟨1936027680960987558297580373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290685120640658372198386915 1936027680960987558297580373)
            ·
              refine ⟨11343912193130786474399885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1936027680960987558297580373 11343912193130786474399885)
              ·
                refine ⟨4253967072424044927899957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11343912193130786474399885 4253967072424044927899957)
                ·
                  refine ⟨398809413039754211990621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4253967072424044927899957 398809413039754211990621)
                  ·
                    rfl

theorem cell23_6990107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 5].length) (baseStart_6990107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990107 prefixEnd_6990107 := by exact prefixLift 6990107
  have htrace : WordTrace (prefixWord ++ tailWord_6990107) baseStart_6990107 baseEnd_6990107 := by
    simpa [prefixWord, tailWord_6990107, baseEnd_6990107] using wordTrace_append hprefix tailTrace_6990107
  have hstable : (prefixWord ++ tailWord_6990107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990107).length < 2 ^ (prefixWord ++ tailWord_6990107).sum := by decide
  have hdescent : baseEnd_6990107 < baseStart_6990107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990170 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_6990170 : Nat := 118140960795 + 6990170 * 2 ^ 59
def prefixEnd_6990170 : Nat := 4983230072969 + 3 ^ 40 * 6990170 * 2
def baseEnd_6990170 : Nat := 3589317066639021161427799

theorem tailTrace_6990170 : CollatzResearch.WordTrace tailWord_6990170 prefixEnd_6990170 3589317066639021161427799 := by
  unfold tailWord_6990170
  simp only [CollatzResearch.WordTrace]
  refine ⟨63738111271453847708941991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169968296723876927223845309 63738111271453847708941991)
  ·
    refine ⟨95607166907180771563412987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63738111271453847708941991 95607166907180771563412987)
    ·
      refine ⟨143410750360771157345119481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95607166907180771563412987 143410750360771157345119481)
      ·
        refine ⟨107558062770578368008839611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143410750360771157345119481 107558062770578368008839611)
        ·
          refine ⟨161337094155867552013259417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107558062770578368008839611 161337094155867552013259417)
          ·
            refine ⟨121002820616900664009944563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161337094155867552013259417 121002820616900664009944563)
            ·
              refine ⟨181504230925350996014916845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121002820616900664009944563 181504230925350996014916845)
              ·
                refine ⟨68064086597006623505593817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181504230925350996014916845 68064086597006623505593817)
                ·
                  refine ⟨51048064947754967629195363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68064086597006623505593817 51048064947754967629195363)
                  ·
                    refine ⟨76572097421632451443793045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51048064947754967629195363 76572097421632451443793045)
                    ·
                      refine ⟨3589317066639021161427799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76572097421632451443793045 3589317066639021161427799)
                      ·
                        rfl

theorem cell23_6990170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_6990170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990170 prefixEnd_6990170 := by exact prefixLift 6990170
  have htrace : WordTrace (prefixWord ++ tailWord_6990170) baseStart_6990170 baseEnd_6990170 := by
    simpa [prefixWord, tailWord_6990170, baseEnd_6990170] using wordTrace_append hprefix tailTrace_6990170
  have hstable : (prefixWord ++ tailWord_6990170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990170).length < 2 ^ (prefixWord ++ tailWord_6990170).sum := by decide
  have hdescent : baseEnd_6990170 < baseStart_6990170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990211 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 3]
def baseStart_6990211 : Nat := 118140960795 + 6990211 * 2 ^ 59
def prefixEnd_6990211 : Nat := 4983230072969 + 3 ^ 40 * 6990211 * 2
def baseEnd_6990211 : Nat := 3589338119345855501015111

theorem tailTrace_6990211 : CollatzResearch.WordTrace tailWord_6990211 prefixEnd_6990211 3589338119345855501015111 := by
  unfold tailWord_6990211
  simp only [CollatzResearch.WordTrace]
  refine ⟨254953940478666854838010487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169969293652444569892006991 254953940478666854838010487)
  ·
    refine ⟨382430910718000282257015731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254953940478666854838010487 382430910718000282257015731)
    ·
      refine ⟨573646366077000423385523597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382430910718000282257015731 573646366077000423385523597)
      ·
        refine ⟨215117387278875158769571349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 573646366077000423385523597 215117387278875158769571349)
        ·
          refine ⟨10083627528697273067323657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 215117387278875158769571349 10083627528697273067323657)
          ·
            refine ⟨7562720646522954800492743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10083627528697273067323657 7562720646522954800492743)
            ·
              refine ⟨11344080969784432200739115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7562720646522954800492743 11344080969784432200739115)
              ·
                refine ⟨17016121454676648301108673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11344080969784432200739115 17016121454676648301108673)
                ·
                  refine ⟨12762091091007486225831505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17016121454676648301108673 12762091091007486225831505)
                  ·
                    refine ⟨9571568318255614669373629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12762091091007486225831505 9571568318255614669373629)
                    ·
                      refine ⟨3589338119345855501015111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9571568318255614669373629 3589338119345855501015111)
                      ·
                        rfl

theorem cell23_6990211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_6990211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990211 prefixEnd_6990211 := by exact prefixLift 6990211
  have htrace : WordTrace (prefixWord ++ tailWord_6990211) baseStart_6990211 baseEnd_6990211 := by
    simpa [prefixWord, tailWord_6990211, baseEnd_6990211] using wordTrace_append hprefix tailTrace_6990211
  have hstable : (prefixWord ++ tailWord_6990211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990211).length < 2 ^ (prefixWord ++ tailWord_6990211).sum := by decide
  have hdescent : baseEnd_6990211 < baseStart_6990211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990261 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_6990261 : Nat := 118140960795 + 6990261 * 2 ^ 59
def prefixEnd_6990261 : Nat := 4983230072969 + 3 ^ 40 * 6990261 * 2
def baseEnd_6990261 : Nat := 1196454597792860101796627

theorem tailTrace_6990261 : CollatzResearch.WordTrace tailWord_6990261 prefixEnd_6990261 1196454597792860101796627 := by
  unfold tailWord_6990261
  simp only [CollatzResearch.WordTrace]
  refine ⟨254955764128485713377330637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169970509418990475584887091 254955764128485713377330637)
  ·
    refine ⟨95608411548182142516498989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254955764128485713377330637 95608411548182142516498989)
    ·
      refine ⟨35853154330568303443687121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95608411548182142516498989 35853154330568303443687121)
      ·
        refine ⟨26889865747926227582765341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35853154330568303443687121 26889865747926227582765341)
        ·
          refine ⟨10083699655472335343537003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26889865747926227582765341 10083699655472335343537003)
          ·
            refine ⟨15125549483208503015305505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10083699655472335343537003 15125549483208503015305505)
            ·
              refine ⟨11344162112406377261479129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15125549483208503015305505 11344162112406377261479129)
              ·
                refine ⟨8508121584304782946109347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11344162112406377261479129 8508121584304782946109347)
                ·
                  refine ⟨12762182376457174419164021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8508121584304782946109347 12762182376457174419164021)
                  ·
                    refine ⟨1196454597792860101796627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12762182376457174419164021 1196454597792860101796627)
                    ·
                      rfl

theorem cell23_6990261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_6990261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990261 prefixEnd_6990261 := by exact prefixLift 6990261
  have htrace : WordTrace (prefixWord ++ tailWord_6990261) baseStart_6990261 baseEnd_6990261 := by
    simpa [prefixWord, tailWord_6990261, baseEnd_6990261] using wordTrace_append hprefix tailTrace_6990261
  have hstable : (prefixWord ++ tailWord_6990261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990261).length < 2 ^ (prefixWord ++ tailWord_6990261).sum := by decide
  have hdescent : baseEnd_6990261 < baseStart_6990261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990294 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_6990294 : Nat := 118140960795 + 6990294 * 2 ^ 59
def prefixEnd_6990294 : Nat := 4983230072969 + 3 ^ 40 * 6990294 * 2
def baseEnd_6990294 : Nat := 3589380738240178676277229

theorem tailTrace_6990294 : CollatzResearch.WordTrace tailWord_6990294 prefixEnd_6990294 3589380738240178676277229 := by
  unfold tailWord_6990294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15934810483585385000830121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169971311824910773342187957 15934810483585385000830121)
  ·
    refine ⟨11951107862689038750622591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15934810483585385000830121 11951107862689038750622591)
    ·
      refine ⟨17926661794033558125933887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11951107862689038750622591 17926661794033558125933887)
      ·
        refine ⟨26889992691050337188900831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17926661794033558125933887 26889992691050337188900831)
        ·
          refine ⟨40334989036575505783351247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26889992691050337188900831 40334989036575505783351247)
          ·
            refine ⟨60502483554863258675026871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40334989036575505783351247 60502483554863258675026871)
            ·
              refine ⟨90753725332294888012540307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60502483554863258675026871 90753725332294888012540307)
              ·
                refine ⟨136130587998442332018810461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90753725332294888012540307 136130587998442332018810461)
                ·
                  refine ⟨51048970499415874507053923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136130587998442332018810461 51048970499415874507053923)
                  ·
                    refine ⟨76573455749123811760580885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51048970499415874507053923 76573455749123811760580885)
                    ·
                      refine ⟨3589380738240178676277229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76573455749123811760580885 3589380738240178676277229)
                      ·
                        rfl

theorem cell23_6990294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_6990294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990294 prefixEnd_6990294 := by exact prefixLift 6990294
  have htrace : WordTrace (prefixWord ++ tailWord_6990294) baseStart_6990294 baseEnd_6990294 := by
    simpa [prefixWord, tailWord_6990294, baseEnd_6990294] using wordTrace_append hprefix tailTrace_6990294
  have hstable : (prefixWord ++ tailWord_6990294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990294).length < 2 ^ (prefixWord ++ tailWord_6990294).sum := by decide
  have hdescent : baseEnd_6990294 < baseStart_6990294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990318 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_6990318 : Nat := 118140960795 + 6990318 * 2 ^ 59
def prefixEnd_6990318 : Nat := 4983230072969 + 3 ^ 40 * 6990318 * 2
def baseEnd_6990318 : Nat := 3589393061775886582377119

theorem tailTrace_6990318 : CollatzResearch.WordTrace tailWord_6990318 prefixEnd_6990318 3589393061775886582377119 := by
  unfold tailWord_6990318
  simp only [CollatzResearch.WordTrace]
  refine ⟨31869730386159901514019451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169971895392852808074770405 31869730386159901514019451)
  ·
    refine ⟨47804595579239852271029177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31869730386159901514019451 47804595579239852271029177)
    ·
      refine ⟨35853446684429889203271883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47804595579239852271029177 35853446684429889203271883)
      ·
        refine ⟨53780170026644833804907825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35853446684429889203271883 53780170026644833804907825)
        ·
          refine ⟨40335127519983625353680869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53780170026644833804907825 40335127519983625353680869)
          ·
            refine ⟨7562836409996929753815163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40335127519983625353680869 7562836409996929753815163)
            ·
              refine ⟨11344254614995394630722745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7562836409996929753815163 11344254614995394630722745)
              ·
                refine ⟨8508190961246545973042059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11344254614995394630722745 8508190961246545973042059)
                ·
                  refine ⟨12762286441869818959563089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8508190961246545973042059 12762286441869818959563089)
                  ·
                    refine ⟨9571714831402364219672317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12762286441869818959563089 9571714831402364219672317)
                    ·
                      refine ⟨3589393061775886582377119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9571714831402364219672317 3589393061775886582377119)
                      ·
                        rfl

theorem cell23_6990318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_6990318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990318 prefixEnd_6990318 := by exact prefixLift 6990318
  have htrace : WordTrace (prefixWord ++ tailWord_6990318) baseStart_6990318 baseEnd_6990318 := by
    simpa [prefixWord, tailWord_6990318, baseEnd_6990318] using wordTrace_append hprefix tailTrace_6990318
  have hstable : (prefixWord ++ tailWord_6990318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990318).length < 2 ^ (prefixWord ++ tailWord_6990318).sum := by decide
  have hdescent : baseEnd_6990318 < baseStart_6990318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990341 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 1, 3, 2]
def baseStart_6990341 : Nat := 118140960795 + 6990341 * 2 ^ 59
def prefixEnd_6990341 : Nat := 4983230072969 + 3 ^ 40 * 6990341 * 2
def baseEnd_6990341 : Nat := 3589404871830939992389513

theorem tailTrace_6990341 : CollatzResearch.WordTrace tailWord_6990341 prefixEnd_6990341 3589404871830939992389513 := by
  unfold tailWord_6990341
  simp only [CollatzResearch.WordTrace]
  refine ⟨254958681968195887040242877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169972454645463924693495251 254958681968195887040242877)
  ·
    refine ⟨95609505738073457640091079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254958681968195887040242877 95609505738073457640091079)
    ·
      refine ⟨143414258607110186460136619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95609505738073457640091079 143414258607110186460136619)
      ·
        refine ⟨215121387910665279690204929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143414258607110186460136619 215121387910665279690204929)
        ·
          refine ⟨161341040932998959767653697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215121387910665279690204929 161341040932998959767653697)
          ·
            refine ⟨121005780699749219825740273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161341040932998959767653697 121005780699749219825740273)
            ·
              refine ⟨90754335524811914869305205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121005780699749219825740273 90754335524811914869305205)
              ·
                refine ⟨8508218955451117018997363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90754335524811914869305205 8508218955451117018997363)
                ·
                  refine ⟨12762328433176675528496045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8508218955451117018997363 12762328433176675528496045)
                  ·
                    refine ⟨4785873162441253323186017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12762328433176675528496045 4785873162441253323186017)
                    ·
                      refine ⟨3589404871830939992389513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785873162441253323186017 3589404871830939992389513)
                      ·
                        rfl

theorem cell23_6990341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_6990341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990341 prefixEnd_6990341 := by exact prefixLift 6990341
  have htrace : WordTrace (prefixWord ++ tailWord_6990341) baseStart_6990341 baseEnd_6990341 := by
    simpa [prefixWord, tailWord_6990341, baseEnd_6990341] using wordTrace_append hprefix tailTrace_6990341
  have hstable : (prefixWord ++ tailWord_6990341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990341).length < 2 ^ (prefixWord ++ tailWord_6990341).sum := by decide
  have hdescent : baseEnd_6990341 < baseStart_6990341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990342 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6990342 : Nat := 118140960795 + 6990342 * 2 ^ 59
def prefixEnd_6990342 : Nat := 4983230072969 + 3 ^ 40 * 6990342 * 2
def baseEnd_6990342 : Nat := 1196468461770531496159003

theorem tailTrace_6990342 : CollatzResearch.WordTrace tailWord_6990342 prefixEnd_6990342 1196468461770531496159003 := by
  unfold tailWord_6990342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7967459951287258256594665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169972478960794842807352853 7967459951287258256594665)
  ·
    refine ⟨5975594963465443692445999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7967459951287258256594665 5975594963465443692445999)
    ·
      refine ⟨8963392445198165538668999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5975594963465443692445999 8963392445198165538668999)
      ·
        refine ⟨13445088667797248308003499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8963392445198165538668999 13445088667797248308003499)
        ·
          refine ⟨20167633001695872462005249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13445088667797248308003499 20167633001695872462005249)
          ·
            refine ⟨15125724751271904346503937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20167633001695872462005249 15125724751271904346503937)
            ·
              refine ⟨11344293563453928259877953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15125724751271904346503937 11344293563453928259877953)
              ·
                refine ⟨8508220172590446194908465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11344293563453928259877953 8508220172590446194908465)
                ·
                  refine ⟨6381165129442834646181349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8508220172590446194908465 6381165129442834646181349)
                  ·
                    refine ⟨1196468461770531496159003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6381165129442834646181349 1196468461770531496159003)
                    ·
                      rfl

theorem cell23_6990342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6990342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990342 prefixEnd_6990342 := by exact prefixLift 6990342
  have htrace : WordTrace (prefixWord ++ tailWord_6990342) baseStart_6990342 baseEnd_6990342 := by
    simpa [prefixWord, tailWord_6990342, baseEnd_6990342] using wordTrace_append hprefix tailTrace_6990342
  have hstable : (prefixWord ++ tailWord_6990342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990342).length < 2 ^ (prefixWord ++ tailWord_6990342).sum := by decide
  have hdescent : baseEnd_6990342 < baseStart_6990342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990348 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 2, 1, 3]
def baseStart_6990348 : Nat := 118140960795 + 6990348 * 2 ^ 59
def prefixEnd_6990348 : Nat := 4983230072969 + 3 ^ 40 * 6990348 * 2
def baseEnd_6990348 : Nat := 3589408466195521465001981

theorem tailTrace_6990348 : CollatzResearch.WordTrace tailWord_6990348 prefixEnd_6990348 3589408466195521465001981 := by
  unfold tailWord_6990348
  simp only [CollatzResearch.WordTrace]
  refine ⟨127479468639585263617873849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169972624852780351490498465 127479468639585263617873849)
  ·
    refine ⟨95609601479688947713405387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127479468639585263617873849 95609601479688947713405387)
    ·
      refine ⟨143414402219533421570108081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95609601479688947713405387 143414402219533421570108081)
      ·
        refine ⟨107560801664650066177581061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143414402219533421570108081 107560801664650066177581061)
        ·
          refine ⟨20167650312121887408296449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107560801664650066177581061 20167650312121887408296449)
          ·
            refine ⟨15125737734091415556222337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20167650312121887408296449 15125737734091415556222337)
            ·
              refine ⟨11344303300568561667166753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15125737734091415556222337 11344303300568561667166753)
              ·
                refine ⟨8508227475426421250375065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11344303300568561667166753 8508227475426421250375065)
                ·
                  refine ⟨6381170606569815937781299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8508227475426421250375065 6381170606569815937781299)
                  ·
                    refine ⟨9571755909854723906671949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6381170606569815937781299 9571755909854723906671949)
                    ·
                      refine ⟨3589408466195521465001981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9571755909854723906671949 3589408466195521465001981)
                      ·
                        rfl

theorem cell23_6990348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_6990348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990348 prefixEnd_6990348 := by exact prefixLift 6990348
  have htrace : WordTrace (prefixWord ++ tailWord_6990348) baseStart_6990348 baseEnd_6990348 := by
    simpa [prefixWord, tailWord_6990348, baseEnd_6990348] using wordTrace_append hprefix tailTrace_6990348
  have hstable : (prefixWord ++ tailWord_6990348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990348).length < 2 ^ (prefixWord ++ tailWord_6990348).sum := by decide
  have hdescent : baseEnd_6990348 < baseStart_6990348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990349 : List Nat := [1, 7, 1, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_6990349 : Nat := 118140960795 + 6990349 * 2 ^ 59
def prefixEnd_6990349 : Nat := 4983230072969 + 3 ^ 40 * 6990349 * 2
def baseEnd_6990349 : Nat := 3589408979676175961089477

theorem tailTrace_6990349 : CollatzResearch.WordTrace tailWord_6990349 prefixEnd_6990349 3589408979676175961089477 := by
  unfold tailWord_6990349
  simp only [CollatzResearch.WordTrace]
  refine ⟨254958973752166904406534101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169972649168111269604356067 254958973752166904406534101)
  ·
    refine ⟨5975600947316411822028143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 254958973752166904406534101 5975600947316411822028143)
    ·
      refine ⟨8963401420974617733042215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5975600947316411822028143 8963401420974617733042215)
      ·
        refine ⟨13445102131461926599563323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8963401420974617733042215 13445102131461926599563323)
        ·
          refine ⟨20167653197192889899344985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13445102131461926599563323 20167653197192889899344985)
          ·
            refine ⟨15125739897894667424508739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20167653197192889899344985 15125739897894667424508739)
            ·
              refine ⟨22688609846842001136763109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15125739897894667424508739 22688609846842001136763109)
              ·
                refine ⟨4254114346282875213143083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22688609846842001136763109 4254114346282875213143083)
                ·
                  refine ⟨6381171519424312819714625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4254114346282875213143083 6381171519424312819714625)
                  ·
                    refine ⟨4785878639568234614785969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6381171519424312819714625 4785878639568234614785969)
                    ·
                      refine ⟨3589408979676175961089477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785878639568234614785969 3589408979676175961089477)
                      ·
                        rfl

theorem cell23_6990349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_6990349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990349 prefixEnd_6990349 := by exact prefixLift 6990349
  have htrace : WordTrace (prefixWord ++ tailWord_6990349) baseStart_6990349 baseEnd_6990349 := by
    simpa [prefixWord, tailWord_6990349, baseEnd_6990349] using wordTrace_append hprefix tailTrace_6990349
  have hstable : (prefixWord ++ tailWord_6990349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990349).length < 2 ^ (prefixWord ++ tailWord_6990349).sum := by decide
  have hdescent : baseEnd_6990349 < baseStart_6990349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990364 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_6990364 : Nat := 118140960795 + 6990364 * 2 ^ 59
def prefixEnd_6990364 : Nat := 4983230072969 + 3 ^ 40 * 6990364 * 2
def baseEnd_6990364 : Nat := 1196472227295331134133969

theorem tailTrace_6990364 : CollatzResearch.WordTrace tailWord_6990364 prefixEnd_6990364 1196472227295331134133969 := by
  unfold tailWord_6990364
  simp only [CollatzResearch.WordTrace]
  refine ⟨127479760423556280984165073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169973013898075041312220097 127479760423556280984165073)
  ·
    refine ⟨95609820317667210738123805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127479760423556280984165073 95609820317667210738123805)
    ·
      refine ⟨35853682619125204026796427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95609820317667210738123805 35853682619125204026796427)
      ·
        refine ⟨53780523928687806040194641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35853682619125204026796427 53780523928687806040194641)
        ·
          refine ⟨40335392946515854530145981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53780523928687806040194641 40335392946515854530145981)
          ·
            refine ⟨15125772354943445448804743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40335392946515854530145981 15125772354943445448804743)
            ·
              refine ⟨22688658532415168173207115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15125772354943445448804743 22688658532415168173207115)
              ·
                refine ⟨34032987798622752259810673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22688658532415168173207115 34032987798622752259810673)
                ·
                  refine ⟨25524740848967064194858005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34032987798622752259810673 25524740848967064194858005)
                  ·
                    refine ⟨1196472227295331134133969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25524740848967064194858005 1196472227295331134133969)
                    ·
                      rfl

theorem cell23_6990364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_6990364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990364 prefixEnd_6990364 := by exact prefixLift 6990364
  have htrace : WordTrace (prefixWord ++ tailWord_6990364) baseStart_6990364 baseEnd_6990364 := by
    simpa [prefixWord, tailWord_6990364, baseEnd_6990364] using wordTrace_append hprefix tailTrace_6990364
  have hstable : (prefixWord ++ tailWord_6990364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990364).length < 2 ^ (prefixWord ++ tailWord_6990364).sum := by decide
  have hdescent : baseEnd_6990364 < baseStart_6990364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990371 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 1, 4, 2]
def baseStart_6990371 : Nat := 118140960795 + 6990371 * 2 ^ 59
def prefixEnd_6990371 : Nat := 4983230072969 + 3 ^ 40 * 6990371 * 2
def baseEnd_6990371 : Nat := 3589420276250574875014375

theorem tailTrace_6990371 : CollatzResearch.WordTrace tailWord_6990371 prefixEnd_6990371 3589420276250574875014375 := by
  unfold tailWord_6990371
  simp only [CollatzResearch.WordTrace]
  refine ⟨254959776158087202163834967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169973184105391468109223311 254959776158087202163834967)
  ·
    refine ⟨382439664237130803245752451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254959776158087202163834967 382439664237130803245752451)
    ·
      refine ⟨573659496355696204868628677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382439664237130803245752451 573659496355696204868628677)
      ·
        refine ⟨107561155566693038412867877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 573659496355696204868628677 107561155566693038412867877)
        ·
          refine ⟨20167716668754944702412727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107561155566693038412867877 20167716668754944702412727)
          ·
            refine ⟨30251575003132417053619091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20167716668754944702412727 30251575003132417053619091)
            ·
              refine ⟨45377362504698625580428637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30251575003132417053619091 45377362504698625580428637)
              ·
                refine ⟨17016510939261984592660739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45377362504698625580428637 17016510939261984592660739)
                ·
                  refine ⟨25524766408892976888991109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17016510939261984592660739 25524766408892976888991109)
                  ·
                    refine ⟨4785893701667433166685833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25524766408892976888991109 4785893701667433166685833)
                    ·
                      refine ⟨3589420276250574875014375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785893701667433166685833 3589420276250574875014375)
                      ·
                        rfl

theorem cell23_6990371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_6990371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990371 prefixEnd_6990371 := by exact prefixLift 6990371
  have htrace : WordTrace (prefixWord ++ tailWord_6990371) baseStart_6990371 baseEnd_6990371 := by
    simpa [prefixWord, tailWord_6990371, baseEnd_6990371] using wordTrace_append hprefix tailTrace_6990371
  have hstable : (prefixWord ++ tailWord_6990371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990371).length < 2 ^ (prefixWord ++ tailWord_6990371).sum := by decide
  have hdescent : baseEnd_6990371 < baseStart_6990371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990405 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 2, 2, 2]
def baseStart_6990405 : Nat := 118140960795 + 6990405 * 2 ^ 59
def prefixEnd_6990405 : Nat := 4983230072969 + 3 ^ 40 * 6990405 * 2
def baseEnd_6990405 : Nat := 3589437734592827741989219

theorem tailTrace_6990405 : CollatzResearch.WordTrace tailWord_6990405 prefixEnd_6990405 3589437734592827741989219 := by
  unfold tailWord_6990405
  simp only [CollatzResearch.WordTrace]
  refine ⟨254961016239964025970572669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169974010826642683980381779 254961016239964025970572669)
  ·
    refine ⟨95610381089986509738964751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254961016239964025970572669 95610381089986509738964751)
    ·
      refine ⟨143415571634979764608447127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95610381089986509738964751 143415571634979764608447127)
      ·
        refine ⟨215123357452469646912670691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143415571634979764608447127 215123357452469646912670691)
        ·
          refine ⟨322685036178704470369006037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215123357452469646912670691 322685036178704470369006037)
          ·
            refine ⟨7562930535438386024273579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 322685036178704470369006037 7562930535438386024273579)
            ·
              refine ⟨11344395803157579036410369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7562930535438386024273579 11344395803157579036410369)
              ·
                refine ⟨8508296852368184277307777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11344395803157579036410369 8508296852368184277307777)
                ·
                  refine ⟨6381222639276138207980833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8508296852368184277307777 6381222639276138207980833)
                  ·
                    refine ⟨4785916979457103655985625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6381222639276138207980833 4785916979457103655985625)
                    ·
                      refine ⟨3589437734592827741989219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785916979457103655985625 3589437734592827741989219)
                      ·
                        rfl

theorem cell23_6990405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_6990405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990405 prefixEnd_6990405 := by exact prefixLift 6990405
  have htrace : WordTrace (prefixWord ++ tailWord_6990405) baseStart_6990405 baseEnd_6990405 := by
    simpa [prefixWord, tailWord_6990405, baseEnd_6990405] using wordTrace_append hprefix tailTrace_6990405
  have hstable : (prefixWord ++ tailWord_6990405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990405).length < 2 ^ (prefixWord ++ tailWord_6990405).sum := by decide
  have hdescent : baseEnd_6990405 < baseStart_6990405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990444 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_6990444 : Nat := 118140960795 + 6990444 * 2 ^ 59
def prefixEnd_6990444 : Nat := 4983230072969 + 3 ^ 40 * 6990444 * 2
def baseEnd_6990444 : Nat := 3589457760338353089401539

theorem tailTrace_6990444 : CollatzResearch.WordTrace tailWord_6990444 prefixEnd_6990444 3589457760338353089401539 := by
  unfold tailWord_6990444
  simp only [CollatzResearch.WordTrace]
  refine ⟨127481219343411367815621193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169974959124548490420828257 127481219343411367815621193)
  ·
    refine ⟨95610914507558525861715895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127481219343411367815621193 95610914507558525861715895)
    ·
      refine ⟨143416371761337788792573843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95610914507558525861715895 143416371761337788792573843)
      ·
        refine ⟨215124557642006683188860765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143416371761337788792573843 215124557642006683188860765)
        ·
          refine ⟨80671709115752506195822787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215124557642006683188860765 80671709115752506195822787)
          ·
            refine ⟨121007563673628759293734181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80671709115752506195822787 121007563673628759293734181)
            ·
              refine ⟨22688918188805392367575159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121007563673628759293734181 22688918188805392367575159)
              ·
                refine ⟨34033377283208088551362739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22688918188805392367575159 34033377283208088551362739)
                ·
                  refine ⟨51050065924812132827044109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34033377283208088551362739 51050065924812132827044109)
                  ·
                    refine ⟨19143774721804549810141541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51050065924812132827044109 19143774721804549810141541)
                    ·
                      refine ⟨3589457760338353089401539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19143774721804549810141541 3589457760338353089401539)
                      ·
                        rfl

theorem cell23_6990444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_6990444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990444 prefixEnd_6990444 := by exact prefixLift 6990444
  have htrace : WordTrace (prefixWord ++ tailWord_6990444) baseStart_6990444 baseEnd_6990444 := by
    simpa [prefixWord, tailWord_6990444, baseEnd_6990444] using wordTrace_append hprefix tailTrace_6990444
  have hstable : (prefixWord ++ tailWord_6990444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990444).length < 2 ^ (prefixWord ++ tailWord_6990444).sum := by decide
  have hdescent : baseEnd_6990444 < baseStart_6990444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990521 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 3, 5, 2]
def baseStart_6990521 : Nat := 118140960795 + 6990521 * 2 ^ 59
def prefixEnd_6990521 : Nat := 4983230072969 + 3 ^ 40 * 6990521 * 2
def baseEnd_6990521 : Nat := 3589497298348749288138685

theorem tailTrace_6990521 : CollatzResearch.WordTrace tailWord_6990521 prefixEnd_6990521 3589497298348749288138685 := by
  unfold tailWord_6990521
  simp only [CollatzResearch.WordTrace]
  refine ⟨254965247107543777781795417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169976831405029185187863611 254965247107543777781795417)
  ·
    refine ⟨191223935330657833336346563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254965247107543777781795417 191223935330657833336346563)
    ·
      refine ⟨286835902995986750004519845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191223935330657833336346563 286835902995986750004519845)
      ·
        refine ⟨53781731811747515625847471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286835902995986750004519845 53781731811747515625847471)
        ·
          refine ⟨80672597717621273438771207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53781731811747515625847471 80672597717621273438771207)
          ·
            refine ⟨121008896576431910158156811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80672597717621273438771207 121008896576431910158156811)
            ·
              refine ⟨181513344864647865237235217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121008896576431910158156811 181513344864647865237235217)
              ·
                refine ⟨136135008648485898927926413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181513344864647865237235217 136135008648485898927926413)
                ·
                  refine ⟨51050628243182212097972405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136135008648485898927926413 51050628243182212097972405)
                  ·
                    refine ⟨4785996397798332384184913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51050628243182212097972405 4785996397798332384184913)
                    ·
                      refine ⟨3589497298348749288138685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4785996397798332384184913 3589497298348749288138685)
                      ·
                        rfl

theorem cell23_6990521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_6990521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990521 prefixEnd_6990521 := by exact prefixLift 6990521
  have htrace : WordTrace (prefixWord ++ tailWord_6990521) baseStart_6990521 baseEnd_6990521 := by
    simpa [prefixWord, tailWord_6990521, baseEnd_6990521] using wordTrace_append hprefix tailTrace_6990521
  have hstable : (prefixWord ++ tailWord_6990521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990521).length < 2 ^ (prefixWord ++ tailWord_6990521).sum := by decide
  have hdescent : baseEnd_6990521 < baseStart_6990521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990551 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_6990551 : Nat := 118140960795 + 6990551 * 2 ^ 59
def prefixEnd_6990551 : Nat := 4983230072969 + 3 ^ 40 * 6990551 * 2
def baseEnd_6990551 : Nat := 3589512702768384170763547

theorem tailTrace_6990551 : CollatzResearch.WordTrace tailWord_6990551 prefixEnd_6990551 3589512702768384170763547 := by
  unfold tailWord_6990551
  simp only [CollatzResearch.WordTrace]
  refine ⟨254966341297435092905387507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169977560864956728603591671 254966341297435092905387507)
  ·
    refine ⟨382449511946152639358081261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254966341297435092905387507 382449511946152639358081261)
    ·
      refine ⟨143418566979807239759280473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382449511946152639358081261 143418566979807239759280473)
      ·
        refine ⟨107563925234855429819460355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143418566979807239759280473 107563925234855429819460355)
        ·
          refine ⟨161345887852283144729190533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107563925234855429819460355 161345887852283144729190533)
          ·
            refine ⟨30252353972303089636723225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161345887852283144729190533 30252353972303089636723225)
            ·
              refine ⟨22689265479227317227542419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30252353972303089636723225 22689265479227317227542419)
              ·
                refine ⟨34033898218840975841313629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22689265479227317227542419 34033898218840975841313629)
                ·
                  refine ⟨12762711832065365940492611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34033898218840975841313629 12762711832065365940492611)
                  ·
                    refine ⟨19144067748098048910738917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12762711832065365940492611 19144067748098048910738917)
                    ·
                      refine ⟨3589512702768384170763547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19144067748098048910738917 3589512702768384170763547)
                      ·
                        rfl

theorem cell23_6990551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_6990551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990551 prefixEnd_6990551 := by exact prefixLift 6990551
  have htrace : WordTrace (prefixWord ++ tailWord_6990551) baseStart_6990551 baseEnd_6990551 := by
    simpa [prefixWord, tailWord_6990551, baseEnd_6990551] using wordTrace_append hprefix tailTrace_6990551
  have hstable : (prefixWord ++ tailWord_6990551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990551).length < 2 ^ (prefixWord ++ tailWord_6990551).sum := by decide
  have hdescent : baseEnd_6990551 < baseStart_6990551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990561 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 1, 6]
def baseStart_6990561 : Nat := 118140960795 + 6990561 * 2 ^ 59
def prefixEnd_6990561 : Nat := 4983230072969 + 3 ^ 40 * 6990561 * 2
def baseEnd_6990561 : Nat := 1196505945858309710546167

theorem tailTrace_6990561 : CollatzResearch.WordTrace tailWord_6990561 prefixEnd_6990561 1196505945858309710546167 := by
  unfold tailWord_6990561
  simp only [CollatzResearch.WordTrace]
  refine ⟨254966706027398864613251537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169977804018265909742167691 254966706027398864613251537)
  ·
    refine ⟨191225029520549148459938653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254966706027398864613251537 191225029520549148459938653)
    ·
      refine ⟨71709386070205930672476995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191225029520549148459938653 71709386070205930672476995)
      ·
        refine ⟨107564079105308896008715493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71709386070205930672476995 107564079105308896008715493)
        ·
          refine ⟨20168264832245418001634155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107564079105308896008715493 20168264832245418001634155)
          ·
            refine ⟨30252397248368127002451233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20168264832245418001634155 30252397248368127002451233)
            ·
              refine ⟨22689297936276095251838425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30252397248368127002451233 22689297936276095251838425)
              ·
                refine ⟨17016973452207071438878819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22689297936276095251838425 17016973452207071438878819)
                ·
                  refine ⟨25525460178310607158318229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17016973452207071438878819 25525460178310607158318229)
                  ·
                    refine ⟨1196505945858309710546167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25525460178310607158318229 1196505945858309710546167)
                    ·
                      rfl

theorem cell23_6990561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_6990561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990561 prefixEnd_6990561 := by exact prefixLift 6990561
  have htrace : WordTrace (prefixWord ++ tailWord_6990561) baseStart_6990561 baseEnd_6990561 := by
    simpa [prefixWord, tailWord_6990561, baseEnd_6990561] using wordTrace_append hprefix tailTrace_6990561
  have hstable : (prefixWord ++ tailWord_6990561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990561).length < 2 ^ (prefixWord ++ tailWord_6990561).sum := by decide
  have hdescent : baseEnd_6990561 < baseStart_6990561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990565 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_6990565 : Nat := 118140960795 + 6990565 * 2 ^ 59
def prefixEnd_6990565 : Nat := 4983230072969 + 3 ^ 40 * 6990565 * 2
def baseEnd_6990565 : Nat := 1196506630499182371996161

theorem tailTrace_6990565 : CollatzResearch.WordTrace tailWord_6990565 prefixEnd_6990565 1196506630499182371996161 := by
  unfold tailWord_6990565
  simp only [CollatzResearch.WordTrace]
  refine ⟨254966851919384373296397149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169977901279589582197598099 254966851919384373296397149)
  ·
    refine ⟨95612569469769139986148931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254966851919384373296397149 95612569469769139986148931)
    ·
      refine ⟨143418854204653709979223397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95612569469769139986148931 143418854204653709979223397)
      ·
        refine ⟨26891035163372570621104387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143418854204653709979223397 26891035163372570621104387)
        ·
          refine ⟨40336552745058855931656581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26891035163372570621104387 40336552745058855931656581)
          ·
            refine ⟨7563103639698535487185609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40336552745058855931656581 7563103639698535487185609)
            ·
              refine ⟨5672327729773901615389207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7563103639698535487185609 5672327729773901615389207)
              ·
                refine ⟨8508491594660852423083811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5672327729773901615389207 8508491594660852423083811)
                ·
                  refine ⟨12762737391991278634625717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8508491594660852423083811 12762737391991278634625717)
                  ·
                    refine ⟨1196506630499182371996161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12762737391991278634625717 1196506630499182371996161)
                    ·
                      rfl

theorem cell23_6990565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_6990565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990565 prefixEnd_6990565 := by exact prefixLift 6990565
  have htrace : WordTrace (prefixWord ++ tailWord_6990565) baseStart_6990565 baseEnd_6990565 := by
    simpa [prefixWord, tailWord_6990565, baseEnd_6990565] using wordTrace_append hprefix tailTrace_6990565
  have hstable : (prefixWord ++ tailWord_6990565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990565).length < 2 ^ (prefixWord ++ tailWord_6990565).sum := by decide
  have hdescent : baseEnd_6990565 < baseStart_6990565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990578 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_6990578 : Nat := 118140960795 + 6990578 * 2 ^ 59
def prefixEnd_6990578 : Nat := 4983230072969 + 3 ^ 40 * 6990578 * 2
def baseEnd_6990578 : Nat := 1196508855582018521708641

theorem tailTrace_6990578 : CollatzResearch.WordTrace tailWord_6990578 prefixEnd_6990578 1196508855582018521708641 := by
  unfold tailWord_6990578
  simp only [CollatzResearch.WordTrace]
  refine ⟨63741831517084319129155097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169978217378891517677746925 63741831517084319129155097)
  ·
    refine ⟨47806373637813239346866323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63741831517084319129155097 47806373637813239346866323)
    ·
      refine ⟨71709560456719859020299485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47806373637813239346866323 71709560456719859020299485)
      ·
        refine ⟨26891085171269947132612307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71709560456719859020299485 26891085171269947132612307)
        ·
          refine ⟨40336627756904920698918461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26891085171269947132612307 40336627756904920698918461)
          ·
            refine ⟨15126235408839345262094423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40336627756904920698918461 15126235408839345262094423)
            ·
              refine ⟨22689353113259017893141635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15126235408839345262094423 22689353113259017893141635)
              ·
                refine ⟨34034029669888526839712453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22689353113259017893141635 34034029669888526839712453)
                ·
                  refine ⟨6381380563104098782446085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34034029669888526839712453 6381380563104098782446085)
                  ·
                    refine ⟨1196508855582018521708641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6381380563104098782446085 1196508855582018521708641)
                    ·
                      rfl

theorem cell23_6990578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_6990578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990578 prefixEnd_6990578 := by exact prefixLift 6990578
  have htrace : WordTrace (prefixWord ++ tailWord_6990578) baseStart_6990578 baseEnd_6990578 := by
    simpa [prefixWord, tailWord_6990578, baseEnd_6990578] using wordTrace_append hprefix tailTrace_6990578
  have hstable : (prefixWord ++ tailWord_6990578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990578).length < 2 ^ (prefixWord ++ tailWord_6990578).sum := by decide
  have hdescent : baseEnd_6990578 < baseStart_6990578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990618 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3]
def baseStart_6990618 : Nat := 118140960795 + 6990618 * 2 ^ 59
def prefixEnd_6990618 : Nat := 4983230072969 + 3 ^ 40 * 6990618 * 2
def baseEnd_6990618 : Nat := 3589547105972235408625739

theorem tailTrace_6990618 : CollatzResearch.WordTrace tailWord_6990618 prefixEnd_6990618 3589547105972235408625739 := by
  unfold tailWord_6990618
  simp only [CollatzResearch.WordTrace]
  refine ⟨63742196247048090837019127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169979189992128242232051005 63742196247048090837019127)
  ·
    refine ⟨95613294370572136255528691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63742196247048090837019127 95613294370572136255528691)
    ·
      refine ⟨143419941555858204383293037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95613294370572136255528691 143419941555858204383293037)
      ·
        refine ⟨53782478083446826643734889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143419941555858204383293037 53782478083446826643734889)
        ·
          refine ⟨40336858562585119982801167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53782478083446826643734889 40336858562585119982801167)
          ·
            refine ⟨60505287843877679974201751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40336858562585119982801167 60505287843877679974201751)
            ·
              refine ⟨90757931765816519961302627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60505287843877679974201751 90757931765816519961302627)
              ·
                refine ⟨136136897648724779941953941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90757931765816519961302627 136136897648724779941953941)
                ·
                  refine ⟨6381417077283974059779091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136136897648724779941953941 6381417077283974059779091)
                  ·
                    refine ⟨9572125615925961089668637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6381417077283974059779091 9572125615925961089668637)
                    ·
                      refine ⟨3589547105972235408625739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9572125615925961089668637 3589547105972235408625739)
                      ·
                        rfl

theorem cell23_6990618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_6990618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990618 prefixEnd_6990618 := by exact prefixLift 6990618
  have htrace : WordTrace (prefixWord ++ tailWord_6990618) baseStart_6990618 baseEnd_6990618 := by
    simpa [prefixWord, tailWord_6990618, baseEnd_6990618] using wordTrace_append hprefix tailTrace_6990618
  have hstable : (prefixWord ++ tailWord_6990618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990618).length < 2 ^ (prefixWord ++ tailWord_6990618).sum := by decide
  have hdescent : baseEnd_6990618 < baseStart_6990618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990641 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_6990641 : Nat := 118140960795 + 6990641 * 2 ^ 59
def prefixEnd_6990641 : Nat := 4983230072969 + 3 ^ 40 * 6990641 * 2
def baseEnd_6990641 : Nat := 3589558916027288818638133

theorem tailTrace_6990641 : CollatzResearch.WordTrace tailWord_6990641 prefixEnd_6990641 3589558916027288818638133 := by
  unfold tailWord_6990641
  simp only [CollatzResearch.WordTrace]
  refine ⟨254969623867109038276163777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169979749244739358850775851 254969623867109038276163777)
  ·
    refine ⟨191227217900331778707122833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254969623867109038276163777 191227217900331778707122833)
    ·
      refine ⟨143420413425248834030342125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191227217900331778707122833 143420413425248834030342125)
      ·
        refine ⟨53782655034468312761378297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143420413425248834030342125 53782655034468312761378297)
        ·
          refine ⟨40336991275851234571033723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53782655034468312761378297 40336991275851234571033723)
          ·
            refine ⟨60505486913776851856550585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40336991275851234571033723 60505486913776851856550585)
            ·
              refine ⟨45379115185332638892412939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60505486913776851856550585 45379115185332638892412939)
              ·
                refine ⟨68068672777998958338619409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45379115185332638892412939 68068672777998958338619409)
                ·
                  refine ⟨51051504583499218753964557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68068672777998958338619409 51051504583499218753964557)
                  ·
                    refine ⟨19144314218812207032736709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51051504583499218753964557 19144314218812207032736709)
                    ·
                      refine ⟨3589558916027288818638133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19144314218812207032736709 3589558916027288818638133)
                      ·
                        rfl

theorem cell23_6990641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_6990641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990641 prefixEnd_6990641 := by exact prefixLift 6990641
  have htrace : WordTrace (prefixWord ++ tailWord_6990641) baseStart_6990641 baseEnd_6990641 := by
    simpa [prefixWord, tailWord_6990641, baseEnd_6990641] using wordTrace_append hprefix tailTrace_6990641
  have hstable : (prefixWord ++ tailWord_6990641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990641).length < 2 ^ (prefixWord ++ tailWord_6990641).sum := by decide
  have hdescent : baseEnd_6990641 < baseStart_6990641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990646 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_6990646 : Nat := 118140960795 + 6990646 * 2 ^ 59
def prefixEnd_6990646 : Nat := 4983230072969 + 3 ^ 40 * 6990646 * 2
def baseEnd_6990646 : Nat := 1196520494476853766358537

theorem tailTrace_6990646 : CollatzResearch.WordTrace tailWord_6990646 prefixEnd_6990646 1196520494476853766358537 := by
  unfold tailWord_6990646
  simp only [CollatzResearch.WordTrace]
  refine ⟨15935612889505682758130987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169979870821393949420063861 15935612889505682758130987)
  ·
    refine ⟨23903419334258524137196481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15935612889505682758130987 23903419334258524137196481)
    ·
      refine ⟨17927564500693893102897361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23903419334258524137196481 17927564500693893102897361)
      ·
        refine ⟨13445673375520419827173021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17927564500693893102897361 13445673375520419827173021)
        ·
          refine ⟨5042127515820157435189883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13445673375520419827173021 5042127515820157435189883)
          ·
            refine ⟨7563191273730236152784825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042127515820157435189883 7563191273730236152784825)
            ·
              refine ⟨5672393455297677114588619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7563191273730236152784825 5672393455297677114588619)
              ·
                refine ⟨8508590182946515671882929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5672393455297677114588619 8508590182946515671882929)
                ·
                  refine ⟨6381442637209886753912197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8508590182946515671882929 6381442637209886753912197)
                  ·
                    refine ⟨1196520494476853766358537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6381442637209886753912197 1196520494476853766358537)
                    ·
                      rfl

theorem cell23_6990646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_6990646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990646 prefixEnd_6990646 := by exact prefixLift 6990646
  have htrace : WordTrace (prefixWord ++ tailWord_6990646) baseStart_6990646 baseEnd_6990646 := by
    simpa [prefixWord, tailWord_6990646, baseEnd_6990646] using wordTrace_append hprefix tailTrace_6990646
  have hstable : (prefixWord ++ tailWord_6990646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990646).length < 2 ^ (prefixWord ++ tailWord_6990646).sum := by decide
  have hdescent : baseEnd_6990646 < baseStart_6990646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990661 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_6990661 : Nat := 118140960795 + 6990661 * 2 ^ 59
def prefixEnd_6990661 : Nat := 4983230072969 + 3 ^ 40 * 6990661 * 2
def baseEnd_6990661 : Nat := 3589569185640378740388041

theorem tailTrace_6990661 : CollatzResearch.WordTrace tailWord_6990661 prefixEnd_6990661 3589569185640378740388041 := by
  unfold tailWord_6990661
  simp only [CollatzResearch.WordTrace]
  refine ⟨254970353327036581691891837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169980235551357721127927891 254970353327036581691891837)
  ·
    refine ⟨95613882497638718134459439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254970353327036581691891837 95613882497638718134459439)
    ·
      refine ⟨143420823746458077201689159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95613882497638718134459439 143420823746458077201689159)
      ·
        refine ⟨215131235619687115802533739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143420823746458077201689159 215131235619687115802533739)
        ·
          refine ⟨322696853429530673703800609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215131235619687115802533739 322696853429530673703800609)
          ·
            refine ⟨242022640072148005277850457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322696853429530673703800609 242022640072148005277850457)
            ·
              refine ⟨181516980054111003958387843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242022640072148005277850457 181516980054111003958387843)
              ·
                refine ⟨272275470081166505937581765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181516980054111003958387843 272275470081166505937581765)
                ·
                  refine ⟨51051650640218719863296581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272275470081166505937581765 51051650640218719863296581)
                  ·
                    refine ⟨9572184495041009974368109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51051650640218719863296581 9572184495041009974368109)
                    ·
                      refine ⟨3589569185640378740388041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9572184495041009974368109 3589569185640378740388041)
                      ·
                        rfl

theorem cell23_6990661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_6990661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990661 prefixEnd_6990661 := by exact prefixLift 6990661
  have htrace : WordTrace (prefixWord ++ tailWord_6990661) baseStart_6990661 baseEnd_6990661 := by
    simpa [prefixWord, tailWord_6990661, baseEnd_6990661] using wordTrace_append hprefix tailTrace_6990661
  have hstable : (prefixWord ++ tailWord_6990661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990661).length < 2 ^ (prefixWord ++ tailWord_6990661).sum := by decide
  have hdescent : baseEnd_6990661 < baseStart_6990661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990692 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_6990692 : Nat := 118140960795 + 6990692 * 2 ^ 59
def prefixEnd_6990692 : Nat := 4983230072969 + 3 ^ 40 * 6990692 * 2
def baseEnd_6990692 : Nat := 3589585103540668119100399

theorem tailTrace_6990692 : CollatzResearch.WordTrace tailWord_6990692 prefixEnd_6990692 3589585103540668119100399 := by
  unfold tailWord_6990692
  simp only [CollatzResearch.WordTrace]
  refine ⟨127485741994962136993135165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169980989326616182657513553 127485741994962136993135165)
  ·
    refine ⟨47807153248110801372425687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127485741994962136993135165 47807153248110801372425687)
    ·
      refine ⟨71710729872166202058638531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47807153248110801372425687 71710729872166202058638531)
      ·
        refine ⟨107566094808249303087957797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71710729872166202058638531 107566094808249303087957797)
        ·
          refine ⟨20168642776546744328992087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107566094808249303087957797 20168642776546744328992087)
          ·
            refine ⟨30252964164820116493488131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20168642776546744328992087 30252964164820116493488131)
            ·
              refine ⟨45379446247230174740232197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30252964164820116493488131 45379446247230174740232197)
              ·
                refine ⟨8508646171355657763793537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45379446247230174740232197 8508646171355657763793537)
                ·
                  refine ⟨6381484628516743322845153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8508646171355657763793537 6381484628516743322845153)
                  ·
                    refine ⟨4786113471387557492133865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6381484628516743322845153 4786113471387557492133865)
                    ·
                      refine ⟨3589585103540668119100399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786113471387557492133865 3589585103540668119100399)
                      ·
                        rfl

theorem cell23_6990692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_6990692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990692 prefixEnd_6990692 := by exact prefixLift 6990692
  have htrace : WordTrace (prefixWord ++ tailWord_6990692) baseStart_6990692 baseEnd_6990692 := by
    simpa [prefixWord, tailWord_6990692, baseEnd_6990692] using wordTrace_append hprefix tailTrace_6990692
  have hstable : (prefixWord ++ tailWord_6990692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990692).length < 2 ^ (prefixWord ++ tailWord_6990692).sum := by decide
  have hdescent : baseEnd_6990692 < baseStart_6990692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990701 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_6990701 : Nat := 118140960795 + 6990701 * 2 ^ 59
def prefixEnd_6990701 : Nat := 4983230072969 + 3 ^ 40 * 6990701 * 2
def baseEnd_6990701 : Nat := 3589589724866558583887857

theorem tailTrace_6990701 : CollatzResearch.WordTrace tailWord_6990701 prefixEnd_6990701 3589589724866558583887857 := by
  unfold tailWord_6990701
  simp only [CollatzResearch.WordTrace]
  refine ⟨254971812246891668523347957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169981208164594445682231971 254971812246891668523347957)
  ·
    refine ⟨23903607398146093924063871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254971812246891668523347957 23903607398146093924063871)
    ·
      refine ⟨35855411097219140886095807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23903607398146093924063871 35855411097219140886095807)
      ·
        refine ⟨53783116645828711329143711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35855411097219140886095807 53783116645828711329143711)
        ·
          refine ⟨80674674968743066993715567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53783116645828711329143711 80674674968743066993715567)
          ·
            refine ⟨121012012453114600490573351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80674674968743066993715567 121012012453114600490573351)
            ·
              refine ⟨181518018679671900735860027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121012012453114600490573351 181518018679671900735860027)
              ·
                refine ⟨272277028019507851103790041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181518018679671900735860027 272277028019507851103790041)
                ·
                  refine ⟨204207771014630888327842531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272277028019507851103790041 204207771014630888327842531)
                  ·
                    refine ⟨306311656521946332491763797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204207771014630888327842531 306311656521946332491763797)
                    ·
                      refine ⟨3589589724866558583887857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 306311656521946332491763797 3589589724866558583887857)
                      ·
                        rfl

theorem cell23_6990701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_6990701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990701 prefixEnd_6990701 := by exact prefixLift 6990701
  have htrace : WordTrace (prefixWord ++ tailWord_6990701) baseStart_6990701 baseEnd_6990701 := by
    simpa [prefixWord, tailWord_6990701, baseEnd_6990701] using wordTrace_append hprefix tailTrace_6990701
  have hstable : (prefixWord ++ tailWord_6990701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990701).length < 2 ^ (prefixWord ++ tailWord_6990701).sum := by decide
  have hdescent : baseEnd_6990701 < baseStart_6990701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990711 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 4, 5]
def baseStart_6990711 : Nat := 118140960795 + 6990711 * 2 ^ 59
def prefixEnd_6990711 : Nat := 4983230072969 + 3 ^ 40 * 6990711 * 2
def baseEnd_6990711 : Nat := 1196531619891034514920937

theorem tailTrace_6990711 : CollatzResearch.WordTrace tailWord_6990711 prefixEnd_6990711 1196531619891034514920937 := by
  unfold tailWord_6990711
  simp only [CollatzResearch.WordTrace]
  refine ⟨254972176976855440231211987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169981451317903626820807991 254972176976855440231211987)
  ·
    refine ⟨382458265465283160346817981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254972176976855440231211987 382458265465283160346817981)
    ·
      refine ⟨143421849549481185130056743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382458265465283160346817981 143421849549481185130056743)
      ·
        refine ⟨215132774324221777695085115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143421849549481185130056743 215132774324221777695085115)
        ·
          refine ⟨322699161486332666542627673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215132774324221777695085115 322699161486332666542627673)
          ·
            refine ⟨242024371114749499906970755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322699161486332666542627673 242024371114749499906970755)
            ·
              refine ⟨363036556672124249860456133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242024371114749499906970755 363036556672124249860456133)
              ·
                refine ⟨68069354376023296848835525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363036556672124249860456133 68069354376023296848835525)
                ·
                  refine ⟨12763003945504368159156661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68069354376023296848835525 12763003945504368159156661)
                  ·
                    refine ⟨1196531619891034514920937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12763003945504368159156661 1196531619891034514920937)
                    ·
                      rfl

theorem cell23_6990711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_6990711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990711 prefixEnd_6990711 := by exact prefixLift 6990711
  have htrace : WordTrace (prefixWord ++ tailWord_6990711) baseStart_6990711 baseEnd_6990711 := by
    simpa [prefixWord, tailWord_6990711, baseEnd_6990711] using wordTrace_append hprefix tailTrace_6990711
  have hstable : (prefixWord ++ tailWord_6990711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990711).length < 2 ^ (prefixWord ++ tailWord_6990711).sum := by decide
  have hdescent : baseEnd_6990711 < baseStart_6990711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990728 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 1, 7]
def baseStart_6990728 : Nat := 118140960795 + 6990728 * 2 ^ 59
def prefixEnd_6990728 : Nat := 4983230072969 + 3 ^ 40 * 6990728 * 2
def baseEnd_6990728 : Nat := 1196534529614743326083411

theorem tailTrace_6990728 : CollatzResearch.WordTrace tailWord_6990728 prefixEnd_6990728 1196534529614743326083411 := by
  unfold tailWord_6990728
  simp only [CollatzResearch.WordTrace]
  refine ⟨127486398508896926067290419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169981864678529234756387225 127486398508896926067290419)
  ·
    refine ⟨191229597763345389100935629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127486398508896926067290419 191229597763345389100935629)
    ·
      refine ⟨71711099161254520912850861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191229597763345389100935629 71711099161254520912850861)
      ·
        refine ⟨26891662185470445342319073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71711099161254520912850861 26891662185470445342319073)
        ·
          refine ⟨20168746639102834006739305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26891662185470445342319073 20168746639102834006739305)
          ·
            refine ⟨15126559979327125505054479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20168746639102834006739305 15126559979327125505054479)
            ·
              refine ⟨22689839968990688257581719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15126559979327125505054479 22689839968990688257581719)
              ·
                refine ⟨34034759953486032386372579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22689839968990688257581719 34034759953486032386372579)
                ·
                  refine ⟨51052139930229048579558869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34034759953486032386372579 51052139930229048579558869)
                  ·
                    refine ⟨1196534529614743326083411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51052139930229048579558869 1196534529614743326083411)
                    ·
                      rfl

theorem cell23_6990728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_6990728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990728 prefixEnd_6990728 := by exact prefixLift 6990728
  have htrace : WordTrace (prefixWord ++ tailWord_6990728) baseStart_6990728 baseEnd_6990728 := by
    simpa [prefixWord, tailWord_6990728, baseEnd_6990728] using wordTrace_append hprefix tailTrace_6990728
  have hstable : (prefixWord ++ tailWord_6990728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990728).length < 2 ^ (prefixWord ++ tailWord_6990728).sum := by decide
  have hdescent : baseEnd_6990728 < baseStart_6990728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990761 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_6990761 : Nat := 118140960795 + 6990761 * 2 ^ 59
def prefixEnd_6990761 : Nat := 4983230072969 + 3 ^ 40 * 6990761 * 2
def baseEnd_6990761 : Nat := 3589620533705828349137581

theorem tailTrace_6990761 : CollatzResearch.WordTrace tailWord_6990761 prefixEnd_6990761 3589620533705828349137581 := by
  unfold tailWord_6990761
  simp only [CollatzResearch.WordTrace]
  refine ⟨254974000626674298770532137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169982667084449532513688091 254974000626674298770532137)
  ·
    refine ⟨191230500470005724077899103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254974000626674298770532137 191230500470005724077899103)
    ·
      refine ⟨286845750705008586116848655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191230500470005724077899103 286845750705008586116848655)
      ·
        refine ⟨430268626057512879175272983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286845750705008586116848655 430268626057512879175272983)
        ·
          refine ⟨645402939086269318762909475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430268626057512879175272983 645402939086269318762909475)
          ·
            refine ⟨968104408629403978144364213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645402939086269318762909475 968104408629403978144364213)
            ·
              refine ⟨90759788309006622951034145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 968104408629403978144364213 90759788309006622951034145)
              ·
                refine ⟨68069841231754967213275609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90759788309006622951034145 68069841231754967213275609)
                ·
                  refine ⟨51052380923816225409956707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68069841231754967213275609 51052380923816225409956707)
                  ·
                    refine ⟨76578571385724338114935061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51052380923816225409956707 76578571385724338114935061)
                    ·
                      refine ⟨3589620533705828349137581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76578571385724338114935061 3589620533705828349137581)
                      ·
                        rfl

theorem cell23_6990761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_6990761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990761 prefixEnd_6990761 := by exact prefixLift 6990761
  have htrace : WordTrace (prefixWord ++ tailWord_6990761) baseStart_6990761 baseEnd_6990761 := by
    simpa [prefixWord, tailWord_6990761, baseEnd_6990761] using wordTrace_append hprefix tailTrace_6990761
  have hstable : (prefixWord ++ tailWord_6990761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990761).length < 2 ^ (prefixWord ++ tailWord_6990761).sum := by decide
  have hdescent : baseEnd_6990761 < baseStart_6990761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990802 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_6990802 : Nat := 118140960795 + 6990802 * 2 ^ 59
def prefixEnd_6990802 : Nat := 4983230072969 + 3 ^ 40 * 6990802 * 2
def baseEnd_6990802 : Nat := 3589641586412662688724893

theorem tailTrace_6990802 : CollatzResearch.WordTrace tailWord_6990802 prefixEnd_6990802 3589641586412662688724893 := by
  unfold tailWord_6990802
  simp only [CollatzResearch.WordTrace]
  refine ⟨63743874004881440693193665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169983664013017175181849773 63743874004881440693193665)
  ·
    refine ⟨47807905503661080519895249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63743874004881440693193665 47807905503661080519895249)
    ·
      refine ⟨35855929127745810389921437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47807905503661080519895249 35855929127745810389921437)
      ·
        refine ⟨13445973422904678896220539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35855929127745810389921437 13445973422904678896220539)
        ·
          refine ⟨20168960134357018344330809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13445973422904678896220539 20168960134357018344330809)
          ·
            refine ⟨15126720100767763758248107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20168960134357018344330809 15126720100767763758248107)
            ·
              refine ⟨22690080151151645637372161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15126720100767763758248107 22690080151151645637372161)
              ·
                refine ⟨17017560113363734228029121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22690080151151645637372161 17017560113363734228029121)
                ·
                  refine ⟨12763170085022800671021841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17017560113363734228029121 12763170085022800671021841)
                  ·
                    refine ⟨9572377563767100503266381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12763170085022800671021841 9572377563767100503266381)
                    ·
                      refine ⟨3589641586412662688724893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9572377563767100503266381 3589641586412662688724893)
                      ·
                        rfl

theorem cell23_6990802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_6990802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990802 prefixEnd_6990802 := by exact prefixLift 6990802
  have htrace : WordTrace (prefixWord ++ tailWord_6990802) baseStart_6990802 baseEnd_6990802 := by
    simpa [prefixWord, tailWord_6990802, baseEnd_6990802] using wordTrace_append hprefix tailTrace_6990802
  have hstable : (prefixWord ++ tailWord_6990802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990802).length < 2 ^ (prefixWord ++ tailWord_6990802).sum := by decide
  have hdescent : baseEnd_6990802 < baseStart_6990802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990809 : List Nat := [1, 2, 1, 2, 5, 2, 3, 2, 1, 4]
def baseStart_6990809 : Nat := 118140960795 + 6990809 * 2 ^ 59
def prefixEnd_6990809 : Nat := 4983230072969 + 3 ^ 40 * 6990809 * 2
def baseEnd_6990809 : Nat := 1196548393592414720445787

theorem tailTrace_6990809 : CollatzResearch.WordTrace tailWord_6990809 prefixEnd_6990809 1196548393592414720445787 := by
  unfold tailWord_6990809
  simp only [CollatzResearch.WordTrace]
  refine ⟨254975751330500402968279481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169983834220333601978852987 254975751330500402968279481)
  ·
    refine ⟨191231813497875302226209611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254975751330500402968279481 191231813497875302226209611)
    ·
      refine ⟨286847720246812953339314417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191231813497875302226209611 286847720246812953339314417)
      ·
        refine ⟨215135790185109715004485813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286847720246812953339314417 215135790185109715004485813)
        ·
          refine ⟨20168980329854035781670545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215135790185109715004485813 20168980329854035781670545)
          ·
            refine ⟨15126735247390526836252909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20168980329854035781670545 15126735247390526836252909)
            ·
              refine ⟨5672525717771447563594841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15126735247390526836252909 5672525717771447563594841)
              ·
                refine ⟨4254394288328585672696131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5672525717771447563594841 4254394288328585672696131)
                ·
                  refine ⟨6381591432492878509044197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4254394288328585672696131 6381591432492878509044197)
                  ·
                    refine ⟨1196548393592414720445787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6381591432492878509044197 1196548393592414720445787)
                    ·
                      rfl

theorem cell23_6990809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 4].length) (baseStart_6990809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990809 prefixEnd_6990809 := by exact prefixLift 6990809
  have htrace : WordTrace (prefixWord ++ tailWord_6990809) baseStart_6990809 baseEnd_6990809 := by
    simpa [prefixWord, tailWord_6990809, baseEnd_6990809] using wordTrace_append hprefix tailTrace_6990809
  have hstable : (prefixWord ++ tailWord_6990809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990809).length < 2 ^ (prefixWord ++ tailWord_6990809).sum := by decide
  have hdescent : baseEnd_6990809 < baseStart_6990809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990882 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_6990882 : Nat := 118140960795 + 6990882 * 2 ^ 59
def prefixEnd_6990882 : Nat := 4983230072969 + 3 ^ 40 * 6990882 * 2
def baseEnd_6990882 : Nat := 1196560888288340791908175

theorem tailTrace_6990882 : CollatzResearch.WordTrace tailWord_6990882 prefixEnd_6990882 1196560888288340791908175 := by
  unfold tailWord_6990882
  simp only [CollatzResearch.WordTrace]
  refine ⟨63744603464808984108921725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169985609239490624290457933 63744603464808984108921725)
  ·
    refine ⟨23904226299303369040845647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63744603464808984108921725 23904226299303369040845647)
    ·
      refine ⟨35856339448955053561268471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23904226299303369040845647 35856339448955053561268471)
      ·
        refine ⟨53784509173432580341902707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35856339448955053561268471 53784509173432580341902707)
        ·
          refine ⟨80676763760148870512854061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53784509173432580341902707 80676763760148870512854061)
          ·
            refine ⟨30253786410055826442320273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80676763760148870512854061 30253786410055826442320273)
            ·
              refine ⟨22690339807541869831740205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30253786410055826442320273 22690339807541869831740205)
              ·
                refine ⟨8508877427828201186902577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22690339807541869831740205 8508877427828201186902577)
                ·
                  refine ⟨6381658070871150890176933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8508877427828201186902577 6381658070871150890176933)
                  ·
                    refine ⟨1196560888288340791908175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6381658070871150890176933 1196560888288340791908175)
                    ·
                      rfl

theorem cell23_6990882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_6990882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990882 prefixEnd_6990882 := by exact prefixLift 6990882
  have htrace : WordTrace (prefixWord ++ tailWord_6990882) baseStart_6990882 baseEnd_6990882 := by
    simpa [prefixWord, tailWord_6990882, baseEnd_6990882] using wordTrace_append hprefix tailTrace_6990882
  have hstable : (prefixWord ++ tailWord_6990882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990882).length < 2 ^ (prefixWord ++ tailWord_6990882).sum := by decide
  have hdescent : baseEnd_6990882 < baseStart_6990882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990885 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_6990885 : Nat := 118140960795 + 6990885 * 2 ^ 59
def prefixEnd_6990885 : Nat := 4983230072969 + 3 ^ 40 * 6990885 * 2
def baseEnd_6990885 : Nat := 3589684205306985863987011

theorem tailTrace_6990885 : CollatzResearch.WordTrace tailWord_6990885 prefixEnd_6990885 3589684205306985863987011 := by
  unfold tailWord_6990885
  simp only [CollatzResearch.WordTrace]
  refine ⟨254978523278225067948046109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169985682185483378632030739 254978523278225067948046109)
  ·
    refine ⟨95616946229334400480517291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254978523278225067948046109 95616946229334400480517291)
    ·
      refine ⟨143425419344001600720775937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95616946229334400480517291 143425419344001600720775937)
      ·
        refine ⟨107569064508001200540581953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143425419344001600720775937 107569064508001200540581953)
        ·
          refine ⟨80676798381000900405436465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107569064508001200540581953 80676798381000900405436465)
          ·
            refine ⟨60507598785750675304077349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80676798381000900405436465 60507598785750675304077349)
            ·
              refine ⟨11345174772328251619514503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60507598785750675304077349 11345174772328251619514503)
              ·
                refine ⟨17017762158492377429271755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11345174772328251619514503 17017762158492377429271755)
                ·
                  refine ⟨25526643237738566143907633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17017762158492377429271755 25526643237738566143907633)
                  ·
                    refine ⟨19144982428303924607930725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25526643237738566143907633 19144982428303924607930725)
                    ·
                      refine ⟨3589684205306985863987011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19144982428303924607930725 3589684205306985863987011)
                      ·
                        rfl

theorem cell23_6990885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_6990885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990885 prefixEnd_6990885 := by exact prefixLift 6990885
  have htrace : WordTrace (prefixWord ++ tailWord_6990885) baseStart_6990885 baseEnd_6990885 := by
    simpa [prefixWord, tailWord_6990885, baseEnd_6990885] using wordTrace_append hprefix tailTrace_6990885
  have hstable : (prefixWord ++ tailWord_6990885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990885).length < 2 ^ (prefixWord ++ tailWord_6990885).sum := by decide
  have hdescent : baseEnd_6990885 < baseStart_6990885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990902 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_6990902 : Nat := 118140960795 + 6990902 * 2 ^ 59
def prefixEnd_6990902 : Nat := 4983230072969 + 3 ^ 40 * 6990902 * 2
def baseEnd_6990902 : Nat := 3589692934478112297474433

theorem tailTrace_6990902 : CollatzResearch.WordTrace tailWord_6990902 prefixEnd_6990902 3589692934478112297474433 := by
  unfold tailWord_6990902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936196457447717490713435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169986095546108986567609973 15936196457447717490713435)
  ·
    refine ⟨23904294686171576236070153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15936196457447717490713435 23904294686171576236070153)
    ·
      refine ⟨17928221014628682177052615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23904294686171576236070153 17928221014628682177052615)
      ·
        refine ⟨26892331521943023265578923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17928221014628682177052615 26892331521943023265578923)
        ·
          refine ⟨40338497282914534898368385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26892331521943023265578923 40338497282914534898368385)
          ·
            refine ⟨30253872962185901173776289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40338497282914534898368385 30253872962185901173776289)
            ·
              refine ⟨22690404721639425880332217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30253872962185901173776289 22690404721639425880332217)
              ·
                refine ⟨17017803541229569410249163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22690404721639425880332217 17017803541229569410249163)
                ·
                  refine ⟨25526705311844354115373745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17017803541229569410249163 25526705311844354115373745)
                  ·
                    refine ⟨19145028983883265586530309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25526705311844354115373745 19145028983883265586530309)
                    ·
                      refine ⟨3589692934478112297474433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19145028983883265586530309 3589692934478112297474433)
                      ·
                        rfl

theorem cell23_6990902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_6990902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990902 prefixEnd_6990902 := by exact prefixLift 6990902
  have htrace : WordTrace (prefixWord ++ tailWord_6990902) baseStart_6990902 baseEnd_6990902 := by
    simpa [prefixWord, tailWord_6990902, baseEnd_6990902] using wordTrace_append hprefix tailTrace_6990902
  have hstable : (prefixWord ++ tailWord_6990902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990902).length < 2 ^ (prefixWord ++ tailWord_6990902).sum := by decide
  have hdescent : baseEnd_6990902 < baseStart_6990902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990909 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_6990909 : Nat := 118140960795 + 6990909 * 2 ^ 59
def prefixEnd_6990909 : Nat := 4983230072969 + 3 ^ 40 * 6990909 * 2
def baseEnd_6990909 : Nat := 3589696528842693770086901

theorem tailTrace_6990909 : CollatzResearch.WordTrace tailWord_6990909 prefixEnd_6990909 3589696528842693770086901 := by
  unfold tailWord_6990909
  simp only [CollatzResearch.WordTrace]
  refine ⟨254979398630138120046919781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169986265753425413364613187 254979398630138120046919781)
  ·
    refine ⟨47808637243150897508797459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254979398630138120046919781 47808637243150897508797459)
    ·
      refine ⟨71712955864726346263196189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47808637243150897508797459 71712955864726346263196189)
      ·
        refine ⟨26892358449272379848698571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71712955864726346263196189 26892358449272379848698571)
        ·
          refine ⟨40338537673908569773047857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26892358449272379848698571 40338537673908569773047857)
          ·
            refine ⟨30253903255431427329785893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40338537673908569773047857 30253903255431427329785893)
            ·
              refine ⟨5672606860393392624334855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30253903255431427329785893 5672606860393392624334855)
              ·
                refine ⟨8508910290590088936502283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5672606860393392624334855 8508910290590088936502283)
                ·
                  refine ⟨12763365435885133404753425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8508910290590088936502283 12763365435885133404753425)
                  ·
                    refine ⟨9572524076913850053565069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12763365435885133404753425 9572524076913850053565069)
                    ·
                      refine ⟨3589696528842693770086901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9572524076913850053565069 3589696528842693770086901)
                      ·
                        rfl

theorem cell23_6990909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_6990909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990909 prefixEnd_6990909 := by exact prefixLift 6990909
  have htrace : WordTrace (prefixWord ++ tailWord_6990909) baseStart_6990909 baseEnd_6990909 := by
    simpa [prefixWord, tailWord_6990909, baseEnd_6990909] using wordTrace_append hprefix tailTrace_6990909
  have hstable : (prefixWord ++ tailWord_6990909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990909).length < 2 ^ (prefixWord ++ tailWord_6990909).sum := by decide
  have hdescent : baseEnd_6990909 < baseStart_6990909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990928 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_6990928 : Nat := 118140960795 + 6990928 * 2 ^ 59
def prefixEnd_6990928 : Nat := 4983230072969 + 3 ^ 40 * 6990928 * 2
def baseEnd_6990928 : Nat := 3589706284975129195749313

theorem tailTrace_6990928 : CollatzResearch.WordTrace tailWord_6990928 prefixEnd_6990928 3589706284975129195749313 := by
  unfold tailWord_6990928
  simp only [CollatzResearch.WordTrace]
  refine ⟨127490045808534643145930719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169986727744712857527907625 127490045808534643145930719)
  ·
    refine ⟨191235068712801964718896079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127490045808534643145930719 191235068712801964718896079)
    ·
      refine ⟨286852603069202947078344119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191235068712801964718896079 286852603069202947078344119)
      ·
        refine ⟨430278904603804420617516179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286852603069202947078344119 430278904603804420617516179)
        ·
          refine ⟨645418356905706630926274269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430278904603804420617516179 645418356905706630926274269)
          ·
            refine ⟨242031883839639986597352851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645418356905706630926274269 242031883839639986597352851)
            ·
              refine ⟨363047825759459979896029277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242031883839639986597352851 363047825759459979896029277)
              ·
                refine ⟨136142934659797492461010979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363047825759459979896029277 136142934659797492461010979)
                ·
                  refine ⟨204214401989696238691516469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136142934659797492461010979 204214401989696238691516469)
                  ·
                    refine ⟨19145100186534022377329669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 204214401989696238691516469 19145100186534022377329669)
                    ·
                      refine ⟨3589706284975129195749313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19145100186534022377329669 3589706284975129195749313)
                      ·
                        rfl

theorem cell23_6990928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_6990928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990928 prefixEnd_6990928 := by exact prefixLift 6990928
  have htrace : WordTrace (prefixWord ++ tailWord_6990928) baseStart_6990928 baseEnd_6990928 := by
    simpa [prefixWord, tailWord_6990928, baseEnd_6990928] using wordTrace_append hprefix tailTrace_6990928
  have hstable : (prefixWord ++ tailWord_6990928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990928).length < 2 ^ (prefixWord ++ tailWord_6990928).sum := by decide
  have hdescent : baseEnd_6990928 < baseStart_6990928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990932 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_6990932 : Nat := 118140960795 + 6990932 * 2 ^ 59
def prefixEnd_6990932 : Nat := 4983230072969 + 3 ^ 40 * 6990932 * 2
def baseEnd_6990932 : Nat := 3589708338897747180099295

theorem tailTrace_6990932 : CollatzResearch.WordTrace tailWord_6990932 prefixEnd_6990932 3589708338897747180099295 := by
  unfold tailWord_6990932
  simp only [CollatzResearch.WordTrace]
  refine ⟨127490118754527397487503525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169986825006036529983338033 127490118754527397487503525)
  ·
    refine ⟨23904397266473887028906911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127490118754527397487503525 23904397266473887028906911)
    ·
      refine ⟨35856595899710830543360367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23904397266473887028906911 35856595899710830543360367)
      ·
        refine ⟨53784893849566245815040551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35856595899710830543360367 53784893849566245815040551)
        ·
          refine ⟨80677340774349368722560827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53784893849566245815040551 80677340774349368722560827)
          ·
            refine ⟨121016011161524053083841241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80677340774349368722560827 121016011161524053083841241)
            ·
              refine ⟨90762008371143039812880931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121016011161524053083841241 90762008371143039812880931)
              ·
                refine ⟨136143012556714559719321397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90762008371143039812880931 136143012556714559719321397)
                ·
                  refine ⟨12763407427191989973686381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136143012556714559719321397 12763407427191989973686381)
                  ·
                    refine ⟨4786277785196996240132393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12763407427191989973686381 4786277785196996240132393)
                    ·
                      refine ⟨3589708338897747180099295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786277785196996240132393 3589708338897747180099295)
                      ·
                        rfl

theorem cell23_6990932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_6990932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990932 prefixEnd_6990932 := by exact prefixLift 6990932
  have htrace : WordTrace (prefixWord ++ tailWord_6990932) baseStart_6990932 baseEnd_6990932 := by
    simpa [prefixWord, tailWord_6990932, baseEnd_6990932] using wordTrace_append hprefix tailTrace_6990932
  have hstable : (prefixWord ++ tailWord_6990932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990932).length < 2 ^ (prefixWord ++ tailWord_6990932).sum := by decide
  have hdescent : baseEnd_6990932 < baseStart_6990932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990938 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_6990938 : Nat := 118140960795 + 6990938 * 2 ^ 59
def prefixEnd_6990938 : Nat := 4983230072969 + 3 ^ 40 * 6990938 * 2
def baseEnd_6990938 : Nat := 1196570473260558052208089

theorem tailTrace_6990938 : CollatzResearch.WordTrace tailWord_6990938 prefixEnd_6990938 1196570473260558052208089 := by
  unfold tailWord_6990938
  simp only [CollatzResearch.WordTrace]
  refine ⟨63745114086758264499931367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169986970898022038666483645 63745114086758264499931367)
  ·
    refine ⟨95617671130137396749897051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63745114086758264499931367 95617671130137396749897051)
    ·
      refine ⟨143426506695206095124845577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95617671130137396749897051 143426506695206095124845577)
      ·
        refine ⟨107569880021404571343634183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143426506695206095124845577 107569880021404571343634183)
        ·
          refine ⟨161354820032106857015451275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107569880021404571343634183 161354820032106857015451275)
          ·
            refine ⟨242032230048160285523176913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161354820032106857015451275 242032230048160285523176913)
            ·
              refine ⟨181524172536120214142382685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242032230048160285523176913 181524172536120214142382685)
              ·
                refine ⟨68071564701045080303393507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181524172536120214142382685 68071564701045080303393507)
                ·
                  refine ⟨102107347051567620455090261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68071564701045080303393507 102107347051567620455090261)
                  ·
                    refine ⟨1196570473260558052208089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102107347051567620455090261 1196570473260558052208089)
                    ·
                      rfl

theorem cell23_6990938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_6990938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990938 prefixEnd_6990938 := by exact prefixLift 6990938
  have htrace : WordTrace (prefixWord ++ tailWord_6990938) baseStart_6990938 baseEnd_6990938 := by
    simpa [prefixWord, tailWord_6990938, baseEnd_6990938] using wordTrace_append hprefix tailTrace_6990938
  have hstable : (prefixWord ++ tailWord_6990938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990938).length < 2 ^ (prefixWord ++ tailWord_6990938).sum := by decide
  have hdescent : baseEnd_6990938 < baseStart_6990938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990949 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 1, 3, 2]
def baseStart_6990949 : Nat := 118140960795 + 6990949 * 2 ^ 59
def prefixEnd_6990949 : Nat := 4983230072969 + 3 ^ 40 * 6990949 * 2
def baseEnd_6990949 : Nat := 3589717068068873613586717

theorem tailTrace_6990949 : CollatzResearch.WordTrace tailWord_6990949 prefixEnd_6990949 3589717068068873613586717 := by
  unfold tailWord_6990949
  simp only [CollatzResearch.WordTrace]
  refine ⟨254980857549993206878375901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169987238366662137918917267 254980857549993206878375901)
  ·
    refine ⟨95617821581247452579390963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254980857549993206878375901 95617821581247452579390963)
    ·
      refine ⟨143426732371871178869086445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95617821581247452579390963 143426732371871178869086445)
      ·
        refine ⟨53785024639451692075907417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143426732371871178869086445 53785024639451692075907417)
        ·
          refine ⟨40338768479588769056930563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53785024639451692075907417 40338768479588769056930563)
          ·
            refine ⟨60508152719383153585395845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40338768479588769056930563 60508152719383153585395845)
            ·
              refine ⟨11345278634884341297261721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60508152719383153585395845 11345278634884341297261721)
              ·
                refine ⟨8508958976163255972946291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11345278634884341297261721 8508958976163255972946291)
                ·
                  refine ⟨12763438464244883959419437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8508958976163255972946291 12763438464244883959419437)
                  ·
                    refine ⟨4786289424091831484782289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12763438464244883959419437 4786289424091831484782289)
                    ·
                      refine ⟨3589717068068873613586717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786289424091831484782289 3589717068068873613586717)
                      ·
                        rfl

theorem cell23_6990949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_6990949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990949 prefixEnd_6990949 := by exact prefixLift 6990949
  have htrace : WordTrace (prefixWord ++ tailWord_6990949) baseStart_6990949 baseEnd_6990949 := by
    simpa [prefixWord, tailWord_6990949, baseEnd_6990949] using wordTrace_append hprefix tailTrace_6990949
  have hstable : (prefixWord ++ tailWord_6990949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990949).length < 2 ^ (prefixWord ++ tailWord_6990949).sum := by decide
  have hdescent : baseEnd_6990949 < baseStart_6990949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990962 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_6990962 : Nat := 118140960795 + 6990962 * 2 ^ 59
def prefixEnd_6990962 : Nat := 4983230072969 + 3 ^ 40 * 6990962 * 2
def baseEnd_6990962 : Nat := 3589723743317382062724157

theorem tailTrace_6990962 : CollatzResearch.WordTrace tailWord_6990962 prefixEnd_6990962 3589723743317382062724157 := by
  unfold tailWord_6990962
  simp only [CollatzResearch.WordTrace]
  refine ⟨63745332924736527524649785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169987554465964073399066093 63745332924736527524649785)
  ·
    refine ⟨47808999693552395643487339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63745332924736527524649785 47808999693552395643487339)
    ·
      refine ⟨71713499540328593465231009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47808999693552395643487339 71713499540328593465231009)
      ·
        refine ⟨53785124655246445098923257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71713499540328593465231009 53785124655246445098923257)
        ·
          refine ⟨40338843491434833824192443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53785124655246445098923257 40338843491434833824192443)
          ·
            refine ⟨60508265237152250736288665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40338843491434833824192443 60508265237152250736288665)
            ·
              refine ⟨45381198927864188052216499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60508265237152250736288665 45381198927864188052216499)
              ·
                refine ⟨68071798391796282078324749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45381198927864188052216499 68071798391796282078324749)
                ·
                  refine ⟨25526924396923605779371781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68071798391796282078324749 25526924396923605779371781)
                  ·
                    refine ⟨4786298324423176083632209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25526924396923605779371781 4786298324423176083632209)
                    ·
                      refine ⟨3589723743317382062724157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786298324423176083632209 3589723743317382062724157)
                      ·
                        rfl

theorem cell23_6990962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_6990962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990962 prefixEnd_6990962 := by exact prefixLift 6990962
  have htrace : WordTrace (prefixWord ++ tailWord_6990962) baseStart_6990962 baseEnd_6990962 := by
    simpa [prefixWord, tailWord_6990962, baseEnd_6990962] using wordTrace_append hprefix tailTrace_6990962
  have hstable : (prefixWord ++ tailWord_6990962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990962).length < 2 ^ (prefixWord ++ tailWord_6990962).sum := by decide
  have hdescent : baseEnd_6990962 < baseStart_6990962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990968 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 9]
def baseStart_6990968 : Nat := 118140960795 + 6990968 * 2 ^ 59
def prefixEnd_6990968 : Nat := 4983230072969 + 3 ^ 40 * 6990968 * 2
def baseEnd_6990968 : Nat := 398858536022367671027681

theorem tailTrace_6990968 : CollatzResearch.WordTrace tailWord_6990968 prefixEnd_6990968 398858536022367671027681 := by
  unfold tailWord_6990968
  simp only [CollatzResearch.WordTrace]
  refine ⟨127490775268462186561658779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169987700357949582082211705 127490775268462186561658779)
  ·
    refine ⟨191236162902693279842488169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127490775268462186561658779 191236162902693279842488169)
    ·
      refine ⟨143427122177019959881866127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191236162902693279842488169 143427122177019959881866127)
      ·
        refine ⟨215140683265529939822799191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143427122177019959881866127 215140683265529939822799191)
        ·
          refine ⟨322711024898294909734198787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215140683265529939822799191 322711024898294909734198787)
          ·
            refine ⟨484066537347442364601298181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322711024898294909734198787 484066537347442364601298181)
            ·
              refine ⟨90762475752645443362743409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 484066537347442364601298181 90762475752645443362743409)
              ·
                refine ⟨68071856814484082522057557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90762475752645443362743409 68071856814484082522057557)
                ·
                  refine ⟨398858536022367671027681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68071856814484082522057557 398858536022367671027681)
                  ·
                    rfl

theorem cell23_6990968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 9].length) (baseStart_6990968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990968 prefixEnd_6990968 := by exact prefixLift 6990968
  have htrace : WordTrace (prefixWord ++ tailWord_6990968) baseStart_6990968 baseEnd_6990968 := by
    simpa [prefixWord, tailWord_6990968, baseEnd_6990968] using wordTrace_append hprefix tailTrace_6990968
  have hstable : (prefixWord ++ tailWord_6990968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990968).length < 2 ^ (prefixWord ++ tailWord_6990968).sum := by decide
  have hdescent : baseEnd_6990968 < baseStart_6990968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990974 : List Nat := [4, 2, 4, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6990974 : Nat := 118140960795 + 6990974 * 2 ^ 59
def prefixEnd_6990974 : Nat := 4983230072969 + 3 ^ 40 * 6990974 * 2
def baseEnd_6990974 : Nat := 3589729905085236015774103

theorem tailTrace_6990974 : CollatzResearch.WordTrace tailWord_6990974 prefixEnd_6990974 3589729905085236015774103 := by
  unfold tailWord_6990974
  simp only [CollatzResearch.WordTrace]
  refine ⟨31872721171862829518504497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169987846249935090765357317 31872721171862829518504497)
  ·
    refine ⟨23904540878897122138878373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31872721171862829518504497 23904540878897122138878373)
    ·
      refine ⟨4482101414793210401039695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23904540878897122138878373 4482101414793210401039695)
      ·
        refine ⟨6723152122189815601559543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482101414793210401039695 6723152122189815601559543)
        ·
          refine ⟨10084728183284723402339315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6723152122189815601559543 10084728183284723402339315)
          ·
            refine ⟨15127092274927085103508973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10084728183284723402339315 15127092274927085103508973)
            ·
              refine ⟨5672659603097656913815865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15127092274927085103508973 5672659603097656913815865)
              ·
                refine ⟨4254494702323242685361899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5672659603097656913815865 4254494702323242685361899)
                ·
                  refine ⟨6381742053484864028042849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4254494702323242685361899 6381742053484864028042849)
                  ·
                    refine ⟨4786306540113648021032137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6381742053484864028042849 4786306540113648021032137)
                    ·
                      refine ⟨3589729905085236015774103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786306540113648021032137 3589729905085236015774103)
                      ·
                        rfl

theorem cell23_6990974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6990974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990974 prefixEnd_6990974 := by exact prefixLift 6990974
  have htrace : WordTrace (prefixWord ++ tailWord_6990974) baseStart_6990974 baseEnd_6990974 := by
    simpa [prefixWord, tailWord_6990974, baseEnd_6990974] using wordTrace_append hprefix tailTrace_6990974
  have hstable : (prefixWord ++ tailWord_6990974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990974).length < 2 ^ (prefixWord ++ tailWord_6990974).sum := by decide
  have hdescent : baseEnd_6990974 < baseStart_6990974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990979 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 2, 2, 2]
def baseStart_6990979 : Nat := 118140960795 + 6990979 * 2 ^ 59
def prefixEnd_6990979 : Nat := 4983230072969 + 3 ^ 40 * 6990979 * 2
def baseEnd_6990979 : Nat := 3589732472488508496211579

theorem tailTrace_6990979 : CollatzResearch.WordTrace tailWord_6990979 prefixEnd_6990979 3589732472488508496211579 := by
  unfold tailWord_6990979
  simp only [CollatzResearch.WordTrace]
  refine ⟨254981951739884522001967991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169987967826589681334645327 254981951739884522001967991)
  ·
    refine ⟨382472927609826783002951987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254981951739884522001967991 382472927609826783002951987)
    ·
      refine ⟨573709391414740174504427981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382472927609826783002951987 573709391414740174504427981)
      ·
        refine ⟨215141021780527565439160493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 573709391414740174504427981 215141021780527565439160493)
        ·
          refine ⟨80677883167697837039685185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215141021780527565439160493 80677883167697837039685185)
          ·
            refine ⟨60508412375773377779763889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80677883167697837039685185 60508412375773377779763889)
            ·
              refine ⟨45381309281830033334822917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60508412375773377779763889 45381309281830033334822917)
              ·
                refine ⟨8508995490343131250279297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45381309281830033334822917 8508995490343131250279297)
                ·
                  refine ⟨6381746617757348437709473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8508995490343131250279297 6381746617757348437709473)
                  ·
                    refine ⟨4786309963318011328282105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6381746617757348437709473 4786309963318011328282105)
                    ·
                      refine ⟨3589732472488508496211579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786309963318011328282105 3589732472488508496211579)
                      ·
                        rfl

theorem cell23_6990979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_6990979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990979 prefixEnd_6990979 := by exact prefixLift 6990979
  have htrace : WordTrace (prefixWord ++ tailWord_6990979) baseStart_6990979 baseEnd_6990979 := by
    simpa [prefixWord, tailWord_6990979, baseEnd_6990979] using wordTrace_append hprefix tailTrace_6990979
  have hstable : (prefixWord ++ tailWord_6990979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990979).length < 2 ^ (prefixWord ++ tailWord_6990979).sum := by decide
  have hdescent : baseEnd_6990979 < baseStart_6990979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990985 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 7]
def baseStart_6990985 : Nat := 118140960795 + 6990985 * 2 ^ 59
def prefixEnd_6990985 : Nat := 4983230072969 + 3 ^ 40 * 6990985 * 2
def baseEnd_6990985 : Nat := 398859505930270608081839

theorem tailTrace_6990985 : CollatzResearch.WordTrace tailWord_6990985 prefixEnd_6990985 398859505930270608081839 := by
  unfold tailWord_6990985
  simp only [CollatzResearch.WordTrace]
  refine ⟨254982170577862785026686409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169988113718575190017790939 254982170577862785026686409)
  ·
    refine ⟨191236627933397088770014807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254982170577862785026686409 191236627933397088770014807)
    ·
      refine ⟨286854941900095633155022211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191236627933397088770014807 286854941900095633155022211)
      ·
        refine ⟨430282412850143449732533317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286854941900095633155022211 430282412850143449732533317)
        ·
          refine ⟨80677952409401896824849997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430282412850143449732533317 80677952409401896824849997)
          ·
            refine ⟨30254232153525711309318749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80677952409401896824849997 30254232153525711309318749)
            ·
              refine ⟨11345337057572141740994531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30254232153525711309318749 11345337057572141740994531)
              ·
                refine ⟨17018005586358212611491797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11345337057572141740994531 17018005586358212611491797)
                ·
                  refine ⟨398859505930270608081839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17018005586358212611491797 398859505930270608081839)
                  ·
                    rfl

theorem cell23_6990985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 7].length) (baseStart_6990985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990985 prefixEnd_6990985 := by exact prefixLift 6990985
  have htrace : WordTrace (prefixWord ++ tailWord_6990985) baseStart_6990985 baseEnd_6990985 := by
    simpa [prefixWord, tailWord_6990985, baseEnd_6990985] using wordTrace_append hprefix tailTrace_6990985
  have hstable : (prefixWord ++ tailWord_6990985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990985).length < 2 ^ (prefixWord ++ tailWord_6990985).sum := by decide
  have hdescent : baseEnd_6990985 < baseStart_6990985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6990995 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 3]
def baseStart_6990995 : Nat := 118140960795 + 6990995 * 2 ^ 59
def prefixEnd_6990995 : Nat := 4983230072969 + 3 ^ 40 * 6990995 * 2
def baseEnd_6990995 : Nat := 3589740688178980433611505

theorem tailTrace_6990995 : CollatzResearch.WordTrace tailWord_6990995 prefixEnd_6990995 3589740688178980433611505 := by
  unfold tailWord_6990995
  simp only [CollatzResearch.WordTrace]
  refine ⟨254982535307826556734550439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169988356871884371156366959 254982535307826556734550439)
  ·
    refine ⟨382473802961739835101825659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254982535307826556734550439 382473802961739835101825659)
    ·
      refine ⟨573710704442609752652738489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382473802961739835101825659 573710704442609752652738489)
      ·
        refine ⟨430283028331957314489553867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573710704442609752652738489 430283028331957314489553867)
        ·
          refine ⟨645424542497935971734330801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430283028331957314489553867 645424542497935971734330801)
          ·
            refine ⟨484068406873451978800748101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645424542497935971734330801 484068406873451978800748101)
            ·
              refine ⟨90762826288772246025140269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 484068406873451978800748101 90762826288772246025140269)
              ·
                refine ⟨34036059858289592259427601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90762826288772246025140269 34036059858289592259427601)
                ·
                  refine ⟨25527044893717194194570701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34036059858289592259427601 25527044893717194194570701)
                  ·
                    refine ⟨9572641835143947822964013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25527044893717194194570701 9572641835143947822964013)
                    ·
                      refine ⟨3589740688178980433611505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9572641835143947822964013 3589740688178980433611505)
                      ·
                        rfl

theorem cell23_6990995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_6990995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6990995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6990995 prefixEnd_6990995 := by exact prefixLift 6990995
  have htrace : WordTrace (prefixWord ++ tailWord_6990995) baseStart_6990995 baseEnd_6990995 := by
    simpa [prefixWord, tailWord_6990995, baseEnd_6990995] using wordTrace_append hprefix tailTrace_6990995
  have hstable : (prefixWord ++ tailWord_6990995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6990995).length < 2 ^ (prefixWord ++ tailWord_6990995).sum := by decide
  have hdescent : baseEnd_6990995 < baseStart_6990995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6990995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991035 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 4]
def baseStart_6991035 : Nat := 118140960795 + 6991035 * 2 ^ 59
def prefixEnd_6991035 : Nat := 4983230072969 + 3 ^ 40 * 6991035 * 2
def baseEnd_6991035 : Nat := 3589761227405160277111321

theorem tailTrace_6991035 : CollatzResearch.WordTrace tailWord_6991035 prefixEnd_6991035 3589761227405160277111321 := by
  unfold tailWord_6991035
  simp only [CollatzResearch.WordTrace]
  refine ⟨254983994227681643566006559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169989329485121095710671039 254983994227681643566006559)
  ·
    refine ⟨382475991341522465349009839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254983994227681643566006559 382475991341522465349009839)
    ·
      refine ⟨573713987012283698023514759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382475991341522465349009839 573713987012283698023514759)
      ·
        refine ⟨860570980518425547035272139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573713987012283698023514759 860570980518425547035272139)
        ·
          refine ⟨1290856470777638320552908209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860570980518425547035272139 1290856470777638320552908209)
          ·
            refine ⟨968142353083228740414681157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290856470777638320552908209 968142353083228740414681157)
            ·
              refine ⟨181526691203105388827752717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 968142353083228740414681157 181526691203105388827752717)
              ·
                refine ⟨68072509201164520810407269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181526691203105388827752717 68072509201164520810407269)
                ·
                  refine ⟨12763595475218347651951363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68072509201164520810407269 12763595475218347651951363)
                  ·
                    refine ⟨19145393212827521477927045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12763595475218347651951363 19145393212827521477927045)
                    ·
                      refine ⟨3589761227405160277111321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19145393212827521477927045 3589761227405160277111321)
                      ·
                        rfl

theorem cell23_6991035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 4].length) (baseStart_6991035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991035 prefixEnd_6991035 := by exact prefixLift 6991035
  have htrace : WordTrace (prefixWord ++ tailWord_6991035) baseStart_6991035 baseEnd_6991035 := by
    simpa [prefixWord, tailWord_6991035, baseEnd_6991035] using wordTrace_append hprefix tailTrace_6991035
  have hstable : (prefixWord ++ tailWord_6991035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991035).length < 2 ^ (prefixWord ++ tailWord_6991035).sum := by decide
  have hdescent : baseEnd_6991035 < baseStart_6991035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991036 : List Nat := [2, 2, 2, 3, 2, 3, 2, 2, 5]
def baseStart_6991036 : Nat := 118140960795 + 6991036 * 2 ^ 59
def prefixEnd_6991036 : Nat := 4983230072969 + 3 ^ 40 * 6991036 * 2
def baseEnd_6991036 : Nat := 398862415653979419244313

theorem tailTrace_6991036 : CollatzResearch.WordTrace tailWord_6991036 prefixEnd_6991036 398862415653979419244313 := by
  unfold tailWord_6991036
  simp only [CollatzResearch.WordTrace]
  refine ⟨127492015350339010368396481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169989353800452013824528641 127492015350339010368396481)
  ·
    refine ⟨95619011512754257776297361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127492015350339010368396481 95619011512754257776297361)
    ·
      refine ⟨71714258634565693332223021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95619011512754257776297361 71714258634565693332223021)
      ·
        refine ⟨26892846987962134999583633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71714258634565693332223021 26892846987962134999583633)
        ·
          refine ⟨20169635240971601249687725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26892846987962134999583633 20169635240971601249687725)
          ·
            refine ⟨7563613215364350468632897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20169635240971601249687725 7563613215364350468632897)
            ·
              refine ⟨5672709911523262851474673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7563613215364350468632897 5672709911523262851474673)
              ·
                refine ⟨4254532433642447138606005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5672709911523262851474673 4254532433642447138606005)
                ·
                  refine ⟨398862415653979419244313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4254532433642447138606005 398862415653979419244313)
                  ·
                    rfl

theorem cell23_6991036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_6991036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991036 prefixEnd_6991036 := by exact prefixLift 6991036
  have htrace : WordTrace (prefixWord ++ tailWord_6991036) baseStart_6991036 baseEnd_6991036 := by
    simpa [prefixWord, tailWord_6991036, baseEnd_6991036] using wordTrace_append hprefix tailTrace_6991036
  have hstable : (prefixWord ++ tailWord_6991036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991036).length < 2 ^ (prefixWord ++ tailWord_6991036).sum := by decide
  have hdescent : baseEnd_6991036 < baseStart_6991036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991069 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6991069 : Nat := 118140960795 + 6991069 * 2 ^ 59
def prefixEnd_6991069 : Nat := 4983230072969 + 3 ^ 40 * 6991069 * 2
def baseEnd_6991069 : Nat := 3589778685747413144086165

theorem tailTrace_6991069 : CollatzResearch.WordTrace tailWord_6991069 prefixEnd_6991069 3589778685747413144086165 := by
  unfold tailWord_6991069
  simp only [CollatzResearch.WordTrace]
  refine ⟨254985234309558467372744261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169990156206372311581829507 254985234309558467372744261)
  ·
    refine ⟨47809731433042212632389549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254985234309558467372744261 47809731433042212632389549)
    ·
      refine ⟨17928649287390829737146081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47809731433042212632389549 17928649287390829737146081)
      ·
        refine ⟨13446486965543122302859561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17928649287390829737146081 13446486965543122302859561)
        ·
          refine ⟨10084865224157341727144671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13446486965543122302859561 10084865224157341727144671)
          ·
            refine ⟨15127297836236012590717007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10084865224157341727144671 15127297836236012590717007)
            ·
              refine ⟨22690946754354018886075511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15127297836236012590717007 22690946754354018886075511)
              ·
                refine ⟨34036420131531028329113267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22690946754354018886075511 34036420131531028329113267)
                ·
                  refine ⟨51054630197296542493669901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34036420131531028329113267 51054630197296542493669901)
                  ·
                    refine ⟨19145486323986203435126213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51054630197296542493669901 19145486323986203435126213)
                    ·
                      refine ⟨3589778685747413144086165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19145486323986203435126213 3589778685747413144086165)
                      ·
                        rfl

theorem cell23_6991069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6991069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991069 prefixEnd_6991069 := by exact prefixLift 6991069
  have htrace : WordTrace (prefixWord ++ tailWord_6991069) baseStart_6991069 baseEnd_6991069 := by
    simpa [prefixWord, tailWord_6991069, baseEnd_6991069] using wordTrace_append hprefix tailTrace_6991069
  have hstable : (prefixWord ++ tailWord_6991069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991069).length < 2 ^ (prefixWord ++ tailWord_6991069).sum := by decide
  have hdescent : baseEnd_6991069 < baseStart_6991069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991072 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 3]
def baseStart_6991072 : Nat := 118140960795 + 6991072 * 2 ^ 59
def prefixEnd_6991072 : Nat := 4983230072969 + 3 ^ 40 * 6991072 * 2
def baseEnd_6991072 : Nat := 3589780226189376632348651

theorem tailTrace_6991072 : CollatzResearch.WordTrace tailWord_6991072 prefixEnd_6991072 3589780226189376632348651 := by
  unfold tailWord_6991072
  simp only [CollatzResearch.WordTrace]
  refine ⟨127492671864273799442551735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169990229152365065923402313 127492671864273799442551735)
  ·
    refine ⟨191239007796410699163827603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127492671864273799442551735 191239007796410699163827603)
    ·
      refine ⟨286858511694616048745741405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191239007796410699163827603 286858511694616048745741405)
      ·
        refine ⟨107571941885481018279653027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286858511694616048745741405 107571941885481018279653027)
        ·
          refine ⟨161357912828221527419479541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107571941885481018279653027 161357912828221527419479541)
          ·
            refine ⟨15127304327645768195576207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161357912828221527419479541 15127304327645768195576207)
            ·
              refine ⟨22690956491468652293364311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15127304327645768195576207 22690956491468652293364311)
              ·
                refine ⟨34036434737202978440046467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22690956491468652293364311 34036434737202978440046467)
                ·
                  refine ⟨51054652105804467660069701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34036434737202978440046467 51054652105804467660069701)
                  ·
                    refine ⟨9572747269838337686263069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51054652105804467660069701 9572747269838337686263069)
                    ·
                      refine ⟨3589780226189376632348651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9572747269838337686263069 3589780226189376632348651)
                      ·
                        rfl

theorem cell23_6991072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_6991072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991072 prefixEnd_6991072 := by exact prefixLift 6991072
  have htrace : WordTrace (prefixWord ++ tailWord_6991072) baseStart_6991072 baseEnd_6991072 := by
    simpa [prefixWord, tailWord_6991072, baseEnd_6991072] using wordTrace_append hprefix tailTrace_6991072
  have hstable : (prefixWord ++ tailWord_6991072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991072).length < 2 ^ (prefixWord ++ tailWord_6991072).sum := by decide
  have hdescent : baseEnd_6991072 < baseStart_6991072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991146 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6991146 : Nat := 118140960795 + 6991146 * 2 ^ 59
def prefixEnd_6991146 : Nat := 4983230072969 + 3 ^ 40 * 6991146 * 2
def baseEnd_6991146 : Nat := 3589818223757809342823311

theorem tailTrace_6991146 : CollatzResearch.WordTrace tailWord_6991146 prefixEnd_6991146 3589818223757809342823311 := by
  unfold tailWord_6991146
  simp only [CollatzResearch.WordTrace]
  refine ⟨63747010682569877380824323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169992028486853006348864861 63747010682569877380824323)
  ·
    refine ⟨95620516023854816071236485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63747010682569877380824323 95620516023854816071236485)
    ·
      refine ⟨17928846754472778013356841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95620516023854816071236485 17928846754472778013356841)
      ·
        refine ⟨13446635065854583510017631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17928846754472778013356841 13446635065854583510017631)
        ·
          refine ⟨20169952598781875265026447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13446635065854583510017631 20169952598781875265026447)
          ·
            refine ⟨30254928898172812897539671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20169952598781875265026447 30254928898172812897539671)
            ·
              refine ⟨45382393347259219346309507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30254928898172812897539671 45382393347259219346309507)
              ·
                refine ⟨68073590020888829019464261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45382393347259219346309507 68073590020888829019464261)
                ·
                  refine ⟨12763798128916655441149549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68073590020888829019464261 12763798128916655441149549)
                  ·
                    refine ⟨4786424298343745790431081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12763798128916655441149549 4786424298343745790431081)
                    ·
                      refine ⟨3589818223757809342823311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786424298343745790431081 3589818223757809342823311)
                      ·
                        rfl

theorem cell23_6991146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6991146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991146 prefixEnd_6991146 := by exact prefixLift 6991146
  have htrace : WordTrace (prefixWord ++ tailWord_6991146) baseStart_6991146 baseEnd_6991146 := by
    simpa [prefixWord, tailWord_6991146, baseEnd_6991146] using wordTrace_append hprefix tailTrace_6991146
  have hstable : (prefixWord ++ tailWord_6991146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991146).length < 2 ^ (prefixWord ++ tailWord_6991146).sum := by decide
  have hdescent : baseEnd_6991146 < baseStart_6991146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991152 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 4, 4]
def baseStart_6991152 : Nat := 118140960795 + 6991152 * 2 ^ 59
def prefixEnd_6991152 : Nat := 4983230072969 + 3 ^ 40 * 6991152 * 2
def baseEnd_6991152 : Nat := 1196607101547245439782761

theorem tailTrace_6991152 : CollatzResearch.WordTrace tailWord_6991152 prefixEnd_6991152 1196607101547245439782761 := by
  unfold tailWord_6991152
  simp only [CollatzResearch.WordTrace]
  refine ⟨127494130784128886274007855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169992174378838515032010473 127494130784128886274007855)
  ·
    refine ⟨191241196176193329411011783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127494130784128886274007855 191241196176193329411011783)
    ·
      refine ⟨286861794264289994116517675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191241196176193329411011783 286861794264289994116517675)
      ·
        refine ⟨430292691396434991174776513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286861794264289994116517675 430292691396434991174776513)
        ·
          refine ⟨322719518547326243381082385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430292691396434991174776513 322719518547326243381082385)
          ·
            refine ⟨242039638910494682535811789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322719518547326243381082385 242039638910494682535811789)
            ·
              refine ⟨90764864591435505950929421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242039638910494682535811789 90764864591435505950929421)
              ·
                refine ⟨34036824221788314731598533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90764864591435505950929421 34036824221788314731598533)
                ·
                  refine ⟨6381904541585309012174725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34036824221788314731598533 6381904541585309012174725)
                  ·
                    refine ⟨1196607101547245439782761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6381904541585309012174725 1196607101547245439782761)
                    ·
                      rfl

theorem cell23_6991152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 4].length) (baseStart_6991152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991152 prefixEnd_6991152 := by exact prefixLift 6991152
  have htrace : WordTrace (prefixWord ++ tailWord_6991152) baseStart_6991152 baseEnd_6991152 := by
    simpa [prefixWord, tailWord_6991152, baseEnd_6991152] using wordTrace_append hprefix tailTrace_6991152
  have hstable : (prefixWord ++ tailWord_6991152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991152).length < 2 ^ (prefixWord ++ tailWord_6991152).sum := by decide
  have hdescent : baseEnd_6991152 < baseStart_6991152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991162 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_6991162 : Nat := 118140960795 + 6991162 * 2 ^ 59
def prefixEnd_6991162 : Nat := 4983230072969 + 3 ^ 40 * 6991162 * 2
def baseEnd_6991162 : Nat := 3589826439448281280223237

theorem tailTrace_6991162 : CollatzResearch.WordTrace tailWord_6991162 prefixEnd_6991162 3589826439448281280223237 := by
  unfold tailWord_6991162
  simp only [CollatzResearch.WordTrace]
  refine ⟨63747156574555386063969935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169992417532147696170586493 63747156574555386063969935)
  ·
    refine ⟨95620734861833079095954903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63747156574555386063969935 95620734861833079095954903)
    ·
      refine ⟨143431102292749618643932355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95620734861833079095954903 143431102292749618643932355)
      ·
        refine ⟨215146653439124427965898533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143431102292749618643932355 215146653439124427965898533)
        ·
          refine ⟨40339997519835830243605975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215146653439124427965898533 40339997519835830243605975)
          ·
            refine ⟨60509996279753745365408963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40339997519835830243605975 60509996279753745365408963)
            ·
              refine ⟨90764994419630618048113445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60509996279753745365408963 90764994419630618048113445)
              ·
                refine ⟨17018436453680740884021271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90764994419630618048113445 17018436453680740884021271)
                ·
                  refine ⟨25527654680521111326031907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17018436453680740884021271 25527654680521111326031907)
                  ·
                    refine ⟨38291482020781666989047861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25527654680521111326031907 38291482020781666989047861)
                    ·
                      refine ⟨3589826439448281280223237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38291482020781666989047861 3589826439448281280223237)
                      ·
                        rfl

theorem cell23_6991162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_6991162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991162 prefixEnd_6991162 := by exact prefixLift 6991162
  have htrace : WordTrace (prefixWord ++ tailWord_6991162) baseStart_6991162 baseEnd_6991162 := by
    simpa [prefixWord, tailWord_6991162, baseEnd_6991162] using wordTrace_append hprefix tailTrace_6991162
  have hstable : (prefixWord ++ tailWord_6991162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991162).length < 2 ^ (prefixWord ++ tailWord_6991162).sum := by decide
  have hdescent : baseEnd_6991162 < baseStart_6991162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991189 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6991189 : Nat := 118140960795 + 6991189 * 2 ^ 59
def prefixEnd_6991189 : Nat := 4983230072969 + 3 ^ 40 * 6991189 * 2
def baseEnd_6991189 : Nat := 3589840303425952674585613

theorem tailTrace_6991189 : CollatzResearch.WordTrace tailWord_6991189 prefixEnd_6991189 3589840303425952674585613 := by
  unfold tailWord_6991189
  simp only [CollatzResearch.WordTrace]
  refine ⟨254989611069123727867112621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169993074046082485244741747 254989611069123727867112621)
  ·
    refine ⟨95621104150921397950167233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254989611069123727867112621 95621104150921397950167233)
    ·
      refine ⟨71715828113191048462625425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95621104150921397950167233 71715828113191048462625425)
      ·
        refine ⟨53786871084893286346969069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71715828113191048462625425 53786871084893286346969069)
        ·
          refine ⟨20170076656834982380113401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53786871084893286346969069 20170076656834982380113401)
          ·
            refine ⟨15127557492626236785085051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20170076656834982380113401 15127557492626236785085051)
            ·
              refine ⟨22691336238939355177627577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15127557492626236785085051 22691336238939355177627577)
              ·
                refine ⟨17018502179204516383220683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22691336238939355177627577 17018502179204516383220683)
                ·
                  refine ⟨25527753268806774574831025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17018502179204516383220683 25527753268806774574831025)
                  ·
                    refine ⟨19145814951605080931123269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25527753268806774574831025 19145814951605080931123269)
                    ·
                      refine ⟨3589840303425952674585613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19145814951605080931123269 3589840303425952674585613)
                      ·
                        rfl

theorem cell23_6991189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6991189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991189 prefixEnd_6991189 := by exact prefixLift 6991189
  have htrace : WordTrace (prefixWord ++ tailWord_6991189) baseStart_6991189 baseEnd_6991189 := by
    simpa [prefixWord, tailWord_6991189, baseEnd_6991189] using wordTrace_append hprefix tailTrace_6991189
  have hstable : (prefixWord ++ tailWord_6991189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991189).length < 2 ^ (prefixWord ++ tailWord_6991189).sum := by decide
  have hdescent : baseEnd_6991189 < baseStart_6991189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991212 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_6991212 : Nat := 118140960795 + 6991212 * 2 ^ 59
def prefixEnd_6991212 : Nat := 4983230072969 + 3 ^ 40 * 6991212 * 2
def baseEnd_6991212 : Nat := 1196617371160335361532669

theorem tailTrace_6991212 : CollatzResearch.WordTrace tailWord_6991212 prefixEnd_6991212 1196617371160335361532669 := by
  unfold tailWord_6991212
  simp only [CollatzResearch.WordTrace]
  refine ⟨127495224974020201397599945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169993633298693601863466593 127495224974020201397599945)
  ·
    refine ⟨95621418730515151048199959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127495224974020201397599945 95621418730515151048199959)
    ·
      refine ⟨143432128095772726572299939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95621418730515151048199959 143432128095772726572299939)
      ·
        refine ⟨215148192143659089858449909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143432128095772726572299939 215148192143659089858449909)
        ·
          refine ⟨20170143013468039674229679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215148192143659089858449909 20170143013468039674229679)
          ·
            refine ⟨30255214520202059511344519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20170143013468039674229679 30255214520202059511344519)
            ·
              refine ⟨45382821780303089267016779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30255214520202059511344519 45382821780303089267016779)
              ·
                refine ⟨68074232670454633900525169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45382821780303089267016779 68074232670454633900525169)
                ·
                  refine ⟨51055674502840975425393877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68074232670454633900525169 51055674502840975425393877)
                  ·
                    refine ⟨1196617371160335361532669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51055674502840975425393877 1196617371160335361532669)
                    ·
                      rfl

theorem cell23_6991212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_6991212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991212 prefixEnd_6991212 := by exact prefixLift 6991212
  have htrace : WordTrace (prefixWord ++ tailWord_6991212) baseStart_6991212 baseEnd_6991212 := by
    simpa [prefixWord, tailWord_6991212, baseEnd_6991212] using wordTrace_append hprefix tailTrace_6991212
  have hstable : (prefixWord ++ tailWord_6991212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991212).length < 2 ^ (prefixWord ++ tailWord_6991212).sum := by decide
  have hdescent : baseEnd_6991212 < baseStart_6991212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991236 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_6991236 : Nat := 118140960795 + 6991236 * 2 ^ 59
def prefixEnd_6991236 : Nat := 4983230072969 + 3 ^ 40 * 6991236 * 2
def baseEnd_6991236 : Nat := 3589864437016713990697897

theorem tailTrace_6991236 : CollatzResearch.WordTrace tailWord_6991236 prefixEnd_6991236 3589864437016713990697897 := by
  unfold tailWord_6991236
  simp only [CollatzResearch.WordTrace]
  refine ⟨127495662649976727447036781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169994216866635636596049041 127495662649976727447036781)
  ·
    refine ⟨47810873493741272792638793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127495662649976727447036781 47810873493741272792638793)
    ·
      refine ⟨35858155120305954594479095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47810873493741272792638793 35858155120305954594479095)
      ·
        refine ⟨53787232680458931891718643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35858155120305954594479095 53787232680458931891718643)
        ·
          refine ⟨80680849020688397837577965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53787232680458931891718643 80680849020688397837577965)
          ·
            refine ⟨30255318382758149189091737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80680849020688397837577965 30255318382758149189091737)
            ·
              refine ⟨22691488787068611891818803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30255318382758149189091737 22691488787068611891818803)
              ·
                refine ⟨34037233180602917837728205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22691488787068611891818803 34037233180602917837728205)
                ·
                  refine ⟨12763962442726094189148077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34037233180602917837728205 12763962442726094189148077)
                  ·
                    refine ⟨4786485916022285320930529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12763962442726094189148077 4786485916022285320930529)
                    ·
                      refine ⟨3589864437016713990697897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786485916022285320930529 3589864437016713990697897)
                      ·
                        rfl

theorem cell23_6991236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_6991236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991236 prefixEnd_6991236 := by exact prefixLift 6991236
  have htrace : WordTrace (prefixWord ++ tailWord_6991236) baseStart_6991236 baseEnd_6991236 := by
    simpa [prefixWord, tailWord_6991236, baseEnd_6991236] using wordTrace_append hprefix tailTrace_6991236
  have hstable : (prefixWord ++ tailWord_6991236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991236).length < 2 ^ (prefixWord ++ tailWord_6991236).sum := by decide
  have hdescent : baseEnd_6991236 < baseStart_6991236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991253 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_6991253 : Nat := 118140960795 + 6991253 * 2 ^ 59
def prefixEnd_6991253 : Nat := 4983230072969 + 3 ^ 40 * 6991253 * 2
def baseEnd_6991253 : Nat := 3589873166187840424185319

theorem tailTrace_6991253 : CollatzResearch.WordTrace tailWord_6991253 prefixEnd_6991253 3589873166187840424185319 := by
  unfold tailWord_6991253
  simp only [CollatzResearch.WordTrace]
  refine ⟨254991945340891866797442413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169994630227261244531628275 254991945340891866797442413)
  ·
    refine ⟨95621979502834450049040905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254991945340891866797442413 95621979502834450049040905)
    ·
      refine ⟨71716484627125837536780679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95621979502834450049040905 71716484627125837536780679)
      ·
        refine ⟨107574726940688756305171019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71716484627125837536780679 107574726940688756305171019)
        ·
          refine ⟨161362090411033134457756529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107574726940688756305171019 161362090411033134457756529)
          ·
            refine ⟨121021567808274850843317397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161362090411033134457756529 121021567808274850843317397)
            ·
              refine ⟨5672885991012883633280503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121021567808274850843317397 5672885991012883633280503)
              ·
                refine ⟨8509328986519325449920755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5672885991012883633280503 8509328986519325449920755)
                ·
                  refine ⟨12763993479778988174881133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8509328986519325449920755 12763993479778988174881133)
                  ·
                    refine ⟨4786497554917120565580425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12763993479778988174881133 4786497554917120565580425)
                    ·
                      refine ⟨3589873166187840424185319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786497554917120565580425 3589873166187840424185319)
                      ·
                        rfl

theorem cell23_6991253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_6991253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991253 prefixEnd_6991253 := by exact prefixLift 6991253
  have htrace : WordTrace (prefixWord ++ tailWord_6991253) baseStart_6991253 baseEnd_6991253 := by
    simpa [prefixWord, tailWord_6991253, baseEnd_6991253] using wordTrace_append hprefix tailTrace_6991253
  have hstable : (prefixWord ++ tailWord_6991253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991253).length < 2 ^ (prefixWord ++ tailWord_6991253).sum := by decide
  have hdescent : baseEnd_6991253 < baseStart_6991253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991306 : List Nat := [3, 1, 2, 1, 2, 3, 3, 3, 5]
def baseStart_6991306 : Nat := 118140960795 + 6991306 * 2 ^ 59
def prefixEnd_6991306 : Nat := 4983230072969 + 3 ^ 40 * 6991306 * 2
def baseEnd_6991306 : Nat := 398877820073614301869175

theorem tailTrace_6991306 : CollatzResearch.WordTrace tailWord_6991306 prefixEnd_6991306 398877820073614301869175 := by
  unfold tailWord_6991306
  simp only [CollatzResearch.WordTrace]
  refine ⟨63748469602424964212280443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169995918939799904566081181 63748469602424964212280443)
  ·
    refine ⟨95622704403637446318420665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63748469602424964212280443 95622704403637446318420665)
    ·
      refine ⟨71717028302728084738815499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95622704403637446318420665 71717028302728084738815499)
      ·
        refine ⟨107575542454092127108223249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71717028302728084738815499 107575542454092127108223249)
        ·
          refine ⟨80681656840569095331167437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107575542454092127108223249 80681656840569095331167437)
          ·
            refine ⟨30255621315213410749187789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80681656840569095331167437 30255621315213410749187789)
            ·
              refine ⟨11345857993205029030945421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30255621315213410749187789 11345857993205029030945421)
              ·
                refine ⟨4254696747451885886604533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11345857993205029030945421 4254696747451885886604533)
                ·
                  refine ⟨398877820073614301869175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4254696747451885886604533 398877820073614301869175)
                  ·
                    rfl

theorem cell23_6991306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_6991306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991306 prefixEnd_6991306 := by exact prefixLift 6991306
  have htrace : WordTrace (prefixWord ++ tailWord_6991306) baseStart_6991306 baseEnd_6991306 := by
    simpa [prefixWord, tailWord_6991306, baseEnd_6991306] using wordTrace_append hprefix tailTrace_6991306
  have hstable : (prefixWord ++ tailWord_6991306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991306).length < 2 ^ (prefixWord ++ tailWord_6991306).sum := by decide
  have hdescent : baseEnd_6991306 < baseStart_6991306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991312 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_6991312 : Nat := 118140960795 + 6991312 * 2 ^ 59
def prefixEnd_6991312 : Nat := 4983230072969 + 3 ^ 40 * 6991312 * 2
def baseEnd_6991312 : Nat := 3589903461546455693347547

theorem tailTrace_6991312 : CollatzResearch.WordTrace tailWord_6991312 prefixEnd_6991312 3589903461546455693347547 := by
  unfold tailWord_6991312
  simp only [CollatzResearch.WordTrace]
  refine ⟨127497048623839059936920095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169996064831785413249226793 127497048623839059936920095)
  ·
    refine ⟨191245572935758589905380143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127497048623839059936920095 191245572935758589905380143)
    ·
      refine ⟨286868359403637884858070215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191245572935758589905380143 286868359403637884858070215)
      ·
        refine ⟨430302539105456827287105323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286868359403637884858070215 430302539105456827287105323)
        ·
          refine ⟨645453808658185240930657985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430302539105456827287105323 645453808658185240930657985)
          ·
            refine ⟨484090356493638930697993489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645453808658185240930657985 484090356493638930697993489)
            ·
              refine ⟨363067767370229198023495117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484090356493638930697993489 363067767370229198023495117)
              ·
                refine ⟨136150412763835949258810669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363067767370229198023495117 136150412763835949258810669)
                ·
                  refine ⟨51056404786438480972054001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136150412763835949258810669 51056404786438480972054001)
                  ·
                    refine ⟨38292303589828860729040501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51056404786438480972054001 38292303589828860729040501)
                    ·
                      refine ⟨3589903461546455693347547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38292303589828860729040501 3589903461546455693347547)
                      ·
                        rfl

theorem cell23_6991312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_6991312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991312 prefixEnd_6991312 := by exact prefixLift 6991312
  have htrace : WordTrace (prefixWord ++ tailWord_6991312) baseStart_6991312 baseEnd_6991312 := by
    simpa [prefixWord, tailWord_6991312, baseEnd_6991312] using wordTrace_append hprefix tailTrace_6991312
  have hstable : (prefixWord ++ tailWord_6991312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991312).length < 2 ^ (prefixWord ++ tailWord_6991312).sum := by decide
  have hdescent : baseEnd_6991312 < baseStart_6991312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991329 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_6991329 : Nat := 118140960795 + 6991329 * 2 ^ 59
def prefixEnd_6991329 : Nat := 4983230072969 + 3 ^ 40 * 6991329 * 2
def baseEnd_6991329 : Nat := 3589912190717582126834969

theorem tailTrace_6991329 : CollatzResearch.WordTrace tailWord_6991329 prefixEnd_6991329 3589912190717582126834969 := by
  unfold tailWord_6991329
  simp only [CollatzResearch.WordTrace]
  refine ⟨254994717288616531777209041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169996478192411021184806027 254994717288616531777209041)
  ·
    refine ⟨191246037966462398832906781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254994717288616531777209041 191246037966462398832906781)
    ·
      refine ⟨71717264237423399562340043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191246037966462398832906781 71717264237423399562340043)
      ·
        refine ⟨107575896356135099343510065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71717264237423399562340043 107575896356135099343510065)
        ·
          refine ⟨80681922267101324507632549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107575896356135099343510065 80681922267101324507632549)
          ·
            refine ⟨15127860425081498345181103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80681922267101324507632549 15127860425081498345181103)
            ·
              refine ⟨22691790637622247517771655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15127860425081498345181103 22691790637622247517771655)
              ·
                refine ⟨34037685956433371276657483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22691790637622247517771655 34037685956433371276657483)
                ·
                  refine ⟨51056528934650056914986225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34037685956433371276657483 51056528934650056914986225)
                  ·
                    refine ⟨38292396700987542686239669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51056528934650056914986225 38292396700987542686239669)
                    ·
                      refine ⟨3589912190717582126834969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38292396700987542686239669 3589912190717582126834969)
                      ·
                        rfl

theorem cell23_6991329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_6991329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991329 prefixEnd_6991329 := by exact prefixLift 6991329
  have htrace : WordTrace (prefixWord ++ tailWord_6991329) baseStart_6991329 baseEnd_6991329 := by
    simpa [prefixWord, tailWord_6991329, baseEnd_6991329] using wordTrace_append hprefix tailTrace_6991329
  have hstable : (prefixWord ++ tailWord_6991329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991329).length < 2 ^ (prefixWord ++ tailWord_6991329).sum := by decide
  have hdescent : baseEnd_6991329 < baseStart_6991329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991379 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 6]
def baseStart_6991379 : Nat := 118140960795 + 6991379 * 2 ^ 59
def prefixEnd_6991379 : Nat := 4983230072969 + 3 ^ 40 * 6991379 * 2
def baseEnd_6991379 : Nat := 398881984972256325689971

theorem tailTrace_6991379 : CollatzResearch.WordTrace tailWord_6991379 prefixEnd_6991379 398881984972256325689971 := by
  unfold tailWord_6991379
  simp only [CollatzResearch.WordTrace]
  refine ⟨254996540938435390316529191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169997693958956926877686127 254996540938435390316529191)
  ·
    refine ⟨382494811407653085474793787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254996540938435390316529191 382494811407653085474793787)
    ·
      refine ⟨573742217111479628212190681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382494811407653085474793787 573742217111479628212190681)
      ·
        refine ⟨430306662833609721159143011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573742217111479628212190681 430306662833609721159143011)
        ·
          refine ⟨645459994250414581738714517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430306662833609721159143011 645459994250414581738714517)
          ·
            refine ⟨30255937230488183519002243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 645459994250414581738714517 30255937230488183519002243)
            ·
              refine ⟨45383905845732275278503365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30255937230488183519002243 45383905845732275278503365)
              ·
                refine ⟨8509482346074801614719381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45383905845732275278503365 8509482346074801614719381)
                ·
                  refine ⟨398881984972256325689971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8509482346074801614719381 398881984972256325689971)
                  ·
                    rfl

theorem cell23_6991379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 6].length) (baseStart_6991379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991379 prefixEnd_6991379 := by exact prefixLift 6991379
  have htrace : WordTrace (prefixWord ++ tailWord_6991379) baseStart_6991379 baseEnd_6991379 := by
    simpa [prefixWord, tailWord_6991379, baseEnd_6991379] using wordTrace_append hprefix tailTrace_6991379
  have hstable : (prefixWord ++ tailWord_6991379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991379).length < 2 ^ (prefixWord ++ tailWord_6991379).sum := by decide
  have hdescent : baseEnd_6991379 < baseStart_6991379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991499 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 2, 7]
def baseStart_6991499 : Nat := 118140960795 + 6991499 * 2 ^ 59
def prefixEnd_6991499 : Nat := 4983230072969 + 3 ^ 40 * 6991499 * 2
def baseEnd_6991499 : Nat := 1196666494142948820569729

theorem tailTrace_6991499 : CollatzResearch.WordTrace tailWord_6991499 prefixEnd_6991499 1196666494142948820569729 := by
  unfold tailWord_6991499
  simp only [CollatzResearch.WordTrace]
  refine ⟨255000917698000650810897551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170000611798667100540598367 255000917698000650810897551)
  ·
    refine ⟨382501376547000976216346327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255000917698000650810897551 382501376547000976216346327)
    ·
      refine ⟨573752064820501464324519491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382501376547000976216346327 573752064820501464324519491)
      ·
        refine ⟨860628097230752196486779237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573752064820501464324519491 860628097230752196486779237)
        ·
          refine ⟨161367768230766036841271107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 860628097230752196486779237 161367768230766036841271107)
          ·
            refine ⟨242051652346149055261906661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161367768230766036841271107 242051652346149055261906661)
            ·
              refine ⟨45384684814902947861607499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242051652346149055261906661 45384684814902947861607499)
              ·
                refine ⟨68077027222354421792411249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45384684814902947861607499 68077027222354421792411249)
                ·
                  refine ⟨51057770416765816344308437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68077027222354421792411249 51057770416765816344308437)
                  ·
                    refine ⟨1196666494142948820569729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51057770416765816344308437 1196666494142948820569729)
                    ·
                      rfl

theorem cell23_6991499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 7].length) (baseStart_6991499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991499 prefixEnd_6991499 := by exact prefixLift 6991499
  have htrace : WordTrace (prefixWord ++ tailWord_6991499) baseStart_6991499 baseEnd_6991499 := by
    simpa [prefixWord, tailWord_6991499, baseEnd_6991499] using wordTrace_append hprefix tailTrace_6991499
  have hstable : (prefixWord ++ tailWord_6991499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991499).length < 2 ^ (prefixWord ++ tailWord_6991499).sum := by decide
  have hdescent : baseEnd_6991499 < baseStart_6991499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991523 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 3, 3, 2]
def baseStart_6991523 : Nat := 118140960795 + 6991523 * 2 ^ 59
def prefixEnd_6991523 : Nat := 4983230072969 + 3 ^ 40 * 6991523 * 2
def baseEnd_6991523 : Nat := 3590011805964554367809077

theorem tailTrace_6991523 : CollatzResearch.WordTrace tailWord_6991523 prefixEnd_6991523 3590011805964554367809077 := by
  unfold tailWord_6991523
  simp only [CollatzResearch.WordTrace]
  refine ⟨255001793049913702909771223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170001195366609135273180815 255001793049913702909771223)
  ·
    refine ⟨382502689574870554364656835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255001793049913702909771223 382502689574870554364656835)
    ·
      refine ⟨573754034362305831546985253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382502689574870554364656835 573754034362305831546985253)
      ·
        refine ⟨107578881442932343415059735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 573754034362305831546985253 107578881442932343415059735)
        ·
          refine ⟨161368322164398515122589603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107578881442932343415059735 161368322164398515122589603)
          ·
            refine ⟨242052483246597772683884405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161368322164398515122589603 242052483246597772683884405)
            ·
              refine ⟨22692420304368541189114163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242052483246597772683884405 22692420304368541189114163)
              ·
                refine ⟨34038630456552811783671245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22692420304368541189114163 34038630456552811783671245)
                ·
                  refine ⟨12764486421207304418876717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34038630456552811783671245 12764486421207304418876717)
                  ·
                    refine ⟨4786682407952739157078769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12764486421207304418876717 4786682407952739157078769)
                    ·
                      refine ⟨3590011805964554367809077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786682407952739157078769 3590011805964554367809077)
                      ·
                        rfl

theorem cell23_6991523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_6991523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991523 prefixEnd_6991523 := by exact prefixLift 6991523
  have htrace : WordTrace (prefixWord ++ tailWord_6991523) baseStart_6991523 baseEnd_6991523 := by
    simpa [prefixWord, tailWord_6991523, baseEnd_6991523] using wordTrace_append hprefix tailTrace_6991523
  have hstable : (prefixWord ++ tailWord_6991523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991523).length < 2 ^ (prefixWord ++ tailWord_6991523).sum := by decide
  have hdescent : baseEnd_6991523 < baseStart_6991523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991534 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6991534 : Nat := 118140960795 + 6991534 * 2 ^ 59
def prefixEnd_6991534 : Nat := 4983230072969 + 3 ^ 40 * 6991534 * 2
def baseEnd_6991534 : Nat := 3590017454251753824771527

theorem tailTrace_6991534 : CollatzResearch.WordTrace tailWord_6991534 prefixEnd_6991534 3590017454251753824771527 := by
  unfold tailWord_6991534
  simp only [CollatzResearch.WordTrace]
  refine ⟨31875274281609231473552707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170001462835249234525614437 31875274281609231473552707)
  ·
    refine ⟨47812911422413847210329061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31875274281609231473552707 47812911422413847210329061)
    ·
      refine ⟨8964920891702596351936699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47812911422413847210329061 8964920891702596351936699)
      ·
        refine ⟨13447381337553894527905049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8964920891702596351936699 13447381337553894527905049)
        ·
          refine ⟨10085536003165420895928787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13447381337553894527905049 10085536003165420895928787)
          ·
            refine ⟨15128304004748131343893181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10085536003165420895928787 15128304004748131343893181)
            ·
              refine ⟨5673114001780549253959943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15128304004748131343893181 5673114001780549253959943)
              ·
                refine ⟨8509671002670823880939915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673114001780549253959943 8509671002670823880939915)
                ·
                  refine ⟨12764506504006235821409873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8509671002670823880939915 12764506504006235821409873)
                  ·
                    refine ⟨9573379878004676866057405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12764506504006235821409873 9573379878004676866057405)
                    ·
                      refine ⟨3590017454251753824771527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9573379878004676866057405 3590017454251753824771527)
                      ·
                        rfl

theorem cell23_6991534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6991534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991534 prefixEnd_6991534 := by exact prefixLift 6991534
  have htrace : WordTrace (prefixWord ++ tailWord_6991534) baseStart_6991534 baseEnd_6991534 := by
    simpa [prefixWord, tailWord_6991534, baseEnd_6991534] using wordTrace_append hprefix tailTrace_6991534
  have hstable : (prefixWord ++ tailWord_6991534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991534).length < 2 ^ (prefixWord ++ tailWord_6991534).sum := by decide
  have hdescent : baseEnd_6991534 < baseStart_6991534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991554 : List Nat := [3, 5, 1, 2, 2, 1, 1, 8]
def baseStart_6991554 : Nat := 118140960795 + 6991554 * 2 ^ 59
def prefixEnd_6991554 : Nat := 4983230072969 + 3 ^ 40 * 6991554 * 2
def baseEnd_6991554 : Nat := 132963989772771990611905

theorem tailTrace_6991554 : CollatzResearch.WordTrace tailWord_6991554 prefixEnd_6991554 132963989772771990611905 := by
  unfold tailWord_6991554
  simp only [CollatzResearch.WordTrace]
  refine ⟨63750730928200348801037429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170001949141867596802766477 63750730928200348801037429)
  ·
    refine ⟨5976631024518782700097259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63750730928200348801037429 5976631024518782700097259)
    ·
      refine ⟨8964946536778174050145889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5976631024518782700097259 8964946536778174050145889)
      ·
        refine ⟨6723709902583630537609417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8964946536778174050145889 6723709902583630537609417)
        ·
          refine ⟨5042782426937722903207063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6723709902583630537609417 5042782426937722903207063)
          ·
            refine ⟨7564173640406584354810595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042782426937722903207063 7564173640406584354810595)
            ·
              refine ⟨11346260460609876532215893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564173640406584354810595 11346260460609876532215893)
              ·
                refine ⟨132963989772771990611905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11346260460609876532215893 132963989772771990611905)
                ·
                  rfl

theorem cell23_6991554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 8].length) (baseStart_6991554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991554 prefixEnd_6991554 := by exact prefixLift 6991554
  have htrace : WordTrace (prefixWord ++ tailWord_6991554) baseStart_6991554 baseEnd_6991554 := by
    simpa [prefixWord, tailWord_6991554, baseEnd_6991554] using wordTrace_append hprefix tailTrace_6991554
  have hstable : (prefixWord ++ tailWord_6991554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991554).length < 2 ^ (prefixWord ++ tailWord_6991554).sum := by decide
  have hdescent : baseEnd_6991554 < baseStart_6991554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991570 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_6991570 : Nat := 118140960795 + 6991570 * 2 ^ 59
def prefixEnd_6991570 : Nat := 4983230072969 + 3 ^ 40 * 6991570 * 2
def baseEnd_6991570 : Nat := 3590035939555315683921361

theorem tailTrace_6991570 : CollatzResearch.WordTrace tailWord_6991570 prefixEnd_6991570 3590035939555315683921361 := by
  unfold tailWord_6991570
  simp only [CollatzResearch.WordTrace]
  refine ⟨63750876820185857484183041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170002338187162286624488109 63750876820185857484183041)
  ·
    refine ⟨47813157615139393113137281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63750876820185857484183041 47813157615139393113137281)
    ·
      refine ⟨35859868211354544834852961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47813157615139393113137281 35859868211354544834852961)
      ·
        refine ⟨26894901158515908626139721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35859868211354544834852961 26894901158515908626139721)
        ·
          refine ⟨20171175868886931469604791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26894901158515908626139721 20171175868886931469604791)
          ·
            refine ⟨30256763803330397204407187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20171175868886931469604791 30256763803330397204407187)
            ·
              refine ⟨45385145704995595806610781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30256763803330397204407187 45385145704995595806610781)
              ·
                refine ⟨17019429639373348427479043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45385145704995595806610781 17019429639373348427479043)
                ·
                  refine ⟨25529144459060022641218565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17019429639373348427479043 25529144459060022641218565)
                  ·
                    refine ⟨4786714586073754245228481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25529144459060022641218565 4786714586073754245228481)
                    ·
                      refine ⟨3590035939555315683921361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786714586073754245228481 3590035939555315683921361)
                      ·
                        rfl

theorem cell23_6991570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_6991570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991570 prefixEnd_6991570 := by exact prefixLift 6991570
  have htrace : WordTrace (prefixWord ++ tailWord_6991570) baseStart_6991570 baseEnd_6991570 := by
    simpa [prefixWord, tailWord_6991570, baseEnd_6991570] using wordTrace_append hprefix tailTrace_6991570
  have hstable : (prefixWord ++ tailWord_6991570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991570).length < 2 ^ (prefixWord ++ tailWord_6991570).sum := by decide
  have hdescent : baseEnd_6991570 < baseStart_6991570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991576 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 7]
def baseStart_6991576 : Nat := 118140960795 + 6991576 * 2 ^ 59
def prefixEnd_6991576 : Nat := 4983230072969 + 3 ^ 40 * 6991576 * 2
def baseEnd_6991576 : Nat := 398893224493249184494037

theorem tailTrace_6991576 : CollatzResearch.WordTrace tailWord_6991576 prefixEnd_6991576 398893224493249184494037 := by
  unfold tailWord_6991576
  simp only [CollatzResearch.WordTrace]
  refine ⟨127501863059360846480725291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170002484079147795307633721 127501863059360846480725291)
  ·
    refine ⟨191252794589041269721087937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127501863059360846480725291 191252794589041269721087937)
    ·
      refine ⟨143439595941780952290815953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191252794589041269721087937 143439595941780952290815953)
      ·
        refine ⟨107579696956335714218111965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143439595941780952290815953 107579696956335714218111965)
        ·
          refine ⟨40342386358625892831791987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107579696956335714218111965 40342386358625892831791987)
          ·
            refine ⟨60513579537938839247687981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40342386358625892831791987 60513579537938839247687981)
            ·
              refine ⟨22692592326727064717882993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60513579537938839247687981 22692592326727064717882993)
              ·
                refine ⟨17019444245045298538412245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22692592326727064717882993 17019444245045298538412245)
                ·
                  refine ⟨398893224493249184494037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17019444245045298538412245 398893224493249184494037)
                  ·
                    rfl

theorem cell23_6991576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 7].length) (baseStart_6991576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991576 prefixEnd_6991576 := by exact prefixLift 6991576
  have htrace : WordTrace (prefixWord ++ tailWord_6991576) baseStart_6991576 baseEnd_6991576 := by
    simpa [prefixWord, tailWord_6991576, baseEnd_6991576] using wordTrace_append hprefix tailTrace_6991576
  have hstable : (prefixWord ++ tailWord_6991576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991576).length < 2 ^ (prefixWord ++ tailWord_6991576).sum := by decide
  have hdescent : baseEnd_6991576 < baseStart_6991576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991591 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6991591 : Nat := 118140960795 + 6991591 * 2 ^ 59
def prefixEnd_6991591 : Nat := 4983230072969 + 3 ^ 40 * 6991591 * 2
def baseEnd_6991591 : Nat := 3590046722649060101758765

theorem tailTrace_6991591 : CollatzResearch.WordTrace tailWord_6991591 prefixEnd_6991591 3590046722649060101758765 := by
  unfold tailWord_6991591
  simp only [CollatzResearch.WordTrace]
  refine ⟨255004273213667350523246627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170002848809111567015497751 255004273213667350523246627)
  ·
    refine ⟨382506409820501025784869941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255004273213667350523246627 382506409820501025784869941)
    ·
      refine ⟨35859975920671971167331557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 382506409820501025784869941 35859975920671971167331557)
      ·
        refine ⟨6723745485125994593874667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35859975920671971167331557 6723745485125994593874667)
        ·
          refine ⟨10085618227688991890812001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6723745485125994593874667 10085618227688991890812001)
          ·
            refine ⟨7564213670766743918109001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10085618227688991890812001 7564213670766743918109001)
            ·
              refine ⟨5673160253075057938581751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7564213670766743918109001 5673160253075057938581751)
              ·
                refine ⟨8509740379612586907872627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673160253075057938581751 8509740379612586907872627)
                ·
                  refine ⟨12764610569418880361808941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8509740379612586907872627 12764610569418880361808941)
                  ·
                    refine ⟨4786728963532080135678353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12764610569418880361808941 4786728963532080135678353)
                    ·
                      refine ⟨3590046722649060101758765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786728963532080135678353 3590046722649060101758765)
                      ·
                        rfl

theorem cell23_6991591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6991591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991591 prefixEnd_6991591 := by exact prefixLift 6991591
  have htrace : WordTrace (prefixWord ++ tailWord_6991591) baseStart_6991591 baseEnd_6991591 := by
    simpa [prefixWord, tailWord_6991591, baseEnd_6991591] using wordTrace_append hprefix tailTrace_6991591
  have hstable : (prefixWord ++ tailWord_6991591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991591).length < 2 ^ (prefixWord ++ tailWord_6991591).sum := by decide
  have hdescent : baseEnd_6991591 < baseStart_6991591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991613 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_6991613 : Nat := 118140960795 + 6991613 * 2 ^ 59
def prefixEnd_6991613 : Nat := 4983230072969 + 3 ^ 40 * 6991613 * 2
def baseEnd_6991613 : Nat := 3590058019223459015683663

theorem tailTrace_6991613 : CollatzResearch.WordTrace tailWord_6991613 prefixEnd_6991613 3590058019223459015683663 := by
  unfold tailWord_6991613
  simp only [CollatzResearch.WordTrace]
  refine ⟨255005075619587648280547493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170003383746391765520364995 255005075619587648280547493)
  ·
    refine ⟨47813451678672684052602655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255005075619587648280547493 47813451678672684052602655)
    ·
      refine ⟨71720177518009026078903983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47813451678672684052602655 71720177518009026078903983)
      ·
        refine ⟨107580266277013539118355975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71720177518009026078903983 107580266277013539118355975)
        ·
          refine ⟨161370399415520308677533963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107580266277013539118355975 161370399415520308677533963)
          ·
            refine ⟨242055599123280463016300945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161370399415520308677533963 242055599123280463016300945)
            ·
              refine ⟨181541699342460347262225709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242055599123280463016300945 181541699342460347262225709)
              ·
                refine ⟨68078137253422630223334641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181541699342460347262225709 68078137253422630223334641)
                ·
                  refine ⟨51058602940066972667500981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68078137253422630223334641 51058602940066972667500981)
                  ·
                    refine ⟨4786744025631278687578217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51058602940066972667500981 4786744025631278687578217)
                    ·
                      refine ⟨3590058019223459015683663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4786744025631278687578217 3590058019223459015683663)
                      ·
                        rfl

theorem cell23_6991613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_6991613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991613 prefixEnd_6991613 := by exact prefixLift 6991613
  have htrace : WordTrace (prefixWord ++ tailWord_6991613) baseStart_6991613 baseEnd_6991613 := by
    simpa [prefixWord, tailWord_6991613, baseEnd_6991613] using wordTrace_append hprefix tailTrace_6991613
  have hstable : (prefixWord ++ tailWord_6991613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991613).length < 2 ^ (prefixWord ++ tailWord_6991613).sum := by decide
  have hdescent : baseEnd_6991613 < baseStart_6991613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991663 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 3]
def baseStart_6991663 : Nat := 118140960795 + 6991663 * 2 ^ 59
def prefixEnd_6991663 : Nat := 4983230072969 + 3 ^ 40 * 6991663 * 2
def baseEnd_6991663 : Nat := 3590083693256183820058433

theorem tailTrace_6991663 : CollatzResearch.WordTrace tailWord_6991663 prefixEnd_6991663 3590083693256183820058433 := by
  unfold tailWord_6991663
  simp only [CollatzResearch.WordTrace]
  refine ⟨255006899269406506819867643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170004599512937671213245095 255006899269406506819867643)
  ·
    refine ⟨382510348904109760229801465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255006899269406506819867643 382510348904109760229801465)
    ·
      refine ⟨286882761678082320172351099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382510348904109760229801465 286882761678082320172351099)
      ·
        refine ⟨430324142517123480258526649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286882761678082320172351099 430324142517123480258526649)
        ·
          refine ⟨322743106887842610193894987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430324142517123480258526649 322743106887842610193894987)
          ·
            refine ⟨484114660331763915290842481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322743106887842610193894987 484114660331763915290842481)
            ·
              refine ⟨363085995248822936468131861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484114660331763915290842481 363085995248822936468131861)
              ·
                refine ⟨17019656027288575146943681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 363085995248822936468131861 17019656027288575146943681)
                ·
                  refine ⟨12764742020466431360207761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17019656027288575146943681 12764742020466431360207761)
                  ·
                    refine ⟨9573556515349823520155821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12764742020466431360207761 9573556515349823520155821)
                    ·
                      refine ⟨3590083693256183820058433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9573556515349823520155821 3590083693256183820058433)
                      ·
                        rfl

theorem cell23_6991663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_6991663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991663 prefixEnd_6991663 := by exact prefixLift 6991663
  have htrace : WordTrace (prefixWord ++ tailWord_6991663) baseStart_6991663 baseEnd_6991663 := by
    simpa [prefixWord, tailWord_6991663, baseEnd_6991663] using wordTrace_append hprefix tailTrace_6991663
  have hstable : (prefixWord ++ tailWord_6991663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991663).length < 2 ^ (prefixWord ++ tailWord_6991663).sum := by decide
  have hdescent : baseEnd_6991663 < baseStart_6991663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6991683 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 6]
def baseStart_6991683 : Nat := 118140960795 + 6991683 * 2 ^ 59
def prefixEnd_6991683 : Nat := 4983230072969 + 3 ^ 40 * 6991683 * 2
def baseEnd_6991683 : Nat := 398899329207697082423149

theorem tailTrace_6991683 : CollatzResearch.WordTrace tailWord_6991683 prefixEnd_6991683 398899329207697082423149 := by
  unfold tailWord_6991683
  simp only [CollatzResearch.WordTrace]
  refine ⟨255007628729334050235595703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170005085819556033490397135 255007628729334050235595703)
  ·
    refine ⟨382511443094001075353393555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255007628729334050235595703 382511443094001075353393555)
    ·
      refine ⟨573767164641001613030090333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382511443094001075353393555 573767164641001613030090333)
      ·
        refine ⟨215162686740375604886283875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 573767164641001613030090333 215162686740375604886283875)
        ·
          refine ⟨322744030110563407329425813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215162686740375604886283875 322744030110563407329425813)
          ·
            refine ⟨15128626411432659718566835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 322744030110563407329425813 15128626411432659718566835)
            ·
              refine ⟨22692939617148989577850253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15128626411432659718566835 22692939617148989577850253)
              ·
                refine ⟨8509852356430871091693845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22692939617148989577850253 8509852356430871091693845)
                ·
                  refine ⟨398899329207697082423149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8509852356430871091693845 398899329207697082423149)
                  ·
                    rfl

theorem cell23_6991683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 6].length) (baseStart_6991683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6991683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6991683 prefixEnd_6991683 := by exact prefixLift 6991683
  have htrace : WordTrace (prefixWord ++ tailWord_6991683) baseStart_6991683 baseEnd_6991683 := by
    simpa [prefixWord, tailWord_6991683, baseEnd_6991683] using wordTrace_append hprefix tailTrace_6991683
  have hstable : (prefixWord ++ tailWord_6991683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6991683).length < 2 ^ (prefixWord ++ tailWord_6991683).sum := by decide
  have hdescent : baseEnd_6991683 < baseStart_6991683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6991683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
