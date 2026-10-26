import V185TrunkScan21Chunk107

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1312117 : List Nat := [1, 3, 4, 1, 3, 1, 2, 6]
def baseStart_1312117 : Nat := 118140960795 + 1312117 * 2 ^ 59
def prefixEnd_1312117 : Nat := 4983230072969 + 3 ^ 40 * 1312117 * 2
def baseEnd_1312117 : Nat := 99814325323784899244917

theorem tailTrace_1312117 : CollatzResearch.WordTrace tailWord_1312117 prefixEnd_1312117 99814325323784899244917 := by
  unfold tailWord_1312117
  simp only [CollatzResearch.WordTrace]
  refine ⟨47856838587431675587854605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31904559058287783725236403 47856838587431675587854605)
  ·
    refine ⟨17946314470286878345445477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47856838587431675587854605 17946314470286878345445477)
    ·
      refine ⟨3364933963178789689771027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17946314470286878345445477 3364933963178789689771027)
      ·
        refine ⟨5047400944768184534656541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3364933963178789689771027 5047400944768184534656541)
        ·
          refine ⟨1892775354288069200496203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5047400944768184534656541 1892775354288069200496203)
          ·
            refine ⟨2839163031432103800744305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892775354288069200496203 2839163031432103800744305)
            ·
              refine ⟨2129372273574077850558229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2839163031432103800744305 2129372273574077850558229)
              ·
                refine ⟨99814325323784899244917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2129372273574077850558229 99814325323784899244917)
                ·
                  rfl

theorem cell21_1312117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 6].length) (baseStart_1312117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312117 prefixEnd_1312117 := by exact prefixLift 1312117
  have htrace : WordTrace (prefixWord ++ tailWord_1312117) baseStart_1312117 baseEnd_1312117 := by
    simpa [prefixWord, tailWord_1312117, baseEnd_1312117] using wordTrace_append hprefix tailTrace_1312117
  have hstable : (prefixWord ++ tailWord_1312117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312117).length < 2 ^ (prefixWord ++ tailWord_1312117).sum := by decide
  have hdescent : baseEnd_1312117 < baseStart_1312117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312159 : List Nat := [1, 1, 2, 5, 1, 11]
def baseStart_1312159 : Nat := 118140960795 + 1312159 * 2 ^ 59
def prefixEnd_1312159 : Nat := 4983230072969 + 3 ^ 40 * 1312159 * 2
def baseEnd_1312159 : Nat := 11090835590502665112395

theorem tailTrace_1312159 : CollatzResearch.WordTrace tailWord_1312159 prefixEnd_1312159 11090835590502665112395 := by
  unfold tailWord_1312159
  simp only [CollatzResearch.WordTrace]
  refine ⟨47858370453279516760883531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31905580302186344507255687 47858370453279516760883531)
  ·
    refine ⟨71787555679919275141325297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47858370453279516760883531 71787555679919275141325297)
    ·
      refine ⟨53840666759939456355993973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71787555679919275141325297 53840666759939456355993973)
      ·
        refine ⟨5047562508744324033374435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53840666759939456355993973 5047562508744324033374435)
        ·
          refine ⟨7571343763116486050061653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5047562508744324033374435 7571343763116486050061653)
          ·
            refine ⟨11090835590502665112395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7571343763116486050061653 11090835590502665112395)
            ·
              rfl

theorem cell21_1312159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 11].length) (baseStart_1312159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312159 prefixEnd_1312159 := by exact prefixLift 1312159
  have htrace : WordTrace (prefixWord ++ tailWord_1312159) baseStart_1312159 baseEnd_1312159 := by
    simpa [prefixWord, tailWord_1312159, baseEnd_1312159] using wordTrace_append hprefix tailTrace_1312159
  have hstable : (prefixWord ++ tailWord_1312159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312159).length < 2 ^ (prefixWord ++ tailWord_1312159).sum := by decide
  have hdescent : baseEnd_1312159 < baseStart_1312159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312162 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1312162 : Nat := 118140960795 + 1312162 * 2 ^ 59
def prefixEnd_1312162 : Nat := 4983230072969 + 3 ^ 40 * 1312162 * 2
def baseEnd_1312162 : Nat := 299453245584444619484659

theorem tailTrace_1312162 : CollatzResearch.WordTrace tailWord_1312162 prefixEnd_1312162 299453245584444619484659 := by
  unfold tailWord_1312162
  simp only [CollatzResearch.WordTrace]
  refine ⟨11964619968067162068310685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31905653248179098848828493 11964619968067162068310685)
  ·
    refine ⟨4486732488025185775616507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11964619968067162068310685 4486732488025185775616507)
    ·
      refine ⟨6730098732037778663424761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4486732488025185775616507 6730098732037778663424761)
      ·
        refine ⟨5047574049028333997568571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6730098732037778663424761 5047574049028333997568571)
        ·
          refine ⟨7571361073542500996352857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5047574049028333997568571 7571361073542500996352857)
          ·
            refine ⟨5678520805156875747264643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7571361073542500996352857 5678520805156875747264643)
            ·
              refine ⟨8517781207735313620896965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5678520805156875747264643 8517781207735313620896965)
              ·
                refine ⟨1597083976450371303918181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8517781207735313620896965 1597083976450371303918181)
                ·
                  refine ⟨299453245584444619484659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597083976450371303918181 299453245584444619484659)
                  ·
                    rfl

theorem cell21_1312162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1312162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312162 prefixEnd_1312162 := by exact prefixLift 1312162
  have htrace : WordTrace (prefixWord ++ tailWord_1312162) baseStart_1312162 baseEnd_1312162 := by
    simpa [prefixWord, tailWord_1312162, baseEnd_1312162] using wordTrace_append hprefix tailTrace_1312162
  have hstable : (prefixWord ++ tailWord_1312162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312162).length < 2 ^ (prefixWord ++ tailWord_1312162).sum := by decide
  have hdescent : baseEnd_1312162 < baseStart_1312162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312207 : List Nat := [1, 1, 2, 1, 1, 4, 3, 5, 3]
def baseStart_1312207 : Nat := 118140960795 + 1312207 * 2 ^ 59
def prefixEnd_1312207 : Nat := 4983230072969 + 3 ^ 40 * 1312207 * 2
def baseEnd_1312207 : Nat := 299463515197534541234567

theorem tailTrace_1312207 : CollatzResearch.WordTrace tailWord_1312207 prefixEnd_1312207 299463515197534541234567 := by
  unfold tailWord_1312207
  simp only [CollatzResearch.WordTrace]
  refine ⟨47860121157105620958630875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31906747438070413972420583 47860121157105620958630875)
  ·
    refine ⟨71790181735658431437946313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47860121157105620958630875 71790181735658431437946313)
    ·
      refine ⟨53842636301743823578459735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71790181735658431437946313 53842636301743823578459735)
      ·
        refine ⟨80763954452615735367689603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53842636301743823578459735 80763954452615735367689603)
        ·
          refine ⟨121145931678923603051534405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80763954452615735367689603 121145931678923603051534405)
          ·
            refine ⟨22714862189798175572162701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121145931678923603051534405 22714862189798175572162701)
            ·
              refine ⟨8518073321174315839561013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22714862189798175572162701 8518073321174315839561013)
              ·
                refine ⟨798569373860092109958845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8518073321174315839561013 798569373860092109958845)
                ·
                  refine ⟨299463515197534541234567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798569373860092109958845 299463515197534541234567)
                  ·
                    rfl

theorem cell21_1312207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 3].length) (baseStart_1312207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312207 prefixEnd_1312207 := by exact prefixLift 1312207
  have htrace : WordTrace (prefixWord ++ tailWord_1312207) baseStart_1312207 baseEnd_1312207 := by
    simpa [prefixWord, tailWord_1312207, baseEnd_1312207] using wordTrace_append hprefix tailTrace_1312207
  have hstable : (prefixWord ++ tailWord_1312207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312207).length < 2 ^ (prefixWord ++ tailWord_1312207).sum := by decide
  have hdescent : baseEnd_1312207 < baseStart_1312207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312252 : List Nat := [2, 2, 2, 1, 2, 1, 6, 5]
def baseStart_1312252 : Nat := 118140960795 + 1312252 * 2 ^ 59
def prefixEnd_1312252 : Nat := 4983230072969 + 3 ^ 40 * 1312252 * 2
def baseEnd_1312252 : Nat := 99824594936874820994825

theorem tailTrace_1312252 : CollatzResearch.WordTrace tailWord_1312252 prefixEnd_1312252 99824594936874820994825 := by
  unfold tailWord_1312252
  simp only [CollatzResearch.WordTrace]
  refine ⟨23930881220971296822009505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31907841627961729096012673 23930881220971296822009505)
  ·
    refine ⟨17948160915728472616507129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23930881220971296822009505 17948160915728472616507129)
    ·
      refine ⟨13461120686796354462380347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17948160915728472616507129 13461120686796354462380347)
      ·
        refine ⟨20191681030194531693570521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13461120686796354462380347 20191681030194531693570521)
        ·
          refine ⟨15143760772645898770177891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20191681030194531693570521 15143760772645898770177891)
          ·
            refine ⟨22715641158968848155266837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15143760772645898770177891 22715641158968848155266837)
            ·
              refine ⟨1064795679326664757278133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22715641158968848155266837 1064795679326664757278133)
              ·
                refine ⟨99824594936874820994825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1064795679326664757278133 99824594936874820994825)
                ·
                  rfl

theorem cell21_1312252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_1312252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312252 prefixEnd_1312252 := by exact prefixLift 1312252
  have htrace : WordTrace (prefixWord ++ tailWord_1312252) baseStart_1312252 baseEnd_1312252 := by
    simpa [prefixWord, tailWord_1312252, baseEnd_1312252] using wordTrace_append hprefix tailTrace_1312252
  have hstable : (prefixWord ++ tailWord_1312252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312252).length < 2 ^ (prefixWord ++ tailWord_1312252).sum := by decide
  have hdescent : baseEnd_1312252 < baseStart_1312252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312258 : List Nat := [3, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1312258 : Nat := 118140960795 + 1312258 * 2 ^ 59
def prefixEnd_1312258 : Nat := 4983230072969 + 3 ^ 40 * 1312258 * 2
def baseEnd_1312258 : Nat := 299475154092369785884463

theorem tailTrace_1312258 : CollatzResearch.WordTrace tailWord_1312258 prefixEnd_1312258 299475154092369785884463 := by
  unfold tailWord_1312258
  simp only [CollatzResearch.WordTrace]
  refine ⟨11965495319980214167184357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31907987519947237779158285 11965495319980214167184357)
  ·
    refine ⟨2243530372496290156347067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11965495319980214167184357 2243530372496290156347067)
    ·
      refine ⟨3365295558744435234520601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243530372496290156347067 3365295558744435234520601)
      ·
        refine ⟨2523971669058326425890451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3365295558744435234520601 2523971669058326425890451)
        ·
          refine ⟨3785957503587489638835677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523971669058326425890451 3785957503587489638835677)
          ·
            refine ⟨1419734063845308614563379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3785957503587489638835677 1419734063845308614563379)
            ·
              refine ⟨2129601095767962921845069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419734063845308614563379 2129601095767962921845069)
              ·
                refine ⟨798600410912986095691901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2129601095767962921845069 798600410912986095691901)
                ·
                  refine ⟨299475154092369785884463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798600410912986095691901 299475154092369785884463)
                  ·
                    rfl

theorem cell21_1312258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1312258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312258 prefixEnd_1312258 := by exact prefixLift 1312258
  have htrace : WordTrace (prefixWord ++ tailWord_1312258) baseStart_1312258 baseEnd_1312258 := by
    simpa [prefixWord, tailWord_1312258, baseEnd_1312258] using wordTrace_append hprefix tailTrace_1312258
  have hstable : (prefixWord ++ tailWord_1312258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312258).length < 2 ^ (prefixWord ++ tailWord_1312258).sum := by decide
  have hdescent : baseEnd_1312258 < baseStart_1312258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312311 : List Nat := [1, 1, 3, 1, 2, 4, 2, 7]
def baseStart_1312311 : Nat := 118140960795 + 1312311 * 2 ^ 59
def prefixEnd_1312311 : Nat := 4983230072969 + 3 ^ 40 * 1312311 * 2
def baseEnd_1312311 : Nat := 99829083138151157167007

theorem tailTrace_1312311 : CollatzResearch.WordTrace tailWord_1312311 prefixEnd_1312311 99829083138151157167007 := by
  unfold tailWord_1312311
  simp only [CollatzResearch.WordTrace]
  refine ⟨47863914348728846720416787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31909276232485897813611191 47863914348728846720416787)
  ·
    refine ⟨71795871523093270080625181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47863914348728846720416787 71795871523093270080625181)
    ·
      refine ⟨26923451821159976280234443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71795871523093270080625181 26923451821159976280234443)
      ·
        refine ⟨40385177731739964420351665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26923451821159976280234443 40385177731739964420351665)
        ·
          refine ⟨30288883298804973315263749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40385177731739964420351665 30288883298804973315263749)
          ·
            refine ⟨5679165618525932496611953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30288883298804973315263749 5679165618525932496611953)
            ·
              refine ⟨4259374213894449372458965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5679165618525932496611953 4259374213894449372458965)
              ·
                refine ⟨99829083138151157167007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4259374213894449372458965 99829083138151157167007)
                ·
                  rfl

theorem cell21_1312311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 7].length) (baseStart_1312311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312311 prefixEnd_1312311 := by exact prefixLift 1312311
  have htrace : WordTrace (prefixWord ++ tailWord_1312311) baseStart_1312311 baseEnd_1312311 := by
    simpa [prefixWord, tailWord_1312311, baseEnd_1312311] using wordTrace_append hprefix tailTrace_1312311
  have hstable : (prefixWord ++ tailWord_1312311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312311).length < 2 ^ (prefixWord ++ tailWord_1312311).sum := by decide
  have hdescent : baseEnd_1312311 < baseStart_1312311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312432 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_1312432 : Nat := 118140960795 + 1312432 * 2 ^ 59
def prefixEnd_1312432 : Nat := 4983230072969 + 3 ^ 40 * 1312432 * 2
def baseEnd_1312432 : Nat := 299514863262984149984107

theorem tailTrace_1312432 : CollatzResearch.WordTrace tailWord_1312432 prefixEnd_1312432 299514863262984149984107 := by
  unfold tailWord_1312432
  simp only [CollatzResearch.WordTrace]
  refine ⟨23934163790645242192785775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31912218387526989590381033 23934163790645242192785775)
  ·
    refine ⟨35901245685967863289178663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23934163790645242192785775 35901245685967863289178663)
    ·
      refine ⟨53851868528951794933767995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35901245685967863289178663 53851868528951794933767995)
      ·
        refine ⟨80777802793427692400651993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53851868528951794933767995 80777802793427692400651993)
        ·
          refine ⟨60583352095070769300488995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80777802793427692400651993 60583352095070769300488995)
          ·
            refine ⟨90875028142606153950733493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60583352095070769300488995 90875028142606153950733493)
            ·
              refine ⟨8519533888369326932881265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90875028142606153950733493 8519533888369326932881265)
              ·
                refine ⟨6389650416276995199660949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8519533888369326932881265 6389650416276995199660949)
                ·
                  refine ⟨299514863262984149984107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6389650416276995199660949 299514863262984149984107)
                  ·
                    rfl

theorem cell21_1312432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_1312432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312432 prefixEnd_1312432 := by exact prefixLift 1312432
  have htrace : WordTrace (prefixWord ++ tailWord_1312432) baseStart_1312432 baseEnd_1312432 := by
    simpa [prefixWord, tailWord_1312432, baseEnd_1312432] using wordTrace_append hprefix tailTrace_1312432
  have hstable : (prefixWord ++ tailWord_1312432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312432).length < 2 ^ (prefixWord ++ tailWord_1312432).sum := by decide
  have hdescent : baseEnd_1312432 < baseStart_1312432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312466 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1312466 : Nat := 118140960795 + 1312466 * 2 ^ 59
def prefixEnd_1312466 : Nat := 4983230072969 + 3 ^ 40 * 1312466 * 2
def baseEnd_1312466 : Nat := 299522622526207646417371

theorem tailTrace_1312466 : CollatzResearch.WordTrace tailWord_1312466 prefixEnd_1312466 299522622526207646417371 := by
  unfold tailWord_1312466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11967391915791827048077313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31913045108778205461539501 11967391915791827048077313)
  ·
    refine ⟨8975543936843870286057985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11967391915791827048077313 8975543936843870286057985)
    ·
      refine ⟨6731657952632902714543489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8975543936843870286057985 6731657952632902714543489)
      ·
        refine ⟨5048743464474677035907617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6731657952632902714543489 5048743464474677035907617)
        ·
          refine ⟨3786557598356007776930713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5048743464474677035907617 3786557598356007776930713)
          ·
            refine ⟨2839918198767005832698035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3786557598356007776930713 2839918198767005832698035)
            ·
              refine ⟨4259877298150508749047053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839918198767005832698035 4259877298150508749047053)
              ·
                refine ⟨1597453986806440780892645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4259877298150508749047053 1597453986806440780892645)
                ·
                  refine ⟨299522622526207646417371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597453986806440780892645 299522622526207646417371)
                  ·
                    rfl

theorem cell21_1312466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1312466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312466 prefixEnd_1312466 := by exact prefixLift 1312466
  have htrace : WordTrace (prefixWord ++ tailWord_1312466) baseStart_1312466 baseEnd_1312466 := by
    simpa [prefixWord, tailWord_1312466, baseEnd_1312466] using wordTrace_append hprefix tailTrace_1312466
  have hstable : (prefixWord ++ tailWord_1312466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312466).length < 2 ^ (prefixWord ++ tailWord_1312466).sum := by decide
  have hdescent : baseEnd_1312466 < baseStart_1312466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312500 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1312500 : Nat := 118140960795 + 1312500 * 2 ^ 59
def prefixEnd_1312500 : Nat := 4983230072969 + 3 ^ 40 * 1312500 * 2
def baseEnd_1312500 : Nat := 299530381789431142850635

theorem tailTrace_1312500 : CollatzResearch.WordTrace tailWord_1312500 prefixEnd_1312500 299530381789431142850635 := by
  unfold tailWord_1312500
  simp only [CollatzResearch.WordTrace]
  refine ⟨23935403872522065999523477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31913871830029421332697969 23935403872522065999523477)
  ·
    refine ⟨1121972056524471843727663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23935403872522065999523477 1121972056524471843727663)
    ·
      refine ⟨1682958084786707765591495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1121972056524471843727663 1682958084786707765591495)
      ·
        refine ⟨2524437127180061648387243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682958084786707765591495 2524437127180061648387243)
        ·
          refine ⟨3786655690770092472580865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2524437127180061648387243 3786655690770092472580865)
          ·
            refine ⟨2839991768077569354435649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3786655690770092472580865 2839991768077569354435649)
            ·
              refine ⟨2129993826058177015826737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2839991768077569354435649 2129993826058177015826737)
              ·
                refine ⟨1597495369543632761870053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129993826058177015826737 1597495369543632761870053)
                ·
                  refine ⟨299530381789431142850635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597495369543632761870053 299530381789431142850635)
                  ·
                    rfl

theorem cell21_1312500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1312500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312500 prefixEnd_1312500 := by exact prefixLift 1312500
  have htrace : WordTrace (prefixWord ++ tailWord_1312500) baseStart_1312500 baseEnd_1312500 := by
    simpa [prefixWord, tailWord_1312500, baseEnd_1312500] using wordTrace_append hprefix tailTrace_1312500
  have hstable : (prefixWord ++ tailWord_1312500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312500).length < 2 ^ (prefixWord ++ tailWord_1312500).sum := by decide
  have hdescent : baseEnd_1312500 < baseStart_1312500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312570 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_1312570 : Nat := 118140960795 + 1312570 * 2 ^ 59
def prefixEnd_1312570 : Nat := 4983230072969 + 3 ^ 40 * 1312570 * 2
def baseEnd_1312570 : Nat := 299546356743126576683825

theorem tailTrace_1312570 : CollatzResearch.WordTrace tailWord_1312570 prefixEnd_1312570 299546356743126576683825 := by
  unfold tailWord_1312570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11968340213697633488523791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31915573903193689302730109 11968340213697633488523791)
  ·
    refine ⟨17952510320546450232785687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11968340213697633488523791 17952510320546450232785687)
    ·
      refine ⟨26928765480819675349178531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17952510320546450232785687 26928765480819675349178531)
      ·
        refine ⟨40393148221229513023767797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26928765480819675349178531 40393148221229513023767797)
        ·
          refine ⟨3786857645740266845978231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40393148221229513023767797 3786857645740266845978231)
          ·
            refine ⟨5680286468610400268967347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786857645740266845978231 5680286468610400268967347)
            ·
              refine ⟨8520429702915600403451021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5680286468610400268967347 8520429702915600403451021)
              ·
                refine ⟨3195161138593350151294133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8520429702915600403451021 3195161138593350151294133)
                ·
                  refine ⟨299546356743126576683825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3195161138593350151294133 299546356743126576683825)
                  ·
                    rfl

theorem cell21_1312570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_1312570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312570 prefixEnd_1312570 := by exact prefixLift 1312570
  have htrace : WordTrace (prefixWord ++ tailWord_1312570) baseStart_1312570 baseEnd_1312570 := by
    simpa [prefixWord, tailWord_1312570, baseEnd_1312570] using wordTrace_append hprefix tailTrace_1312570
  have hstable : (prefixWord ++ tailWord_1312570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312570).length < 2 ^ (prefixWord ++ tailWord_1312570).sum := by decide
  have hdescent : baseEnd_1312570 < baseStart_1312570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312739 : List Nat := [1, 1, 1, 6, 1, 2, 2, 4, 3]
def baseStart_1312739 : Nat := 118140960795 + 1312739 * 2 ^ 59
def prefixEnd_1312739 : Nat := 4983230072969 + 3 ^ 40 * 1312739 * 2
def baseEnd_1312739 : Nat := 299584924845619838366813

theorem tailTrace_1312739 : CollatzResearch.WordTrace tailWord_1312739 prefixEnd_1312739 299584924845619838366813 := by
  unfold tailWord_1312739
  simp only [CollatzResearch.WordTrace]
  refine ⟨47879524791178275816997271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31919683194118850544664847 47879524791178275816997271)
  ·
    refine ⟨71819287186767413725495907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47879524791178275816997271 71819287186767413725495907)
    ·
      refine ⟨107728930780151120588243861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71819287186767413725495907 107728930780151120588243861)
      ·
        refine ⟨5049793630319583777573931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107728930780151120588243861 5049793630319583777573931)
        ·
          refine ⟨7574690445479375666360897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5049793630319583777573931 7574690445479375666360897)
          ·
            refine ⟨5681017834109531749770673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7574690445479375666360897 5681017834109531749770673)
            ·
              refine ⟨4260763375582148812328005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5681017834109531749770673 4260763375582148812328005)
              ·
                refine ⟨798893132921652902311501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4260763375582148812328005 798893132921652902311501)
                ·
                  refine ⟨299584924845619838366813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798893132921652902311501 299584924845619838366813)
                  ·
                    rfl

theorem cell21_1312739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 3].length) (baseStart_1312739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312739 prefixEnd_1312739 := by exact prefixLift 1312739
  have htrace : WordTrace (prefixWord ++ tailWord_1312739) baseStart_1312739 baseEnd_1312739 := by
    simpa [prefixWord, tailWord_1312739, baseEnd_1312739] using wordTrace_append hprefix tailTrace_1312739
  have hstable : (prefixWord ++ tailWord_1312739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312739).length < 2 ^ (prefixWord ++ tailWord_1312739).sum := by decide
  have hdescent : baseEnd_1312739 < baseStart_1312739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312804 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 4]
def baseStart_1312804 : Nat := 118140960795 + 1312804 * 2 ^ 59
def prefixEnd_1312804 : Nat := 4983230072969 + 3 ^ 40 * 1312804 * 2
def baseEnd_1312804 : Nat := 299599758731194169783347

theorem tailTrace_1312804 : CollatzResearch.WordTrace tailWord_1312804 prefixEnd_1312804 299599758731194169783347 := by
  unfold tailWord_1312804
  simp only [CollatzResearch.WordTrace]
  refine ⟨23940947767971395959056733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31921263690628527945408977 23940947767971395959056733)
  ·
    refine ⟨8977855412989273484646275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23940947767971395959056733 8977855412989273484646275)
    ·
      refine ⟨13466783119483910226969413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8977855412989273484646275 13466783119483910226969413)
      ·
        refine ⟨2525021834903233167556765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13466783119483910226969413 2525021834903233167556765)
        ·
          refine ⟨946883188088712437833787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2525021834903233167556765 946883188088712437833787)
          ·
            refine ⟨1420324782133068656750681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946883188088712437833787 1420324782133068656750681)
            ·
              refine ⟨1065243586599801492563011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420324782133068656750681 1065243586599801492563011)
              ·
                refine ⟨1597865379899702238844517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065243586599801492563011 1597865379899702238844517)
                ·
                  refine ⟨299599758731194169783347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597865379899702238844517 299599758731194169783347)
                  ·
                    rfl

theorem cell21_1312804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_1312804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312804 prefixEnd_1312804 := by exact prefixLift 1312804
  have htrace : WordTrace (prefixWord ++ tailWord_1312804) baseStart_1312804 baseEnd_1312804 := by
    simpa [prefixWord, tailWord_1312804, baseEnd_1312804] using wordTrace_append hprefix tailTrace_1312804
  have hstable : (prefixWord ++ tailWord_1312804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312804).length < 2 ^ (prefixWord ++ tailWord_1312804).sum := by decide
  have hdescent : baseEnd_1312804 < baseStart_1312804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312857 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 5]
def baseStart_1312857 : Nat := 118140960795 + 1312857 * 2 ^ 59
def prefixEnd_1312857 : Nat := 4983230072969 + 3 ^ 40 * 1312857 * 2
def baseEnd_1312857 : Nat := 299611854053277855399905

theorem tailTrace_1312857 : CollatzResearch.WordTrace tailWord_1312857 prefixEnd_1312857 299611854053277855399905 := by
  unfold tailWord_1312857
  simp only [CollatzResearch.WordTrace]
  refine ⟨47883828604750781969792825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31922552403167187979861883 47883828604750781969792825)
  ·
    refine ⟨35912871453563086477344619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47883828604750781969792825 35912871453563086477344619)
    ·
      refine ⟨53869307180344629716016929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35912871453563086477344619 53869307180344629716016929)
      ·
        refine ⟨40401980385258472287012697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53869307180344629716016929 40401980385258472287012697)
        ·
          refine ⟨30301485288943854215259523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40401980385258472287012697 30301485288943854215259523)
          ·
            refine ⟨45452227933415781322889285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30301485288943854215259523 45452227933415781322889285)
            ·
              refine ⟨8522292737515458998041741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45452227933415781322889285 8522292737515458998041741)
              ·
                refine ⟨3195859776568297124265653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8522292737515458998041741 3195859776568297124265653)
                ·
                  refine ⟨299611854053277855399905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3195859776568297124265653 299611854053277855399905)
                  ·
                    rfl

theorem cell21_1312857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_1312857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312857 prefixEnd_1312857 := by exact prefixLift 1312857
  have htrace : WordTrace (prefixWord ++ tailWord_1312857) baseStart_1312857 baseEnd_1312857 := by
    simpa [prefixWord, tailWord_1312857, baseEnd_1312857] using wordTrace_append hprefix tailTrace_1312857
  have hstable : (prefixWord ++ tailWord_1312857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312857).length < 2 ^ (prefixWord ++ tailWord_1312857).sum := by decide
  have hdescent : baseEnd_1312857 < baseStart_1312857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312860 : List Nat := [2, 2, 4, 1, 1, 4, 1, 6]
def baseStart_1312860 : Nat := 118140960795 + 1312860 * 2 ^ 59
def prefixEnd_1312860 : Nat := 4983230072969 + 3 ^ 40 * 1312860 * 2
def baseEnd_1312860 : Nat := 99870846231383505616633

theorem tailTrace_1312860 : CollatzResearch.WordTrace tailWord_1312860 prefixEnd_1312860 99870846231383505616633 := by
  unfold tailWord_1312860
  simp only [CollatzResearch.WordTrace]
  refine ⟨23941969011869956741076017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31922625349159942321434689 23941969011869956741076017)
  ·
    refine ⟨17956476758902467555807013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23941969011869956741076017 17956476758902467555807013)
    ·
      refine ⟨3366839392294212666713815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17956476758902467555807013 3366839392294212666713815)
      ·
        refine ⟨5050259088441319000070723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3366839392294212666713815 5050259088441319000070723)
        ·
          refine ⟨7575388632661978500106085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5050259088441319000070723 7575388632661978500106085)
          ·
            refine ⟨1420385368624120968769891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7575388632661978500106085 1420385368624120968769891)
            ·
              refine ⟨2130578052936181453154837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420385368624120968769891 2130578052936181453154837)
              ·
                refine ⟨99870846231383505616633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2130578052936181453154837 99870846231383505616633)
                ·
                  rfl

theorem cell21_1312860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_1312860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312860 prefixEnd_1312860 := by exact prefixLift 1312860
  have htrace : WordTrace (prefixWord ++ tailWord_1312860) baseStart_1312860 baseEnd_1312860 := by
    simpa [prefixWord, tailWord_1312860, baseEnd_1312860] using wordTrace_append hprefix tailTrace_1312860
  have hstable : (prefixWord ++ tailWord_1312860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312860).length < 2 ^ (prefixWord ++ tailWord_1312860).sum := by decide
  have hdescent : baseEnd_1312860 < baseStart_1312860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312933 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 5]
def baseStart_1312933 : Nat := 118140960795 + 1312933 * 2 ^ 59
def prefixEnd_1312933 : Nat := 4983230072969 + 3 ^ 40 * 1312933 * 2
def baseEnd_1312933 : Nat := 299629198288718612133083

theorem tailTrace_1312933 : CollatzResearch.WordTrace tailWord_1312933 prefixEnd_1312933 299629198288718612133083 := by
  unfold tailWord_1312933
  simp only [CollatzResearch.WordTrace]
  refine ⟨47886600552475446949559453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31924400368316964633039635 47886600552475446949559453)
  ·
    refine ⟨17957475207178292606084795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47886600552475446949559453 17957475207178292606084795)
    ·
      refine ⟨26936212810767438909127193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17957475207178292606084795 26936212810767438909127193)
      ·
        refine ⟨20202159608075579181845395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26936212810767438909127193 20202159608075579181845395)
        ·
          refine ⟨30303239412113368772768093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20202159608075579181845395 30303239412113368772768093)
          ·
            refine ⟨11363714779542513289788035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30303239412113368772768093 11363714779542513289788035)
            ·
              refine ⟨17045572169313769934682053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11363714779542513289788035 17045572169313769934682053)
              ·
                refine ⟨3196044781746331862752885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17045572169313769934682053 3196044781746331862752885)
                ·
                  refine ⟨299629198288718612133083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3196044781746331862752885 299629198288718612133083)
                  ·
                    rfl

theorem cell21_1312933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_1312933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312933 prefixEnd_1312933 := by exact prefixLift 1312933
  have htrace : WordTrace (prefixWord ++ tailWord_1312933) baseStart_1312933 baseEnd_1312933 := by
    simpa [prefixWord, tailWord_1312933, baseEnd_1312933] using wordTrace_append hprefix tailTrace_1312933
  have hstable : (prefixWord ++ tailWord_1312933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312933).length < 2 ^ (prefixWord ++ tailWord_1312933).sum := by decide
  have hdescent : baseEnd_1312933 < baseStart_1312933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312942 : List Nat := [4, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_1312942 : Nat := 118140960795 + 1312942 * 2 ^ 59
def prefixEnd_1312942 : Nat := 4983230072969 + 3 ^ 40 * 1312942 * 2
def baseEnd_1312942 : Nat := 299631252211336596483065

theorem tailTrace_1312942 : CollatzResearch.WordTrace tailWord_1312942 prefixEnd_1312942 299631252211336596483065 := by
  unfold tailWord_1312942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985866101180355185829635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31924619206295227657758053 5985866101180355185829635)
  ·
    refine ⟨8978799151770532778744453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5985866101180355185829635 8978799151770532778744453)
    ·
      refine ⟨1683524840956974896014585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8978799151770532778744453 1683524840956974896014585)
      ·
        refine ⟨1262643630717731172010939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683524840956974896014585 1262643630717731172010939)
        ·
          refine ⟨1893965446076596758016409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262643630717731172010939 1893965446076596758016409)
          ·
            refine ⟨1420474084557447568512307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1893965446076596758016409 1420474084557447568512307)
            ·
              refine ⟨2130711126836171352768461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420474084557447568512307 2130711126836171352768461)
              ·
                refine ⟨799016672563564257288173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2130711126836171352768461 799016672563564257288173)
                ·
                  refine ⟨299631252211336596483065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799016672563564257288173 299631252211336596483065)
                  ·
                    rfl

theorem cell21_1312942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_1312942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1312942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1312942 prefixEnd_1312942 := by exact prefixLift 1312942
  have htrace : WordTrace (prefixWord ++ tailWord_1312942) baseStart_1312942 baseEnd_1312942 := by
    simpa [prefixWord, tailWord_1312942, baseEnd_1312942] using wordTrace_append hprefix tailTrace_1312942
  have hstable : (prefixWord ++ tailWord_1312942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312942).length < 2 ^ (prefixWord ++ tailWord_1312942).sum := by decide
  have hdescent : baseEnd_1312942 < baseStart_1312942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313074 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_1313074 : Nat := 118140960795 + 1313074 * 2 ^ 59
def prefixEnd_1313074 : Nat := 4983230072969 + 3 ^ 40 * 1313074 * 2
def baseEnd_1313074 : Nat := 299661376409733700282795

theorem tailTrace_1313074 : CollatzResearch.WordTrace tailWord_1313074 prefixEnd_1313074 299661376409733700282795 := by
  unfold tailWord_1313074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11972935811241157007610569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31927828829976418686961517 11972935811241157007610569)
  ·
    refine ⟨8979701858430867755707927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11972935811241157007610569 8979701858430867755707927)
    ·
      refine ⟨13469552787646301633561891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8979701858430867755707927 13469552787646301633561891)
      ·
        refine ⟨20204329181469452450342837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13469552787646301633561891 20204329181469452450342837)
        ·
          refine ⟨1894155860762761167219641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20204329181469452450342837 1894155860762761167219641)
          ·
            refine ⟨1420616895572070875414731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1894155860762761167219641 1420616895572070875414731)
            ·
              refine ⟨2130925343358106313122097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420616895572070875414731 2130925343358106313122097)
              ·
                refine ⟨1598194007518579734841573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130925343358106313122097 1598194007518579734841573)
                ·
                  refine ⟨299661376409733700282795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1598194007518579734841573 299661376409733700282795)
                  ·
                    rfl

theorem cell21_1313074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_1313074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313074 prefixEnd_1313074 := by exact prefixLift 1313074
  have htrace : WordTrace (prefixWord ++ tailWord_1313074) baseStart_1313074 baseEnd_1313074 := by
    simpa [prefixWord, tailWord_1313074, baseEnd_1313074] using wordTrace_append hprefix tailTrace_1313074
  have hstable : (prefixWord ++ tailWord_1313074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313074).length < 2 ^ (prefixWord ++ tailWord_1313074).sum := by decide
  have hdescent : baseEnd_1313074 < baseStart_1313074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313175 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 8]
def baseStart_1313175 : Nat := 118140960795 + 1313175 * 2 ^ 59
def prefixEnd_1313175 : Nat := 4983230072969 + 3 ^ 40 * 1313175 * 2
def baseEnd_1313175 : Nat := 299684425985779969099255

theorem tailTrace_1313175 : CollatzResearch.WordTrace tailWord_1313175 prefixEnd_1313175 299684425985779969099255 := by
  unfold tailWord_1313175
  simp only [CollatzResearch.WordTrace]
  refine ⟨47895427017598722279868979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31930284678399148186579319 47895427017598722279868979)
  ·
    refine ⟨71843140526398083419803469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47895427017598722279868979 71843140526398083419803469)
    ·
      refine ⟨26941177697399281282426301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71843140526398083419803469 26941177697399281282426301)
      ·
        refine ⟨10102941636524730480909863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26941177697399281282426301 10102941636524730480909863)
        ·
          refine ⟨15154412454787095721364795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10102941636524730480909863 15154412454787095721364795)
          ·
            refine ⟨22731618682180643582047193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15154412454787095721364795 22731618682180643582047193)
            ·
              refine ⟨17048714011635482686535395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22731618682180643582047193 17048714011635482686535395)
              ·
                refine ⟨25573071017453224029803093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17048714011635482686535395 25573071017453224029803093)
                ·
                  refine ⟨299684425985779969099255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25573071017453224029803093 299684425985779969099255)
                  ·
                    rfl

theorem cell21_1313175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_1313175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313175 prefixEnd_1313175 := by exact prefixLift 1313175
  have htrace : WordTrace (prefixWord ++ tailWord_1313175) baseStart_1313175 baseEnd_1313175 := by
    simpa [prefixWord, tailWord_1313175, baseEnd_1313175] using wordTrace_append hprefix tailTrace_1313175
  have hstable : (prefixWord ++ tailWord_1313175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313175).length < 2 ^ (prefixWord ++ tailWord_1313175).sum := by decide
  have hdescent : baseEnd_1313175 < baseStart_1313175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313223 : List Nat := [1, 1, 4, 1, 1, 5, 3, 5]
def baseStart_1313223 : Nat := 118140960795 + 1313223 * 2 ^ 59
def prefixEnd_1313223 : Nat := 4983230072969 + 3 ^ 40 * 1313223 * 2
def baseEnd_1313223 : Nat := 99898460079914184099719

theorem tailTrace_1313223 : CollatzResearch.WordTrace tailWord_1313223 prefixEnd_1313223 99898460079914184099719 := by
  unfold tailWord_1313223
  simp only [CollatzResearch.WordTrace]
  refine ⟨47897177721424826477616323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31931451814283217651744215 47897177721424826477616323)
  ·
    refine ⟨71845766582137239716424485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47897177721424826477616323 71845766582137239716424485)
    ·
      refine ⟨13471081234150732446829591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71845766582137239716424485 13471081234150732446829591)
      ·
        refine ⟨20206621851226098670244387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13471081234150732446829591 20206621851226098670244387)
        ·
          refine ⟨30309932776839148005366581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20206621851226098670244387 30309932776839148005366581)
          ·
            refine ⟨2841556197828670125503117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30309932776839148005366581 2841556197828670125503117)
            ·
              refine ⟨1065583574185751297063669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2841556197828670125503117 1065583574185751297063669)
              ·
                refine ⟨99898460079914184099719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1065583574185751297063669 99898460079914184099719)
                ·
                  rfl

theorem cell21_1313223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 5].length) (baseStart_1313223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313223 prefixEnd_1313223 := by exact prefixLift 1313223
  have htrace : WordTrace (prefixWord ++ tailWord_1313223) baseStart_1313223 baseEnd_1313223 := by
    simpa [prefixWord, tailWord_1313223, baseEnd_1313223] using wordTrace_append hprefix tailTrace_1313223
  have hstable : (prefixWord ++ tailWord_1313223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313223).length < 2 ^ (prefixWord ++ tailWord_1313223).sum := by decide
  have hdescent : baseEnd_1313223 < baseStart_1313223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313316 : List Nat := [2, 3, 1, 5, 1, 1, 2, 6]
def baseStart_1313316 : Nat := 118140960795 + 1313316 * 2 ^ 59
def prefixEnd_1313316 : Nat := 4983230072969 + 3 ^ 40 * 1313316 * 2
def baseEnd_1313316 : Nat := 99905534702265019082989

theorem tailTrace_1313316 : CollatzResearch.WordTrace tailWord_1313316 prefixEnd_1313316 99905534702265019082989 := by
  unfold tailWord_1313316
  simp only [CollatzResearch.WordTrace]
  refine ⟨23950284855043951680375901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31933713140058602240501201 23950284855043951680375901)
  ·
    refine ⟨8981356820641481880140963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23950284855043951680375901 8981356820641481880140963)
    ·
      refine ⟨13472035230962222820211445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8981356820641481880140963 13472035230962222820211445)
      ·
        refine ⟨1263003302902708389394823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13472035230962222820211445 1263003302902708389394823)
        ·
          refine ⟨1894504954354062584092235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263003302902708389394823 1894504954354062584092235)
          ·
            refine ⟨2841757431531093876138353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894504954354062584092235 2841757431531093876138353)
            ·
              refine ⟨2131318073648320407103765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841757431531093876138353 2131318073648320407103765)
              ·
                refine ⟨99905534702265019082989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2131318073648320407103765 99905534702265019082989)
                ·
                  rfl

theorem cell21_1313316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_1313316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313316 prefixEnd_1313316 := by exact prefixLift 1313316
  have htrace : WordTrace (prefixWord ++ tailWord_1313316) baseStart_1313316 baseEnd_1313316 := by
    simpa [prefixWord, tailWord_1313316, baseEnd_1313316] using wordTrace_append hprefix tailTrace_1313316
  have hstable : (prefixWord ++ tailWord_1313316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313316).length < 2 ^ (prefixWord ++ tailWord_1313316).sum := by decide
  have hdescent : baseEnd_1313316 < baseStart_1313316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313364 : List Nat := [2, 4, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1313364 : Nat := 118140960795 + 1313364 * 2 ^ 59
def prefixEnd_1313364 : Nat := 4983230072969 + 3 ^ 40 * 1313364 * 2
def baseEnd_1313364 : Nat := 299727558360757640448869

theorem tailTrace_1313364 : CollatzResearch.WordTrace tailWord_1313364 prefixEnd_1313364 299727558360757640448869 := by
  unfold tailWord_1313364
  simp only [CollatzResearch.WordTrace]
  refine ⟨23951160206957003779249573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31934880275942671705666097 23951160206957003779249573)
  ·
    refine ⟨4490842538804438208609295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23951160206957003779249573 4490842538804438208609295)
    ·
      refine ⟨6736263808206657312913943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4490842538804438208609295 6736263808206657312913943)
      ·
        refine ⟨10104395712309985969370915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6736263808206657312913943 10104395712309985969370915)
        ·
          refine ⟨15156593568464978954056373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10104395712309985969370915 15156593568464978954056373)
          ·
            refine ⟨1420930647043591776942785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15156593568464978954056373 1420930647043591776942785)
            ·
              refine ⟨1065697985282693832707089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420930647043591776942785 1065697985282693832707089)
              ·
                refine ⟨799273488962020374530317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065697985282693832707089 799273488962020374530317)
                ·
                  refine ⟨299727558360757640448869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799273488962020374530317 299727558360757640448869)
                  ·
                    rfl

theorem cell21_1313364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1313364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313364 prefixEnd_1313364 := by exact prefixLift 1313364
  have htrace : WordTrace (prefixWord ++ tailWord_1313364) baseStart_1313364 baseEnd_1313364 := by
    simpa [prefixWord, tailWord_1313364, baseEnd_1313364] using wordTrace_append hprefix tailTrace_1313364
  have hstable : (prefixWord ++ tailWord_1313364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313364).length < 2 ^ (prefixWord ++ tailWord_1313364).sum := by decide
  have hdescent : baseEnd_1313364 < baseStart_1313364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313389 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1313389 : Nat := 118140960795 + 1313389 * 2 ^ 59
def prefixEnd_1313389 : Nat := 4983230072969 + 3 ^ 40 * 1313389 * 2
def baseEnd_1313389 : Nat := 299733263701363152532151

theorem tailTrace_1313389 : CollatzResearch.WordTrace tailWord_1313389 prefixEnd_1313389 299733263701363152532151 := by
  unfold tailWord_1313389
  simp only [CollatzResearch.WordTrace]
  refine ⟨47903232238823436828159221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31935488159215624552106147 47903232238823436828159221)
  ·
    refine ⟨4490928022389697202639927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47903232238823436828159221 4490928022389697202639927)
    ·
      refine ⟨6736392033584545803959891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4490928022389697202639927 6736392033584545803959891)
      ·
        refine ⟨10104588050376818705939837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6736392033584545803959891 10104588050376818705939837)
        ·
          refine ⟨3789220518891307014727439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10104588050376818705939837 3789220518891307014727439)
          ·
            refine ⟨5683830778336960522091159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789220518891307014727439 5683830778336960522091159)
            ·
              refine ⟨8525746167505440783136739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5683830778336960522091159 8525746167505440783136739)
              ·
                refine ⟨12788619251258161174705109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8525746167505440783136739 12788619251258161174705109)
                ·
                  refine ⟨299733263701363152532151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12788619251258161174705109 299733263701363152532151)
                  ·
                    rfl

theorem cell21_1313389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1313389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313389 prefixEnd_1313389 := by exact prefixLift 1313389
  have htrace : WordTrace (prefixWord ++ tailWord_1313389) baseStart_1313389 baseEnd_1313389 := by
    simpa [prefixWord, tailWord_1313389, baseEnd_1313389] using wordTrace_append hprefix tailTrace_1313389
  have hstable : (prefixWord ++ tailWord_1313389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313389).length < 2 ^ (prefixWord ++ tailWord_1313389).sum := by decide
  have hdescent : baseEnd_1313389 < baseStart_1313389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313457 : List Nat := [1, 2, 2, 6, 2, 1, 1, 3, 3]
def baseStart_1313457 : Nat := 118140960795 + 1313457 * 2 ^ 59
def prefixEnd_1313457 : Nat := 4983230072969 + 3 ^ 40 * 1313457 * 2
def baseEnd_1313457 : Nat := 299748782227810145398679

theorem tailTrace_1313457 : CollatzResearch.WordTrace tailWord_1313457 prefixEnd_1313457 299748782227810145398679 := by
  unfold tailWord_1313457
  simp only [CollatzResearch.WordTrace]
  refine ⟨47905712402577084441634625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31937141601718056294423083 47905712402577084441634625)
  ·
    refine ⟨35929284301932813331225969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47905712402577084441634625 35929284301932813331225969)
    ·
      refine ⟨26946963226449609998419477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35929284301932813331225969 26946963226449609998419477)
      ·
        refine ⟨1263138901239825468675913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26946963226449609998419477 1263138901239825468675913)
        ·
          refine ⟨947354175929869101506935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1263138901239825468675913 947354175929869101506935)
          ·
            refine ⟨1421031263894803652260403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947354175929869101506935 1421031263894803652260403)
            ·
              refine ⟨2131546895842205478390605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421031263894803652260403 2131546895842205478390605)
              ·
                refine ⟨799330085940827054396477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2131546895842205478390605 799330085940827054396477)
                ·
                  refine ⟨299748782227810145398679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799330085940827054396477 299748782227810145398679)
                  ·
                    rfl

theorem cell21_1313457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_1313457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313457 prefixEnd_1313457 := by exact prefixLift 1313457
  have htrace : WordTrace (prefixWord ++ tailWord_1313457) baseStart_1313457 baseEnd_1313457 := by
    simpa [prefixWord, tailWord_1313457, baseEnd_1313457] using wordTrace_append hprefix tailTrace_1313457
  have hstable : (prefixWord ++ tailWord_1313457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313457).length < 2 ^ (prefixWord ++ tailWord_1313457).sum := by decide
  have hdescent : baseEnd_1313457 < baseStart_1313457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313482 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_1313482 : Nat := 118140960795 + 1313482 * 2 ^ 59
def prefixEnd_1313482 : Nat := 4983230072969 + 3 ^ 40 * 1313482 * 2
def baseEnd_1313482 : Nat := 299754487568415657481961

theorem tailTrace_1313482 : CollatzResearch.WordTrace tailWord_1313482 prefixEnd_1313482 299754487568415657481961 := by
  unfold tailWord_1313482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11976656056871628427823675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31937749484991009140863133 11976656056871628427823675)
  ·
    refine ⟨17964984085307442641735513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11976656056871628427823675 17964984085307442641735513)
    ·
      refine ⟨13473738063980581981301635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17964984085307442641735513 13473738063980581981301635)
      ·
        refine ⟨20210607095970872971952453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13473738063980581981301635 20210607095970872971952453)
        ·
          refine ⟨3789488830494538682241085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20210607095970872971952453 3789488830494538682241085)
          ·
            refine ⟨1421058311435452005840407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3789488830494538682241085 1421058311435452005840407)
            ·
              refine ⟨2131587467153178008760611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421058311435452005840407 2131587467153178008760611)
              ·
                refine ⟨3197381200729767013140917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131587467153178008760611 3197381200729767013140917)
                ·
                  refine ⟨299754487568415657481961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3197381200729767013140917 299754487568415657481961)
                  ·
                    rfl

theorem cell21_1313482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_1313482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313482 prefixEnd_1313482 := by exact prefixLift 1313482
  have htrace : WordTrace (prefixWord ++ tailWord_1313482) baseStart_1313482 baseEnd_1313482 := by
    simpa [prefixWord, tailWord_1313482, baseEnd_1313482] using wordTrace_append hprefix tailTrace_1313482
  have hstable : (prefixWord ++ tailWord_1313482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313482).length < 2 ^ (prefixWord ++ tailWord_1313482).sum := by decide
  have hdescent : baseEnd_1313482 < baseStart_1313482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313496 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_1313496 : Nat := 118140960795 + 1313496 * 2 ^ 59
def prefixEnd_1313496 : Nat := 4983230072969 + 3 ^ 40 * 1313496 * 2
def baseEnd_1313496 : Nat := 299757682559154744248599

theorem tailTrace_1313496 : CollatzResearch.WordTrace tailWord_1313496 prefixEnd_1313496 299757682559154744248599 := by
  unfold tailWord_1313496
  simp only [CollatzResearch.WordTrace]
  refine ⟨23953567424717897051152171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31938089899623862734869561 23953567424717897051152171)
  ·
    refine ⟨35930351137076845576728257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23953567424717897051152171 35930351137076845576728257)
    ·
      refine ⟨26947763352807634182546193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35930351137076845576728257 26947763352807634182546193)
      ·
        refine ⟨20210822514605725636909645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26947763352807634182546193 20210822514605725636909645)
        ·
          refine ⟨7579058442977147113841117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20210822514605725636909645 7579058442977147113841117)
          ·
            refine ⟨2842146916116430167690419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7579058442977147113841117 2842146916116430167690419)
            ·
              refine ⟨4263220374174645251535629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842146916116430167690419 4263220374174645251535629)
              ·
                refine ⟨1598707640315491969325861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4263220374174645251535629 1598707640315491969325861)
                ·
                  refine ⟨299757682559154744248599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1598707640315491969325861 299757682559154744248599)
                  ·
                    rfl

theorem cell21_1313496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_1313496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313496 prefixEnd_1313496 := by exact prefixLift 1313496
  have htrace : WordTrace (prefixWord ++ tailWord_1313496) baseStart_1313496 baseEnd_1313496 := by
    simpa [prefixWord, tailWord_1313496, baseEnd_1313496] using wordTrace_append hprefix tailTrace_1313496
  have hstable : (prefixWord ++ tailWord_1313496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313496).length < 2 ^ (prefixWord ++ tailWord_1313496).sum := by decide
  have hdescent : baseEnd_1313496 < baseStart_1313496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313555 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 4]
def baseStart_1313555 : Nat := 118140960795 + 1313555 * 2 ^ 59
def prefixEnd_1313555 : Nat := 4983230072969 + 3 ^ 40 * 1313555 * 2
def baseEnd_1313555 : Nat := 299771147162983752765145

theorem tailTrace_1313555 : CollatzResearch.WordTrace tailWord_1313555 prefixEnd_1313555 299771147162983752765145 := by
  unfold tailWord_1313555
  simp only [CollatzResearch.WordTrace]
  refine ⟨47909286756222047178702119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31939524504148031452468079 47909286756222047178702119)
  ·
    refine ⟨71863930134333070768053179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47909286756222047178702119 71863930134333070768053179)
    ·
      refine ⟨107795895201499606152079769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71863930134333070768053179 107795895201499606152079769)
      ·
        refine ⟨80846921401124704614059827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107795895201499606152079769 80846921401124704614059827)
        ·
          refine ⟨121270382101687056921089741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80846921401124704614059827 121270382101687056921089741)
          ·
            refine ⟨45476393288132646345408653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121270382101687056921089741 45476393288132646345408653)
            ·
              refine ⟨17053647483049742379528245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45476393288132646345408653 17053647483049742379528245)
              ·
                refine ⟨1598779451535913348080773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17053647483049742379528245 1598779451535913348080773)
                ·
                  refine ⟨299771147162983752765145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1598779451535913348080773 299771147162983752765145)
                  ·
                    rfl

theorem cell21_1313555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 4].length) (baseStart_1313555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313555 prefixEnd_1313555 := by exact prefixLift 1313555
  have htrace : WordTrace (prefixWord ++ tailWord_1313555) baseStart_1313555 baseEnd_1313555 := by
    simpa [prefixWord, tailWord_1313555, baseEnd_1313555] using wordTrace_append hprefix tailTrace_1313555
  have hstable : (prefixWord ++ tailWord_1313555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313555).length < 2 ^ (prefixWord ++ tailWord_1313555).sum := by decide
  have hdescent : baseEnd_1313555 < baseStart_1313555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313589 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 4]
def baseStart_1313589 : Nat := 118140960795 + 1313589 * 2 ^ 59
def prefixEnd_1313589 : Nat := 4983230072969 + 3 ^ 40 * 1313589 * 2
def baseEnd_1313589 : Nat := 299778906426207249198409

theorem tailTrace_1313589 : CollatzResearch.WordTrace tailWord_1313589 prefixEnd_1313589 299778906426207249198409 := by
  unfold tailWord_1313589
  simp only [CollatzResearch.WordTrace]
  refine ⟨47910526838098870985439821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31940351225399247323626547 47910526838098870985439821)
  ·
    refine ⟨17966447564287076619539933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47910526838098870985439821 17966447564287076619539933)
    ·
      refine ⟨6737417836607653732327475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17966447564287076619539933 6737417836607653732327475)
      ·
        refine ⟨10106126754911480598491213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737417836607653732327475 10106126754911480598491213)
        ·
          refine ⟨3789797533091805224434205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10106126754911480598491213 3789797533091805224434205)
          ·
            refine ⟨1421174074909426959162827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3789797533091805224434205 1421174074909426959162827)
            ·
              refine ⟨2131761112364140438744241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421174074909426959162827 2131761112364140438744241)
              ·
                refine ⟨1598820834273105329058181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2131761112364140438744241 1598820834273105329058181)
                ·
                  refine ⟨299778906426207249198409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1598820834273105329058181 299778906426207249198409)
                  ·
                    rfl

theorem cell21_1313589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_1313589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313589 prefixEnd_1313589 := by exact prefixLift 1313589
  have htrace : WordTrace (prefixWord ++ tailWord_1313589) baseStart_1313589 baseEnd_1313589 := by
    simpa [prefixWord, tailWord_1313589, baseEnd_1313589] using wordTrace_append hprefix tailTrace_1313589
  have hstable : (prefixWord ++ tailWord_1313589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313589).length < 2 ^ (prefixWord ++ tailWord_1313589).sum := by decide
  have hdescent : baseEnd_1313589 < baseStart_1313589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313620 : List Nat := [2, 4, 1, 1, 4, 2, 2, 5]
def baseStart_1313620 : Nat := 118140960795 + 1313620 * 2 ^ 59
def prefixEnd_1313620 : Nat := 4983230072969 + 3 ^ 40 * 1313620 * 2
def baseEnd_1313620 : Nat := 99928660349519361393893

theorem tailTrace_1313620 : CollatzResearch.WordTrace tailWord_1313620 prefixEnd_1313620 99928660349519361393893 := by
  unfold tailWord_1313620
  simp only [CollatzResearch.WordTrace]
  refine ⟨23955828750493281639909157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31941105000657708853212209 23955828750493281639909157)
  ·
    refine ⟨4491717890717490307482967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23955828750493281639909157 4491717890717490307482967)
    ·
      refine ⟨6737576836076235461224451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4491717890717490307482967 6737576836076235461224451)
      ·
        refine ⟨10106365254114353191836677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737576836076235461224451 10106365254114353191836677)
        ·
          refine ⟨1894943485146441223469377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10106365254114353191836677 1894943485146441223469377)
          ·
            refine ⟨1421207613859830917602033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1894943485146441223469377 1421207613859830917602033)
            ·
              refine ⟨1065905710394873188201525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421207613859830917602033 1065905710394873188201525)
              ·
                refine ⟨99928660349519361393893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1065905710394873188201525 99928660349519361393893)
                ·
                  rfl

theorem cell21_1313620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_1313620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313620 prefixEnd_1313620 := by exact prefixLift 1313620
  have htrace : WordTrace (prefixWord ++ tailWord_1313620) baseStart_1313620 baseEnd_1313620 := by
    simpa [prefixWord, tailWord_1313620, baseEnd_1313620] using wordTrace_append hprefix tailTrace_1313620
  have hstable : (prefixWord ++ tailWord_1313620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313620).length < 2 ^ (prefixWord ++ tailWord_1313620).sum := by decide
  have hdescent : baseEnd_1313620 < baseStart_1313620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313676 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_1313676 : Nat := 118140960795 + 1313676 * 2 ^ 59
def prefixEnd_1313676 : Nat := 4983230072969 + 3 ^ 40 * 1313676 * 2
def baseEnd_1313676 : Nat := 299798761011514431248231

theorem tailTrace_1313676 : CollatzResearch.WordTrace tailWord_1313676 prefixEnd_1313676 299798761011514431248231 := by
  unfold tailWord_1313676
  simp only [CollatzResearch.WordTrace]
  refine ⟨23956849994391842421928441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31942466659189123229237921 23956849994391842421928441)
  ·
    refine ⟨17967637495793881816446331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23956849994391842421928441 17967637495793881816446331)
    ·
      refine ⟨26951456243690822724669497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17967637495793881816446331 26951456243690822724669497)
      ·
        refine ⟨20213592182768117043502123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26951456243690822724669497 20213592182768117043502123)
        ·
          refine ⟨30320388274152175565253185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20213592182768117043502123 30320388274152175565253185)
          ·
            refine ⟨22740291205614131673939889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30320388274152175565253185 22740291205614131673939889)
            ·
              refine ⟨17055218404210598755454917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22740291205614131673939889 17055218404210598755454917)
              ·
                refine ⟨3197853450789487266647797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17055218404210598755454917 3197853450789487266647797)
                ·
                  refine ⟨299798761011514431248231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3197853450789487266647797 299798761011514431248231)
                  ·
                    rfl

theorem cell21_1313676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_1313676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313676 prefixEnd_1313676 := by exact prefixLift 1313676
  have htrace : WordTrace (prefixWord ++ tailWord_1313676) baseStart_1313676 baseEnd_1313676 := by
    simpa [prefixWord, tailWord_1313676, baseEnd_1313676] using wordTrace_append hprefix tailTrace_1313676
  have hstable : (prefixWord ++ tailWord_1313676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313676).length < 2 ^ (prefixWord ++ tailWord_1313676).sum := by decide
  have hdescent : baseEnd_1313676 < baseStart_1313676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313797 : List Nat := [1, 3, 1, 1, 2, 3, 3, 7]
def baseStart_1313797 : Nat := 118140960795 + 1313797 * 2 ^ 59
def prefixEnd_1313797 : Nat := 4983230072969 + 3 ^ 40 * 1313797 * 2
def baseEnd_1313797 : Nat := 99942124953348369910439

theorem tailTrace_1313797 : CollatzResearch.WordTrace tailWord_1313797 prefixEnd_1313797 99942124953348369910439 := by
  unfold tailWord_1313797
  simp only [CollatzResearch.WordTrace]
  refine ⟨47918113221345322509011645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31945408814230215006007763 47918113221345322509011645)
  ·
    refine ⟨17969292458004495940879367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47918113221345322509011645 17969292458004495940879367)
    ·
      refine ⟨26953938687006743911319051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17969292458004495940879367 26953938687006743911319051)
      ·
        refine ⟨40430908030510115866978577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26953938687006743911319051 40430908030510115866978577)
        ·
          refine ⟨30323181022882586900233933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40430908030510115866978577 30323181022882586900233933)
          ·
            refine ⟨11371192883580970087587725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30323181022882586900233933 11371192883580970087587725)
            ·
              refine ⟨4264197331342863782845397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11371192883580970087587725 4264197331342863782845397)
              ·
                refine ⟨99942124953348369910439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4264197331342863782845397 99942124953348369910439)
                ·
                  rfl

theorem cell21_1313797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 7].length) (baseStart_1313797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313797 prefixEnd_1313797 := by exact prefixLift 1313797
  have htrace : WordTrace (prefixWord ++ tailWord_1313797) baseStart_1313797 baseEnd_1313797 := by
    simpa [prefixWord, tailWord_1313797, baseEnd_1313797] using wordTrace_append hprefix tailTrace_1313797
  have hstable : (prefixWord ++ tailWord_1313797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313797).length < 2 ^ (prefixWord ++ tailWord_1313797).sum := by decide
  have hdescent : baseEnd_1313797 < baseStart_1313797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313831 : List Nat := [1, 1, 7, 1, 1, 2, 2, 6]
def baseStart_1313831 : Nat := 118140960795 + 1313831 * 2 ^ 59
def prefixEnd_1313831 : Nat := 4983230072969 + 3 ^ 40 * 1313831 * 2
def baseEnd_1313831 : Nat := 99944711374422868721527

theorem tailTrace_1313831 : CollatzResearch.WordTrace tailWord_1313831 prefixEnd_1313831 99944711374422868721527 := by
  unfold tailWord_1313831
  simp only [CollatzResearch.WordTrace]
  refine ⟨47919353303222146315749347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31946235535481430877166231 47919353303222146315749347)
  ·
    refine ⟨71879029954833219473624021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47919353303222146315749347 71879029954833219473624021)
    ·
      refine ⟨1684664764566403581413063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 71879029954833219473624021 1684664764566403581413063)
      ·
        refine ⟨2526997146849605372119595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684664764566403581413063 2526997146849605372119595)
        ·
          refine ⟨3790495720274408058179393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526997146849605372119595 3790495720274408058179393)
          ·
            refine ⟨2842871790205806043634545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3790495720274408058179393 2842871790205806043634545)
            ·
              refine ⟨2132153842654354532725909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2842871790205806043634545 2132153842654354532725909)
              ·
                refine ⟨99944711374422868721527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2132153842654354532725909 99944711374422868721527)
                ·
                  rfl

theorem cell21_1313831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 6].length) (baseStart_1313831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313831 prefixEnd_1313831 := by exact prefixLift 1313831
  have htrace : WordTrace (prefixWord ++ tailWord_1313831) baseStart_1313831 baseEnd_1313831 := by
    simpa [prefixWord, tailWord_1313831, baseEnd_1313831] using wordTrace_append hprefix tailTrace_1313831
  have hstable : (prefixWord ++ tailWord_1313831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313831).length < 2 ^ (prefixWord ++ tailWord_1313831).sum := by decide
  have hdescent : baseEnd_1313831 < baseStart_1313831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313834 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_1313834 : Nat := 118140960795 + 1313834 * 2 ^ 59
def prefixEnd_1313834 : Nat := 4983230072969 + 3 ^ 40 * 1313834 * 2
def baseEnd_1313834 : Nat := 299834818764141267614575

theorem tailTrace_1313834 : CollatzResearch.WordTrace tailWord_1313834 prefixEnd_1313834 299834818764141267614575 := by
  unfold tailWord_1313834
  simp only [CollatzResearch.WordTrace]
  refine ⟨11979865680552819457027139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31946308481474185218739037 11979865680552819457027139)
  ·
    refine ⟨17969798520829229185540709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11979865680552819457027139 17969798520829229185540709)
    ·
      refine ⟨3369337222655480472288883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17969798520829229185540709 3369337222655480472288883)
      ·
        refine ⟨5054005833983220708433325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369337222655480472288883 5054005833983220708433325)
        ·
          refine ⟨1895252187743707765662497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5054005833983220708433325 1895252187743707765662497)
          ·
            refine ⟨1421439140807780824246873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895252187743707765662497 1421439140807780824246873)
            ·
              refine ⟨1066079355605835618185155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421439140807780824246873 1066079355605835618185155)
              ·
                refine ⟨1599119033408753427277733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066079355605835618185155 1599119033408753427277733)
                ·
                  refine ⟨299834818764141267614575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599119033408753427277733 299834818764141267614575)
                  ·
                    rfl

theorem cell21_1313834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_1313834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313834 prefixEnd_1313834 := by exact prefixLift 1313834
  have htrace : WordTrace (prefixWord ++ tailWord_1313834) baseStart_1313834 baseEnd_1313834 := by
    simpa [prefixWord, tailWord_1313834, baseEnd_1313834] using wordTrace_append hprefix tailTrace_1313834
  have hstable : (prefixWord ++ tailWord_1313834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313834).length < 2 ^ (prefixWord ++ tailWord_1313834).sum := by decide
  have hdescent : baseEnd_1313834 < baseStart_1313834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313904 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_1313904 : Nat := 118140960795 + 1313904 * 2 ^ 59
def prefixEnd_1313904 : Nat := 4983230072969 + 3 ^ 40 * 1313904 * 2
def baseEnd_1313904 : Nat := 299850793717836701447765

theorem tailTrace_1313904 : CollatzResearch.WordTrace tailWord_1313904 prefixEnd_1313904 299850793717836701447765 := by
  unfold tailWord_1313904
  simp only [CollatzResearch.WordTrace]
  refine ⟨23961007915978839891578383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31948010554638453188771177 23961007915978839891578383)
  ·
    refine ⟨35941511873968259837367575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23961007915978839891578383 35941511873968259837367575)
    ·
      refine ⟨53912267810952389756051363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35941511873968259837367575 53912267810952389756051363)
      ·
        refine ⟨80868401716428584634077045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53912267810952389756051363 80868401716428584634077045)
        ·
          refine ⟨7581412660915179809444723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80868401716428584634077045 7581412660915179809444723)
          ·
            refine ⟨11372118991372769714167085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7581412660915179809444723 11372118991372769714167085)
            ·
              refine ⟨4264544621764788642812657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11372118991372769714167085 4264544621764788642812657)
              ·
                refine ⟨3198408466323591482109493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4264544621764788642812657 3198408466323591482109493)
                ·
                  refine ⟨299850793717836701447765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3198408466323591482109493 299850793717836701447765)
                  ·
                    rfl

theorem cell21_1313904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_1313904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313904 prefixEnd_1313904 := by exact prefixLift 1313904
  have htrace : WordTrace (prefixWord ++ tailWord_1313904) baseStart_1313904 baseEnd_1313904 := by
    simpa [prefixWord, tailWord_1313904, baseEnd_1313904] using wordTrace_append hprefix tailTrace_1313904
  have hstable : (prefixWord ++ tailWord_1313904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313904).length < 2 ^ (prefixWord ++ tailWord_1313904).sum := by decide
  have hdescent : baseEnd_1313904 < baseStart_1313904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313938 : List Nat := [3, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_1313938 : Nat := 118140960795 + 1313938 * 2 ^ 59
def prefixEnd_1313938 : Nat := 4983230072969 + 3 ^ 40 * 1313938 * 2
def baseEnd_1313938 : Nat := 299858552981060197881029

theorem tailTrace_1313938 : CollatzResearch.WordTrace tailWord_1313938 prefixEnd_1313938 299858552981060197881029 := by
  unfold tailWord_1313938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980813978458625897473617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31948837275889669059929645 11980813978458625897473617)
  ·
    refine ⟨8985610483843969423105213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11980813978458625897473617 8985610483843969423105213)
    ·
      refine ⟨3369603931441488533664455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8985610483843969423105213 3369603931441488533664455)
      ·
        refine ⟨5054405897162232800496683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369603931441488533664455 5054405897162232800496683)
        ·
          refine ⟨7581608845743349200745025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5054405897162232800496683 7581608845743349200745025)
          ·
            refine ⟨5686206634307511900558769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7581608845743349200745025 5686206634307511900558769)
            ·
              refine ⟨4264654975730633925419077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5686206634307511900558769 4264654975730633925419077)
              ·
                refine ⟨799622807949493861016077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4264654975730633925419077 799622807949493861016077)
                ·
                  refine ⟨299858552981060197881029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799622807949493861016077 299858552981060197881029)
                  ·
                    rfl

theorem cell21_1313938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_1313938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313938 prefixEnd_1313938 := by exact prefixLift 1313938
  have htrace : WordTrace (prefixWord ++ tailWord_1313938) baseStart_1313938 baseEnd_1313938 := by
    simpa [prefixWord, tailWord_1313938, baseEnd_1313938] using wordTrace_append hprefix tailTrace_1313938
  have hstable : (prefixWord ++ tailWord_1313938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313938).length < 2 ^ (prefixWord ++ tailWord_1313938).sum := by decide
  have hdescent : baseEnd_1313938 < baseStart_1313938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313949 : List Nat := [1, 4, 2, 1, 1, 2, 2, 8]
def baseStart_1313949 : Nat := 118140960795 + 1313949 * 2 ^ 59
def prefixEnd_1313949 : Nat := 4983230072969 + 3 ^ 40 * 1313949 * 2
def baseEnd_1313949 : Nat := 99953687776975541065891

theorem tailTrace_1313949 : CollatzResearch.WordTrace tailWord_1313949 prefixEnd_1313949 99953687776975541065891 := by
  unfold tailWord_1313949
  simp only [CollatzResearch.WordTrace]
  refine ⟨47923657116794652468544901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31949104744529768312363267 47923657116794652468544901)
  ·
    refine ⟨8985685709398997337852169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47923657116794652468544901 8985685709398997337852169)
    ·
      refine ⟨6739264282049248003389127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8985685709398997337852169 6739264282049248003389127)
      ·
        refine ⟨10108896423073872005083691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6739264282049248003389127 10108896423073872005083691)
        ·
          refine ⟨15163344634610808007625537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10108896423073872005083691 15163344634610808007625537)
          ·
            refine ⟨11372508475958106005719153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15163344634610808007625537 11372508475958106005719153)
            ·
              refine ⟨8529381356968579504289365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11372508475958106005719153 8529381356968579504289365)
              ·
                refine ⟨99953687776975541065891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8529381356968579504289365 99953687776975541065891)
                ·
                  rfl

theorem cell21_1313949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 8].length) (baseStart_1313949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313949 prefixEnd_1313949 := by exact prefixLift 1313949
  have htrace : WordTrace (prefixWord ++ tailWord_1313949) baseStart_1313949 baseEnd_1313949 := by
    simpa [prefixWord, tailWord_1313949, baseEnd_1313949] using wordTrace_append hprefix tailTrace_1313949
  have hstable : (prefixWord ++ tailWord_1313949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313949).length < 2 ^ (prefixWord ++ tailWord_1313949).sum := by decide
  have hdescent : baseEnd_1313949 < baseStart_1313949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313952 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_1313952 : Nat := 118140960795 + 1313952 * 2 ^ 59
def prefixEnd_1313952 : Nat := 4983230072969 + 3 ^ 40 * 1313952 * 2
def baseEnd_1313952 : Nat := 299861747971799284647667

theorem tailTrace_1313952 : CollatzResearch.WordTrace tailWord_1313952 prefixEnd_1313952 299861747971799284647667 := by
  unfold tailWord_1313952
  simp only [CollatzResearch.WordTrace]
  refine ⟨23961883267891891990452055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31949177690522522653936073 23961883267891891990452055)
  ·
    refine ⟨35942824901837837985678083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23961883267891891990452055 35942824901837837985678083)
    ·
      refine ⟨53914237352756756978517125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35942824901837837985678083 53914237352756756978517125)
      ·
        refine ⟨10108919503641891933471961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53914237352756756978517125 10108919503641891933471961)
        ·
          refine ⟨7581689627731418950103971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10108919503641891933471961 7581689627731418950103971)
          ·
            refine ⟨11372534441597128425155957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7581689627731418950103971 11372534441597128425155957)
            ·
              refine ⟨1066175103899730789858371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11372534441597128425155957 1066175103899730789858371)
              ·
                refine ⟨1599262655849596184787557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066175103899730789858371 1599262655849596184787557)
                ·
                  refine ⟨299861747971799284647667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599262655849596184787557 299861747971799284647667)
                  ·
                    rfl

theorem cell21_1313952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_1313952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1313952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1313952 prefixEnd_1313952 := by exact prefixLift 1313952
  have htrace : WordTrace (prefixWord ++ tailWord_1313952) baseStart_1313952 baseEnd_1313952 := by
    simpa [prefixWord, tailWord_1313952, baseEnd_1313952] using wordTrace_append hprefix tailTrace_1313952
  have hstable : (prefixWord ++ tailWord_1313952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313952).length < 2 ^ (prefixWord ++ tailWord_1313952).sum := by decide
  have hdescent : baseEnd_1313952 < baseStart_1313952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314039 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 7]
def baseStart_1314039 : Nat := 118140960795 + 1314039 * 2 ^ 59
def prefixEnd_1314039 : Nat := 4983230072969 + 3 ^ 40 * 1314039 * 2
def baseEnd_1314039 : Nat := 299881602557106466697489

theorem tailTrace_1314039 : CollatzResearch.WordTrace tailWord_1314039 prefixEnd_1314039 299881602557106466697489 := by
  unfold tailWord_1314039
  simp only [CollatzResearch.WordTrace]
  refine ⟨47926939686468597839321171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31951293124312398559547447 47926939686468597839321171)
  ·
    refine ⟨71890409529702896758981757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47926939686468597839321171 71890409529702896758981757)
    ·
      refine ⟨26958903573638586284618159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71890409529702896758981757 26958903573638586284618159)
      ·
        refine ⟨40438355360457879426927239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26958903573638586284618159 40438355360457879426927239)
        ·
          refine ⟨60657533040686819140390859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40438355360457879426927239 60657533040686819140390859)
          ·
            refine ⟨90986299561030228710586289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60657533040686819140390859 90986299561030228710586289)
            ·
              refine ⟨68239724670772671532939717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90986299561030228710586289 68239724670772671532939717)
              ·
                refine ⟨12794948375769875912426197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68239724670772671532939717 12794948375769875912426197)
                ·
                  refine ⟨299881602557106466697489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12794948375769875912426197 299881602557106466697489)
                  ·
                    rfl

theorem cell21_1314039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_1314039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314039 prefixEnd_1314039 := by exact prefixLift 1314039
  have htrace : WordTrace (prefixWord ++ tailWord_1314039) baseStart_1314039 baseEnd_1314039 := by
    simpa [prefixWord, tailWord_1314039, baseEnd_1314039] using wordTrace_append hprefix tailTrace_1314039
  have hstable : (prefixWord ++ tailWord_1314039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314039).length < 2 ^ (prefixWord ++ tailWord_1314039).sum := by decide
  have hdescent : baseEnd_1314039 < baseStart_1314039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314090 : List Nat := [3, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_1314090 : Nat := 118140960795 + 1314090 * 2 ^ 59
def prefixEnd_1314090 : Nat := 4983230072969 + 3 ^ 40 * 1314090 * 2
def baseEnd_1314090 : Nat := 299893241451941711347385

theorem tailTrace_1314090 : CollatzResearch.WordTrace tailWord_1314090 prefixEnd_1314090 299893241451941711347385 := by
  unfold tailWord_1314090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11982199952320958387356931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31952533206189222366285149 11982199952320958387356931)
  ·
    refine ⟨17973299928481437581035397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11982199952320958387356931 17973299928481437581035397)
    ·
      refine ⟨3369993736590269546444137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17973299928481437581035397 3369993736590269546444137)
      ·
        refine ⟨2527495302442702159833103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3369993736590269546444137 2527495302442702159833103)
        ·
          refine ⟨3791242953664053239749655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527495302442702159833103 3791242953664053239749655)
          ·
            refine ⟨5686864430496079859624483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3791242953664053239749655 5686864430496079859624483)
            ·
              refine ⟨8530296645744119789436725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5686864430496079859624483 8530296645744119789436725)
              ·
                refine ⟨799715310538511230259693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8530296645744119789436725 799715310538511230259693)
                ·
                  refine ⟨299893241451941711347385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799715310538511230259693 299893241451941711347385)
                  ·
                    rfl

theorem cell21_1314090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_1314090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314090 prefixEnd_1314090 := by exact prefixLift 1314090
  have htrace : WordTrace (prefixWord ++ tailWord_1314090) baseStart_1314090 baseEnd_1314090 := by
    simpa [prefixWord, tailWord_1314090, baseEnd_1314090] using wordTrace_append hprefix tailTrace_1314090
  have hstable : (prefixWord ++ tailWord_1314090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314090).length < 2 ^ (prefixWord ++ tailWord_1314090).sum := by decide
  have hdescent : baseEnd_1314090 < baseStart_1314090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314101 : List Nat := [1, 3, 3, 1, 2, 3, 8]
def baseStart_1314101 : Nat := 118140960795 + 1314101 * 2 ^ 59
def prefixEnd_1314101 : Nat := 4983230072969 + 3 ^ 40 * 1314101 * 2
def baseEnd_1314101 : Nat := 33321750200200904073781

theorem tailTrace_1314101 : CollatzResearch.WordTrace tailWord_1314101 prefixEnd_1314101 33321750200200904073781 := by
  unfold tailWord_1314101
  simp only [CollatzResearch.WordTrace]
  refine ⟨47929201012243982428078157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31952800674829321618718771 47929201012243982428078157)
  ·
    refine ⟨17973450379591493410529309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47929201012243982428078157 17973450379591493410529309)
    ·
      refine ⟨6740043892346810028948491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17973450379591493410529309 6740043892346810028948491)
      ·
        refine ⟨10110065838520215043422737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6740043892346810028948491 10110065838520215043422737)
        ·
          refine ⟨7582549378890161282567053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10110065838520215043422737 7582549378890161282567053)
          ·
            refine ⟨2843456017083810480962645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7582549378890161282567053 2843456017083810480962645)
            ·
              refine ⟨33321750200200904073781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2843456017083810480962645 33321750200200904073781)
              ·
                rfl

theorem cell21_1314101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 8].length) (baseStart_1314101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314101 prefixEnd_1314101 := by exact prefixLift 1314101
  have htrace : WordTrace (prefixWord ++ tailWord_1314101) baseStart_1314101 baseEnd_1314101 := by
    simpa [prefixWord, tailWord_1314101, baseEnd_1314101] using wordTrace_append hprefix tailTrace_1314101
  have hstable : (prefixWord ++ tailWord_1314101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314101).length < 2 ^ (prefixWord ++ tailWord_1314101).sum := by decide
  have hdescent : baseEnd_1314101 < baseStart_1314101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314132 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1314132 : Nat := 118140960795 + 1314132 * 2 ^ 59
def prefixEnd_1314132 : Nat := 4983230072969 + 3 ^ 40 * 1314132 * 2
def baseEnd_1314132 : Nat := 299902826424158971647299

theorem tailTrace_1314132 : CollatzResearch.WordTrace tailWord_1314132 prefixEnd_1314132 299902826424158971647299 := by
  unfold tailWord_1314132
  simp only [CollatzResearch.WordTrace]
  refine ⟨23965165837565837361228325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31953554450087783148304433 23965165837565837361228325)
  ·
    refine ⟨4493468594543594505230311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23965165837565837361228325 4493468594543594505230311)
    ·
      refine ⟨6740202891815391757845467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4493468594543594505230311 6740202891815391757845467)
      ·
        refine ⟨10110304337723087636768201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6740202891815391757845467 10110304337723087636768201)
        ·
          refine ⟨7582728253292315727576151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10110304337723087636768201 7582728253292315727576151)
          ·
            refine ⟨11374092379938473591364227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7582728253292315727576151 11374092379938473591364227)
            ·
              refine ⟨17061138569907710387046341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11374092379938473591364227 17061138569907710387046341)
              ·
                refine ⟨3198963481857695697571189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17061138569907710387046341 3198963481857695697571189)
                ·
                  refine ⟨299902826424158971647299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3198963481857695697571189 299902826424158971647299)
                  ·
                    rfl

theorem cell21_1314132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1314132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314132 prefixEnd_1314132 := by exact prefixLift 1314132
  have htrace : WordTrace (prefixWord ++ tailWord_1314132) baseStart_1314132 baseEnd_1314132 := by
    simpa [prefixWord, tailWord_1314132, baseEnd_1314132] using wordTrace_append hprefix tailTrace_1314132
  have hstable : (prefixWord ++ tailWord_1314132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314132).length < 2 ^ (prefixWord ++ tailWord_1314132).sum := by decide
  have hdescent : baseEnd_1314132 < baseStart_1314132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314141 : List Nat := [1, 4, 5, 1, 1, 2, 1, 3, 3]
def baseStart_1314141 : Nat := 118140960795 + 1314141 * 2 ^ 59
def prefixEnd_1314141 : Nat := 4983230072969 + 3 ^ 40 * 1314141 * 2
def baseEnd_1314141 : Nat := 299904880346776955997281

theorem tailTrace_1314141 : CollatzResearch.WordTrace tailWord_1314141 prefixEnd_1314141 299904880346776955997281 := by
  unfold tailWord_1314141
  simp only [CollatzResearch.WordTrace]
  refine ⟨47930659932099069259534277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31953773288066046173022851 47930659932099069259534277)
  ·
    refine ⟨8986998737268575486162677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47930659932099069259534277 8986998737268575486162677)
    ·
      refine ⟨842531131618928951827751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8986998737268575486162677 842531131618928951827751)
      ·
        refine ⟨1263796697428393427741627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842531131618928951827751 1263796697428393427741627)
        ·
          refine ⟨1895695046142590141612441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263796697428393427741627 1895695046142590141612441)
          ·
            refine ⟨1421771284606942606209331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895695046142590141612441 1421771284606942606209331)
            ·
              refine ⟨2132656926910413909313997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421771284606942606209331 2132656926910413909313997)
              ·
                refine ⟨799746347591405215992749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2132656926910413909313997 799746347591405215992749)
                ·
                  refine ⟨299904880346776955997281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799746347591405215992749 299904880346776955997281)
                  ·
                    rfl

theorem cell21_1314141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_1314141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314141 prefixEnd_1314141 := by exact prefixLift 1314141
  have htrace : WordTrace (prefixWord ++ tailWord_1314141) baseStart_1314141 baseEnd_1314141 := by
    simpa [prefixWord, tailWord_1314141, baseEnd_1314141] using wordTrace_append hprefix tailTrace_1314141
  have hstable : (prefixWord ++ tailWord_1314141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314141).length < 2 ^ (prefixWord ++ tailWord_1314141).sum := by decide
  have hdescent : baseEnd_1314141 < baseStart_1314141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314180 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1314180 : Nat := 118140960795 + 1314180 * 2 ^ 59
def prefixEnd_1314180 : Nat := 4983230072969 + 3 ^ 40 * 1314180 * 2
def baseEnd_1314180 : Nat := 299913780678121554847201

theorem tailTrace_1314180 : CollatzResearch.WordTrace tailWord_1314180 prefixEnd_1314180 299913780678121554847201 := by
  unfold tailWord_1314180
  simp only [CollatzResearch.WordTrace]
  refine ⟨23966041189478889460101997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31954721585971852613469329 23966041189478889460101997)
  ·
    refine ⟨8987265446054583547538249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23966041189478889460101997 8987265446054583547538249)
    ·
      refine ⟨6740449084540937660653687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8987265446054583547538249 6740449084540937660653687)
      ·
        refine ⟨10110673626811406490980531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6740449084540937660653687 10110673626811406490980531)
        ·
          refine ⟨15166010440217109736470797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10110673626811406490980531 15166010440217109736470797)
          ·
            refine ⟨5687253915081416151176549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15166010440217109736470797 5687253915081416151176549)
            ·
              refine ⟨1066360109077765528345603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5687253915081416151176549 1066360109077765528345603)
              ·
                refine ⟨1599540163616648292518405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066360109077765528345603 1599540163616648292518405)
                ·
                  refine ⟨299913780678121554847201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599540163616648292518405 299913780678121554847201)
                  ·
                    rfl

theorem cell21_1314180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1314180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314180 prefixEnd_1314180 := by exact prefixLift 1314180
  have htrace : WordTrace (prefixWord ++ tailWord_1314180) baseStart_1314180 baseEnd_1314180 := by
    simpa [prefixWord, tailWord_1314180, baseEnd_1314180] using wordTrace_append hprefix tailTrace_1314180
  have hstable : (prefixWord ++ tailWord_1314180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314180).length < 2 ^ (prefixWord ++ tailWord_1314180).sum := by decide
  have hdescent : baseEnd_1314180 < baseStart_1314180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314225 : List Nat := [1, 2, 2, 4, 1, 1, 3, 4, 3]
def baseStart_1314225 : Nat := 118140960795 + 1314225 * 2 ^ 59
def prefixEnd_1314225 : Nat := 4983230072969 + 3 ^ 40 * 1314225 * 2
def baseEnd_1314225 : Nat := 299924050291211476597109

theorem tailTrace_1314225 : CollatzResearch.WordTrace tailWord_1314225 prefixEnd_1314225 299924050291211476597109 := by
  unfold tailWord_1314225
  simp only [CollatzResearch.WordTrace]
  refine ⟨47933723663794751605592129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31955815775863167737061419 47933723663794751605592129)
  ·
    refine ⟨35950292747846063704194097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47933723663794751605592129 35950292747846063704194097)
    ·
      refine ⟨26962719560884547778145573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35950292747846063704194097 26962719560884547778145573)
      ·
        refine ⟨5055509917665852708402295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26962719560884547778145573 5055509917665852708402295)
        ·
          refine ⟨7583264876498779062603443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5055509917665852708402295 7583264876498779062603443)
          ·
            refine ⟨11374897314748168593905165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7583264876498779062603443 11374897314748168593905165)
            ·
              refine ⟨4265586493030563222714437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11374897314748168593905165 4265586493030563222714437)
              ·
                refine ⟨799797467443230604258957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4265586493030563222714437 799797467443230604258957)
                ·
                  refine ⟨299924050291211476597109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799797467443230604258957 299924050291211476597109)
                  ·
                    rfl

theorem cell21_1314225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_1314225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314225 prefixEnd_1314225 := by exact prefixLift 1314225
  have htrace : WordTrace (prefixWord ++ tailWord_1314225) baseStart_1314225 baseEnd_1314225 := by
    simpa [prefixWord, tailWord_1314225, baseEnd_1314225] using wordTrace_append hprefix tailTrace_1314225
  have hstable : (prefixWord ++ tailWord_1314225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314225).length < 2 ^ (prefixWord ++ tailWord_1314225).sum := by decide
  have hdescent : baseEnd_1314225 < baseStart_1314225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314310 : List Nat := [6, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1314310 : Nat := 118140960795 + 1314310 * 2 ^ 59
def prefixEnd_1314310 : Nat := 4983230072969 + 3 ^ 40 * 1314310 * 2
def baseEnd_1314310 : Nat := 299943448449270217680269

theorem tailTrace_1314310 : CollatzResearch.WordTrace tailWord_1314310 prefixEnd_1314310 299943448449270217680269 := by
  unfold tailWord_1314310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498025745890212847576137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31957882578991207414957589 1498025745890212847576137)
  ·
    refine ⟨1123519309417659635682103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1498025745890212847576137 1123519309417659635682103)
    ·
      refine ⟨1685278964126489453523155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123519309417659635682103 1685278964126489453523155)
      ·
        refine ⟨2527918446189734180284733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685278964126489453523155 2527918446189734180284733)
        ·
          refine ⟨947969417321150317606775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2527918446189734180284733 947969417321150317606775)
          ·
            refine ⟨1421954125981725476410163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947969417321150317606775 1421954125981725476410163)
            ·
              refine ⟨2132931188972588214615245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421954125981725476410163 2132931188972588214615245)
              ·
                refine ⟨799849195864720580480717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2132931188972588214615245 799849195864720580480717)
                ·
                  refine ⟨299943448449270217680269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799849195864720580480717 299943448449270217680269)
                  ·
                    rfl

theorem cell21_1314310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1314310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314310 prefixEnd_1314310 := by exact prefixLift 1314310
  have htrace : WordTrace (prefixWord ++ tailWord_1314310) baseStart_1314310 baseEnd_1314310 := by
    simpa [prefixWord, tailWord_1314310, baseEnd_1314310] using wordTrace_append hprefix tailTrace_1314310
  have hstable : (prefixWord ++ tailWord_1314310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314310).length < 2 ^ (prefixWord ++ tailWord_1314310).sum := by decide
  have hdescent : baseEnd_1314310 < baseStart_1314310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314391 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 4]
def baseStart_1314391 : Nat := 118140960795 + 1314391 * 2 ^ 59
def prefixEnd_1314391 : Nat := 4983230072969 + 3 ^ 40 * 1314391 * 2
def baseEnd_1314391 : Nat := 299961933752832076830103

theorem tailTrace_1314391 : CollatzResearch.WordTrace tailWord_1314391 prefixEnd_1314391 299961933752832076830103 := by
  unfold tailWord_1314391
  simp only [CollatzResearch.WordTrace]
  refine ⟨47939778181193361956135027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31959852120795574637423351 47939778181193361956135027)
  ·
    refine ⟨71909667271790042934202541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47939778181193361956135027 71909667271790042934202541)
    ·
      refine ⟨26966125226921266100325953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71909667271790042934202541 26966125226921266100325953)
      ·
        refine ⟨20224593920190949575244465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26966125226921266100325953 20224593920190949575244465)
        ·
          refine ⟨15168445440143212181433349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20224593920190949575244465 15168445440143212181433349)
          ·
            refine ⟨2844083520026852284018753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15168445440143212181433349 2844083520026852284018753)
            ·
              refine ⟨2133062640020139213014065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2844083520026852284018753 2133062640020139213014065)
              ·
                refine ⟨1599796980015104409760549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133062640020139213014065 1599796980015104409760549)
                ·
                  refine ⟨299961933752832076830103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599796980015104409760549 299961933752832076830103)
                  ·
                    rfl

theorem cell21_1314391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 4].length) (baseStart_1314391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314391 prefixEnd_1314391 := by exact prefixLift 1314391
  have htrace : WordTrace (prefixWord ++ tailWord_1314391) baseStart_1314391 baseEnd_1314391 := by
    simpa [prefixWord, tailWord_1314391, baseEnd_1314391] using wordTrace_append hprefix tailTrace_1314391
  have hstable : (prefixWord ++ tailWord_1314391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314391).length < 2 ^ (prefixWord ++ tailWord_1314391).sum := by decide
  have hdescent : baseEnd_1314391 < baseStart_1314391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314405 : List Nat := [1, 3, 1, 3, 3, 1, 3, 6]
def baseStart_1314405 : Nat := 118140960795 + 1314405 * 2 ^ 59
def prefixEnd_1314405 : Nat := 4983230072969 + 3 ^ 40 * 1314405 * 2
def baseEnd_1314405 : Nat := 99988376247857054532247

theorem tailTrace_1314405 : CollatzResearch.WordTrace tailWord_1314405 prefixEnd_1314405 99988376247857054532247 := by
  unfold tailWord_1314405
  simp only [CollatzResearch.WordTrace]
  refine ⟨47940288803142642347144669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31960192535428428231429779 47940288803142642347144669)
  ·
    refine ⟨17977608301178490880179251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47940288803142642347144669 17977608301178490880179251)
    ·
      refine ⟨26966412451767736320268877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17977608301178490880179251 26966412451767736320268877)
      ·
        refine ⟨10112404669412901120100829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26966412451767736320268877 10112404669412901120100829)
        ·
          refine ⟨3792151751029837920037811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10112404669412901120100829 3792151751029837920037811)
          ·
            refine ⟨5688227626544756880056717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3792151751029837920037811 5688227626544756880056717)
            ·
              refine ⟨2133085359954283830021269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5688227626544756880056717 2133085359954283830021269)
              ·
                refine ⟨99988376247857054532247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2133085359954283830021269 99988376247857054532247)
                ·
                  rfl

theorem cell21_1314405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 6].length) (baseStart_1314405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314405 prefixEnd_1314405 := by exact prefixLift 1314405
  have htrace : WordTrace (prefixWord ++ tailWord_1314405) baseStart_1314405 baseEnd_1314405 := by
    simpa [prefixWord, tailWord_1314405, baseEnd_1314405] using wordTrace_append hprefix tailTrace_1314405
  have hstable : (prefixWord ++ tailWord_1314405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314405).length < 2 ^ (prefixWord ++ tailWord_1314405).sum := by decide
  have hdescent : baseEnd_1314405 < baseStart_1314405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314467 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 4]
def baseStart_1314467 : Nat := 118140960795 + 1314467 * 2 ^ 59
def prefixEnd_1314467 : Nat := 4983230072969 + 3 ^ 40 * 1314467 * 2
def baseEnd_1314467 : Nat := 299979277988272833563281

theorem tailTrace_1314467 : CollatzResearch.WordTrace tailWord_1314467 prefixEnd_1314467 299979277988272833563281 := by
  unfold tailWord_1314467
  simp only [CollatzResearch.WordTrace]
  refine ⟨47942550128918026935901655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31961700085945351290601103 47942550128918026935901655)
  ·
    refine ⟨71913825193377040403852483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47942550128918026935901655 71913825193377040403852483)
    ·
      refine ⟨107870737790065560605778725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71913825193377040403852483 107870737790065560605778725)
      ·
        refine ⟨20225763335637292613583511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107870737790065560605778725 20225763335637292613583511)
        ·
          refine ⟨30338645003455938920375267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20225763335637292613583511 30338645003455938920375267)
          ·
            refine ⟨45507967505183908380562901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30338645003455938920375267 45507967505183908380562901)
            ·
              refine ⟨1066592988402747852669443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45507967505183908380562901 1066592988402747852669443)
              ·
                refine ⟨1599889482604121779004165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066592988402747852669443 1599889482604121779004165)
                ·
                  refine ⟨299979277988272833563281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599889482604121779004165 299979277988272833563281)
                  ·
                    rfl

theorem cell21_1314467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 4].length) (baseStart_1314467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314467 prefixEnd_1314467 := by exact prefixLift 1314467
  have htrace : WordTrace (prefixWord ++ tailWord_1314467) baseStart_1314467 baseEnd_1314467 := by
    simpa [prefixWord, tailWord_1314467, baseEnd_1314467] using wordTrace_append hprefix tailTrace_1314467
  have hstable : (prefixWord ++ tailWord_1314467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314467).length < 2 ^ (prefixWord ++ tailWord_1314467).sum := by decide
  have hdescent : baseEnd_1314467 < baseStart_1314467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314540 : List Nat := [2, 2, 1, 1, 2, 2, 4, 7]
def baseStart_1314540 : Nat := 118140960795 + 1314540 * 2 ^ 59
def prefixEnd_1314540 : Nat := 4983230072969 + 3 ^ 40 * 1314540 * 2
def baseEnd_1314540 : Nat := 99998645860946976282155

theorem tailTrace_1314540 : CollatzResearch.WordTrace tailWord_1314540 prefixEnd_1314540 99998645860946976282155 := by
  unfold tailWord_1314540
  simp only [CollatzResearch.WordTrace]
  refine ⟨23972606328826780201654537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31963475105102373602206049 23972606328826780201654537)
  ·
    refine ⟨17979454746620085151240903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23972606328826780201654537 17979454746620085151240903)
    ·
      refine ⟨26969182119930127726861355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17979454746620085151240903 26969182119930127726861355)
      ·
        refine ⟨40453773179895191590292033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26969182119930127726861355 40453773179895191590292033)
        ·
          refine ⟨30340329884921393692719025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40453773179895191590292033 30340329884921393692719025)
          ·
            refine ⟨22755247413691045269539269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30340329884921393692719025 22755247413691045269539269)
            ·
              refine ⟨4266608890067070988038613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22755247413691045269539269 4266608890067070988038613)
              ·
                refine ⟨99998645860946976282155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4266608890067070988038613 99998645860946976282155)
                ·
                  rfl

theorem cell21_1314540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_1314540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314540 prefixEnd_1314540 := by exact prefixLift 1314540
  have htrace : WordTrace (prefixWord ++ tailWord_1314540) baseStart_1314540 baseEnd_1314540 := by
    simpa [prefixWord, tailWord_1314540, baseEnd_1314540] using wordTrace_append hprefix tailTrace_1314540
  have hstable : (prefixWord ++ tailWord_1314540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314540).length < 2 ^ (prefixWord ++ tailWord_1314540).sum := by decide
  have hdescent : baseEnd_1314540 < baseStart_1314540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314566 : List Nat := [6, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1314566 : Nat := 118140960795 + 1314566 * 2 ^ 59
def prefixEnd_1314566 : Nat := 4983230072969 + 3 ^ 40 * 1314566 * 2
def baseEnd_1314566 : Nat := 100000623712356887137693

theorem tailTrace_1314566 : CollatzResearch.WordTrace tailWord_1314566 prefixEnd_1314566 100000623712356887137693 := by
  unfold tailWord_1314566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498317529861230213867361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31964107303706244562503701 1498317529861230213867361)
  ·
    refine ⟨1123738147395922660400521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1498317529861230213867361 1123738147395922660400521)
    ·
      refine ⟨842803610546941995300391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1123738147395922660400521 842803610546941995300391)
      ·
        refine ⟨1264205415820412992950587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842803610546941995300391 1264205415820412992950587)
        ·
          refine ⟨1896308123730619489425881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264205415820412992950587 1896308123730619489425881)
          ·
            refine ⟨1422231092797964617069411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1896308123730619489425881 1422231092797964617069411)
            ·
              refine ⟨2133346639196946925604117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422231092797964617069411 2133346639196946925604117)
              ·
                refine ⟨100000623712356887137693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2133346639196946925604117 100000623712356887137693)
                ·
                  rfl

theorem cell21_1314566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1314566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314566 prefixEnd_1314566 := by exact prefixLift 1314566
  have htrace : WordTrace (prefixWord ++ tailWord_1314566) baseStart_1314566 baseEnd_1314566 := by
    simpa [prefixWord, tailWord_1314566, baseEnd_1314566] using wordTrace_append hprefix tailTrace_1314566
  have hstable : (prefixWord ++ tailWord_1314566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314566).length < 2 ^ (prefixWord ++ tailWord_1314566).sum := by decide
  have hdescent : baseEnd_1314566 < baseStart_1314566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314616 : List Nat := [2, 1, 2, 1, 3, 4, 8]
def baseStart_1314616 : Nat := 118140960795 + 1314616 * 2 ^ 59
def prefixEnd_1314616 : Nat := 4983230072969 + 3 ^ 40 * 1314616 * 2
def baseEnd_1314616 : Nat := 33334809090920187286627

theorem tailTrace_1314616 : CollatzResearch.WordTrace tailWord_1314616 prefixEnd_1314616 33334809090920187286627 := by
  unfold tailWord_1314616
  simp only [CollatzResearch.WordTrace]
  refine ⟨23973992302689112691537851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31965323070252150255383801 23973992302689112691537851)
  ·
    refine ⟨35960988454033669037306777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23973992302689112691537851 35960988454033669037306777)
    ·
      refine ⟨26970741340525251777980083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35960988454033669037306777 26970741340525251777980083)
      ·
        refine ⟨40456112010787877666970125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26970741340525251777980083 40456112010787877666970125)
        ·
          refine ⟨15171042004045454125113797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40456112010787877666970125 15171042004045454125113797)
          ·
            refine ⟨2844570375758522648458837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15171042004045454125113797 2844570375758522648458837)
            ·
              refine ⟨33334809090920187286627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2844570375758522648458837 33334809090920187286627)
              ·
                rfl

theorem cell21_1314616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 8].length) (baseStart_1314616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314616 prefixEnd_1314616 := by exact prefixLift 1314616
  have htrace : WordTrace (prefixWord ++ tailWord_1314616) baseStart_1314616 baseEnd_1314616 := by
    simpa [prefixWord, tailWord_1314616, baseEnd_1314616] using wordTrace_append hprefix tailTrace_1314616
  have hstable : (prefixWord ++ tailWord_1314616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314616).length < 2 ^ (prefixWord ++ tailWord_1314616).sum := by decide
  have hdescent : baseEnd_1314616 < baseStart_1314616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314636 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_1314636 : Nat := 118140960795 + 1314636 * 2 ^ 59
def prefixEnd_1314636 : Nat := 4983230072969 + 3 ^ 40 * 1314636 * 2
def baseEnd_1314636 : Nat := 300017846090766095246269

theorem tailTrace_1314636 : CollatzResearch.WordTrace tailWord_1314636 prefixEnd_1314636 300017846090766095246269 := by
  unfold tailWord_1314636
  simp only [CollatzResearch.WordTrace]
  refine ⟨23974357032652884399401881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31965809376870512532535841 23974357032652884399401881)
  ·
    refine ⟨17980767774489663299551411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23974357032652884399401881 17980767774489663299551411)
    ·
      refine ⟨26971151661734494949327117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17980767774489663299551411 26971151661734494949327117)
      ·
        refine ⟨10114181873150435605997669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26971151661734494949327117 10114181873150435605997669)
        ·
          refine ⟨1896409101215706676124563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10114181873150435605997669 1896409101215706676124563)
          ·
            refine ⟨2844613651823560014186845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896409101215706676124563 2844613651823560014186845)
            ·
              refine ⟨1066730119433835005320067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2844613651823560014186845 1066730119433835005320067)
              ·
                refine ⟨1600095179150752507980101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066730119433835005320067 1600095179150752507980101)
                ·
                  refine ⟨300017846090766095246269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600095179150752507980101 300017846090766095246269)
                  ·
                    rfl

theorem cell21_1314636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_1314636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314636 prefixEnd_1314636 := by exact prefixLift 1314636
  have htrace : WordTrace (prefixWord ++ tailWord_1314636) baseStart_1314636 baseEnd_1314636 := by
    simpa [prefixWord, tailWord_1314636, baseEnd_1314636] using wordTrace_append hprefix tailTrace_1314636
  have hstable : (prefixWord ++ tailWord_1314636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314636).length < 2 ^ (prefixWord ++ tailWord_1314636).sum := by decide
  have hdescent : baseEnd_1314636 < baseStart_1314636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314681 : List Nat := [1, 2, 1, 3, 2, 2, 5, 2, 3]
def baseStart_1314681 : Nat := 118140960795 + 1314681 * 2 ^ 59
def prefixEnd_1314681 : Nat := 4983230072969 + 3 ^ 40 * 1314681 * 2
def baseEnd_1314681 : Nat := 300028115703856016996177

theorem tailTrace_1314681 : CollatzResearch.WordTrace tailWord_1314681 prefixEnd_1314681 300028115703856016996177 := by
  unfold tailWord_1314681
  simp only [CollatzResearch.WordTrace]
  refine ⟨47950355350142741484191897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31966903566761827656127931 47950355350142741484191897)
  ·
    refine ⟨35962766512607056113143923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47950355350142741484191897 35962766512607056113143923)
    ·
      refine ⟨53944149768910584169715885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35962766512607056113143923 53944149768910584169715885)
      ·
        refine ⟨20229056163341469063643457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53944149768910584169715885 20229056163341469063643457)
        ·
          refine ⟨15171792122506101797732593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20229056163341469063643457 15171792122506101797732593)
          ·
            refine ⟨11378844091879576348299445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15171792122506101797732593 11378844091879576348299445)
            ·
              refine ⟨1066766633613710282653073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11378844091879576348299445 1066766633613710282653073)
              ·
                refine ⟨800074975210282711989805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1066766633613710282653073 800074975210282711989805)
                ·
                  refine ⟨300028115703856016996177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800074975210282711989805 300028115703856016996177)
                  ·
                    rfl

theorem cell21_1314681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_1314681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314681 prefixEnd_1314681 := by exact prefixLift 1314681
  have htrace : WordTrace (prefixWord ++ tailWord_1314681) baseStart_1314681 baseEnd_1314681 := by
    simpa [prefixWord, tailWord_1314681, baseEnd_1314681] using wordTrace_append hprefix tailTrace_1314681
  have hstable : (prefixWord ++ tailWord_1314681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314681).length < 2 ^ (prefixWord ++ tailWord_1314681).sum := by decide
  have hdescent : baseEnd_1314681 < baseStart_1314681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314692 : List Nat := [2, 3, 2, 1, 1, 1, 3, 8]
def baseStart_1314692 : Nat := 118140960795 + 1314692 * 2 ^ 59
def prefixEnd_1314692 : Nat := 4983230072969 + 3 ^ 40 * 1314692 * 2
def baseEnd_1314692 : Nat := 100010208684574147437607

theorem tailTrace_1314692 : CollatzResearch.WordTrace tailWord_1314692 prefixEnd_1314692 100010208684574147437607 := by
  unfold tailWord_1314692
  simp only [CollatzResearch.WordTrace]
  refine ⟨23975378276551445181421165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31967171035401926908561553 23975378276551445181421165)
  ·
    refine ⟨8990766853706791943032937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23975378276551445181421165 8990766853706791943032937)
    ·
      refine ⟨6743075140280093957274703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8990766853706791943032937 6743075140280093957274703)
      ·
        refine ⟨10114612710420140935912055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6743075140280093957274703 10114612710420140935912055)
        ·
          refine ⟨15171919065630211403868083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10114612710420140935912055 15171919065630211403868083)
          ·
            refine ⟨22757878598445317105802125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15171919065630211403868083 22757878598445317105802125)
            ·
              refine ⟨8534204474416993914675797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22757878598445317105802125 8534204474416993914675797)
              ·
                refine ⟨100010208684574147437607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8534204474416993914675797 100010208684574147437607)
                ·
                  rfl

theorem cell21_1314692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_1314692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314692 prefixEnd_1314692 := by exact prefixLift 1314692
  have htrace : WordTrace (prefixWord ++ tailWord_1314692) baseStart_1314692 baseEnd_1314692 := by
    simpa [prefixWord, tailWord_1314692, baseEnd_1314692] using wordTrace_append hprefix tailTrace_1314692
  have hstable : (prefixWord ++ tailWord_1314692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314692).length < 2 ^ (prefixWord ++ tailWord_1314692).sum := by decide
  have hdescent : baseEnd_1314692 < baseStart_1314692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314695 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 4]
def baseStart_1314695 : Nat := 118140960795 + 1314695 * 2 ^ 59
def prefixEnd_1314695 : Nat := 4983230072969 + 3 ^ 40 * 1314695 * 2
def baseEnd_1314695 : Nat := 300031310694595103762815

theorem tailTrace_1314695 : CollatzResearch.WordTrace tailWord_1314695 prefixEnd_1314695 300031310694595103762815 := by
  unfold tailWord_1314695
  simp only [CollatzResearch.WordTrace]
  refine ⟨47950865972092021875201539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31967243981394681250134359 47950865972092021875201539)
  ·
    refine ⟨71926298958138032812802309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47950865972092021875201539 71926298958138032812802309)
    ·
      refine ⟨13486181054650881152400433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71926298958138032812802309 13486181054650881152400433)
      ·
        refine ⟨10114635790988160864300325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13486181054650881152400433 10114635790988160864300325)
        ·
          refine ⟨1896494210810280162056311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10114635790988160864300325 1896494210810280162056311)
          ·
            refine ⟨2844741316215420243084467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896494210810280162056311 2844741316215420243084467)
            ·
              refine ⟨4267111974323130364626701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844741316215420243084467 4267111974323130364626701)
              ·
                refine ⟨1600166990371173886735013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4267111974323130364626701 1600166990371173886735013)
                ·
                  refine ⟨300031310694595103762815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600166990371173886735013 300031310694595103762815)
                  ·
                    rfl

theorem cell21_1314695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 4].length) (baseStart_1314695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314695 prefixEnd_1314695 := by exact prefixLift 1314695
  have htrace : WordTrace (prefixWord ++ tailWord_1314695) baseStart_1314695 baseEnd_1314695 := by
    simpa [prefixWord, tailWord_1314695, baseEnd_1314695] using wordTrace_append hprefix tailTrace_1314695
  have hstable : (prefixWord ++ tailWord_1314695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314695).length < 2 ^ (prefixWord ++ tailWord_1314695).sum := by decide
  have hdescent : baseEnd_1314695 < baseStart_1314695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314799 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 5]
def baseStart_1314799 : Nat := 118140960795 + 1314799 * 2 ^ 59
def prefixEnd_1314799 : Nat := 4983230072969 + 3 ^ 40 * 1314799 * 2
def baseEnd_1314799 : Nat := 300055044911514034029269

theorem tailTrace_1314799 : CollatzResearch.WordTrace tailWord_1314799 prefixEnd_1314799 300055044911514034029269 := by
  unfold tailWord_1314799
  simp only [CollatzResearch.WordTrace]
  refine ⟨47954659163715247636987451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31969772775810165091324967 47954659163715247636987451)
  ·
    refine ⟨71931988745572871455481177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47954659163715247636987451 71931988745572871455481177)
    ·
      refine ⟨53948991559179653591610883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71931988745572871455481177 53948991559179653591610883)
      ·
        refine ⟨80923487338769480387416325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53948991559179653591610883 80923487338769480387416325)
        ·
          refine ⟨15173153876019277572640561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80923487338769480387416325 15173153876019277572640561)
          ·
            refine ⟨11379865407014458179480421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15173153876019277572640561 11379865407014458179480421)
            ·
              refine ⟨2133724763815210908652579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11379865407014458179480421 2133724763815210908652579)
              ·
                refine ⟨3200587145722816362978869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133724763815210908652579 3200587145722816362978869)
                ·
                  refine ⟨300055044911514034029269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3200587145722816362978869 300055044911514034029269)
                  ·
                    rfl

theorem cell21_1314799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 5].length) (baseStart_1314799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314799 prefixEnd_1314799 := by exact prefixLift 1314799
  have htrace : WordTrace (prefixWord ++ tailWord_1314799) baseStart_1314799 baseEnd_1314799 := by
    simpa [prefixWord, tailWord_1314799, baseEnd_1314799] using wordTrace_append hprefix tailTrace_1314799
  have hstable : (prefixWord ++ tailWord_1314799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314799).length < 2 ^ (prefixWord ++ tailWord_1314799).sum := by decide
  have hdescent : baseEnd_1314799 < baseStart_1314799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314844 : List Nat := [2, 2, 3, 1, 3, 1, 9]
def baseStart_1314844 : Nat := 118140960795 + 1314844 * 2 ^ 59
def prefixEnd_1314844 : Nat := 4983230072969 + 3 ^ 40 * 1314844 * 2
def baseEnd_1314844 : Nat := 33340590502733772864353

theorem tailTrace_1314844 : CollatzResearch.WordTrace tailWord_1314844 prefixEnd_1314844 33340590502733772864353 := by
  unfold tailWord_1314844
  simp only [CollatzResearch.WordTrace]
  refine ⟨23978150224276110161187793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31970866965701480214917057 23978150224276110161187793)
  ·
    refine ⟨17983612668207082620890845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23978150224276110161187793 17983612668207082620890845)
    ·
      refine ⟨6743854750577655982834067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17983612668207082620890845 6743854750577655982834067)
      ·
        refine ⟨10115782125866483974251101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6743854750577655982834067 10115782125866483974251101)
        ·
          refine ⟨3793418297199931490344163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10115782125866483974251101 3793418297199931490344163)
          ·
            refine ⟨5690127445799897235516245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793418297199931490344163 5690127445799897235516245)
            ·
              refine ⟨33340590502733772864353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5690127445799897235516245 33340590502733772864353)
              ·
                rfl

theorem cell21_1314844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 9].length) (baseStart_1314844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314844 prefixEnd_1314844 := by exact prefixLift 1314844
  have htrace : WordTrace (prefixWord ++ tailWord_1314844) baseStart_1314844 baseEnd_1314844 := by
    simpa [prefixWord, tailWord_1314844, baseEnd_1314844] using wordTrace_append hprefix tailTrace_1314844
  have hstable : (prefixWord ++ tailWord_1314844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314844).length < 2 ^ (prefixWord ++ tailWord_1314844).sum := by decide
  have hdescent : baseEnd_1314844 < baseStart_1314844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314906 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_1314906 : Nat := 118140960795 + 1314906 * 2 ^ 59
def prefixEnd_1314906 : Nat := 4983230072969 + 3 ^ 40 * 1314906 * 2
def baseEnd_1314906 : Nat := 300079463769305625745717

theorem tailTrace_1314906 : CollatzResearch.WordTrace tailWord_1314906 prefixEnd_1314906 300079463769305625745717 := by
  unfold tailWord_1314906
  simp only [CollatzResearch.WordTrace]
  refine ⟨11989640443581901227783143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31972374516218403274088381 11989640443581901227783143)
  ·
    refine ⟨17984460665372851841674715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11989640443581901227783143 17984460665372851841674715)
    ·
      refine ⟨26976690998059277762512073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17984460665372851841674715 26976690998059277762512073)
      ·
        refine ⟨20232518248544458321884055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26976690998059277762512073 20232518248544458321884055)
        ·
          refine ⟨30348777372816687482826083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20232518248544458321884055 30348777372816687482826083)
          ·
            refine ⟨45523166059225031224239125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30348777372816687482826083 45523166059225031224239125)
            ·
              refine ⟨2133898409026173338636209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45523166059225031224239125 2133898409026173338636209)
              ·
                refine ⟨1600423806769630003977157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133898409026173338636209 1600423806769630003977157)
                ·
                  refine ⟨300079463769305625745717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600423806769630003977157 300079463769305625745717)
                  ·
                    rfl

theorem cell21_1314906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_1314906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314906 prefixEnd_1314906 := by exact prefixLift 1314906
  have htrace : WordTrace (prefixWord ++ tailWord_1314906) baseStart_1314906 baseEnd_1314906 := by
    simpa [prefixWord, tailWord_1314906, baseEnd_1314906] using wordTrace_append hprefix tailTrace_1314906
  have hstable : (prefixWord ++ tailWord_1314906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314906).length < 2 ^ (prefixWord ++ tailWord_1314906).sum := by decide
  have hdescent : baseEnd_1314906 < baseStart_1314906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314937 : List Nat := [1, 2, 1, 3, 4, 2, 3, 5]
def baseStart_1314937 : Nat := 118140960795 + 1314937 * 2 ^ 59
def prefixEnd_1314937 : Nat := 4983230072969 + 3 ^ 40 * 1314937 * 2
def baseEnd_1314937 : Nat := 100028846130552153576329

theorem tailTrace_1314937 : CollatzResearch.WordTrace tailWord_1314937 prefixEnd_1314937 100028846130552153576329 := by
  unfold tailWord_1314937
  simp only [CollatzResearch.WordTrace]
  refine ⟨47959692437215297205511065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31973128291476864803674043 47959692437215297205511065)
  ·
    refine ⟨35969769327911472904133299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47959692437215297205511065 35969769327911472904133299)
    ·
      refine ⟨53954653991867209356199949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35969769327911472904133299 53954653991867209356199949)
      ·
        refine ⟨20232995246950203508574981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53954653991867209356199949 20232995246950203508574981)
        ·
          refine ⟨3793686608803163157857809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20232995246950203508574981 3793686608803163157857809)
          ·
            refine ⟨2845264956602372368393357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3793686608803163157857809 2845264956602372368393357)
            ·
              refine ⟨1066974358725889638147509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2845264956602372368393357 1066974358725889638147509)
              ·
                refine ⟨100028846130552153576329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1066974358725889638147509 100028846130552153576329)
                ·
                  rfl

theorem cell21_1314937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 5].length) (baseStart_1314937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314937 prefixEnd_1314937 := by exact prefixLift 1314937
  have htrace : WordTrace (prefixWord ++ tailWord_1314937) baseStart_1314937 baseEnd_1314937 := by
    simpa [prefixWord, tailWord_1314937, baseEnd_1314937] using wordTrace_append hprefix tailTrace_1314937
  have hstable : (prefixWord ++ tailWord_1314937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314937).length < 2 ^ (prefixWord ++ tailWord_1314937).sum := by decide
  have hdescent : baseEnd_1314937 < baseStart_1314937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314965 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 6]
def baseStart_1314965 : Nat := 118140960795 + 1314965 * 2 ^ 59
def prefixEnd_1314965 : Nat := 4983230072969 + 3 ^ 40 * 1314965 * 2
def baseEnd_1314965 : Nat := 300092928373134634262263

theorem tailTrace_1314965 : CollatzResearch.WordTrace tailWord_1314965 prefixEnd_1314965 300092928373134634262263 := by
  unfold tailWord_1314965
  simp only [CollatzResearch.WordTrace]
  refine ⟨47960713681113857987530349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31973809120742571991686899 47960713681113857987530349)
  ·
    refine ⟨17985267630417696745323881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47960713681113857987530349 17985267630417696745323881)
    ·
      refine ⟨13488950722813272558992911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17985267630417696745323881 13488950722813272558992911)
      ·
        refine ⟨20233426084219908838489367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13488950722813272558992911 20233426084219908838489367)
        ·
          refine ⟨30350139126329863257734051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20233426084219908838489367 30350139126329863257734051)
          ·
            refine ⟨45525208689494794886601077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30350139126329863257734051 45525208689494794886601077)
            ·
              refine ⟨4267988314640137020618851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45525208689494794886601077 4267988314640137020618851)
              ·
                refine ⟨6401982471960205530928277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4267988314640137020618851 6401982471960205530928277)
                ·
                  refine ⟨300092928373134634262263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6401982471960205530928277 300092928373134634262263)
                  ·
                    rfl

theorem cell21_1314965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_1314965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314965 prefixEnd_1314965 := by exact prefixLift 1314965
  have htrace : WordTrace (prefixWord ++ tailWord_1314965) baseStart_1314965 baseEnd_1314965 := by
    simpa [prefixWord, tailWord_1314965, baseEnd_1314965] using wordTrace_append hprefix tailTrace_1314965
  have hstable : (prefixWord ++ tailWord_1314965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314965).length < 2 ^ (prefixWord ++ tailWord_1314965).sum := by decide
  have hdescent : baseEnd_1314965 < baseStart_1314965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314968 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_1314968 : Nat := 118140960795 + 1314968 * 2 ^ 59
def prefixEnd_1314968 : Nat := 4983230072969 + 3 ^ 40 * 1314968 * 2
def baseEnd_1314968 : Nat := 300093613014007295712257

theorem tailTrace_1314968 : CollatzResearch.WordTrace tailWord_1314968 prefixEnd_1314968 300093613014007295712257 := by
  unfold tailWord_1314968
  simp only [CollatzResearch.WordTrace]
  refine ⟨23980411550051494749944779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31973882066735326333259705 23980411550051494749944779)
  ·
    refine ⟨35970617325077242124917169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23980411550051494749944779 35970617325077242124917169)
    ·
      refine ⟨26977962993807931593687877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35970617325077242124917169 26977962993807931593687877)
      ·
        refine ⟨5058368061338987173816477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26977962993807931593687877 5058368061338987173816477)
        ·
          refine ⟨1896888023002120190181179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5058368061338987173816477 1896888023002120190181179)
          ·
            refine ⟨2845332034503180285271769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896888023002120190181179 2845332034503180285271769)
            ·
              refine ⟨2133999025877385213953827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2845332034503180285271769 2133999025877385213953827)
              ·
                refine ⟨3200998538816077820930741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133999025877385213953827 3200998538816077820930741)
                ·
                  refine ⟨300093613014007295712257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3200998538816077820930741 300093613014007295712257)
                  ·
                    rfl

theorem cell21_1314968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_1314968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1314968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1314968 prefixEnd_1314968 := by exact prefixLift 1314968
  have htrace : WordTrace (prefixWord ++ tailWord_1314968) baseStart_1314968 baseEnd_1314968 := by
    simpa [prefixWord, tailWord_1314968, baseEnd_1314968] using wordTrace_append hprefix tailTrace_1314968
  have hstable : (prefixWord ++ tailWord_1314968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314968).length < 2 ^ (prefixWord ++ tailWord_1314968).sum := by decide
  have hdescent : baseEnd_1314968 < baseStart_1314968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315030 : List Nat := [5, 2, 1, 2, 1, 2, 2, 6]
def baseStart_1315030 : Nat := 118140960795 + 1315030 * 2 ^ 59
def prefixEnd_1315030 : Nat := 4983230072969 + 3 ^ 40 * 1315030 * 2
def baseEnd_1315030 : Nat := 100035920752902988559599

theorem tailTrace_1315030 : CollatzResearch.WordTrace tailWord_1315030 prefixEnd_1315030 100035920752902988559599 := by
  unfold tailWord_1315030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997692776617398380540409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31975389617252249392431029 2997692776617398380540409)
  ·
    refine ⟨2248269582463048785405307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2997692776617398380540409 2248269582463048785405307)
    ·
      refine ⟨3372404373694573178107961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2248269582463048785405307 3372404373694573178107961)
      ·
        refine ⟨2529303280270929883580971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3372404373694573178107961 2529303280270929883580971)
        ·
          refine ⟨3793954920406394825371457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529303280270929883580971 3793954920406394825371457)
          ·
            refine ⟨2845466190304796119028593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3793954920406394825371457 2845466190304796119028593)
            ·
              refine ⟨2134099642728597089271445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2845466190304796119028593 2134099642728597089271445)
              ·
                refine ⟨100035920752902988559599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2134099642728597089271445 100035920752902988559599)
                ·
                  rfl

theorem cell21_1315030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_1315030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315030 prefixEnd_1315030 := by exact prefixLift 1315030
  have htrace : WordTrace (prefixWord ++ tailWord_1315030) baseStart_1315030 baseEnd_1315030 := by
    simpa [prefixWord, tailWord_1315030, baseEnd_1315030] using wordTrace_append hprefix tailTrace_1315030
  have hstable : (prefixWord ++ tailWord_1315030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315030).length < 2 ^ (prefixWord ++ tailWord_1315030).sum := by decide
  have hdescent : baseEnd_1315030 < baseStart_1315030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315103 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 5]
def baseStart_1315103 : Nat := 118140960795 + 1315103 * 2 ^ 59
def prefixEnd_1315103 : Nat := 4983230072969 + 3 ^ 40 * 1315103 * 2
def baseEnd_1315103 : Nat := 300124421853277060961981

theorem tailTrace_1315103 : CollatzResearch.WordTrace tailWord_1315103 prefixEnd_1315103 300124421853277060961981 := by
  unfold tailWord_1315103
  simp only [CollatzResearch.WordTrace]
  refine ⟨47965746954613907556053963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31977164636409271704035975 47965746954613907556053963)
  ·
    refine ⟨71948620431920861334080945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47965746954613907556053963 71948620431920861334080945)
    ·
      refine ⟨53961465323940646000560709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71948620431920861334080945 53961465323940646000560709)
      ·
        refine ⟨10117774748238871125105133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53961465323940646000560709 10117774748238871125105133)
        ·
          refine ⟨3794165530589576671914425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10117774748238871125105133 3794165530589576671914425)
          ·
            refine ⟨2845624147942182503935819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3794165530589576671914425 2845624147942182503935819)
            ·
              refine ⟨4268436221913273755903729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845624147942182503935819 4268436221913273755903729)
              ·
                refine ⟨3201327166434955316927797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4268436221913273755903729 3201327166434955316927797)
                ·
                  refine ⟨300124421853277060961981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3201327166434955316927797 300124421853277060961981)
                  ·
                    rfl

theorem cell21_1315103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_1315103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315103 prefixEnd_1315103 := by exact prefixLift 1315103
  have htrace : WordTrace (prefixWord ++ tailWord_1315103) baseStart_1315103 baseEnd_1315103 := by
    simpa [prefixWord, tailWord_1315103, baseEnd_1315103] using wordTrace_append hprefix tailTrace_1315103
  have hstable : (prefixWord ++ tailWord_1315103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315103).length < 2 ^ (prefixWord ++ tailWord_1315103).sum := by decide
  have hdescent : baseEnd_1315103 < baseStart_1315103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315134 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1315134 : Nat := 118140960795 + 1315134 * 2 ^ 59
def prefixEnd_1315134 : Nat := 4983230072969 + 3 ^ 40 * 1315134 * 2
def baseEnd_1315134 : Nat := 300131496475627895945251

theorem tailTrace_1315134 : CollatzResearch.WordTrace tailWord_1315134 prefixEnd_1315134 300131496475627895945251 := by
  unfold tailWord_1315134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5995859702187699981304057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31977918411667733233621637 5995859702187699981304057)
  ·
    refine ⟨4496894776640774985978043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5995859702187699981304057 4496894776640774985978043)
    ·
      refine ⟨6745342164961162478967065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4496894776640774985978043 6745342164961162478967065)
      ·
        refine ⟨5059006623720871859225299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6745342164961162478967065 5059006623720871859225299)
        ·
          refine ⟨7588509935581307788837949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5059006623720871859225299 7588509935581307788837949)
          ·
            refine ⟨2845691225842990420814231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7588509935581307788837949 2845691225842990420814231)
            ·
              refine ⟨4268536838764485631221347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845691225842990420814231 4268536838764485631221347)
              ·
                refine ⟨6402805258146728446832021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268536838764485631221347 6402805258146728446832021)
                ·
                  refine ⟨300131496475627895945251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6402805258146728446832021 300131496475627895945251)
                  ·
                    rfl

theorem cell21_1315134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1315134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315134 prefixEnd_1315134 := by exact prefixLift 1315134
  have htrace : WordTrace (prefixWord ++ tailWord_1315134) baseStart_1315134 baseEnd_1315134 := by
    simpa [prefixWord, tailWord_1315134, baseEnd_1315134] using wordTrace_append hprefix tailTrace_1315134
  have hstable : (prefixWord ++ tailWord_1315134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315134).length < 2 ^ (prefixWord ++ tailWord_1315134).sum := by decide
  have hdescent : baseEnd_1315134 < baseStart_1315134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315193 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 4]
def baseStart_1315193 : Nat := 118140960795 + 1315193 * 2 ^ 59
def prefixEnd_1315193 : Nat := 4983230072969 + 3 ^ 40 * 1315193 * 2
def baseEnd_1315193 : Nat := 300144961079456904461797

theorem tailTrace_1315193 : CollatzResearch.WordTrace tailWord_1315193 prefixEnd_1315193 300144961079456904461797 := by
  unfold tailWord_1315193
  simp only [CollatzResearch.WordTrace]
  refine ⟨47969029524287852926830233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31979353016191901951220155 47969029524287852926830233)
  ·
    refine ⟨35976772143215889695122675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47969029524287852926830233 35976772143215889695122675)
    ·
      refine ⟨53965158214823834542684013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35976772143215889695122675 53965158214823834542684013)
      ·
        refine ⟨20236934330558937953506505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53965158214823834542684013 20236934330558937953506505)
        ·
          refine ⟨15177700747919203465129879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20236934330558937953506505 15177700747919203465129879)
          ·
            refine ⟨22766551121878805197694819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15177700747919203465129879 22766551121878805197694819)
            ·
              refine ⟨34149826682818207796542229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22766551121878805197694819 34149826682818207796542229)
              ·
                refine ⟨1600773125757103490462917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34149826682818207796542229 1600773125757103490462917)
                ·
                  refine ⟨300144961079456904461797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600773125757103490462917 300144961079456904461797)
                  ·
                    rfl

theorem cell21_1315193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_1315193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315193 prefixEnd_1315193 := by exact prefixLift 1315193
  have htrace : WordTrace (prefixWord ++ tailWord_1315193) baseStart_1315193 baseEnd_1315193 := by
    simpa [prefixWord, tailWord_1315193, baseEnd_1315193] using wordTrace_append hprefix tailTrace_1315193
  have hstable : (prefixWord ++ tailWord_1315193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315193).length < 2 ^ (prefixWord ++ tailWord_1315193).sum := by decide
  have hdescent : baseEnd_1315193 < baseStart_1315193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315202 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1315202 : Nat := 118140960795 + 1315202 * 2 ^ 59
def prefixEnd_1315202 : Nat := 4983230072969 + 3 ^ 40 * 1315202 * 2
def baseEnd_1315202 : Nat := 300147015002074888811779

theorem tailTrace_1315202 : CollatzResearch.WordTrace tailWord_1315202 prefixEnd_1315202 300147015002074888811779 := by
  unfold tailWord_1315202
  simp only [CollatzResearch.WordTrace]
  refine ⟨11992339445313811865976965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31979571854170164975938573 11992339445313811865976965)
  ·
    refine ⟨2248563645996339724870681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11992339445313811865976965 2248563645996339724870681)
    ·
      refine ⟨1686422734497254793653011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2248563645996339724870681 1686422734497254793653011)
      ·
        refine ⟨2529634101745882190479517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686422734497254793653011 2529634101745882190479517)
        ·
          refine ⟨948612788154705821429819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2529634101745882190479517 948612788154705821429819)
          ·
            refine ⟨1422919182232058732144729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948612788154705821429819 1422919182232058732144729)
            ·
              refine ⟨1067189386674044049108547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422919182232058732144729 1067189386674044049108547)
              ·
                refine ⟨1600784080011066073662821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067189386674044049108547 1600784080011066073662821)
                ·
                  refine ⟨300147015002074888811779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600784080011066073662821 300147015002074888811779)
                  ·
                    rfl

theorem cell21_1315202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1315202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315202 prefixEnd_1315202 := by exact prefixLift 1315202
  have htrace : WordTrace (prefixWord ++ tailWord_1315202) baseStart_1315202 baseEnd_1315202 := by
    simpa [prefixWord, tailWord_1315202, baseEnd_1315202] using wordTrace_append hprefix tailTrace_1315202
  have hstable : (prefixWord ++ tailWord_1315202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315202).length < 2 ^ (prefixWord ++ tailWord_1315202).sum := by decide
  have hdescent : baseEnd_1315202 < baseStart_1315202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315224 : List Nat := [2, 1, 2, 5, 1, 1, 2, 7]
def baseStart_1315224 : Nat := 118140960795 + 1315224 * 2 ^ 59
def prefixEnd_1315224 : Nat := 4983230072969 + 3 ^ 40 * 1315224 * 2
def baseEnd_1315224 : Nat := 100050678567269246481689

theorem tailTrace_1315224 : CollatzResearch.WordTrace tailWord_1315224 prefixEnd_1315224 100050678567269246481689 := by
  unfold tailWord_1315224
  simp only [CollatzResearch.WordTrace]
  refine ⟨23985080093587772610604363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31980106791450363480805817 23985080093587772610604363)
  ·
    refine ⟨35977620140381658915906545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23985080093587772610604363 35977620140381658915906545)
    ·
      refine ⟨26983215105286244186929909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35977620140381658915906545 26983215105286244186929909)
      ·
        refine ⟨2529676416120585392524679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26983215105286244186929909 2529676416120585392524679)
        ·
          refine ⟨3794514624180878088787019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529676416120585392524679 3794514624180878088787019)
          ·
            refine ⟨5691771936271317133180529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794514624180878088787019 5691771936271317133180529)
            ·
              refine ⟨4268828952203487849885397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5691771936271317133180529 4268828952203487849885397)
              ·
                refine ⟨100050678567269246481689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4268828952203487849885397 100050678567269246481689)
                ·
                  rfl

theorem cell21_1315224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_1315224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315224 prefixEnd_1315224 := by exact prefixLift 1315224
  have htrace : WordTrace (prefixWord ++ tailWord_1315224) baseStart_1315224 baseEnd_1315224 := by
    simpa [prefixWord, tailWord_1315224, baseEnd_1315224] using wordTrace_append hprefix tailTrace_1315224
  have hstable : (prefixWord ++ tailWord_1315224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315224).length < 2 ^ (prefixWord ++ tailWord_1315224).sum := by decide
  have hdescent : baseEnd_1315224 < baseStart_1315224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315286 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1315286 : Nat := 118140960795 + 1315286 * 2 ^ 59
def prefixEnd_1315286 : Nat := 4983230072969 + 3 ^ 40 * 1315286 * 2
def baseEnd_1315286 : Nat := 300166184946509409411607

theorem tailTrace_1315286 : CollatzResearch.WordTrace tailWord_1315286 prefixEnd_1315286 300166184946509409411607 := by
  unfold tailWord_1315286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998276344559433113122857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31981614341967286539977141 2998276344559433113122857)
  ·
    refine ⟨2248707258419574834842143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2998276344559433113122857 2248707258419574834842143)
    ·
      refine ⟨3373060887629362252263215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2248707258419574834842143 3373060887629362252263215)
      ·
        refine ⟨5059591331444043378394823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3373060887629362252263215 5059591331444043378394823)
        ·
          refine ⟨7589386997166065067592235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5059591331444043378394823 7589386997166065067592235)
          ·
            refine ⟨11384080495749097601388353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589386997166065067592235 11384080495749097601388353)
            ·
              refine ⟨8538060371811823201041265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11384080495749097601388353 8538060371811823201041265)
              ·
                refine ⟨6403545278858867400780949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8538060371811823201041265 6403545278858867400780949)
                ·
                  refine ⟨300166184946509409411607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6403545278858867400780949 300166184946509409411607)
                  ·
                    rfl

theorem cell21_1315286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1315286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315286 prefixEnd_1315286 := by exact prefixLift 1315286
  have htrace : WordTrace (prefixWord ++ tailWord_1315286) baseStart_1315286 baseEnd_1315286 := by
    simpa [prefixWord, tailWord_1315286, baseEnd_1315286] using wordTrace_append hprefix tailTrace_1315286
  have hstable : (prefixWord ++ tailWord_1315286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315286).length < 2 ^ (prefixWord ++ tailWord_1315286).sum := by decide
  have hdescent : baseEnd_1315286 < baseStart_1315286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315424 : List Nat := [2, 1, 1, 3, 2, 1, 6, 2, 3]
def baseStart_1315424 : Nat := 118140960795 + 1315424 * 2 ^ 59
def prefixEnd_1315424 : Nat := 4983230072969 + 3 ^ 40 * 1315424 * 2
def baseEnd_1315424 : Nat := 300197678426651836111325

theorem tailTrace_1315424 : CollatzResearch.WordTrace tailWord_1315424 prefixEnd_1315424 300197678426651836111325 := by
  unfold tailWord_1315424
  simp only [CollatzResearch.WordTrace]
  refine ⟨23988727393225489689244663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31984969857633986252326217 23988727393225489689244663)
  ·
    refine ⟨35983091089838234533866995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23988727393225489689244663 35983091089838234533866995)
    ·
      refine ⟨53974636634757351800800493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35983091089838234533866995 53974636634757351800800493)
      ·
        refine ⟨20240488738034006925300185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53974636634757351800800493 20240488738034006925300185)
        ·
          refine ⟨15180366553525505193975139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20240488738034006925300185 15180366553525505193975139)
          ·
            refine ⟨22770549830288257790962709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15180366553525505193975139 22770549830288257790962709)
            ·
              refine ⟨1067369523294762083951377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22770549830288257790962709 1067369523294762083951377)
              ·
                refine ⟨800527142471071562963533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067369523294762083951377 800527142471071562963533)
                ·
                  refine ⟨300197678426651836111325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800527142471071562963533 300197678426651836111325)
                  ·
                    rfl

theorem cell21_1315424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_1315424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315424 prefixEnd_1315424 := by exact prefixLift 1315424
  have htrace : WordTrace (prefixWord ++ tailWord_1315424) baseStart_1315424 baseEnd_1315424 := by
    simpa [prefixWord, tailWord_1315424, baseEnd_1315424] using wordTrace_append hprefix tailTrace_1315424
  have hstable : (prefixWord ++ tailWord_1315424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315424).length < 2 ^ (prefixWord ++ tailWord_1315424).sum := by decide
  have hdescent : baseEnd_1315424 < baseStart_1315424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315438 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_1315438 : Nat := 118140960795 + 1315438 * 2 ^ 59
def prefixEnd_1315438 : Nat := 4983230072969 + 3 ^ 40 * 1315438 * 2
def baseEnd_1315438 : Nat := 300200873417390922877963

theorem tailTrace_1315438 : CollatzResearch.WordTrace tailWord_1315438 prefixEnd_1315438 300200873417390922877963 := by
  unfold tailWord_1315438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5997245676050032471187371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31985310272266839846332645 5997245676050032471187371)
  ·
    refine ⟨8995868514075048706781057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5997245676050032471187371 8995868514075048706781057)
    ·
      refine ⟨6746901385556286530085793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8995868514075048706781057 6746901385556286530085793)
      ·
        refine ⟨5060176039167214897564345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6746901385556286530085793 5060176039167214897564345)
        ·
          refine ⟨3795132029375411173173259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5060176039167214897564345 3795132029375411173173259)
          ·
            refine ⟨5692698044063116759759889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795132029375411173173259 5692698044063116759759889)
            ·
              refine ⟨4269523533047337569819917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5692698044063116759759889 4269523533047337569819917)
              ·
                refine ⟨1601071324892751588682469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4269523533047337569819917 1601071324892751588682469)
                ·
                  refine ⟨300200873417390922877963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1601071324892751588682469 300200873417390922877963)
                  ·
                    rfl

theorem cell21_1315438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_1315438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315438 prefixEnd_1315438 := by exact prefixLift 1315438
  have htrace : WordTrace (prefixWord ++ tailWord_1315438) baseStart_1315438 baseEnd_1315438 := by
    simpa [prefixWord, tailWord_1315438, baseEnd_1315438] using wordTrace_append hprefix tailTrace_1315438
  have hstable : (prefixWord ++ tailWord_1315438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315438).length < 2 ^ (prefixWord ++ tailWord_1315438).sum := by decide
  have hdescent : baseEnd_1315438 < baseStart_1315438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315548 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_1315548 : Nat := 118140960795 + 1315548 * 2 ^ 59
def prefixEnd_1315548 : Nat := 4983230072969 + 3 ^ 40 * 1315548 * 2
def baseEnd_1315548 : Nat := 300225976916055176044405

theorem tailTrace_1315548 : CollatzResearch.WordTrace tailWord_1315548 prefixEnd_1315548 300225976916055176044405 := by
  unfold tailWord_1315548
  simp only [CollatzResearch.WordTrace]
  refine ⟨23990988719000874278001649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31987984958667832370668865 23990988719000874278001649)
  ·
    refine ⟨17993241539250655708501237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23990988719000874278001649 17993241539250655708501237)
    ·
      refine ⟨1686866394304748972671991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17993241539250655708501237 1686866394304748972671991)
      ·
        refine ⟨2530299591457123459007987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686866394304748972671991 2530299591457123459007987)
        ·
          refine ⟨3795449387185685188511981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2530299591457123459007987 3795449387185685188511981)
          ·
            refine ⟨1423293520194631945691993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3795449387185685188511981 1423293520194631945691993)
            ·
              refine ⟨1067470140145973959268995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423293520194631945691993 1067470140145973959268995)
              ·
                refine ⟨1601205210218960938903493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067470140145973959268995 1601205210218960938903493)
                ·
                  refine ⟨300225976916055176044405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1601205210218960938903493 300225976916055176044405)
                  ·
                    rfl

theorem cell21_1315548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_1315548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315548 prefixEnd_1315548 := by exact prefixLift 1315548
  have htrace : WordTrace (prefixWord ++ tailWord_1315548) baseStart_1315548 baseEnd_1315548 := by
    simpa [prefixWord, tailWord_1315548, baseEnd_1315548] using wordTrace_append hprefix tailTrace_1315548
  have hstable : (prefixWord ++ tailWord_1315548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315548).length < 2 ^ (prefixWord ++ tailWord_1315548).sum := by decide
  have hdescent : baseEnd_1315548 < baseStart_1315548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315618 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1315618 : Nat := 118140960795 + 1315618 * 2 ^ 59
def prefixEnd_1315618 : Nat := 4983230072969 + 3 ^ 40 * 1315618 * 2
def baseEnd_1315618 : Nat := 300241951869750609877595

theorem tailTrace_1315618 : CollatzResearch.WordTrace tailWord_1315618 prefixEnd_1315618 300241951869750609877595 := by
  unfold tailWord_1315618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11996132636937037627762877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31989687031832100340701005 11996132636937037627762877)
  ·
    refine ⟨4498549738851389110411079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11996132636937037627762877 4498549738851389110411079)
    ·
      refine ⟨6747824608277083665616619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4498549738851389110411079 6747824608277083665616619)
      ·
        refine ⟨10121736912415625498424929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6747824608277083665616619 10121736912415625498424929)
        ·
          refine ⟨7591302684311719123818697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10121736912415625498424929 7591302684311719123818697)
          ·
            refine ⟨5693477013233789342864023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7591302684311719123818697 5693477013233789342864023)
            ·
              refine ⟨8540215519850684014296035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693477013233789342864023 8540215519850684014296035)
              ·
                refine ⟨12810323279776026021444053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8540215519850684014296035 12810323279776026021444053)
                ·
                  refine ⟨300241951869750609877595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12810323279776026021444053 300241951869750609877595)
                  ·
                    rfl

theorem cell21_1315618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1315618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315618 prefixEnd_1315618 := by exact prefixLift 1315618
  have htrace : WordTrace (prefixWord ++ tailWord_1315618) baseStart_1315618 baseEnd_1315618 := by
    simpa [prefixWord, tailWord_1315618, baseEnd_1315618] using wordTrace_append hprefix tailTrace_1315618
  have hstable : (prefixWord ++ tailWord_1315618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315618).length < 2 ^ (prefixWord ++ tailWord_1315618).sum := by decide
  have hdescent : baseEnd_1315618 < baseStart_1315618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315635 : List Nat := [1, 1, 1, 2, 6, 1, 1, 5, 3]
def baseStart_1315635 : Nat := 118140960795 + 1315635 * 2 ^ 59
def prefixEnd_1315635 : Nat := 4983230072969 + 3 ^ 40 * 1315635 * 2
def baseEnd_1315635 : Nat := 300245831501362358094227

theorem tailTrace_1315635 : CollatzResearch.WordTrace tailWord_1315635 prefixEnd_1315635 300245831501362358094227 := by
  unfold tailWord_1315635
  simp only [CollatzResearch.WordTrace]
  refine ⟨47985150588686562414420359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31990100392457708276280239 47985150588686562414420359)
  ·
    refine ⟨71977725883029843621630539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47985150588686562414420359 71977725883029843621630539)
    ·
      refine ⟨107966588824544765432445809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71977725883029843621630539 107966588824544765432445809)
      ·
        refine ⟨80974941618408574074334357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107966588824544765432445809 80974941618408574074334357)
        ·
          refine ⟨3795700388362901909734423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80974941618408574074334357 3795700388362901909734423)
          ·
            refine ⟨5693550582544352864601635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795700388362901909734423 5693550582544352864601635)
            ·
              refine ⟨8540325873816529296902453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693550582544352864601635 8540325873816529296902453)
              ·
                refine ⟨800655550670299621584605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8540325873816529296902453 800655550670299621584605)
                ·
                  refine ⟨300245831501362358094227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800655550670299621584605 300245831501362358094227)
                  ·
                    rfl

theorem cell21_1315635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 3].length) (baseStart_1315635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315635 prefixEnd_1315635 := by exact prefixLift 1315635
  have htrace : WordTrace (prefixWord ++ tailWord_1315635) baseStart_1315635 baseEnd_1315635 := by
    simpa [prefixWord, tailWord_1315635, baseEnd_1315635] using wordTrace_append hprefix tailTrace_1315635
  have hstable : (prefixWord ++ tailWord_1315635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315635).length < 2 ^ (prefixWord ++ tailWord_1315635).sum := by decide
  have hdescent : baseEnd_1315635 < baseStart_1315635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315666 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_1315666 : Nat := 118140960795 + 1315666 * 2 ^ 59
def prefixEnd_1315666 : Nat := 4983230072969 + 3 ^ 40 * 1315666 * 2
def baseEnd_1315666 : Nat := 300252906123713193077497

theorem tailTrace_1315666 : CollatzResearch.WordTrace tailWord_1315666 prefixEnd_1315666 300252906123713193077497 := by
  unfold tailWord_1315666
  simp only [CollatzResearch.WordTrace]
  refine ⟨11996570312893563677199713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31990854167716169805865901 11996570312893563677199713)
  ·
    refine ⟨8997427734670172757899785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11996570312893563677199713 8997427734670172757899785)
    ·
      refine ⟨6748070801002629568424839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8997427734670172757899785 6748070801002629568424839)
      ·
        refine ⟨10122106201503944352637259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6748070801002629568424839 10122106201503944352637259)
        ·
          refine ⟨15183159302255916528955889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10122106201503944352637259 15183159302255916528955889)
          ·
            refine ⟨11387369476691937396716917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15183159302255916528955889 11387369476691937396716917)
            ·
              refine ⟨1067565888439869130942211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11387369476691937396716917 1067565888439869130942211)
              ·
                refine ⟨1601348832659803696413317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067565888439869130942211 1601348832659803696413317)
                ·
                  refine ⟨300252906123713193077497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1601348832659803696413317 300252906123713193077497)
                  ·
                    rfl

theorem cell21_1315666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_1315666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315666 prefixEnd_1315666 := by exact prefixLift 1315666
  have htrace : WordTrace (prefixWord ++ tailWord_1315666) baseStart_1315666 baseEnd_1315666 := by
    simpa [prefixWord, tailWord_1315666, baseEnd_1315666] using wordTrace_append hprefix tailTrace_1315666
  have hstable : (prefixWord ++ tailWord_1315666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315666).length < 2 ^ (prefixWord ++ tailWord_1315666).sum := by decide
  have hdescent : baseEnd_1315666 < baseStart_1315666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315714 : List Nat := [3, 4, 2, 2, 1, 1, 2, 6]
def baseStart_1315714 : Nat := 118140960795 + 1315714 * 2 ^ 59
def prefixEnd_1315714 : Nat := 4983230072969 + 3 ^ 40 * 1315714 * 2
def baseEnd_1315714 : Nat := 100087953459225258759133

theorem tailTrace_1315714 : CollatzResearch.WordTrace tailWord_1315714 prefixEnd_1315714 100087953459225258759133 := by
  unfold tailWord_1315714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11997007988850089726636549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31992021303600239271030797 11997007988850089726636549)
  ·
    refine ⟨2249438997909391823744353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11997007988850089726636549 2249438997909391823744353)
    ·
      refine ⟨1687079248432043867808265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2249438997909391823744353 1687079248432043867808265)
      ·
        refine ⟨1265309436324032900856199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1687079248432043867808265 1265309436324032900856199)
        ·
          refine ⟨1897964154486049351284299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265309436324032900856199 1897964154486049351284299)
          ·
            refine ⟨2846946231729074026926449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897964154486049351284299 2846946231729074026926449)
            ·
              refine ⟨2135209673796805520194837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2846946231729074026926449 2135209673796805520194837)
              ·
                refine ⟨100087953459225258759133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2135209673796805520194837 100087953459225258759133)
                ·
                  rfl

theorem cell21_1315714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_1315714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315714 prefixEnd_1315714 := by exact prefixLift 1315714
  have htrace : WordTrace (prefixWord ++ tailWord_1315714) baseStart_1315714 baseEnd_1315714 := by
    simpa [prefixWord, tailWord_1315714, baseEnd_1315714] using wordTrace_append hprefix tailTrace_1315714
  have hstable : (prefixWord ++ tailWord_1315714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315714).length < 2 ^ (prefixWord ++ tailWord_1315714).sum := by decide
  have hdescent : baseEnd_1315714 < baseStart_1315714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315773 : List Nat := [1, 4, 1, 2, 5, 1, 1, 6]
def baseStart_1315773 : Nat := 118140960795 + 1315773 * 2 ^ 59
def prefixEnd_1315773 : Nat := 4983230072969 + 3 ^ 40 * 1315773 * 2
def baseEnd_1315773 : Nat := 100092441660501594931315

theorem tailTrace_1315773 : CollatzResearch.WordTrace tailWord_1315773 prefixEnd_1315773 100092441660501594931315 := by
  unfold tailWord_1315773
  simp only [CollatzResearch.WordTrace]
  refine ⟨47990183862186611982943973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31993455908124407988629315 47990183862186611982943973)
  ·
    refine ⟨8998159474159989746801995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47990183862186611982943973 8998159474159989746801995)
    ·
      refine ⟨13497239211239984620202993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8998159474159989746801995 13497239211239984620202993)
      ·
        refine ⟨10122929408429988465152245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13497239211239984620202993 10122929408429988465152245)
        ·
          refine ⟨949024632040311418608023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10122929408429988465152245 949024632040311418608023)
          ·
            refine ⟨1423536948060467127912035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949024632040311418608023 1423536948060467127912035)
            ·
              refine ⟨2135305422090700691868053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423536948060467127912035 2135305422090700691868053)
              ·
                refine ⟨100092441660501594931315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2135305422090700691868053 100092441660501594931315)
                ·
                  rfl

theorem cell21_1315773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 6].length) (baseStart_1315773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315773 prefixEnd_1315773 := by exact prefixLift 1315773
  have htrace : WordTrace (prefixWord ++ tailWord_1315773) baseStart_1315773 baseEnd_1315773 := by
    simpa [prefixWord, tailWord_1315773, baseEnd_1315773] using wordTrace_append hprefix tailTrace_1315773
  have hstable : (prefixWord ++ tailWord_1315773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315773).length < 2 ^ (prefixWord ++ tailWord_1315773).sum := by decide
  have hdescent : baseEnd_1315773 < baseStart_1315773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315815 : List Nat := [1, 1, 5, 2, 2, 2, 8]
def baseStart_1315815 : Nat := 118140960795 + 1315815 * 2 ^ 59
def prefixEnd_1315815 : Nat := 4983230072969 + 3 ^ 40 * 1315815 * 2
def baseEnd_1315815 : Nat := 33365212217080227232651

theorem tailTrace_1315815 : CollatzResearch.WordTrace tailWord_1315815 prefixEnd_1315815 33365212217080227232651 := by
  unfold tailWord_1315815
  simp only [CollatzResearch.WordTrace]
  refine ⟨47991715728034453155972899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31994477152022968770648599 47991715728034453155972899)
  ·
    refine ⟨71987573592051679733959349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47991715728034453155972899 71987573592051679733959349)
    ·
      refine ⟨6748835024254844975058689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71987573592051679733959349 6748835024254844975058689)
      ·
        refine ⟨5061626268191133731294017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6748835024254844975058689 5061626268191133731294017)
        ·
          refine ⟨3796219701143350298470513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5061626268191133731294017 3796219701143350298470513)
          ·
            refine ⟨2847164775857512723852885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3796219701143350298470513 2847164775857512723852885)
            ·
              refine ⟨33365212217080227232651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2847164775857512723852885 33365212217080227232651)
              ·
                rfl

theorem cell21_1315815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 8].length) (baseStart_1315815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315815 prefixEnd_1315815 := by exact prefixLift 1315815
  have htrace : WordTrace (prefixWord ++ tailWord_1315815) baseStart_1315815 baseEnd_1315815 := by
    simpa [prefixWord, tailWord_1315815, baseEnd_1315815] using wordTrace_append hprefix tailTrace_1315815
  have hstable : (prefixWord ++ tailWord_1315815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315815).length < 2 ^ (prefixWord ++ tailWord_1315815).sum := by decide
  have hdescent : baseEnd_1315815 < baseStart_1315815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315818 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_1315818 : Nat := 118140960795 + 1315818 * 2 ^ 59
def prefixEnd_1315818 : Nat := 4983230072969 + 3 ^ 40 * 1315818 * 2
def baseEnd_1315818 : Nat := 300287594594594706543853

theorem tailTrace_1315818 : CollatzResearch.WordTrace tailWord_1315818 prefixEnd_1315818 300287594594594706543853 := by
  unfold tailWord_1315818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11997956286755896167083027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31994550098015723112221405 11997956286755896167083027)
  ·
    refine ⟨17996934430133844250624541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11997956286755896167083027 17996934430133844250624541)
    ·
      refine ⟨6748850411300191593984203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17996934430133844250624541 6748850411300191593984203)
      ·
        refine ⟨10123275616950287390976305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6748850411300191593984203 10123275616950287390976305)
        ·
          refine ⟨7592456712712715543232229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10123275616950287390976305 7592456712712715543232229)
          ·
            refine ⟨1423585633633634164356043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7592456712712715543232229 1423585633633634164356043)
            ·
              refine ⟨2135378450450451246534065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423585633633634164356043 2135378450450451246534065)
              ·
                refine ⟨1601533837837838434900549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135378450450451246534065 1601533837837838434900549)
                ·
                  refine ⟨300287594594594706543853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1601533837837838434900549 300287594594594706543853)
                  ·
                    rfl

theorem cell21_1315818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_1315818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315818 prefixEnd_1315818 := by exact prefixLift 1315818
  have htrace : WordTrace (prefixWord ++ tailWord_1315818) baseStart_1315818 baseEnd_1315818 := by
    simpa [prefixWord, tailWord_1315818, baseEnd_1315818] using wordTrace_append hprefix tailTrace_1315818
  have hstable : (prefixWord ++ tailWord_1315818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315818).length < 2 ^ (prefixWord ++ tailWord_1315818).sum := by decide
  have hdescent : baseEnd_1315818 < baseStart_1315818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315894 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1315894 : Nat := 118140960795 + 1315894 * 2 ^ 59
def prefixEnd_1315894 : Nat := 4983230072969 + 3 ^ 40 * 1315894 * 2
def baseEnd_1315894 : Nat := 300304938830035463277031

theorem tailTrace_1315894 : CollatzResearch.WordTrace tailWord_1315894 prefixEnd_1315894 300304938830035463277031 := by
  unfold tailWord_1315894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2999662318421765603006171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31996398063165499765399157 2999662318421765603006171)
  ·
    refine ⟨4499493477632648404509257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2999662318421765603006171 4499493477632648404509257)
    ·
      refine ⟨3374620108224486303381943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4499493477632648404509257 3374620108224486303381943)
      ·
        refine ⟨5061930162336729455072915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374620108224486303381943 5061930162336729455072915)
        ·
          refine ⟨7592895243505094182609373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061930162336729455072915 7592895243505094182609373)
          ·
            refine ⟨2847335716314410318478515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7592895243505094182609373 2847335716314410318478515)
            ·
              refine ⟨4271003574471615477717773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847335716314410318478515 4271003574471615477717773)
              ·
                refine ⟨1601626340426855804144165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4271003574471615477717773 1601626340426855804144165)
                ·
                  refine ⟨300304938830035463277031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1601626340426855804144165 300304938830035463277031)
                  ·
                    rfl

theorem cell21_1315894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1315894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1315894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1315894 prefixEnd_1315894 := by exact prefixLift 1315894
  have htrace : WordTrace (prefixWord ++ tailWord_1315894) baseStart_1315894 baseEnd_1315894 := by
    simpa [prefixWord, tailWord_1315894, baseEnd_1315894] using wordTrace_append hprefix tailTrace_1315894
  have hstable : (prefixWord ++ tailWord_1315894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315894).length < 2 ^ (prefixWord ++ tailWord_1315894).sum := by decide
  have hdescent : baseEnd_1315894 < baseStart_1315894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316032 : List Nat := [2, 1, 1, 2, 6, 2, 1, 3, 3]
def baseStart_1316032 : Nat := 118140960795 + 1316032 * 2 ^ 59
def prefixEnd_1316032 : Nat := 4983230072969 + 3 ^ 40 * 1316032 * 2
def baseEnd_1316032 : Nat := 300336432310177889976749

theorem tailTrace_1316032 : CollatzResearch.WordTrace tailWord_1316032 prefixEnd_1316032 300336432310177889976749 := by
  unfold tailWord_1316032
  simp only [CollatzResearch.WordTrace]
  refine ⟨23999815184124149608311175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31999753578832199477748233 23999815184124149608311175)
  ·
    refine ⟨35999722776186224412466763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23999815184124149608311175 35999722776186224412466763)
    ·
      refine ⟨53999584164279336618700145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35999722776186224412466763 53999584164279336618700145)
      ·
        refine ⟨40499688123209502464025109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53999584164279336618700145 40499688123209502464025109)
        ·
          refine ⟨1898422880775445428001177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40499688123209502464025109 1898422880775445428001177)
          ·
            refine ⟨1423817160581584071000883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898422880775445428001177 1423817160581584071000883)
            ·
              refine ⟨2135725740872376106501325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423817160581584071000883 2135725740872376106501325)
              ·
                refine ⟨800897152827141039937997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2135725740872376106501325 800897152827141039937997)
                ·
                  refine ⟨300336432310177889976749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800897152827141039937997 300336432310177889976749)
                  ·
                    rfl

theorem cell21_1316032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_1316032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316032 prefixEnd_1316032 := by exact prefixLift 1316032
  have htrace : WordTrace (prefixWord ++ tailWord_1316032) baseStart_1316032 baseEnd_1316032 := by
    simpa [prefixWord, tailWord_1316032, baseEnd_1316032] using wordTrace_append hprefix tailTrace_1316032
  have hstable : (prefixWord ++ tailWord_1316032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316032).length < 2 ^ (prefixWord ++ tailWord_1316032).sum := by decide
  have hdescent : baseEnd_1316032 < baseStart_1316032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316108 : List Nat := [2, 2, 1, 2, 2, 5, 2, 2, 3]
def baseStart_1316108 : Nat := 118140960795 + 1316108 * 2 ^ 59
def prefixEnd_1316108 : Nat := 4983230072969 + 3 ^ 40 * 1316108 * 2
def baseEnd_1316108 : Nat := 300353776545618646709927

theorem tailTrace_1316108 : CollatzResearch.WordTrace tailWord_1316108 prefixEnd_1316108 300353776545618646709927 := by
  unfold tailWord_1316108
  simp only [CollatzResearch.WordTrace]
  refine ⟨24001201157986482098194489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32001601543981976130925985 24001201157986482098194489)
  ·
    refine ⟨18000900868489861573645867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24001201157986482098194489 18000900868489861573645867)
    ·
      refine ⟨27001351302734792360468801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18000900868489861573645867 27001351302734792360468801)
      ·
        refine ⟨20251013477051094270351601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27001351302734792360468801 20251013477051094270351601)
        ·
          refine ⟨15188260107788320702763701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20251013477051094270351601 15188260107788320702763701)
          ·
            refine ⟨1423899385105155065884097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15188260107788320702763701 1423899385105155065884097)
            ·
              refine ⟨1067924538828866299413073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423899385105155065884097 1067924538828866299413073)
              ·
                refine ⟨800943404121649724559805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067924538828866299413073 800943404121649724559805)
                ·
                  refine ⟨300353776545618646709927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800943404121649724559805 300353776545618646709927)
                  ·
                    rfl

theorem cell21_1316108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_1316108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316108 prefixEnd_1316108 := by exact prefixLift 1316108
  have htrace : WordTrace (prefixWord ++ tailWord_1316108) baseStart_1316108 baseEnd_1316108 := by
    simpa [prefixWord, tailWord_1316108, baseEnd_1316108] using wordTrace_append hprefix tailTrace_1316108
  have hstable : (prefixWord ++ tailWord_1316108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316108).length < 2 ^ (prefixWord ++ tailWord_1316108).sum := by decide
  have hdescent : baseEnd_1316108 < baseStart_1316108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316133 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 7]
def baseStart_1316133 : Nat := 118140960795 + 1316133 * 2 ^ 59
def prefixEnd_1316133 : Nat := 4983230072969 + 3 ^ 40 * 1316133 * 2
def baseEnd_1316133 : Nat := 300359481886224158793209

theorem tailTrace_1316133 : CollatzResearch.WordTrace tailWord_1316133 prefixEnd_1316133 300359481886224158793209 := by
  unfold tailWord_1316133
  simp only [CollatzResearch.WordTrace]
  refine ⟨48003314140882393466049053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32002209427254928977366035 48003314140882393466049053)
  ·
    refine ⟨18001242802830897549768395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48003314140882393466049053 18001242802830897549768395)
    ·
      refine ⟨27001864204246346324652593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18001242802830897549768395 27001864204246346324652593)
      ·
        refine ⟨20251398153184759743489445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27001864204246346324652593 20251398153184759743489445)
        ·
          refine ⟨3797137153722142451904271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20251398153184759743489445 3797137153722142451904271)
          ·
            refine ⟨5695705730583213677856407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797137153722142451904271 5695705730583213677856407)
            ·
              refine ⟨8543558595874820516784611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5695705730583213677856407 8543558595874820516784611)
              ·
                refine ⟨12815337893812230775176917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8543558595874820516784611 12815337893812230775176917)
                ·
                  refine ⟨300359481886224158793209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12815337893812230775176917 300359481886224158793209)
                  ·
                    rfl

theorem cell21_1316133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_1316133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316133 prefixEnd_1316133 := by exact prefixLift 1316133
  have htrace : WordTrace (prefixWord ++ tailWord_1316133) baseStart_1316133 baseEnd_1316133 := by
    simpa [prefixWord, tailWord_1316133, baseEnd_1316133] using wordTrace_append hprefix tailTrace_1316133
  have hstable : (prefixWord ++ tailWord_1316133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316133).length < 2 ^ (prefixWord ++ tailWord_1316133).sum := by decide
  have hdescent : baseEnd_1316133 < baseStart_1316133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316136 : List Nat := [2, 1, 5, 1, 2, 2, 3, 5]
def baseStart_1316136 : Nat := 118140960795 + 1316136 * 2 ^ 59
def prefixEnd_1316136 : Nat := 4983230072969 + 3 ^ 40 * 1316136 * 2
def baseEnd_1316136 : Nat := 100120055509032273414401

theorem tailTrace_1316136 : CollatzResearch.WordTrace tailWord_1316136 prefixEnd_1316136 100120055509032273414401 := by
  unfold tailWord_1316136
  simp only [CollatzResearch.WordTrace]
  refine ⟨24001711779935762489204131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32002282373247683318938841 24001711779935762489204131)
  ·
    refine ⟨36002567669903643733806197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24001711779935762489204131 36002567669903643733806197)
    ·
      refine ⟨3375240719053466600044331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36002567669903643733806197 3375240719053466600044331)
      ·
        refine ⟨5062861078580199900066497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3375240719053466600044331 5062861078580199900066497)
        ·
          refine ⟨3797145808935149925049873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5062861078580199900066497 3797145808935149925049873)
          ·
            refine ⟨2847859356701362443787405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3797145808935149925049873 2847859356701362443787405)
            ·
              refine ⟨1067947258763010916420277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2847859356701362443787405 1067947258763010916420277)
              ·
                refine ⟨100120055509032273414401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1067947258763010916420277 100120055509032273414401)
                ·
                  rfl

theorem cell21_1316136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_1316136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316136 prefixEnd_1316136 := by exact prefixLift 1316136
  have htrace : WordTrace (prefixWord ++ tailWord_1316136) baseStart_1316136 baseEnd_1316136 := by
    simpa [prefixWord, tailWord_1316136, baseEnd_1316136] using wordTrace_append hprefix tailTrace_1316136
  have hstable : (prefixWord ++ tailWord_1316136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316136).length < 2 ^ (prefixWord ++ tailWord_1316136).sum := by decide
  have hdescent : baseEnd_1316136 < baseStart_1316136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316178 : List Nat := [3, 2, 2, 1, 1, 1, 1, 10]
def baseStart_1316178 : Nat := 118140960795 + 1316178 * 2 ^ 59
def prefixEnd_1316178 : Nat := 4983230072969 + 3 ^ 40 * 1316178 * 2
def baseEnd_1316178 : Nat := 100123250499771360181039

theorem tailTrace_1316178 : CollatzResearch.WordTrace tailWord_1316178 prefixEnd_1316178 100123250499771360181039 := by
  unfold tailWord_1316178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12001238856429841537859297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32003303617146244100958125 12001238856429841537859297)
  ·
    refine ⟨9000929142322381153394473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12001238856429841537859297 9000929142322381153394473)
    ·
      refine ⟨6750696856741785865045855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9000929142322381153394473 6750696856741785865045855)
      ·
        refine ⟨10126045285112678797568783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6750696856741785865045855 10126045285112678797568783)
        ·
          refine ⟨15189067927669018196353175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10126045285112678797568783 15189067927669018196353175)
          ·
            refine ⟨22783601891503527294529763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15189067927669018196353175 22783601891503527294529763)
            ·
              refine ⟨34175402837255290941794645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22783601891503527294529763 34175402837255290941794645)
              ·
                refine ⟨100123250499771360181039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34175402837255290941794645 100123250499771360181039)
                ·
                  rfl

theorem cell21_1316178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_1316178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316178 prefixEnd_1316178 := by exact prefixLift 1316178
  have htrace : WordTrace (prefixWord ++ tailWord_1316178) baseStart_1316178 baseEnd_1316178 := by
    simpa [prefixWord, tailWord_1316178, baseEnd_1316178] using wordTrace_append hprefix tailTrace_1316178
  have hstable : (prefixWord ++ tailWord_1316178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316178).length < 2 ^ (prefixWord ++ tailWord_1316178).sum := by decide
  have hdescent : baseEnd_1316178 < baseStart_1316178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316195 : List Nat := [1, 1, 1, 5, 2, 2, 4, 5]
def baseStart_1316195 : Nat := 118140960795 + 1316195 * 2 ^ 59
def prefixEnd_1316195 : Nat := 4983230072969 + 3 ^ 40 * 1316195 * 2
def baseEnd_1316195 : Nat := 100124543710308609586583

theorem tailTrace_1316195 : CollatzResearch.WordTrace tailWord_1316195 prefixEnd_1316195 100124543710308609586583 := by
  unfold tailWord_1316195
  simp only [CollatzResearch.WordTrace]
  refine ⟨48005575466657778054806039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32003716977771852036537359 48005575466657778054806039)
  ·
    refine ⟨72008363199986667082209059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48005575466657778054806039 72008363199986667082209059)
    ·
      refine ⟨108012544799980000623313589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72008363199986667082209059 108012544799980000623313589)
      ·
        refine ⟨10126176074998125058435649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108012544799980000623313589 10126176074998125058435649)
        ·
          refine ⟨7594632056248593793826737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10126176074998125058435649 7594632056248593793826737)
          ·
            refine ⟨5695974042186445345370053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7594632056248593793826737 5695974042186445345370053)
            ·
              refine ⟨1067995132909958502256885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5695974042186445345370053 1067995132909958502256885)
              ·
                refine ⟨100124543710308609586583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1067995132909958502256885 100124543710308609586583)
                ·
                  rfl

theorem cell21_1316195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 5].length) (baseStart_1316195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316195 prefixEnd_1316195 := by exact prefixLift 1316195
  have htrace : WordTrace (prefixWord ++ tailWord_1316195) baseStart_1316195 baseEnd_1316195 := by
    simpa [prefixWord, tailWord_1316195, baseEnd_1316195] using wordTrace_append hprefix tailTrace_1316195
  have hstable : (prefixWord ++ tailWord_1316195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316195).length < 2 ^ (prefixWord ++ tailWord_1316195).sum := by decide
  have hdescent : baseEnd_1316195 < baseStart_1316195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316285 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 5]
def baseStart_1316285 : Nat := 118140960795 + 1316285 * 2 ^ 59
def prefixEnd_1316285 : Nat := 4983230072969 + 3 ^ 40 * 1316285 * 2
def baseEnd_1316285 : Nat := 300394170357105672259565

theorem tailTrace_1316285 : CollatzResearch.WordTrace tailWord_1316285 prefixEnd_1316285 300394170357105672259565 := by
  unfold tailWord_1316285
  simp only [CollatzResearch.WordTrace]
  refine ⟨48008858036331723425582309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32005905357554482283721539 48008858036331723425582309)
  ·
    refine ⟨9001660881812198142296683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48008858036331723425582309 9001660881812198142296683)
    ·
      refine ⟨13502491322718297213445025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9001660881812198142296683 13502491322718297213445025)
      ·
        refine ⟨10126868492038722910083769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13502491322718297213445025 10126868492038722910083769)
        ·
          refine ⟨7595151369029042182562827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10126868492038722910083769 7595151369029042182562827)
          ·
            refine ⟨11392727053543563273844241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7595151369029042182562827 11392727053543563273844241)
            ·
              refine ⟨8544545290157672455383181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11392727053543563273844241 8544545290157672455383181)
              ·
                refine ⟨3204204483809127170768693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8544545290157672455383181 3204204483809127170768693)
                ·
                  refine ⟨300394170357105672259565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3204204483809127170768693 300394170357105672259565)
                  ·
                    rfl

theorem cell21_1316285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_1316285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316285 prefixEnd_1316285 := by exact prefixLift 1316285
  have htrace : WordTrace (prefixWord ++ tailWord_1316285) baseStart_1316285 baseEnd_1316285 := by
    simpa [prefixWord, tailWord_1316285, baseEnd_1316285] using wordTrace_append hprefix tailTrace_1316285
  have hstable : (prefixWord ++ tailWord_1316285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316285).length < 2 ^ (prefixWord ++ tailWord_1316285).sum := by decide
  have hdescent : baseEnd_1316285 < baseStart_1316285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316333 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1316333 : Nat := 118140960795 + 1316333 * 2 ^ 59
def prefixEnd_1316333 : Nat := 4983230072969 + 3 ^ 40 * 1316333 * 2
def baseEnd_1316333 : Nat := 300405124611068255459467

theorem tailTrace_1316333 : CollatzResearch.WordTrace tailWord_1316333 prefixEnd_1316333 300405124611068255459467 := by
  unfold tailWord_1316333
  simp only [CollatzResearch.WordTrace]
  refine ⟨48010608740157827623329653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32007072493438551748886435 48010608740157827623329653)
  ·
    refine ⟨4500994569389796339687155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48010608740157827623329653 4500994569389796339687155)
    ·
      refine ⟨6751491854084694509530733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4500994569389796339687155 6751491854084694509530733)
      ·
        refine ⟨2531809445281760441074025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6751491854084694509530733 2531809445281760441074025)
        ·
          refine ⟨1898857083961320330805519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2531809445281760441074025 1898857083961320330805519)
          ·
            refine ⟨2848285625941980496208279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898857083961320330805519 2848285625941980496208279)
            ·
              refine ⟨4272428438912970744312419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848285625941980496208279 4272428438912970744312419)
              ·
                refine ⟨6408642658369456116468629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272428438912970744312419 6408642658369456116468629)
                ·
                  refine ⟨300405124611068255459467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6408642658369456116468629 300405124611068255459467)
                  ·
                    rfl

theorem cell21_1316333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1316333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316333 prefixEnd_1316333 := by exact prefixLift 1316333
  have htrace : WordTrace (prefixWord ++ tailWord_1316333) baseStart_1316333 baseEnd_1316333 := by
    simpa [prefixWord, tailWord_1316333, baseEnd_1316333] using wordTrace_append hprefix tailTrace_1316333
  have hstable : (prefixWord ++ tailWord_1316333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316333).length < 2 ^ (prefixWord ++ tailWord_1316333).sum := by decide
  have hdescent : baseEnd_1316333 < baseStart_1316333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316364 : List Nat := [2, 2, 1, 2, 5, 2, 2, 5]
def baseStart_1316364 : Nat := 118140960795 + 1316364 * 2 ^ 59
def prefixEnd_1316364 : Nat := 4983230072969 + 3 ^ 40 * 1316364 * 2
def baseEnd_1316364 : Nat := 100137399744473030147579

theorem tailTrace_1316364 : CollatzResearch.WordTrace tailWord_1316364 prefixEnd_1316364 100137399744473030147579 := by
  unfold tailWord_1316364
  simp only [CollatzResearch.WordTrace]
  refine ⟨24005869701522759958854073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32007826268697013278472097 24005869701522759958854073)
  ·
    refine ⟨18004402276142069969140555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24005869701522759958854073 18004402276142069969140555)
    ·
      refine ⟨27006603414213104953710833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18004402276142069969140555 27006603414213104953710833)
      ·
        refine ⟨20254952560659828715283125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27006603414213104953710833 20254952560659828715283125)
        ·
          refine ⟨1898901802561858942057793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20254952560659828715283125 1898901802561858942057793)
          ·
            refine ⟨1424176351921394206543345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898901802561858942057793 1424176351921394206543345)
            ·
              refine ⟨1068132263941045654907509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424176351921394206543345 1068132263941045654907509)
              ·
                refine ⟨100137399744473030147579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1068132263941045654907509 100137399744473030147579)
                ·
                  rfl

theorem cell21_1316364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_1316364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316364 prefixEnd_1316364 := by exact prefixLift 1316364
  have htrace : WordTrace (prefixWord ++ tailWord_1316364) baseStart_1316364 baseEnd_1316364 := by
    simpa [prefixWord, tailWord_1316364, baseEnd_1316364] using wordTrace_append hprefix tailTrace_1316364
  have hstable : (prefixWord ++ tailWord_1316364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316364).length < 2 ^ (prefixWord ++ tailWord_1316364).sum := by decide
  have hdescent : baseEnd_1316364 < baseStart_1316364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316409 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 4]
def baseStart_1316409 : Nat := 118140960795 + 1316409 * 2 ^ 59
def prefixEnd_1316409 : Nat := 4983230072969 + 3 ^ 40 * 1316409 * 2
def baseEnd_1316409 : Nat := 300422468846509012192645

theorem tailTrace_1316409 : CollatzResearch.WordTrace tailWord_1316409 prefixEnd_1316409 300422468846509012192645 := by
  unfold tailWord_1316409
  simp only [CollatzResearch.WordTrace]
  refine ⟨48013380687882492603096281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32008920458588328402064187 48013380687882492603096281)
  ·
    refine ⟨36010035515911869452322211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48013380687882492603096281 36010035515911869452322211)
    ·
      refine ⟨54015053273867804178483317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36010035515911869452322211 54015053273867804178483317)
      ·
        refine ⟨5063911244425106641732811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54015053273867804178483317 5063911244425106641732811)
        ·
          refine ⟨7595866866637659962599217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5063911244425106641732811 7595866866637659962599217)
          ·
            refine ⟨5696900149978244971949413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7595866866637659962599217 5696900149978244971949413)
            ·
              refine ⟨1068168778120920932240515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5696900149978244971949413 1068168778120920932240515)
              ·
                refine ⟨1602253167181381398360773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068168778120920932240515 1602253167181381398360773)
                ·
                  refine ⟨300422468846509012192645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1602253167181381398360773 300422468846509012192645)
                  ·
                    rfl

theorem cell21_1316409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_1316409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316409 prefixEnd_1316409 := by exact prefixLift 1316409
  have htrace : WordTrace (prefixWord ++ tailWord_1316409) baseStart_1316409 baseEnd_1316409 := by
    simpa [prefixWord, tailWord_1316409, baseEnd_1316409] using wordTrace_append hprefix tailTrace_1316409
  have hstable : (prefixWord ++ tailWord_1316409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316409).length < 2 ^ (prefixWord ++ tailWord_1316409).sum := by decide
  have hdescent : baseEnd_1316409 < baseStart_1316409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316488 : List Nat := [2, 1, 3, 5, 1, 1, 2, 3, 3]
def baseStart_1316488 : Nat := 118140960795 + 1316488 * 2 ^ 59
def prefixEnd_1316488 : Nat := 4983230072969 + 3 ^ 40 * 1316488 * 2
def baseEnd_1316488 : Nat := 300440497722822430375817

theorem tailTrace_1316488 : CollatzResearch.WordTrace tailWord_1316488 prefixEnd_1316488 300440497722822430375817 := by
  unfold tailWord_1316488
  simp only [CollatzResearch.WordTrace]
  refine ⟨24008131027298144547611059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32010841369730859396814745 24008131027298144547611059)
  ·
    refine ⟨36012196540947216821416589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24008131027298144547611059 36012196540947216821416589)
    ·
      refine ⟨13504573702855206308031221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36012196540947216821416589 13504573702855206308031221)
      ·
        refine ⟨1266053784642675591377927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13504573702855206308031221 1266053784642675591377927)
        ·
          refine ⟨1899080676964013387066891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266053784642675591377927 1899080676964013387066891)
          ·
            refine ⟨2848621015446020080600337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899080676964013387066891 2848621015446020080600337)
            ·
              refine ⟨2136465761584515060450253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848621015446020080600337 2136465761584515060450253)
              ·
                refine ⟨801174660594193147668845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2136465761584515060450253 801174660594193147668845)
                ·
                  refine ⟨300440497722822430375817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801174660594193147668845 300440497722822430375817)
                  ·
                    rfl

theorem cell21_1316488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_1316488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316488 prefixEnd_1316488 := by exact prefixLift 1316488
  have htrace : WordTrace (prefixWord ++ tailWord_1316488) baseStart_1316488 baseEnd_1316488 := by
    simpa [prefixWord, tailWord_1316488, baseEnd_1316488] using wordTrace_append hprefix tailTrace_1316488
  have hstable : (prefixWord ++ tailWord_1316488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316488).length < 2 ^ (prefixWord ++ tailWord_1316488).sum := by decide
  have hdescent : baseEnd_1316488 < baseStart_1316488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316513 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 5]
def baseStart_1316513 : Nat := 118140960795 + 1316513 * 2 ^ 59
def prefixEnd_1316513 : Nat := 4983230072969 + 3 ^ 40 * 1316513 * 2
def baseEnd_1316513 : Nat := 300446203063427942459099

theorem tailTrace_1316513 : CollatzResearch.WordTrace tailWord_1316513 prefixEnd_1316513 300446203063427942459099 := by
  unfold tailWord_1316513
  simp only [CollatzResearch.WordTrace]
  refine ⟨48017173879505718364882193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32011449253003812243254795 48017173879505718364882193)
  ·
    refine ⟨36012880409629288773661645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48017173879505718364882193 36012880409629288773661645)
    ·
      refine ⟨13504830153610983290123117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36012880409629288773661645 13504830153610983290123117)
      ·
        refine ⟨5064311307604118733796169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13504830153610983290123117 5064311307604118733796169)
        ·
          refine ⟨3798233480703089050347127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5064311307604118733796169 3798233480703089050347127)
          ·
            refine ⟨5697350221054633575520691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798233480703089050347127 5697350221054633575520691)
            ·
              refine ⟨8546025331581950363281037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697350221054633575520691 8546025331581950363281037)
              ·
                refine ⟨3204759499343231386230389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8546025331581950363281037 3204759499343231386230389)
                ·
                  refine ⟨300446203063427942459099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3204759499343231386230389 300446203063427942459099)
                  ·
                    rfl

theorem cell21_1316513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_1316513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316513 prefixEnd_1316513 := by exact prefixLift 1316513
  have htrace : WordTrace (prefixWord ++ tailWord_1316513) baseStart_1316513 baseEnd_1316513 := by
    simpa [prefixWord, tailWord_1316513, baseEnd_1316513] using wordTrace_append hprefix tailTrace_1316513
  have hstable : (prefixWord ++ tailWord_1316513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316513).length < 2 ^ (prefixWord ++ tailWord_1316513).sum := by decide
  have hdescent : baseEnd_1316513 < baseStart_1316513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316533 : List Nat := [1, 3, 3, 3, 3, 1, 2, 5]
def baseStart_1316533 : Nat := 118140960795 + 1316533 * 2 ^ 59
def prefixEnd_1316533 : Nat := 4983230072969 + 3 ^ 40 * 1316533 * 2
def baseEnd_1316533 : Nat := 100150255778637450708575

theorem tailTrace_1316533 : CollatzResearch.WordTrace tailWord_1316533 prefixEnd_1316533 100150255778637450708575 := by
  unfold tailWord_1316533
  simp only [CollatzResearch.WordTrace]
  refine ⟨48017903339433261780610253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32011935559622174520406835 48017903339433261780610253)
  ·
    refine ⟨18006713752287473167728845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48017903339433261780610253 18006713752287473167728845)
    ·
      refine ⟨6752517657107802437898317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18006713752287473167728845 6752517657107802437898317)
      ·
        refine ⟨2532194121415425914211869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6752517657107802437898317 2532194121415425914211869)
        ·
          refine ⟨949572795530784717829451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2532194121415425914211869 949572795530784717829451)
          ·
            refine ⟨1424359193296177076744177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949572795530784717829451 1424359193296177076744177)
            ·
              refine ⟨1068269394972132807558133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424359193296177076744177 1068269394972132807558133)
              ·
                refine ⟨100150255778637450708575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1068269394972132807558133 100150255778637450708575)
                ·
                  rfl

theorem cell21_1316533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 5].length) (baseStart_1316533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316533 prefixEnd_1316533 := by exact prefixLift 1316533
  have htrace : WordTrace (prefixWord ++ tailWord_1316533) baseStart_1316533 baseEnd_1316533 := by
    simpa [prefixWord, tailWord_1316533, baseEnd_1316533] using wordTrace_append hprefix tailTrace_1316533
  have hstable : (prefixWord ++ tailWord_1316533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316533).length < 2 ^ (prefixWord ++ tailWord_1316533).sum := by decide
  have hdescent : baseEnd_1316533 < baseStart_1316533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316564 : List Nat := [2, 4, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1316564 : Nat := 118140960795 + 1316564 * 2 ^ 59
def prefixEnd_1316564 : Nat := 4983230072969 + 3 ^ 40 * 1316564 * 2
def baseEnd_1316564 : Nat := 300457841958263187108995

theorem tailTrace_1316564 : CollatzResearch.WordTrace tailWord_1316564 prefixEnd_1316564 300457841958263187108995 := by
  unfold tailWord_1316564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24009517001160477037494373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32012689334880636049992497 24009517001160477037494373)
  ·
    refine ⟨4501784437717589444530195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24009517001160477037494373 4501784437717589444530195)
    ·
      refine ⟨6752676656576384166795293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4501784437717589444530195 6752676656576384166795293)
      ·
        refine ⟨2532253746216144062548235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6752676656576384166795293 2532253746216144062548235)
        ·
          refine ⟨3798380619324216093822353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2532253746216144062548235 3798380619324216093822353)
          ·
            refine ⟨2848785464493162070366765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3798380619324216093822353 2848785464493162070366765)
            ·
              refine ⟨1068294549184935776387537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2848785464493162070366765 1068294549184935776387537)
              ·
                refine ⟨801220911888701832290653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068294549184935776387537 801220911888701832290653)
                ·
                  refine ⟨300457841958263187108995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801220911888701832290653 300457841958263187108995)
                  ·
                    rfl

theorem cell21_1316564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1316564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316564 prefixEnd_1316564 := by exact prefixLift 1316564
  have htrace : WordTrace (prefixWord ++ tailWord_1316564) baseStart_1316564 baseEnd_1316564 := by
    simpa [prefixWord, tailWord_1316564, baseEnd_1316564] using wordTrace_append hprefix tailTrace_1316564
  have hstable : (prefixWord ++ tailWord_1316564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316564).length < 2 ^ (prefixWord ++ tailWord_1316564).sum := by decide
  have hdescent : baseEnd_1316564 < baseStart_1316564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316634 : List Nat := [3, 1, 1, 3, 2, 2, 3, 6]
def baseStart_1316634 : Nat := 118140960795 + 1316634 * 2 ^ 59
def prefixEnd_1316634 : Nat := 4983230072969 + 3 ^ 40 * 1316634 * 2
def baseEnd_1316634 : Nat := 100157938970652873647395

theorem tailTrace_1316634 : CollatzResearch.WordTrace tailWord_1316634 prefixEnd_1316634 100157938970652873647395 := by
  unfold tailWord_1316634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12005396778016839007509239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32014391408044904020024637 12005396778016839007509239)
  ·
    refine ⟨18008095167025258511263859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12005396778016839007509239 18008095167025258511263859)
    ·
      refine ⟨27012142750537887766895789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18008095167025258511263859 27012142750537887766895789)
      ·
        refine ⟨10129553531451707912585921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27012142750537887766895789 10129553531451707912585921)
        ·
          refine ⟨7597165148588780934439441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10129553531451707912585921 7597165148588780934439441)
          ·
            refine ⟨5697873861441585700829581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7597165148588780934439441 5697873861441585700829581)
            ·
              refine ⟨2136702698040594637811093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5697873861441585700829581 2136702698040594637811093)
              ·
                refine ⟨100157938970652873647395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2136702698040594637811093 100157938970652873647395)
                ·
                  rfl

theorem cell21_1316634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_1316634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316634 prefixEnd_1316634 := by exact prefixLift 1316634
  have htrace : WordTrace (prefixWord ++ tailWord_1316634) baseStart_1316634 baseEnd_1316634 := by
    simpa [prefixWord, tailWord_1316634, baseEnd_1316634] using wordTrace_append hprefix tailTrace_1316634
  have hstable : (prefixWord ++ tailWord_1316634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316634).length < 2 ^ (prefixWord ++ tailWord_1316634).sum := by decide
  have hdescent : baseEnd_1316634 < baseStart_1316634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316800 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_1316800 : Nat := 118140960795 + 1316800 * 2 ^ 59
def prefixEnd_1316800 : Nat := 4983230072969 + 3 ^ 40 * 1316800 * 2
def baseEnd_1316800 : Nat := 300511700373579221175179

theorem tailTrace_1316800 : CollatzResearch.WordTrace tailWord_1316800 prefixEnd_1316800 300511700373579221175179 := by
  unfold tailWord_1316800
  simp only [CollatzResearch.WordTrace]
  refine ⟨24013820814732983190289927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32018427752977310920386569 24013820814732983190289927)
  ·
    refine ⟨36020731222099474785434891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24013820814732983190289927 36020731222099474785434891)
    ·
      refine ⟨54031096833149212178152337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36020731222099474785434891 54031096833149212178152337)
      ·
        refine ⟨40523322624861909133614253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54031096833149212178152337 40523322624861909133614253)
        ·
          refine ⟨15196245984323215925105345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40523322624861909133614253 15196245984323215925105345)
          ·
            refine ⟨11397184488242411943829009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15196245984323215925105345 11397184488242411943829009)
            ·
              refine ⟨8547888366181808957871757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11397184488242411943829009 8547888366181808957871757)
              ·
                refine ⟨3205458137318178359201909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8547888366181808957871757 3205458137318178359201909)
                ·
                  refine ⟨300511700373579221175179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3205458137318178359201909 300511700373579221175179)
                  ·
                    rfl

theorem cell21_1316800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_1316800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316800 prefixEnd_1316800 := by exact prefixLift 1316800
  have htrace : WordTrace (prefixWord ++ tailWord_1316800) baseStart_1316800 baseEnd_1316800 := by
    simpa [prefixWord, tailWord_1316800, baseEnd_1316800] using wordTrace_append hprefix tailTrace_1316800
  have hstable : (prefixWord ++ tailWord_1316800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316800).length < 2 ^ (prefixWord ++ tailWord_1316800).sum := by decide
  have hdescent : baseEnd_1316800 < baseStart_1316800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316876 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_1316876 : Nat := 118140960795 + 1316876 * 2 ^ 59
def prefixEnd_1316876 : Nat := 4983230072969 + 3 ^ 40 * 1316876 * 2
def baseEnd_1316876 : Nat := 300529044609019977908357

theorem tailTrace_1316876 : CollatzResearch.WordTrace tailWord_1316876 prefixEnd_1316876 300529044609019977908357 := by
  unfold tailWord_1316876
  simp only [CollatzResearch.WordTrace]
  refine ⟨24015206788595315680173241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32020275718127087573564321 24015206788595315680173241)
  ·
    refine ⟨18011405091446486760129931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24015206788595315680173241 18011405091446486760129931)
    ·
      refine ⟨27017107637169730140194897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18011405091446486760129931 27017107637169730140194897)
      ·
        refine ⟨20262830727877297605146173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27017107637169730140194897 20262830727877297605146173)
        ·
          refine ⟨7598561522953986601929815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20262830727877297605146173 7598561522953986601929815)
          ·
            refine ⟨11397842284430979902894723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7598561522953986601929815 11397842284430979902894723)
            ·
              refine ⟨17096763426646469854342085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11397842284430979902894723 17096763426646469854342085)
              ·
                refine ⟨3205643142496213097689141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17096763426646469854342085 3205643142496213097689141)
                ·
                  refine ⟨300529044609019977908357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3205643142496213097689141 300529044609019977908357)
                  ·
                    rfl

theorem cell21_1316876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_1316876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316876 prefixEnd_1316876 := by exact prefixLift 1316876
  have htrace : WordTrace (prefixWord ++ tailWord_1316876) baseStart_1316876 baseEnd_1316876 := by
    simpa [prefixWord, tailWord_1316876, baseEnd_1316876] using wordTrace_append hprefix tailTrace_1316876
  have hstable : (prefixWord ++ tailWord_1316876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316876).length < 2 ^ (prefixWord ++ tailWord_1316876).sum := by decide
  have hdescent : baseEnd_1316876 < baseStart_1316876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316910 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_1316910 : Nat := 118140960795 + 1316910 * 2 ^ 59
def prefixEnd_1316910 : Nat := 4983230072969 + 3 ^ 40 * 1316910 * 2
def baseEnd_1316910 : Nat := 300536803872243474341621

theorem tailTrace_1316910 : CollatzResearch.WordTrace tailWord_1316910 prefixEnd_1316910 300536803872243474341621 := by
  unfold tailWord_1316910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6003956707383431895885523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32021102439378303444722789 6003956707383431895885523)
  ·
    refine ⟨9005935061075147843828285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6003956707383431895885523 9005935061075147843828285)
    ·
      refine ⟨3377225647903180441435607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9005935061075147843828285 3377225647903180441435607)
      ·
        refine ⟨5065838471854770662153411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377225647903180441435607 5065838471854770662153411)
        ·
          refine ⟨7598757707782155993230117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5065838471854770662153411 7598757707782155993230117)
          ·
            refine ⟨1424767070209154248730647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7598757707782155993230117 1424767070209154248730647)
            ·
              refine ⟨2137150605313731373095971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424767070209154248730647 2137150605313731373095971)
              ·
                refine ⟨3205725907970597059643957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2137150605313731373095971 3205725907970597059643957)
                ·
                  refine ⟨300536803872243474341621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3205725907970597059643957 300536803872243474341621)
                  ·
                    rfl

theorem cell21_1316910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_1316910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316910 prefixEnd_1316910 := by exact prefixLift 1316910
  have htrace : WordTrace (prefixWord ++ tailWord_1316910) baseStart_1316910 baseEnd_1316910 := by
    simpa [prefixWord, tailWord_1316910, baseEnd_1316910] using wordTrace_append hprefix tailTrace_1316910
  have hstable : (prefixWord ++ tailWord_1316910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316910).length < 2 ^ (prefixWord ++ tailWord_1316910).sum := by decide
  have hdescent : baseEnd_1316910 < baseStart_1316910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316969 : List Nat := [1, 2, 1, 1, 1, 5, 3, 4, 3]
def baseStart_1316969 : Nat := 118140960795 + 1316969 * 2 ^ 59
def prefixEnd_1316969 : Nat := 4983230072969 + 3 ^ 40 * 1316969 * 2
def baseEnd_1316969 : Nat := 300550268476072482858167

theorem tailTrace_1316969 : CollatzResearch.WordTrace tailWord_1316969 prefixEnd_1316969 300550268476072482858167 := by
  unfold tailWord_1316969
  simp only [CollatzResearch.WordTrace]
  refine ⟨48033805565853708243481961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32022537043902472162321307 48033805565853708243481961)
  ·
    refine ⟨36025354174390281182611471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48033805565853708243481961 36025354174390281182611471)
    ·
      refine ⟨54038031261585421773917207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36025354174390281182611471 54038031261585421773917207)
      ·
        refine ⟨81057046892378132660875811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54038031261585421773917207 81057046892378132660875811)
        ·
          refine ⟨121585570338567198991313717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81057046892378132660875811 121585570338567198991313717)
          ·
            refine ⟨11398647219240674905435661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121585570338567198991313717 11398647219240674905435661)
            ·
              refine ⟨4274492707215253089538373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11398647219240674905435661 4274492707215253089538373)
              ·
                refine ⟨801467382602859954288445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4274492707215253089538373 801467382602859954288445)
                ·
                  refine ⟨300550268476072482858167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801467382602859954288445 300550268476072482858167)
                  ·
                    rfl

theorem cell21_1316969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_1316969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316969 prefixEnd_1316969 := by exact prefixLift 1316969
  have htrace : WordTrace (prefixWord ++ tailWord_1316969) baseStart_1316969 baseEnd_1316969 := by
    simpa [prefixWord, tailWord_1316969, baseEnd_1316969] using wordTrace_append hprefix tailTrace_1316969
  have hstable : (prefixWord ++ tailWord_1316969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316969).length < 2 ^ (prefixWord ++ tailWord_1316969).sum := by decide
  have hdescent : baseEnd_1316969 < baseStart_1316969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316983 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 4]
def baseStart_1316983 : Nat := 118140960795 + 1316983 * 2 ^ 59
def prefixEnd_1316983 : Nat := 4983230072969 + 3 ^ 40 * 1316983 * 2
def baseEnd_1316983 : Nat := 300553463466811569624805

theorem tailTrace_1316983 : CollatzResearch.WordTrace tailWord_1316983 prefixEnd_1316983 300553463466811569624805 := by
  unfold tailWord_1316983
  simp only [CollatzResearch.WordTrace]
  refine ⟨48034316187802988634491603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32022877458535325756327735 48034316187802988634491603)
  ·
    refine ⟨72051474281704482951737405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48034316187802988634491603 72051474281704482951737405)
    ·
      refine ⟨27019302855639181106901527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72051474281704482951737405 27019302855639181106901527)
      ·
        refine ⟨40528954283458771660352291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27019302855639181106901527 40528954283458771660352291)
        ·
          refine ⟨60793431425188157490528437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40528954283458771660352291 60793431425188157490528437)
          ·
            refine ⟨5699384196111389764737041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60793431425188157490528437 5699384196111389764737041)
            ·
              refine ⟨4274538147083542323552781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5699384196111389764737041 4274538147083542323552781)
              ·
                refine ⟨1602951805156328371332293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4274538147083542323552781 1602951805156328371332293)
                ·
                  refine ⟨300553463466811569624805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1602951805156328371332293 300553463466811569624805)
                  ·
                    rfl

theorem cell21_1316983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 4].length) (baseStart_1316983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1316983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1316983 prefixEnd_1316983 := by exact prefixLift 1316983
  have htrace : WordTrace (prefixWord ++ tailWord_1316983) baseStart_1316983 baseEnd_1316983 := by
    simpa [prefixWord, tailWord_1316983, baseEnd_1316983] using wordTrace_append hprefix tailTrace_1316983
  have hstable : (prefixWord ++ tailWord_1316983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316983).length < 2 ^ (prefixWord ++ tailWord_1316983).sum := by decide
  have hdescent : baseEnd_1316983 < baseStart_1316983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317011 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 9]
def baseStart_1317011 : Nat := 118140960795 + 1317011 * 2 ^ 59
def prefixEnd_1317011 : Nat := 4983230072969 + 3 ^ 40 * 1317011 * 2
def baseEnd_1317011 : Nat := 300559853448289743158081

theorem tailTrace_1317011 : CollatzResearch.WordTrace tailWord_1317011 prefixEnd_1317011 300559853448289743158081 := by
  unfold tailWord_1317011
  simp only [CollatzResearch.WordTrace]
  refine ⟨48035337431701549416510887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32023558287801032944340591 48035337431701549416510887)
  ·
    refine ⟨72053006147552324124766331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48035337431701549416510887 72053006147552324124766331)
    ·
      refine ⟨108079509221328486187149497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72053006147552324124766331 108079509221328486187149497)
      ·
        refine ⟨81059631915996364640362123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108079509221328486187149497 81059631915996364640362123)
        ·
          refine ⟨121589447873994546960543185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81059631915996364640362123 121589447873994546960543185)
          ·
            refine ⟨91192085905495910220407389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121589447873994546960543185 91192085905495910220407389)
            ·
              refine ⟨34197032214560966332652771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91192085905495910220407389 34197032214560966332652771)
              ·
                refine ⟨51295548321841449498979157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34197032214560966332652771 51295548321841449498979157)
                ·
                  refine ⟨300559853448289743158081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51295548321841449498979157 300559853448289743158081)
                  ·
                    rfl

theorem cell21_1317011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_1317011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317011 prefixEnd_1317011 := by exact prefixLift 1317011
  have htrace : WordTrace (prefixWord ++ tailWord_1317011) baseStart_1317011 baseEnd_1317011 := by
    simpa [prefixWord, tailWord_1317011, baseEnd_1317011] using wordTrace_append hprefix tailTrace_1317011
  have hstable : (prefixWord ++ tailWord_1317011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317011).length < 2 ^ (prefixWord ++ tailWord_1317011).sum := by decide
  have hdescent : baseEnd_1317011 < baseStart_1317011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317034 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_1317034 : Nat := 118140960795 + 1317034 * 2 ^ 59
def prefixEnd_1317034 : Nat := 4983230072969 + 3 ^ 40 * 1317034 * 2
def baseEnd_1317034 : Nat := 300565102361646814274701

theorem tailTrace_1317034 : CollatzResearch.WordTrace tailWord_1317034 prefixEnd_1317034 300565102361646814274701 := by
  unfold tailWord_1317034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12009044077654556086149539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32024117540412149563065437 12009044077654556086149539)
  ·
    refine ⟨18013566116481834129224309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12009044077654556086149539 18013566116481834129224309)
    ·
      refine ⟨1688771823420171949614779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18013566116481834129224309 1688771823420171949614779)
      ·
        refine ⟨2533157735130257924422169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688771823420171949614779 2533157735130257924422169)
        ·
          refine ⟨1899868301347693443316627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2533157735130257924422169 1899868301347693443316627)
          ·
            refine ⟨2849802452021540164974941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899868301347693443316627 2849802452021540164974941)
            ·
              refine ⟨1068675919508077561865603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2849802452021540164974941 1068675919508077561865603)
              ·
                refine ⟨1603013879262116342798405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068675919508077561865603 1603013879262116342798405)
                ·
                  refine ⟨300565102361646814274701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1603013879262116342798405 300565102361646814274701)
                  ·
                    rfl

theorem cell21_1317034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_1317034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317034 prefixEnd_1317034 := by exact prefixLift 1317034
  have htrace : WordTrace (prefixWord ++ tailWord_1317034) baseStart_1317034 baseEnd_1317034 := by
    simpa [prefixWord, tailWord_1317034, baseEnd_1317034] using wordTrace_append hprefix tailTrace_1317034
  have hstable : (prefixWord ++ tailWord_1317034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317034).length < 2 ^ (prefixWord ++ tailWord_1317034).sum := by decide
  have hdescent : baseEnd_1317034 < baseStart_1317034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317093 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 4]
def baseStart_1317093 : Nat := 118140960795 + 1317093 * 2 ^ 59
def prefixEnd_1317093 : Nat := 4983230072969 + 3 ^ 40 * 1317093 * 2
def baseEnd_1317093 : Nat := 300578566965475822791247

theorem tailTrace_1317093 : CollatzResearch.WordTrace tailWord_1317093 prefixEnd_1317093 300578566965475822791247 := by
  unfold tailWord_1317093
  simp only [CollatzResearch.WordTrace]
  refine ⟨48038328217404477420995933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32025552144936318280663955 48038328217404477420995933)
  ·
    refine ⟨18014373081526679032873475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48038328217404477420995933 18014373081526679032873475)
    ·
      refine ⟨27021559622290018549310213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18014373081526679032873475 27021559622290018549310213)
      ·
        refine ⟨5066542429179378477995665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27021559622290018549310213 5066542429179378477995665)
        ·
          refine ⟨3799906821884533858496749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5066542429179378477995665 3799906821884533858496749)
          ·
            refine ⟨1424965058206700196936281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3799906821884533858496749 1424965058206700196936281)
            ·
              refine ⟨1068723793655025147702211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424965058206700196936281 1068723793655025147702211)
              ·
                refine ⟨1603085690482537721553317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068723793655025147702211 1603085690482537721553317)
                ·
                  refine ⟨300578566965475822791247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1603085690482537721553317 300578566965475822791247)
                  ·
                    rfl

theorem cell21_1317093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_1317093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317093 prefixEnd_1317093 := by exact prefixLift 1317093
  have htrace : WordTrace (prefixWord ++ tailWord_1317093) baseStart_1317093 baseEnd_1317093 := by
    simpa [prefixWord, tailWord_1317093, baseEnd_1317093] using wordTrace_append hprefix tailTrace_1317093
  have hstable : (prefixWord ++ tailWord_1317093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317093).length < 2 ^ (prefixWord ++ tailWord_1317093).sum := by decide
  have hdescent : baseEnd_1317093 < baseStart_1317093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317121 : List Nat := [1, 2, 4, 1, 1, 2, 2, 5, 3]
def baseStart_1317121 : Nat := 118140960795 + 1317121 * 2 ^ 59
def prefixEnd_1317121 : Nat := 4983230072969 + 3 ^ 40 * 1317121 * 2
def baseEnd_1317121 : Nat := 300584956946953996324523

theorem tailTrace_1317121 : CollatzResearch.WordTrace tailWord_1317121 prefixEnd_1317121 300584956946953996324523 := by
  unfold tailWord_1317121
  simp only [CollatzResearch.WordTrace]
  refine ⟨48039349461303038203015217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32026232974202025468676811 48039349461303038203015217)
  ·
    refine ⟨36029512095977278652261413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48039349461303038203015217 36029512095977278652261413)
    ·
      refine ⟨6755533517995739747299015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36029512095977278652261413 6755533517995739747299015)
      ·
        refine ⟨10133300276993609620948523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6755533517995739747299015 10133300276993609620948523)
        ·
          refine ⟨15199950415490414431422785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10133300276993609620948523 15199950415490414431422785)
          ·
            refine ⟨11399962811617810823567089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15199950415490414431422785 11399962811617810823567089)
            ·
              refine ⟨8549972108713358117675317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11399962811617810823567089 8549972108713358117675317)
              ·
                refine ⟨801559885191877323532061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8549972108713358117675317 801559885191877323532061)
                ·
                  refine ⟨300584956946953996324523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801559885191877323532061 300584956946953996324523)
                  ·
                    rfl

theorem cell21_1317121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_1317121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317121 prefixEnd_1317121 := by exact prefixLift 1317121
  have htrace : WordTrace (prefixWord ++ tailWord_1317121) baseStart_1317121 baseEnd_1317121 := by
    simpa [prefixWord, tailWord_1317121, baseEnd_1317121] using wordTrace_append hprefix tailTrace_1317121
  have hstable : (prefixWord ++ tailWord_1317121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317121).length < 2 ^ (prefixWord ++ tailWord_1317121).sum := by decide
  have hdescent : baseEnd_1317121 < baseStart_1317121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317301 : List Nat := [1, 3, 3, 2, 3, 9]
def baseStart_1317301 : Nat := 118140960795 + 1317301 * 2 ^ 59
def prefixEnd_1317301 : Nat := 4983230072969 + 3 ^ 40 * 1317301 * 2
def baseEnd_1317301 : Nat := 11134297607381988271265

theorem tailTrace_1317301 : CollatzResearch.WordTrace tailWord_1317301 prefixEnd_1317301 11134297607381988271265 := by
  unfold tailWord_1317301
  simp only [CollatzResearch.WordTrace]
  refine ⟨48045914600650928944567757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32030609733767285963045171 48045914600650928944567757)
  ·
    refine ⟨18017217975244098354212909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48045914600650928944567757 18017217975244098354212909)
    ·
      refine ⟨6756456740716536882829841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18017217975244098354212909 6756456740716536882829841)
      ·
        refine ⟨5067342555537402662122381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6756456740716536882829841 5067342555537402662122381)
        ·
          refine ⟨1900253458326525998295893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5067342555537402662122381 1900253458326525998295893)
          ·
            refine ⟨11134297607381988271265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1900253458326525998295893 11134297607381988271265)
            ·
              rfl

theorem cell21_1317301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 9].length) (baseStart_1317301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317301 prefixEnd_1317301 := by exact prefixLift 1317301
  have htrace : WordTrace (prefixWord ++ tailWord_1317301) baseStart_1317301 baseEnd_1317301 := by
    simpa [prefixWord, tailWord_1317301, baseEnd_1317301] using wordTrace_append hprefix tailTrace_1317301
  have hstable : (prefixWord ++ tailWord_1317301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317301).length < 2 ^ (prefixWord ++ tailWord_1317301).sum := by decide
  have hdescent : baseEnd_1317301 < baseStart_1317301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317315 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 5]
def baseStart_1317315 : Nat := 118140960795 + 1317315 * 2 ^ 59
def prefixEnd_1317315 : Nat := 4983230072969 + 3 ^ 40 * 1317315 * 2
def baseEnd_1317315 : Nat := 300629230390052770090793

theorem tailTrace_1317315 : CollatzResearch.WordTrace tailWord_1317315 prefixEnd_1317315 300629230390052770090793 := by
  unfold tailWord_1317315
  simp only [CollatzResearch.WordTrace]
  refine ⟨48046425222600209335577399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32030950148400139557051599 48046425222600209335577399)
  ·
    refine ⟨72069637833900314003366099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48046425222600209335577399 72069637833900314003366099)
    ·
      refine ⟨108104456750850471005049149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72069637833900314003366099 108104456750850471005049149)
      ·
        refine ⟨40539171281568926626893431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108104456750850471005049149 40539171281568926626893431)
        ·
          refine ⟨60808756922353389940340147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40539171281568926626893431 60808756922353389940340147)
          ·
            refine ⟨91213135383530084910510221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60808756922353389940340147 91213135383530084910510221)
            ·
              refine ⟨34204925768823781841441333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91213135383530084910510221 34204925768823781841441333)
              ·
                refine ⟨3206711790827229547635125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34204925768823781841441333 3206711790827229547635125)
                ·
                  refine ⟨300629230390052770090793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3206711790827229547635125 300629230390052770090793)
                  ·
                    rfl

theorem cell21_1317315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_1317315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317315 prefixEnd_1317315 := by exact prefixLift 1317315
  have htrace : WordTrace (prefixWord ++ tailWord_1317315) baseStart_1317315 baseEnd_1317315 := by
    simpa [prefixWord, tailWord_1317315, baseEnd_1317315] using wordTrace_append hprefix tailTrace_1317315
  have hstable : (prefixWord ++ tailWord_1317315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317315).length < 2 ^ (prefixWord ++ tailWord_1317315).sum := by decide
  have hdescent : baseEnd_1317315 < baseStart_1317315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317332 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1317332 : Nat := 118140960795 + 1317332 * 2 ^ 59
def prefixEnd_1317332 : Nat := 4983230072969 + 3 ^ 40 * 1317332 * 2
def baseEnd_1317332 : Nat := 300633110021664518307425

theorem tailTrace_1317332 : CollatzResearch.WordTrace tailWord_1317332 prefixEnd_1317332 300633110021664518307425 := by
  unfold tailWord_1317332
  simp only [CollatzResearch.WordTrace]
  refine ⟨24023522631769310619473125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32031363509025747492630833 24023522631769310619473125)
  ·
    refine ⟨4504410493456745741151211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24023522631769310619473125 4504410493456745741151211)
    ·
      refine ⟨6756615740185118611726817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4504410493456745741151211 6756615740185118611726817)
      ·
        refine ⟨5067461805138838958795113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6756615740185118611726817 5067461805138838958795113)
        ·
          refine ⟨3800596353854129219096335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5067461805138838958795113 3800596353854129219096335)
          ·
            refine ⟨5700894530781193828644503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800596353854129219096335 5700894530781193828644503)
            ·
              refine ⟨8551341796171790742966755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700894530781193828644503 8551341796171790742966755)
              ·
                refine ⟨12827012694257686114450133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8551341796171790742966755 12827012694257686114450133)
                ·
                  refine ⟨300633110021664518307425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12827012694257686114450133 300633110021664518307425)
                  ·
                    rfl

theorem cell21_1317332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1317332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317332 prefixEnd_1317332 := by exact prefixLift 1317332
  have htrace : WordTrace (prefixWord ++ tailWord_1317332) baseStart_1317332 baseEnd_1317332 := by
    simpa [prefixWord, tailWord_1317332, baseEnd_1317332] using wordTrace_append hprefix tailTrace_1317332
  have hstable : (prefixWord ++ tailWord_1317332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317332).length < 2 ^ (prefixWord ++ tailWord_1317332).sum := by decide
  have hdescent : baseEnd_1317332 < baseStart_1317332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317360 : List Nat := [2, 1, 1, 1, 3, 3, 10]
def baseStart_1317360 : Nat := 118140960795 + 1317360 * 2 ^ 59
def prefixEnd_1317360 : Nat := 4983230072969 + 3 ^ 40 * 1317360 * 2
def baseEnd_1317360 : Nat := 33404388889238076871189

theorem tailTrace_1317360 : CollatzResearch.WordTrace tailWord_1317360 prefixEnd_1317360 33404388889238076871189 := by
  unfold tailWord_1317360
  simp only [CollatzResearch.WordTrace]
  refine ⟨24024033253718591010482767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32032044338291454680643689 24024033253718591010482767)
  ·
    refine ⟨36036049880577886515724151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24024033253718591010482767 36036049880577886515724151)
    ·
      refine ⟨54054074820866829773586227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36036049880577886515724151 54054074820866829773586227)
      ·
        refine ⟨81081112231300244660379341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54054074820866829773586227 81081112231300244660379341)
        ·
          refine ⟨30405417086737591747642253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81081112231300244660379341 30405417086737591747642253)
          ·
            refine ⟨11402031407526596905365845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30405417086737591747642253 11402031407526596905365845)
            ·
              refine ⟨33404388889238076871189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11402031407526596905365845 33404388889238076871189)
              ·
                rfl

theorem cell21_1317360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 10].length) (baseStart_1317360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317360 prefixEnd_1317360 := by exact prefixLift 1317360
  have htrace : WordTrace (prefixWord ++ tailWord_1317360) baseStart_1317360 baseEnd_1317360 := by
    simpa [prefixWord, tailWord_1317360, baseEnd_1317360] using wordTrace_append hprefix tailTrace_1317360
  have hstable : (prefixWord ++ tailWord_1317360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317360).length < 2 ^ (prefixWord ++ tailWord_1317360).sum := by decide
  have hdescent : baseEnd_1317360 < baseStart_1317360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317532 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_1317532 : Nat := 118140960795 + 1317532 * 2 ^ 59
def prefixEnd_1317532 : Nat := 4983230072969 + 3 ^ 40 * 1317532 * 2
def baseEnd_1317532 : Nat := 300678752746508614973683

theorem tailTrace_1317532 : CollatzResearch.WordTrace tailWord_1317532 prefixEnd_1317532 300678752746508614973683 := by
  unfold tailWord_1317532
  simp only [CollatzResearch.WordTrace]
  refine ⟨24027169931407027698113425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32036226575209370264151233 24027169931407027698113425)
  ·
    refine ⟨18020377448555270773585069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24027169931407027698113425 18020377448555270773585069)
    ·
      refine ⟨6757641543208226540094401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18020377448555270773585069 6757641543208226540094401)
      ·
        refine ⟨5068231157406169905070801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6757641543208226540094401 5068231157406169905070801)
        ·
          refine ⟨3801173368054627428803101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5068231157406169905070801 3801173368054627428803101)
          ·
            refine ⟨1425440013020485285801163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3801173368054627428803101 1425440013020485285801163)
            ·
              refine ⟨2138160019530727928701745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425440013020485285801163 2138160019530727928701745)
              ·
                refine ⟨1603620014648045946526309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138160019530727928701745 1603620014648045946526309)
                ·
                  refine ⟨300678752746508614973683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1603620014648045946526309 300678752746508614973683)
                  ·
                    rfl

theorem cell21_1317532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_1317532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317532 prefixEnd_1317532 := by exact prefixLift 1317532
  have htrace : WordTrace (prefixWord ++ tailWord_1317532) baseStart_1317532 baseEnd_1317532 := by
    simpa [prefixWord, tailWord_1317532, baseEnd_1317532] using wordTrace_append hprefix tailTrace_1317532
  have hstable : (prefixWord ++ tailWord_1317532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317532).length < 2 ^ (prefixWord ++ tailWord_1317532).sum := by decide
  have hdescent : baseEnd_1317532 < baseStart_1317532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317605 : List Nat := [1, 3, 1, 4, 1, 3, 2, 6]
def baseStart_1317605 : Nat := 118140960795 + 1317605 * 2 ^ 59
def prefixEnd_1317605 : Nat := 4983230072969 + 3 ^ 40 * 1317605 * 2
def baseEnd_1317605 : Nat := 100231804113692236752289

theorem tailTrace_1317605 : CollatzResearch.WordTrace tailWord_1317605 prefixEnd_1317605 100231804113692236752289 := by
  unfold tailWord_1317605
  simp only [CollatzResearch.WordTrace]
  refine ⟨48057002391549588863634269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32038001594366392575756179 48057002391549588863634269)
  ·
    refine ⟨18021375896831095823862851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48057002391549588863634269 18021375896831095823862851)
    ·
      refine ⟨27032063845246643735794277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18021375896831095823862851 27032063845246643735794277)
      ·
        refine ⟨5068511970983745700461427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27032063845246643735794277 5068511970983745700461427)
        ·
          refine ⟨7602767956475618550692141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5068511970983745700461427 7602767956475618550692141)
          ·
            refine ⟨2851037983678356956509553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7602767956475618550692141 2851037983678356956509553)
            ·
              refine ⟨2138278487758767717382165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2851037983678356956509553 2138278487758767717382165)
              ·
                refine ⟨100231804113692236752289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2138278487758767717382165 100231804113692236752289)
                ·
                  rfl

theorem cell21_1317605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 6].length) (baseStart_1317605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317605 prefixEnd_1317605 := by exact prefixLift 1317605
  have htrace : WordTrace (prefixWord ++ tailWord_1317605) baseStart_1317605 baseEnd_1317605 := by
    simpa [prefixWord, tailWord_1317605, baseEnd_1317605] using wordTrace_append hprefix tailTrace_1317605
  have hstable : (prefixWord ++ tailWord_1317605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317605).length < 2 ^ (prefixWord ++ tailWord_1317605).sum := by decide
  have hdescent : baseEnd_1317605 < baseStart_1317605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317681 : List Nat := [1, 2, 2, 3, 2, 1, 5, 5]
def baseStart_1317681 : Nat := 118140960795 + 1317681 * 2 ^ 59
def prefixEnd_1317681 : Nat := 4983230072969 + 3 ^ 40 * 1317681 * 2
def baseEnd_1317681 : Nat := 100237585525505822330015

theorem tailTrace_1317681 : CollatzResearch.WordTrace tailWord_1317681 prefixEnd_1317681 100237585525505822330015 := by
  unfold tailWord_1317681
  simp only [CollatzResearch.WordTrace]
  refine ⟨48059774339274253843400897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32039849559516169228933931 48059774339274253843400897)
  ·
    refine ⟨36044830754455690382550673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48059774339274253843400897 36044830754455690382550673)
    ·
      refine ⟨27033623065841767786913005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36044830754455690382550673 27033623065841767786913005)
      ·
        refine ⟨10137608649690662920092377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27033623065841767786913005 10137608649690662920092377)
        ·
          refine ⟨7603206487267997190069283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10137608649690662920092377 7603206487267997190069283)
          ·
            refine ⟨11404809730901995785103925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7603206487267997190069283 11404809730901995785103925)
            ·
              refine ⟨1069200912272062104853493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11404809730901995785103925 1069200912272062104853493)
              ·
                refine ⟨100237585525505822330015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1069200912272062104853493 100237585525505822330015)
                ·
                  rfl

theorem cell21_1317681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 5].length) (baseStart_1317681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317681 prefixEnd_1317681 := by exact prefixLift 1317681
  have htrace : WordTrace (prefixWord ++ tailWord_1317681) baseStart_1317681 baseEnd_1317681 := by
    simpa [prefixWord, tailWord_1317681, baseEnd_1317681] using wordTrace_append hprefix tailTrace_1317681
  have hstable : (prefixWord ++ tailWord_1317681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317681).length < 2 ^ (prefixWord ++ tailWord_1317681).sum := by decide
  have hdescent : baseEnd_1317681 < baseStart_1317681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317712 : List Nat := [2, 1, 1, 1, 1, 4, 4, 4, 3]
def baseStart_1317712 : Nat := 118140960795 + 1317712 * 2 ^ 59
def prefixEnd_1317712 : Nat := 4983230072969 + 3 ^ 40 * 1317712 * 2
def baseEnd_1317712 : Nat := 300719831198868301973315

theorem tailTrace_1317712 : CollatzResearch.WordTrace tailWord_1317712 prefixEnd_1317712 300719831198868301973315 := by
  unfold tailWord_1317712
  simp only [CollatzResearch.WordTrace]
  refine ⟨24030452501080973068889695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32040603334774630758519593 24030452501080973068889695)
  ·
    refine ⟨36045678751621459603334543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24030452501080973068889695 36045678751621459603334543)
    ·
      refine ⟨54068518127432189405001815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36045678751621459603334543 54068518127432189405001815)
      ·
        refine ⟨81102777191148284107502723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54068518127432189405001815 81102777191148284107502723)
        ·
          refine ⟨121654165786722426161254085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81102777191148284107502723 121654165786722426161254085)
          ·
            refine ⟨22810156085010454905235141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121654165786722426161254085 22810156085010454905235141)
            ·
              refine ⟨4276904265939460294731589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22810156085010454905235141 4276904265939460294731589)
              ·
                refine ⟨801919549863648805262173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4276904265939460294731589 801919549863648805262173)
                ·
                  refine ⟨300719831198868301973315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801919549863648805262173 300719831198868301973315)
                  ·
                    rfl

theorem cell21_1317712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_1317712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317712 prefixEnd_1317712 := by exact prefixLift 1317712
  have htrace : WordTrace (prefixWord ++ tailWord_1317712) baseStart_1317712 baseEnd_1317712 := by
    simpa [prefixWord, tailWord_1317712, baseEnd_1317712] using wordTrace_append hprefix tailTrace_1317712
  have hstable : (prefixWord ++ tailWord_1317712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317712).length < 2 ^ (prefixWord ++ tailWord_1317712).sum := by decide
  have hdescent : baseEnd_1317712 < baseStart_1317712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317740 : List Nat := [2, 2, 1, 1, 4, 1, 3, 7]
def baseStart_1317740 : Nat := 118140960795 + 1317740 * 2 ^ 59
def prefixEnd_1317740 : Nat := 4983230072969 + 3 ^ 40 * 1317740 * 2
def baseEnd_1317740 : Nat := 100242073726782158502197

theorem tailTrace_1317740 : CollatzResearch.WordTrace tailWord_1317740 prefixEnd_1317740 100242073726782158502197 := by
  unfold tailWord_1317740
  simp only [CollatzResearch.WordTrace]
  refine ⟨24030963123030253459899337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32041284164040337946532449 24030963123030253459899337)
  ·
    refine ⟨18023222342272690094924503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24030963123030253459899337 18023222342272690094924503)
    ·
      refine ⟨27034833513409035142386755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18023222342272690094924503 27034833513409035142386755)
      ·
        refine ⟨40552250270113552713580133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27034833513409035142386755 40552250270113552713580133)
        ·
          refine ⟨7603546925646291133796275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40552250270113552713580133 7603546925646291133796275)
          ·
            refine ⟨11405320388469436700694413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7603546925646291133796275 11405320388469436700694413)
            ·
              refine ⟨4276995145676038762760405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11405320388469436700694413 4276995145676038762760405)
              ·
                refine ⟨100242073726782158502197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4276995145676038762760405 100242073726782158502197)
                ·
                  rfl

theorem cell21_1317740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_1317740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317740 prefixEnd_1317740 := by exact prefixLift 1317740
  have htrace : WordTrace (prefixWord ++ tailWord_1317740) baseStart_1317740 baseEnd_1317740 := by
    simpa [prefixWord, tailWord_1317740, baseEnd_1317740] using wordTrace_append hprefix tailTrace_1317740
  have hstable : (prefixWord ++ tailWord_1317740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317740).length < 2 ^ (prefixWord ++ tailWord_1317740).sum := by decide
  have hdescent : baseEnd_1317740 < baseStart_1317740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317771 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 5]
def baseStart_1317771 : Nat := 118140960795 + 1317771 * 2 ^ 59
def prefixEnd_1317771 : Nat := 4983230072969 + 3 ^ 40 * 1317771 * 2
def baseEnd_1317771 : Nat := 300733295802697310489861

theorem tailTrace_1317771 : CollatzResearch.WordTrace tailWord_1317771 prefixEnd_1317771 300733295802697310489861 := by
  unfold tailWord_1317771
  simp only [CollatzResearch.WordTrace]
  refine ⟨48063056908948199214177167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32042037939298799476118111 48063056908948199214177167)
  ·
    refine ⟨72094585363422298821265751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48063056908948199214177167 72094585363422298821265751)
    ·
      refine ⟨108141878045133448231898627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72094585363422298821265751 108141878045133448231898627)
      ·
        refine ⟨162212817067700172347847941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108141878045133448231898627 162212817067700172347847941)
        ·
          refine ⟨30414903200193782315221489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162212817067700172347847941 30414903200193782315221489)
          ·
            refine ⟨22811177400145336736416117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30414903200193782315221489 22811177400145336736416117)
            ·
              refine ⟨2138547881263625319039011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22811177400145336736416117 2138547881263625319039011)
              ·
                refine ⟨3207821821895437978558517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138547881263625319039011 3207821821895437978558517)
                ·
                  refine ⟨300733295802697310489861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3207821821895437978558517 300733295802697310489861)
                  ·
                    rfl

theorem cell21_1317771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 5].length) (baseStart_1317771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317771 prefixEnd_1317771 := by exact prefixLift 1317771
  have htrace : WordTrace (prefixWord ++ tailWord_1317771) baseStart_1317771 baseEnd_1317771 := by
    simpa [prefixWord, tailWord_1317771, baseEnd_1317771] using wordTrace_append hprefix tailTrace_1317771
  have hstable : (prefixWord ++ tailWord_1317771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317771).length < 2 ^ (prefixWord ++ tailWord_1317771).sum := by decide
  have hdescent : baseEnd_1317771 < baseStart_1317771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317814 : List Nat := [5, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1317814 : Nat := 118140960795 + 1317814 * 2 ^ 59
def prefixEnd_1317814 : Nat := 4983230072969 + 3 ^ 40 * 1317814 * 2
def baseEnd_1317814 : Nat := 300743108988538791273107

theorem tailTrace_1317814 : CollatzResearch.WordTrace tailWord_1317814 prefixEnd_1317814 300743108988538791273107 := by
  unfold tailWord_1317814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3004039077987026097374531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32043083498528278371994997 3004039077987026097374531)
  ·
    refine ⟨4506058616980539146061797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3004039077987026097374531 4506058616980539146061797)
    ·
      refine ⟨844885990683851089886587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4506058616980539146061797 844885990683851089886587)
      ·
        refine ⟨1267328986025776634829881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844885990683851089886587 1267328986025776634829881)
        ·
          refine ⟨950496739519332476122411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1267328986025776634829881 950496739519332476122411)
          ·
            refine ⟨1425745109278998714183617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950496739519332476122411 1425745109278998714183617)
            ·
              refine ⟨1069308831959249035637713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425745109278998714183617 1069308831959249035637713)
              ·
                refine ⟨801981623969436776728285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1069308831959249035637713 801981623969436776728285)
                ·
                  refine ⟨300743108988538791273107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801981623969436776728285 300743108988538791273107)
                  ·
                    rfl

theorem cell21_1317814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1317814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317814 prefixEnd_1317814 := by exact prefixLift 1317814
  have htrace : WordTrace (prefixWord ++ tailWord_1317814) baseStart_1317814 baseEnd_1317814 := by
    simpa [prefixWord, tailWord_1317814, baseEnd_1317814] using wordTrace_append hprefix tailTrace_1317814
  have hstable : (prefixWord ++ tailWord_1317814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317814).length < 2 ^ (prefixWord ++ tailWord_1317814).sum := by decide
  have hdescent : baseEnd_1317814 < baseStart_1317814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317864 : List Nat := [2, 1, 4, 1, 1, 1, 3, 5, 3]
def baseStart_1317864 : Nat := 118140960795 + 1317864 * 2 ^ 59
def prefixEnd_1317864 : Nat := 4983230072969 + 3 ^ 40 * 1317864 * 2
def baseEnd_1317864 : Nat := 300754519669749815439671

theorem tailTrace_1317864 : CollatzResearch.WordTrace tailWord_1317864 prefixEnd_1317864 300754519669749815439671 := by
  unfold tailWord_1317864
  simp only [CollatzResearch.WordTrace]
  refine ⟨24033224448805638048656323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32044299265074184064875097 24033224448805638048656323)
  ·
    refine ⟨36049836673208457072984485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24033224448805638048656323 36049836673208457072984485)
    ·
      refine ⟨6759344376226585701184591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36049836673208457072984485 6759344376226585701184591)
      ·
        refine ⟨10139016564339878551776887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6759344376226585701184591 10139016564339878551776887)
        ·
          refine ⟨15208524846509817827665331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10139016564339878551776887 15208524846509817827665331)
          ·
            refine ⟨22812787269764726741497997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15208524846509817827665331 22812787269764726741497997)
            ·
              refine ⟨8554795226161772528061749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22812787269764726741497997 8554795226161772528061749)
              ·
                refine ⟨802012052452666174505789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8554795226161772528061749 802012052452666174505789)
                ·
                  refine ⟨300754519669749815439671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802012052452666174505789 300754519669749815439671)
                  ·
                    rfl

theorem cell21_1317864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_1317864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317864 prefixEnd_1317864 := by exact prefixLift 1317864
  have htrace : WordTrace (prefixWord ++ tailWord_1317864) baseStart_1317864 baseEnd_1317864 := by
    simpa [prefixWord, tailWord_1317864, baseEnd_1317864] using wordTrace_append hprefix tailTrace_1317864
  have hstable : (prefixWord ++ tailWord_1317864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317864).length < 2 ^ (prefixWord ++ tailWord_1317864).sum := by decide
  have hdescent : baseEnd_1317864 < baseStart_1317864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317895 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 4]
def baseStart_1317895 : Nat := 118140960795 + 1317895 * 2 ^ 59
def prefixEnd_1317895 : Nat := 4983230072969 + 3 ^ 40 * 1317895 * 2
def baseEnd_1317895 : Nat := 300761594292100650422941

theorem tailTrace_1317895 : CollatzResearch.WordTrace tailWord_1317895 prefixEnd_1317895 300761594292100650422941 := by
  unfold tailWord_1317895
  simp only [CollatzResearch.WordTrace]
  refine ⟨48067579560498968391691139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32045053040332645594460759 48067579560498968391691139)
  ·
    refine ⟨72101369340748452587536709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48067579560498968391691139 72101369340748452587536709)
    ·
      refine ⟨13519006751390334860163133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72101369340748452587536709 13519006751390334860163133)
      ·
        refine ⟨5069627531771375572561175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13519006751390334860163133 5069627531771375572561175)
        ·
          refine ⟨7604441297657063358841763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5069627531771375572561175 7604441297657063358841763)
          ·
            refine ⟨11406661946485595038262645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7604441297657063358841763 11406661946485595038262645)
            ·
              refine ⟨1069374557483024534837123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11406661946485595038262645 1069374557483024534837123)
              ·
                refine ⟨1604061836224536802255685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069374557483024534837123 1604061836224536802255685)
                ·
                  refine ⟨300761594292100650422941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604061836224536802255685 300761594292100650422941)
                  ·
                    rfl

theorem cell21_1317895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 4].length) (baseStart_1317895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317895 prefixEnd_1317895 := by exact prefixLift 1317895
  have htrace : WordTrace (prefixWord ++ tailWord_1317895) baseStart_1317895 baseEnd_1317895 := by
    simpa [prefixWord, tailWord_1317895, baseEnd_1317895] using wordTrace_append hprefix tailTrace_1317895
  have hstable : (prefixWord ++ tailWord_1317895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317895).length < 2 ^ (prefixWord ++ tailWord_1317895).sum := by decide
  have hdescent : baseEnd_1317895 < baseStart_1317895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317909 : List Nat := [1, 3, 2, 1, 4, 1, 4, 5]
def baseStart_1317909 : Nat := 118140960795 + 1317909 * 2 ^ 59
def prefixEnd_1317909 : Nat := 4983230072969 + 3 ^ 40 * 1317909 * 2
def baseEnd_1317909 : Nat := 100254929760946579063193

theorem tailTrace_1317909 : CollatzResearch.WordTrace tailWord_1317909 prefixEnd_1317909 100254929760946579063193 := by
  unfold tailWord_1317909
  simp only [CollatzResearch.WordTrace]
  refine ⟨48068090182448248782700781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32045393454965499188467187 48068090182448248782700781)
  ·
    refine ⟨18025533818418093293512793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48068090182448248782700781 18025533818418093293512793)
    ·
      refine ⟨13519150363813569970134595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18025533818418093293512793 13519150363813569970134595)
      ·
        refine ⟨20278725545720354955201893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13519150363813569970134595 20278725545720354955201893)
        ·
          refine ⟨3802261039822566554100355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20278725545720354955201893 3802261039822566554100355)
          ·
            refine ⟨5703391559733849831150533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3802261039822566554100355 5703391559733849831150533)
            ·
              refine ⟨1069385917450096843340725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5703391559733849831150533 1069385917450096843340725)
              ·
                refine ⟨100254929760946579063193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1069385917450096843340725 100254929760946579063193)
                ·
                  rfl

theorem cell21_1317909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 5].length) (baseStart_1317909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317909 prefixEnd_1317909 := by exact prefixLift 1317909
  have htrace : WordTrace (prefixWord ++ tailWord_1317909) baseStart_1317909 baseEnd_1317909 := by
    simpa [prefixWord, tailWord_1317909, baseEnd_1317909] using wordTrace_append hprefix tailTrace_1317909
  have hstable : (prefixWord ++ tailWord_1317909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317909).length < 2 ^ (prefixWord ++ tailWord_1317909).sum := by decide
  have hdescent : baseEnd_1317909 < baseStart_1317909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317937 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 6]
def baseStart_1317937 : Nat := 118140960795 + 1317937 * 2 ^ 59
def prefixEnd_1317937 : Nat := 4983230072969 + 3 ^ 40 * 1317937 * 2
def baseEnd_1317937 : Nat := 300771179264317910722855

theorem tailTrace_1317937 : CollatzResearch.WordTrace tailWord_1317937 prefixEnd_1317937 300771179264317910722855 := by
  unfold tailWord_1317937
  simp only [CollatzResearch.WordTrace]
  refine ⟨48069111426346809564720065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32046074284231206376480043 48069111426346809564720065)
  ·
    refine ⟨36051833569760107173540049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48069111426346809564720065 36051833569760107173540049)
    ·
      refine ⟨27038875177320080380155037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36051833569760107173540049 27038875177320080380155037)
      ·
        refine ⟨10139578191495030142558139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27038875177320080380155037 10139578191495030142558139)
        ·
          refine ⟨15209367287242545213837209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10139578191495030142558139 15209367287242545213837209)
          ·
            refine ⟨11407025465431908910377907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15209367287242545213837209 11407025465431908910377907)
            ·
              refine ⟨17110538198147863365566861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11407025465431908910377907 17110538198147863365566861)
              ·
                refine ⟨6416451824305448762087573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17110538198147863365566861 6416451824305448762087573)
                ·
                  refine ⟨300771179264317910722855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6416451824305448762087573 300771179264317910722855)
                  ·
                    rfl

theorem cell21_1317937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_1317937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1317937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1317937 prefixEnd_1317937 := by exact prefixLift 1317937
  have htrace : WordTrace (prefixWord ++ tailWord_1317937) baseStart_1317937 baseEnd_1317937 := by
    simpa [prefixWord, tailWord_1317937, baseEnd_1317937] using wordTrace_append hprefix tailTrace_1317937
  have hstable : (prefixWord ++ tailWord_1317937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317937).length < 2 ^ (prefixWord ++ tailWord_1317937).sum := by decide
  have hdescent : baseEnd_1317937 < baseStart_1317937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318027 : List Nat := [1, 1, 1, 1, 4, 1, 1, 11]
def baseStart_1318027 : Nat := 118140960795 + 1318027 * 2 ^ 59
def prefixEnd_1318027 : Nat := 4983230072969 + 3 ^ 40 * 1318027 * 2
def baseEnd_1318027 : Nat := 100263906163499251407557

theorem tailTrace_1318027 : CollatzResearch.WordTrace tailWord_1318027 prefixEnd_1318027 100263906163499251407557 := by
  unfold tailWord_1318027
  simp only [CollatzResearch.WordTrace]
  refine ⟨48072393996020754935496335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32048262664013836623664223 48072393996020754935496335)
  ·
    refine ⟨72108590994031132403244503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48072393996020754935496335 72108590994031132403244503)
    ·
      refine ⟨108162886491046698604866755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72108590994031132403244503 108162886491046698604866755)
      ·
        refine ⟨162244329736570047907300133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108162886491046698604866755 162244329736570047907300133)
        ·
          refine ⟨30420811825606883982618775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162244329736570047907300133 30420811825606883982618775)
          ·
            refine ⟨45631217738410325973928163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30420811825606883982618775 45631217738410325973928163)
            ·
              refine ⟨68446826607615488960892245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45631217738410325973928163 68446826607615488960892245)
              ·
                refine ⟨100263906163499251407557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 68446826607615488960892245 100263906163499251407557)
                ·
                  rfl

theorem cell21_1318027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 11].length) (baseStart_1318027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318027 prefixEnd_1318027 := by exact prefixLift 1318027
  have htrace : WordTrace (prefixWord ++ tailWord_1318027) baseStart_1318027 baseEnd_1318027 := by
    simpa [prefixWord, tailWord_1318027, baseEnd_1318027] using wordTrace_append hprefix tailTrace_1318027
  have hstable : (prefixWord ++ tailWord_1318027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318027).length < 2 ^ (prefixWord ++ tailWord_1318027).sum := by decide
  have hdescent : baseEnd_1318027 < baseStart_1318027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318044 : List Nat := [2, 2, 3, 2, 1, 3, 8]
def baseStart_1318044 : Nat := 118140960795 + 1318044 * 2 ^ 59
def prefixEnd_1318044 : Nat := 4983230072969 + 3 ^ 40 * 1318044 * 2
def baseEnd_1318044 : Nat := 33421733124678833604367

theorem tailTrace_1318044 : CollatzResearch.WordTrace tailWord_1318044 prefixEnd_1318044 33421733124678833604367 := by
  unfold tailWord_1318044
  simp only [CollatzResearch.WordTrace]
  refine ⟨24036507018479583419432593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32048676024639444559243457 24036507018479583419432593)
  ·
    refine ⟨18027380263859687564574445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24036507018479583419432593 18027380263859687564574445)
    ·
      refine ⟨6760267598947382836715417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18027380263859687564574445 6760267598947382836715417)
      ·
        refine ⟨5070200699210537127536563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6760267598947382836715417 5070200699210537127536563)
        ·
          refine ⟨7605301048815805691304845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5070200699210537127536563 7605301048815805691304845)
          ·
            refine ⟨2851987893305927134239317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7605301048815805691304845 2851987893305927134239317)
            ·
              refine ⟨33421733124678833604367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2851987893305927134239317 33421733124678833604367)
              ·
                rfl

theorem cell21_1318044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 8].length) (baseStart_1318044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318044 prefixEnd_1318044 := by exact prefixLift 1318044
  have htrace : WordTrace (prefixWord ++ tailWord_1318044) baseStart_1318044 baseEnd_1318044 := by
    simpa [prefixWord, tailWord_1318044, baseEnd_1318044] using wordTrace_append hprefix tailTrace_1318044
  have hstable : (prefixWord ++ tailWord_1318044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318044).length < 2 ^ (prefixWord ++ tailWord_1318044).sum := by decide
  have hdescent : baseEnd_1318044 < baseStart_1318044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318078 : List Nat := [4, 2, 1, 1, 3, 3, 2, 5]
def baseStart_1318078 : Nat := 118140960795 + 1318078 * 2 ^ 59
def prefixEnd_1318078 : Nat := 4983230072969 + 3 ^ 40 * 1318078 * 2
def baseEnd_1318078 : Nat := 100267785795110999624189

theorem tailTrace_1318078 : CollatzResearch.WordTrace tailWord_1318078 prefixEnd_1318078 100267785795110999624189 := by
  unfold tailWord_1318078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6009281764854498830700361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32049502745890660430401925 6009281764854498830700361)
  ·
    refine ⟨4506961323640874123025271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6009281764854498830700361 4506961323640874123025271)
    ·
      refine ⟨6760441985461311184537907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4506961323640874123025271 6760441985461311184537907)
      ·
        refine ⟨10140662978191966776806861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760441985461311184537907 10140662978191966776806861)
        ·
          refine ⟨3802748616821987541302573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10140662978191966776806861 3802748616821987541302573)
          ·
            refine ⟨1426030731308245327988465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3802748616821987541302573 1426030731308245327988465)
            ·
              refine ⟨1069523048481183995991349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1426030731308245327988465 1069523048481183995991349)
              ·
                refine ⟨100267785795110999624189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1069523048481183995991349 100267785795110999624189)
                ·
                  rfl

theorem cell21_1318078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_1318078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318078 prefixEnd_1318078 := by exact prefixLift 1318078
  have htrace : WordTrace (prefixWord ++ tailWord_1318078) baseStart_1318078 baseEnd_1318078 := by
    simpa [prefixWord, tailWord_1318078, baseEnd_1318078] using wordTrace_append hprefix tailTrace_1318078
  have hstable : (prefixWord ++ tailWord_1318078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318078).length < 2 ^ (prefixWord ++ tailWord_1318078).sum := by decide
  have hdescent : baseEnd_1318078 < baseStart_1318078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318103 : List Nat := [1, 1, 3, 2, 1, 2, 11]
def baseStart_1318103 : Nat := 118140960795 + 1318103 * 2 ^ 59
def prefixEnd_1318103 : Nat := 4983230072969 + 3 ^ 40 * 1318103 * 2
def baseEnd_1318103 : Nat := 33423229191770945661761

theorem tailTrace_1318103 : CollatzResearch.WordTrace tailWord_1318103 prefixEnd_1318103 33423229191770945661761 := by
  unfold tailWord_1318103
  simp only [CollatzResearch.WordTrace]
  refine ⟨48075165943745419915262963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32050110629163613276841975 48075165943745419915262963)
  ·
    refine ⟨72112748915618129872894445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48075165943745419915262963 72112748915618129872894445)
    ·
      refine ⟨27042280843356798702335417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72112748915618129872894445 27042280843356798702335417)
      ·
        refine ⟨20281710632517599026751563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27042280843356798702335417 20281710632517599026751563)
        ·
          refine ⟨30422565948776398540127345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20281710632517599026751563 30422565948776398540127345)
          ·
            refine ⟨22816924461582298905095509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30422565948776398540127345 22816924461582298905095509)
            ·
              refine ⟨33423229191770945661761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22816924461582298905095509 33423229191770945661761)
              ·
                rfl

theorem cell21_1318103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 11].length) (baseStart_1318103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318103 prefixEnd_1318103 := by exact prefixLift 1318103
  have htrace : WordTrace (prefixWord ++ tailWord_1318103) baseStart_1318103 baseEnd_1318103 := by
    simpa [prefixWord, tailWord_1318103, baseEnd_1318103] using wordTrace_append hprefix tailTrace_1318103
  have hstable : (prefixWord ++ tailWord_1318103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318103).length < 2 ^ (prefixWord ++ tailWord_1318103).sum := by decide
  have hdescent : baseEnd_1318103 < baseStart_1318103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318109 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 5]
def baseStart_1318109 : Nat := 118140960795 + 1318109 * 2 ^ 59
def prefixEnd_1318109 : Nat := 4983230072969 + 3 ^ 40 * 1318109 * 2
def baseEnd_1318109 : Nat := 300810432007683833855837

theorem tailTrace_1318109 : CollatzResearch.WordTrace tailWord_1318109 prefixEnd_1318109 300810432007683833855837 := by
  unfold tailWord_1318109
  simp only [CollatzResearch.WordTrace]
  refine ⟨48075384781723682939981381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32050256521149121959987587 48075384781723682939981381)
  ·
    refine ⟨9014134646573190551246509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48075384781723682939981381 9014134646573190551246509)
    ·
      refine ⟨3380300492464946456717441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9014134646573190551246509 3380300492464946456717441)
      ·
        refine ⟨2535225369348709842538081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3380300492464946456717441 2535225369348709842538081)
        ·
          refine ⟨1901419027011532381903561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2535225369348709842538081 1901419027011532381903561)
          ·
            refine ⟨1426064270258649286427671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1901419027011532381903561 1426064270258649286427671)
            ·
              refine ⟨2139096405387973929641507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426064270258649286427671 2139096405387973929641507)
              ·
                refine ⟨3208644608081960894462261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139096405387973929641507 3208644608081960894462261)
                ·
                  refine ⟨300810432007683833855837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3208644608081960894462261 300810432007683833855837)
                  ·
                    rfl

theorem cell21_1318109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_1318109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318109 prefixEnd_1318109 := by exact prefixLift 1318109
  have htrace : WordTrace (prefixWord ++ tailWord_1318109) baseStart_1318109 baseEnd_1318109 := by
    simpa [prefixWord, tailWord_1318109, baseEnd_1318109] using wordTrace_append hprefix tailTrace_1318109
  have hstable : (prefixWord ++ tailWord_1318109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318109).length < 2 ^ (prefixWord ++ tailWord_1318109).sum := by decide
  have hdescent : baseEnd_1318109 < baseStart_1318109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318120 : List Nat := [2, 1, 4, 1, 2, 1, 4, 6]
def baseStart_1318120 : Nat := 118140960795 + 1318120 * 2 ^ 59
def prefixEnd_1318120 : Nat := 4983230072969 + 3 ^ 40 * 1318120 * 2
def baseEnd_1318120 : Nat := 100270980785850086390827

theorem tailTrace_1318120 : CollatzResearch.WordTrace tailWord_1318120 prefixEnd_1318120 100270980785850086390827 := by
  unfold tailWord_1318120
  simp only [CollatzResearch.WordTrace]
  refine ⟨24037892992341915909315907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32050523989789221212421209 24037892992341915909315907)
  ·
    refine ⟨36056839488512873863973861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24037892992341915909315907 36056839488512873863973861)
    ·
      refine ⟨6760657404096163849495099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36056839488512873863973861 6760657404096163849495099)
      ·
        refine ⟨10140986106144245774242649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760657404096163849495099 10140986106144245774242649)
        ·
          refine ⟨7605739579608184330681987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10140986106144245774242649 7605739579608184330681987)
          ·
            refine ⟨11408609369412276496022981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7605739579608184330681987 11408609369412276496022981)
            ·
              refine ⟨2139114256764801843004309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11408609369412276496022981 2139114256764801843004309)
              ·
                refine ⟨100270980785850086390827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2139114256764801843004309 100270980785850086390827)
                ·
                  rfl

theorem cell21_1318120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_1318120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318120 prefixEnd_1318120 := by exact prefixLift 1318120
  have htrace : WordTrace (prefixWord ++ tailWord_1318120) baseStart_1318120 baseEnd_1318120 := by
    simpa [prefixWord, tailWord_1318120, baseEnd_1318120] using wordTrace_append hprefix tailTrace_1318120
  have hstable : (prefixWord ++ tailWord_1318120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318120).length < 2 ^ (prefixWord ++ tailWord_1318120).sum := by decide
  have hdescent : baseEnd_1318120 < baseStart_1318120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318123 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 4]
def baseStart_1318123 : Nat := 118140960795 + 1318123 * 2 ^ 59
def prefixEnd_1318123 : Nat := 4983230072969 + 3 ^ 40 * 1318123 * 2
def baseEnd_1318123 : Nat := 300813626998422920622475

theorem tailTrace_1318123 : CollatzResearch.WordTrace tailWord_1318123 prefixEnd_1318123 300813626998422920622475 := by
  unfold tailWord_1318123
  simp only [CollatzResearch.WordTrace]
  refine ⟨48075895403672963330991023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32050596935781975553994015 48075895403672963330991023)
  ·
    refine ⟨72113843105509444996486535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48075895403672963330991023 72113843105509444996486535)
    ·
      refine ⟨108170764658264167494729803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72113843105509444996486535 108170764658264167494729803)
      ·
        refine ⟨162256146987396251242094705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108170764658264167494729803 162256146987396251242094705)
        ·
          refine ⟨121692110240547188431571029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162256146987396251242094705 121692110240547188431571029)
          ·
            refine ⟨1426079416881412364432473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 121692110240547188431571029 1426079416881412364432473)
            ·
              refine ⟨1069559562661059273324355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1426079416881412364432473 1069559562661059273324355)
              ·
                refine ⟨1604339343991588909986533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069559562661059273324355 1604339343991588909986533)
                ·
                  refine ⟨300813626998422920622475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604339343991588909986533 300813626998422920622475)
                  ·
                    rfl

theorem cell21_1318123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 4].length) (baseStart_1318123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318123 prefixEnd_1318123 := by exact prefixLift 1318123
  have htrace : WordTrace (prefixWord ++ tailWord_1318123) baseStart_1318123 baseEnd_1318123 := by
    simpa [prefixWord, tailWord_1318123, baseEnd_1318123] using wordTrace_append hprefix tailTrace_1318123
  have hstable : (prefixWord ++ tailWord_1318123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318123).length < 2 ^ (prefixWord ++ tailWord_1318123).sum := by decide
  have hdescent : baseEnd_1318123 < baseStart_1318123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318168 : List Nat := [2, 1, 2, 3, 1, 4, 1, 4, 3]
def baseStart_1318168 : Nat := 118140960795 + 1318168 * 2 ^ 59
def prefixEnd_1318168 : Nat := 4983230072969 + 3 ^ 40 * 1318168 * 2
def baseEnd_1318168 : Nat := 300823896611512842372383

theorem tailTrace_1318168 : CollatzResearch.WordTrace tailWord_1318168 prefixEnd_1318168 300823896611512842372383 := by
  unfold tailWord_1318168
  simp only [CollatzResearch.WordTrace]
  refine ⟨24038768344254968008189579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32051691125673290677586105 24038768344254968008189579)
  ·
    refine ⟨36058152516382452012284369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24038768344254968008189579 36058152516382452012284369)
    ·
      refine ⟨27043614387286839009213277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36058152516382452012284369 27043614387286839009213277)
      ·
        refine ⟨10141355395232564628454979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27043614387286839009213277 10141355395232564628454979)
        ·
          refine ⟨15212033092848846942682469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10141355395232564628454979 15212033092848846942682469)
          ·
            refine ⟨2852256204909158801752963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15212033092848846942682469 2852256204909158801752963)
            ·
              refine ⟨4278384307363738202629445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852256204909158801752963 4278384307363738202629445)
              ·
                refine ⟨802197057630700912993021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4278384307363738202629445 802197057630700912993021)
                ·
                  refine ⟨300823896611512842372383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802197057630700912993021 300823896611512842372383)
                  ·
                    rfl

theorem cell21_1318168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_1318168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318168 prefixEnd_1318168 := by exact prefixLift 1318168
  have htrace : WordTrace (prefixWord ++ tailWord_1318168) baseStart_1318168 baseEnd_1318168 := by
    simpa [prefixWord, tailWord_1318168, baseEnd_1318168] using wordTrace_append hprefix tailTrace_1318168
  have hstable : (prefixWord ++ tailWord_1318168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318168).length < 2 ^ (prefixWord ++ tailWord_1318168).sum := by decide
  have hdescent : baseEnd_1318168 < baseStart_1318168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318227 : List Nat := [1, 1, 1, 2, 1, 1, 5, 6, 3]
def baseStart_1318227 : Nat := 118140960795 + 1318227 * 2 ^ 59
def prefixEnd_1318227 : Nat := 4983230072969 + 3 ^ 40 * 1318227 * 2
def baseEnd_1318227 : Nat := 300837361215341850888929

theorem tailTrace_1318227 : CollatzResearch.WordTrace tailWord_1318227 prefixEnd_1318227 300837361215341850888929 := by
  unfold tailWord_1318227
  simp only [CollatzResearch.WordTrace]
  refine ⟨48079688595296189092776935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32053125730197459395184623 48079688595296189092776935)
  ·
    refine ⟨72119532892944283639165403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48079688595296189092776935 72119532892944283639165403)
    ·
      refine ⟨108179299339416425458748105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72119532892944283639165403 108179299339416425458748105)
      ·
        refine ⟨81134474504562319094061079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108179299339416425458748105 81134474504562319094061079)
        ·
          refine ⟨121701711756843478641091619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81134474504562319094061079 121701711756843478641091619)
          ·
            refine ⟨182552567635265217961637429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121701711756843478641091619 182552567635265217961637429)
            ·
              refine ⟨17114303215806114183903509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 182552567635265217961637429 17114303215806114183903509)
              ·
                refine ⟨802232963240911602370477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17114303215806114183903509 802232963240911602370477)
                ·
                  refine ⟨300837361215341850888929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802232963240911602370477 300837361215341850888929)
                  ·
                    rfl

theorem cell21_1318227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 3].length) (baseStart_1318227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318227 prefixEnd_1318227 := by exact prefixLift 1318227
  have htrace : WordTrace (prefixWord ++ tailWord_1318227) baseStart_1318227 baseEnd_1318227 := by
    simpa [prefixWord, tailWord_1318227, baseEnd_1318227] using wordTrace_append hprefix tailTrace_1318227
  have hstable : (prefixWord ++ tailWord_1318227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318227).length < 2 ^ (prefixWord ++ tailWord_1318227).sum := by decide
  have hdescent : baseEnd_1318227 < baseStart_1318227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318241 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 4]
def baseStart_1318241 : Nat := 118140960795 + 1318241 * 2 ^ 59
def prefixEnd_1318241 : Nat := 4983230072969 + 3 ^ 40 * 1318241 * 2
def baseEnd_1318241 : Nat := 300840556206080937655567

theorem tailTrace_1318241 : CollatzResearch.WordTrace tailWord_1318241 prefixEnd_1318241 300840556206080937655567 := by
  unfold tailWord_1318241
  simp only [CollatzResearch.WordTrace]
  refine ⟨48080199217245469483786577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32053466144830312989191051 48080199217245469483786577)
  ·
    refine ⟨36060149412934102112839933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48080199217245469483786577 36060149412934102112839933)
    ·
      refine ⟨13522556029850288292314975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36060149412934102112839933 13522556029850288292314975)
      ·
        refine ⟨20283834044775432438472463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13522556029850288292314975 20283834044775432438472463)
        ·
          refine ⟨30425751067163148657708695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20283834044775432438472463 30425751067163148657708695)
          ·
            refine ⟨45638626600744722986563043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30425751067163148657708695 45638626600744722986563043)
            ·
              refine ⟨68457939901117084479844565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45638626600744722986563043 68457939901117084479844565)
              ·
                refine ⟨1604482966432431667496357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68457939901117084479844565 1604482966432431667496357)
                ·
                  refine ⟨300840556206080937655567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604482966432431667496357 300840556206080937655567)
                  ·
                    rfl

theorem cell21_1318241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_1318241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318241 prefixEnd_1318241 := by exact prefixLift 1318241
  have htrace : WordTrace (prefixWord ++ tailWord_1318241) baseStart_1318241 baseEnd_1318241 := by
    simpa [prefixWord, tailWord_1318241, baseEnd_1318241] using wordTrace_append hprefix tailTrace_1318241
  have hstable : (prefixWord ++ tailWord_1318241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318241).length < 2 ^ (prefixWord ++ tailWord_1318241).sum := by decide
  have hdescent : baseEnd_1318241 < baseStart_1318241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318255 : List Nat := [1, 1, 2, 1, 3, 1, 5, 7]
def baseStart_1318255 : Nat := 118140960795 + 1318255 * 2 ^ 59
def prefixEnd_1318255 : Nat := 4983230072969 + 3 ^ 40 * 1318255 * 2
def baseEnd_1318255 : Nat := 100281250398940008140735

theorem tailTrace_1318255 : CollatzResearch.WordTrace tailWord_1318255 prefixEnd_1318255 100281250398940008140735 := by
  unfold tailWord_1318255
  simp only [CollatzResearch.WordTrace]
  refine ⟨48080709839194749874796219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32053806559463166583197479 48080709839194749874796219)
  ·
    refine ⟨72121064758792124812194329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48080709839194749874796219 72121064758792124812194329)
    ·
      refine ⟨54090798569094093609145747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72121064758792124812194329 54090798569094093609145747)
      ·
        refine ⟨81136197853641140413718621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54090798569094093609145747 81136197853641140413718621)
        ·
          refine ⟨30426074195115427655144483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81136197853641140413718621 30426074195115427655144483)
          ·
            refine ⟨45639111292673141482716725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30426074195115427655144483 45639111292673141482716725)
            ·
              refine ⟨4278666683688107014004693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45639111292673141482716725 4278666683688107014004693)
              ·
                refine ⟨100281250398940008140735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4278666683688107014004693 100281250398940008140735)
                ·
                  rfl

theorem cell21_1318255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 7].length) (baseStart_1318255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318255 prefixEnd_1318255 := by exact prefixLift 1318255
  have htrace : WordTrace (prefixWord ++ tailWord_1318255) baseStart_1318255 baseEnd_1318255 := by
    simpa [prefixWord, tailWord_1318255, baseEnd_1318255] using wordTrace_append hprefix tailTrace_1318255
  have hstable : (prefixWord ++ tailWord_1318255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318255).length < 2 ^ (prefixWord ++ tailWord_1318255).sum := by decide
  have hdescent : baseEnd_1318255 < baseStart_1318255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318292 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1318292 : Nat := 118140960795 + 1318292 * 2 ^ 59
def prefixEnd_1318292 : Nat := 4983230072969 + 3 ^ 40 * 1318292 * 2
def baseEnd_1318292 : Nat := 300852195100916182305463

theorem tailTrace_1318292 : CollatzResearch.WordTrace tailWord_1318292 prefixEnd_1318292 300852195100916182305463 := by
  unfold tailWord_1318292
  simp only [CollatzResearch.WordTrace]
  refine ⟨24041029670030352596946565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32054706226707136795928753 24041029670030352596946565)
  ·
    refine ⟨4507693063130691111927481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24041029670030352596946565 4507693063130691111927481)
    ·
      refine ⟨3380769797348018333945611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4507693063130691111927481 3380769797348018333945611)
      ·
        refine ⟨5071154696022027500918417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380769797348018333945611 5071154696022027500918417)
        ·
          refine ⟨3803366022016520625688813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5071154696022027500918417 3803366022016520625688813)
          ·
            refine ⟨1426262258256195234633305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3803366022016520625688813 1426262258256195234633305)
            ·
              refine ⟨1069696693692146425974979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1426262258256195234633305 1069696693692146425974979)
              ·
                refine ⟨1604545040538219638962469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069696693692146425974979 1604545040538219638962469)
                ·
                  refine ⟨300852195100916182305463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604545040538219638962469 300852195100916182305463)
                  ·
                    rfl

theorem cell21_1318292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1318292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318292 prefixEnd_1318292 := by exact prefixLift 1318292
  have htrace : WordTrace (prefixWord ++ tailWord_1318292) baseStart_1318292 baseEnd_1318292 := by
    simpa [prefixWord, tailWord_1318292, baseEnd_1318292] using wordTrace_append hprefix tailTrace_1318292
  have hstable : (prefixWord ++ tailWord_1318292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318292).length < 2 ^ (prefixWord ++ tailWord_1318292).sum := by decide
  have hdescent : baseEnd_1318292 < baseStart_1318292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318348 : List Nat := [2, 2, 1, 4, 2, 1, 3, 6]
def baseStart_1318348 : Nat := 118140960795 + 1318348 * 2 ^ 59
def prefixEnd_1318348 : Nat := 4983230072969 + 3 ^ 40 * 1318348 * 2
def baseEnd_1318348 : Nat := 100288325021290843124005

theorem tailTrace_1318348 : CollatzResearch.WordTrace tailWord_1318348 prefixEnd_1318348 100288325021290843124005 := by
  unfold tailWord_1318348
  simp only [CollatzResearch.WordTrace]
  refine ⟨24042050913928913378965849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32056067885238551171954465 24042050913928913378965849)
  ·
    refine ⟨18031538185446685034224387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24042050913928913378965849 18031538185446685034224387)
    ·
      refine ⟨27047307278170027551336581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18031538185446685034224387 27047307278170027551336581)
      ·
        refine ⟨5071370114656880165875609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27047307278170027551336581 5071370114656880165875609)
        ·
          refine ⟨3803527585992660124406707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5071370114656880165875609 3803527585992660124406707)
          ·
            refine ⟨5705291378988990186610061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3803527585992660124406707 5705291378988990186610061)
            ·
              refine ⟨2139484267120871319978773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5705291378988990186610061 2139484267120871319978773)
              ·
                refine ⟨100288325021290843124005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2139484267120871319978773 100288325021290843124005)
                ·
                  rfl

theorem cell21_1318348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_1318348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318348 prefixEnd_1318348 := by exact prefixLift 1318348
  have htrace : WordTrace (prefixWord ++ tailWord_1318348) baseStart_1318348 baseEnd_1318348 := by
    simpa [prefixWord, tailWord_1318348, baseEnd_1318348] using wordTrace_append hprefix tailTrace_1318348
  have hstable : (prefixWord ++ tailWord_1318348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318348).length < 2 ^ (prefixWord ++ tailWord_1318348).sum := by decide
  have hdescent : baseEnd_1318348 < baseStart_1318348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318362 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_1318362 : Nat := 118140960795 + 1318362 * 2 ^ 59
def prefixEnd_1318362 : Nat := 4983230072969 + 3 ^ 40 * 1318362 * 2
def baseEnd_1318362 : Nat := 300868170054611616138653

theorem tailTrace_1318362 : CollatzResearch.WordTrace tailWord_1318362 prefixEnd_1318362 300868170054611616138653 := by
  unfold tailWord_1318362
  simp only [CollatzResearch.WordTrace]
  refine ⟨12021153112451776787235335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32056408299871404765960893 12021153112451776787235335)
  ·
    refine ⟨18031729668677665180853003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12021153112451776787235335 18031729668677665180853003)
    ·
      refine ⟨27047594503016497771279505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18031729668677665180853003 27047594503016497771279505)
      ·
        refine ⟨20285695877262373328459629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27047594503016497771279505 20285695877262373328459629)
        ·
          refine ⟨7607135953973389998172361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20285695877262373328459629 7607135953973389998172361)
          ·
            refine ⟨5705351965480042498629271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7607135953973389998172361 5705351965480042498629271)
            ·
              refine ⟨8558027948220063747943907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5705351965480042498629271 8558027948220063747943907)
              ·
                refine ⟨12837041922330095621915861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8558027948220063747943907 12837041922330095621915861)
                ·
                  refine ⟨300868170054611616138653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12837041922330095621915861 300868170054611616138653)
                  ·
                    rfl

theorem cell21_1318362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_1318362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318362 prefixEnd_1318362 := by exact prefixLift 1318362
  have htrace : WordTrace (prefixWord ++ tailWord_1318362) baseStart_1318362 baseEnd_1318362 := by
    simpa [prefixWord, tailWord_1318362, baseEnd_1318362] using wordTrace_append hprefix tailTrace_1318362
  have hstable : (prefixWord ++ tailWord_1318362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318362).length < 2 ^ (prefixWord ++ tailWord_1318362).sum := by decide
  have hdescent : baseEnd_1318362 < baseStart_1318362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318365 : List Nat := [1, 4, 3, 1, 1, 3, 3, 5]
def baseStart_1318365 : Nat := 118140960795 + 1318365 * 2 ^ 59
def prefixEnd_1318365 : Nat := 4983230072969 + 3 ^ 40 * 1318365 * 2
def baseEnd_1318365 : Nat := 100289618231828092529549

theorem tailTrace_1318365 : CollatzResearch.WordTrace tailWord_1318365 prefixEnd_1318365 100289618231828092529549 := by
  unfold tailWord_1318365
  simp only [CollatzResearch.WordTrace]
  refine ⟨48084721868796238661300549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32056481245864159107533699 48084721868796238661300549)
  ·
    refine ⟨9015885350399294748993853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48084721868796238661300549 9015885350399294748993853)
    ·
      refine ⟨3380957006399735530872695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9015885350399294748993853 3380957006399735530872695)
      ·
        refine ⟨5071435509599603296309043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380957006399735530872695 5071435509599603296309043)
        ·
          refine ⟨7607153264399404944463565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5071435509599603296309043 7607153264399404944463565)
          ·
            refine ⟨2852682474149776854173837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7607153264399404944463565 2852682474149776854173837)
            ·
              refine ⟨1069755927806166320315189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2852682474149776854173837 1069755927806166320315189)
              ·
                refine ⟨100289618231828092529549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1069755927806166320315189 100289618231828092529549)
                ·
                  rfl

theorem cell21_1318365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 5].length) (baseStart_1318365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318365 prefixEnd_1318365 := by exact prefixLift 1318365
  have htrace : WordTrace (prefixWord ++ tailWord_1318365) baseStart_1318365 baseEnd_1318365 := by
    simpa [prefixWord, tailWord_1318365, baseEnd_1318365] using wordTrace_append hprefix tailTrace_1318365
  have hstable : (prefixWord ++ tailWord_1318365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318365).length < 2 ^ (prefixWord ++ tailWord_1318365).sum := by decide
  have hdescent : baseEnd_1318365 < baseStart_1318365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318424 : List Nat := [2, 1, 2, 3, 4, 1, 1, 7]
def baseStart_1318424 : Nat := 118140960795 + 1318424 * 2 ^ 59
def prefixEnd_1318424 : Nat := 4983230072969 + 3 ^ 40 * 1318424 * 2
def baseEnd_1318424 : Nat := 100294106433104428701731

theorem tailTrace_1318424 : CollatzResearch.WordTrace tailWord_1318424 prefixEnd_1318424 100294106433104428701731 := by
  unfold tailWord_1318424
  simp only [CollatzResearch.WordTrace]
  refine ⟨24043436887791245868849163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32057915850388327825132217 24043436887791245868849163)
  ·
    refine ⟨36065155331686868803273745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24043436887791245868849163 36065155331686868803273745)
    ·
      refine ⟨27048866498765151602455309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36065155331686868803273745 27048866498765151602455309)
      ·
        refine ⟨10143324937036931850920741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27048866498765151602455309 10143324937036931850920741)
        ·
          refine ⟨1901873425694424722047639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10143324937036931850920741 1901873425694424722047639)
          ·
            refine ⟨2852810138541637083071459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901873425694424722047639 2852810138541637083071459)
            ·
              refine ⟨4279215207812455624607189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852810138541637083071459 4279215207812455624607189)
              ·
                refine ⟨100294106433104428701731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4279215207812455624607189 100294106433104428701731)
                ·
                  rfl

theorem cell21_1318424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_1318424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318424 prefixEnd_1318424 := by exact prefixLift 1318424
  have htrace : WordTrace (prefixWord ++ tailWord_1318424) baseStart_1318424 baseEnd_1318424 := by
    simpa [prefixWord, tailWord_1318424, baseEnd_1318424] using wordTrace_append hprefix tailTrace_1318424
  have hstable : (prefixWord ++ tailWord_1318424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318424).length < 2 ^ (prefixWord ++ tailWord_1318424).sum := by decide
  have hdescent : baseEnd_1318424 < baseStart_1318424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318455 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 5]
def baseStart_1318455 : Nat := 118140960795 + 1318455 * 2 ^ 59
def prefixEnd_1318455 : Nat := 4983230072969 + 3 ^ 40 * 1318455 * 2
def baseEnd_1318455 : Nat := 300889393921664121088463

theorem tailTrace_1318455 : CollatzResearch.WordTrace tailWord_1318455 prefixEnd_1318455 300889393921664121088463 := by
  unfold tailWord_1318455
  simp only [CollatzResearch.WordTrace]
  refine ⟨48088004438470184032076819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32058669625646789354717879 48088004438470184032076819)
  ·
    refine ⟨72132006657705276048115229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48088004438470184032076819 72132006657705276048115229)
    ·
      refine ⟨27049502496639478518043211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72132006657705276048115229 27049502496639478518043211)
      ·
        refine ⟨40574253744959217777064817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27049502496639478518043211 40574253744959217777064817)
        ·
          refine ⟨30430690308719413332798613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40574253744959217777064817 30430690308719413332798613)
          ·
            refine ⟨1426438608221222499974935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30430690308719413332798613 1426438608221222499974935)
            ·
              refine ⟨2139657912331833749962403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426438608221222499974935 2139657912331833749962403)
              ·
                refine ⟨3209486868497750624943605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139657912331833749962403 3209486868497750624943605)
                ·
                  refine ⟨300889393921664121088463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3209486868497750624943605 300889393921664121088463)
                  ·
                    rfl

theorem cell21_1318455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 5].length) (baseStart_1318455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318455 prefixEnd_1318455 := by exact prefixLift 1318455
  have htrace : WordTrace (prefixWord ++ tailWord_1318455) baseStart_1318455 baseEnd_1318455 := by
    simpa [prefixWord, tailWord_1318455, baseEnd_1318455] using wordTrace_append hprefix tailTrace_1318455
  have hstable : (prefixWord ++ tailWord_1318455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318455).length < 2 ^ (prefixWord ++ tailWord_1318455).sum := by decide
  have hdescent : baseEnd_1318455 < baseStart_1318455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318469 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 4]
def baseStart_1318469 : Nat := 118140960795 + 1318469 * 2 ^ 59
def prefixEnd_1318469 : Nat := 4983230072969 + 3 ^ 40 * 1318469 * 2
def baseEnd_1318469 : Nat := 300892588912403207855101

theorem tailTrace_1318469 : CollatzResearch.WordTrace tailWord_1318469 prefixEnd_1318469 300892588912403207855101 := by
  unfold tailWord_1318469
  simp only [CollatzResearch.WordTrace]
  refine ⟨48088515060419464423086461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32059010040279642948724307 48088515060419464423086461)
  ·
    refine ⟨18033193147657299158657423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48088515060419464423086461 18033193147657299158657423)
    ·
      refine ⟨27049789721485948737986135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18033193147657299158657423 27049789721485948737986135)
      ·
        refine ⟨40574684582228923106979203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27049789721485948737986135 40574684582228923106979203)
        ·
          refine ⟨60862026873343384660468805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40574684582228923106979203 60862026873343384660468805)
          ·
            refine ⟨11411630038751884623837901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60862026873343384660468805 11411630038751884623837901)
            ·
              refine ⟨4279361264531956733939213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11411630038751884623837901 4279361264531956733939213)
              ·
                refine ⟨1604760474199483775227205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4279361264531956733939213 1604760474199483775227205)
                ·
                  refine ⟨300892588912403207855101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604760474199483775227205 300892588912403207855101)
                  ·
                    rfl

theorem cell21_1318469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_1318469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318469 prefixEnd_1318469 := by exact prefixLift 1318469
  have htrace : WordTrace (prefixWord ++ tailWord_1318469) baseStart_1318469 baseEnd_1318469 := by
    simpa [prefixWord, tailWord_1318469, baseEnd_1318469] using wordTrace_append hprefix tailTrace_1318469
  have hstable : (prefixWord ++ tailWord_1318469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318469).length < 2 ^ (prefixWord ++ tailWord_1318469).sum := by decide
  have hdescent : baseEnd_1318469 < baseStart_1318469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318517 : List Nat := [1, 3, 4, 2, 1, 3, 1, 6]
def baseStart_1318517 : Nat := 118140960795 + 1318517 * 2 ^ 59
def prefixEnd_1318517 : Nat := 4983230072969 + 3 ^ 40 * 1318517 * 2
def baseEnd_1318517 : Nat := 100301181055455263685001

theorem tailTrace_1318517 : CollatzResearch.WordTrace tailWord_1318517 prefixEnd_1318517 100301181055455263685001 := by
  unfold tailWord_1318517
  simp only [CollatzResearch.WordTrace]
  refine ⟨48090265764245568620833805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32060177176163712413889203 48090265764245568620833805)
  ·
    refine ⟨18033849661592088232812677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48090265764245568620833805 18033849661592088232812677)
    ·
      refine ⟨3381346811548516543652377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18033849661592088232812677 3381346811548516543652377)
      ·
        refine ⟨2536010108661387407739283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3381346811548516543652377 2536010108661387407739283)
        ·
          refine ⟨3804015162992081111608925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2536010108661387407739283 3804015162992081111608925)
          ·
            refine ⟨1426505686122030416853347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3804015162992081111608925 1426505686122030416853347)
            ·
              refine ⟨2139758529183045625280021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426505686122030416853347 2139758529183045625280021)
              ·
                refine ⟨100301181055455263685001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2139758529183045625280021 100301181055455263685001)
                ·
                  rfl

theorem cell21_1318517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 6].length) (baseStart_1318517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318517 prefixEnd_1318517 := by exact prefixLift 1318517
  have htrace : WordTrace (prefixWord ++ tailWord_1318517) baseStart_1318517 baseEnd_1318517 := by
    simpa [prefixWord, tailWord_1318517, baseEnd_1318517] using wordTrace_append hprefix tailTrace_1318517
  have hstable : (prefixWord ++ tailWord_1318517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318517).length < 2 ^ (prefixWord ++ tailWord_1318517).sum := by decide
  have hdescent : baseEnd_1318517 < baseStart_1318517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318680 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_1318680 : Nat := 118140960795 + 1318680 * 2 ^ 59
def prefixEnd_1318680 : Nat := 4983230072969 + 3 ^ 40 * 1318680 * 2
def baseEnd_1318680 : Nat := 300940741987113729838003

theorem tailTrace_1318680 : CollatzResearch.WordTrace tailWord_1318680 prefixEnd_1318680 300940741987113729838003 := by
  unfold tailWord_1318680
  simp only [CollatzResearch.WordTrace]
  refine ⟨24048105431327523729508747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32064140575103364972678329 24048105431327523729508747)
  ·
    refine ⟨36072158146991285594263121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24048105431327523729508747 36072158146991285594263121)
    ·
      refine ⟨27054118610243464195697341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36072158146991285594263121 27054118610243464195697341)
      ·
        refine ⟨10145294478841299073386503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27054118610243464195697341 10145294478841299073386503)
        ·
          refine ⟨15217941718261948610079755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10145294478841299073386503 15217941718261948610079755)
          ·
            refine ⟨22826912577392922915119633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15217941718261948610079755 22826912577392922915119633)
            ·
              refine ⟨17120184433044692186339725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22826912577392922915119633 17120184433044692186339725)
              ·
                refine ⟨6420069162391759569877397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17120184433044692186339725 6420069162391759569877397)
                ·
                  refine ⟨300940741987113729838003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6420069162391759569877397 300940741987113729838003)
                  ·
                    rfl

theorem cell21_1318680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_1318680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318680 prefixEnd_1318680 := by exact prefixLift 1318680
  have htrace : WordTrace (prefixWord ++ tailWord_1318680) baseStart_1318680 baseEnd_1318680 := by
    simpa [prefixWord, tailWord_1318680, baseEnd_1318680] using wordTrace_append hprefix tailTrace_1318680
  have hstable : (prefixWord ++ tailWord_1318680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318680).length < 2 ^ (prefixWord ++ tailWord_1318680).sum := by decide
  have hdescent : baseEnd_1318680 < baseStart_1318680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318725 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 7]
def baseStart_1318725 : Nat := 118140960795 + 1318725 * 2 ^ 59
def prefixEnd_1318725 : Nat := 4983230072969 + 3 ^ 40 * 1318725 * 2
def baseEnd_1318725 : Nat := 300951011600203651587911

theorem tailTrace_1318725 : CollatzResearch.WordTrace tailWord_1318725 prefixEnd_1318725 300951011600203651587911 := by
  unfold tailWord_1318725
  simp only [CollatzResearch.WordTrace]
  refine ⟨48097852147492020144405629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32065234764994680096270419 48097852147492020144405629)
  ·
    refine ⟨18036694555309507554152111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48097852147492020144405629 18036694555309507554152111)
    ·
      refine ⟨27055041832964261331228167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18036694555309507554152111 27055041832964261331228167)
      ·
        refine ⟨40582562749446391996842251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27055041832964261331228167 40582562749446391996842251)
        ·
          refine ⟨60873844124169587995263377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40582562749446391996842251 60873844124169587995263377)
          ·
            refine ⟨45655383093127190996447533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60873844124169587995263377 45655383093127190996447533)
            ·
              refine ⟨17120768659922696623667825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45655383093127190996447533 17120768659922696623667825)
              ·
                refine ⟨12840576494942022467750869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17120768659922696623667825 12840576494942022467750869)
                ·
                  refine ⟨300951011600203651587911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12840576494942022467750869 300951011600203651587911)
                  ·
                    rfl

theorem cell21_1318725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_1318725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318725 prefixEnd_1318725 := by exact prefixLift 1318725
  have htrace : WordTrace (prefixWord ++ tailWord_1318725) baseStart_1318725 baseEnd_1318725 := by
    simpa [prefixWord, tailWord_1318725, baseEnd_1318725] using wordTrace_append hprefix tailTrace_1318725
  have hstable : (prefixWord ++ tailWord_1318725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318725).length < 2 ^ (prefixWord ++ tailWord_1318725).sum := by decide
  have hdescent : baseEnd_1318725 < baseStart_1318725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318762 : List Nat := [3, 1, 3, 4, 1, 2, 2, 5]
def baseStart_1318762 : Nat := 118140960795 + 1318762 * 2 ^ 59
def prefixEnd_1318762 : Nat := 4983230072969 + 3 ^ 40 * 1318762 * 2
def baseEnd_1318762 : Nat := 100319818501433269823723

theorem tailTrace_1318762 : CollatzResearch.WordTrace tailWord_1318762 prefixEnd_1318762 100319818501433269823723 := by
  unfold tailWord_1318762
  simp only [CollatzResearch.WordTrace]
  refine ⟨12024800412089493865875635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32066134432238650309001693 12024800412089493865875635)
  ·
    refine ⟨18037200618134240798813453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12024800412089493865875635 18037200618134240798813453)
    ·
      refine ⟨6763950231800340299555045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18037200618134240798813453 6763950231800340299555045)
      ·
        refine ⟨1268240668462563806166571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6763950231800340299555045 1268240668462563806166571)
        ·
          refine ⟨1902361002693845709249857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268240668462563806166571 1902361002693845709249857)
          ·
            refine ⟨1426770752020384281937393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1902361002693845709249857 1426770752020384281937393)
            ·
              refine ⟨1070078064015288211453045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1426770752020384281937393 1070078064015288211453045)
              ·
                refine ⟨100319818501433269823723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1070078064015288211453045 100319818501433269823723)
                ·
                  rfl

theorem cell21_1318762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_1318762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318762 prefixEnd_1318762 := by exact prefixLift 1318762
  have htrace : WordTrace (prefixWord ++ tailWord_1318762) baseStart_1318762 baseEnd_1318762 := by
    simpa [prefixWord, tailWord_1318762, baseEnd_1318762] using wordTrace_append hprefix tailTrace_1318762
  have hstable : (prefixWord ++ tailWord_1318762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318762).length < 2 ^ (prefixWord ++ tailWord_1318762).sum := by decide
  have hdescent : baseEnd_1318762 < baseStart_1318762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318787 : List Nat := [1, 1, 1, 3, 4, 4, 7]
def baseStart_1318787 : Nat := 118140960795 + 1318787 * 2 ^ 59
def prefixEnd_1318787 : Nat := 4983230072969 + 3 ^ 40 * 1318787 * 2
def baseEnd_1318787 : Nat := 33440573427211702394939

theorem tailTrace_1318787 : CollatzResearch.WordTrace tailWord_1318787 prefixEnd_1318787 33440573427211702394939 := by
  unfold tailWord_1318787
  simp only [CollatzResearch.WordTrace]
  refine ⟨48100113473267404733162615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32066742315511603155441743 48100113473267404733162615)
  ·
    refine ⟨72150170209901107099743923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48100113473267404733162615 72150170209901107099743923)
    ·
      refine ⟨108225255314851660649615885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72150170209901107099743923 108225255314851660649615885)
      ·
        refine ⟨40584470743069372743605957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108225255314851660649615885 40584470743069372743605957)
        ·
          refine ⟨7609588264325507389426117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40584470743069372743605957 7609588264325507389426117)
          ·
            refine ⟨1426797799561032635517397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7609588264325507389426117 1426797799561032635517397)
            ·
              refine ⟨33440573427211702394939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1426797799561032635517397 33440573427211702394939)
              ·
                rfl

theorem cell21_1318787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 7].length) (baseStart_1318787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318787 prefixEnd_1318787 := by exact prefixLift 1318787
  have htrace : WordTrace (prefixWord ++ tailWord_1318787) baseStart_1318787 baseEnd_1318787 := by
    simpa [prefixWord, tailWord_1318787, baseEnd_1318787] using wordTrace_append hprefix tailTrace_1318787
  have hstable : (prefixWord ++ tailWord_1318787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318787).length < 2 ^ (prefixWord ++ tailWord_1318787).sum := by decide
  have hdescent : baseEnd_1318787 < baseStart_1318787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318804 : List Nat := [2, 4, 2, 1, 1, 3, 2, 6]
def baseStart_1318804 : Nat := 118140960795 + 1318804 * 2 ^ 59
def prefixEnd_1318804 : Nat := 4983230072969 + 3 ^ 40 * 1318804 * 2
def baseEnd_1318804 : Nat := 100323013492172356590361

theorem tailTrace_1318804 : CollatzResearch.WordTrace tailWord_1318804 prefixEnd_1318804 100323013492172356590361 := by
  unfold tailWord_1318804
  simp only [CollatzResearch.WordTrace]
  refine ⟨24050366757102908318265733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32067155676137211091020977 24050366757102908318265733)
  ·
    refine ⟨4509443766956795309674825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24050366757102908318265733 4509443766956795309674825)
    ·
      refine ⟨3382082825217596482256119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4509443766956795309674825 3382082825217596482256119)
      ·
        refine ⟨5073124237826394723384179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3382082825217596482256119 5073124237826394723384179)
        ·
          refine ⟨7609686356739592085076269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5073124237826394723384179 7609686356739592085076269)
          ·
            refine ⟨2853632383777347031903601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7609686356739592085076269 2853632383777347031903601)
            ·
              refine ⟨2140224287833010273927701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2853632383777347031903601 2140224287833010273927701)
              ·
                refine ⟨100323013492172356590361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2140224287833010273927701 100323013492172356590361)
                ·
                  rfl

theorem cell21_1318804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_1318804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318804 prefixEnd_1318804 := by exact prefixLift 1318804
  have htrace : WordTrace (prefixWord ++ tailWord_1318804) baseStart_1318804 baseEnd_1318804 := by
    simpa [prefixWord, tailWord_1318804, baseEnd_1318804] using wordTrace_append hprefix tailTrace_1318804
  have hstable : (prefixWord ++ tailWord_1318804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318804).length < 2 ^ (prefixWord ++ tailWord_1318804).sum := by decide
  have hdescent : baseEnd_1318804 < baseStart_1318804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318908 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_1318908 : Nat := 118140960795 + 1318908 * 2 ^ 59
def prefixEnd_1318908 : Nat := 4983230072969 + 3 ^ 40 * 1318908 * 2
def baseEnd_1318908 : Nat := 300992774693436000037537

theorem tailTrace_1318908 : CollatzResearch.WordTrace tailWord_1318908 prefixEnd_1318908 300992774693436000037537 := by
  unfold tailWord_1318908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24052263352914521199158689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32069684470552694932211585 24052263352914521199158689)
  ·
    refine ⟨18039197514685890899369017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24052263352914521199158689 18039197514685890899369017)
    ·
      refine ⟨13529398136014418174526763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18039197514685890899369017 13529398136014418174526763)
      ·
        refine ⟨20294097204021627261790145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13529398136014418174526763 20294097204021627261790145)
        ·
          refine ⟨15220572903016220446342609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20294097204021627261790145 15220572903016220446342609)
          ·
            refine ⟨11415429677262165334756957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15220572903016220446342609 11415429677262165334756957)
            ·
              refine ⟨4280786128973312000533859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11415429677262165334756957 4280786128973312000533859)
              ·
                refine ⟨6421179193459968000800789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4280786128973312000533859 6421179193459968000800789)
                ·
                  refine ⟨300992774693436000037537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6421179193459968000800789 300992774693436000037537)
                  ·
                    rfl

theorem cell21_1318908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_1318908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318908 prefixEnd_1318908 := by exact prefixLift 1318908
  have htrace : WordTrace (prefixWord ++ tailWord_1318908) baseStart_1318908 baseEnd_1318908 := by
    simpa [prefixWord, tailWord_1318908, baseEnd_1318908] using wordTrace_append hprefix tailTrace_1318908
  have hstable : (prefixWord ++ tailWord_1318908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318908).length < 2 ^ (prefixWord ++ tailWord_1318908).sum := by decide
  have hdescent : baseEnd_1318908 < baseStart_1318908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318945 : List Nat := [1, 2, 3, 2, 5, 1, 1, 3, 3]
def baseStart_1318945 : Nat := 118140960795 + 1318945 * 2 ^ 59
def prefixEnd_1318945 : Nat := 4983230072969 + 3 ^ 40 * 1318945 * 2
def baseEnd_1318945 : Nat := 301001218597532157920795

theorem tailTrace_1318945 : CollatzResearch.WordTrace tailWord_1318945 prefixEnd_1318945 301001218597532157920795 := by
  unfold tailWord_1318945
  simp only [CollatzResearch.WordTrace]
  refine ⟨48105876206694997717414289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32070584137796665144942859 48105876206694997717414289)
  ·
    refine ⟨36079407155021248288060717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48105876206694997717414289 36079407155021248288060717)
    ·
      refine ⟨13529777683132968108022769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36079407155021248288060717 13529777683132968108022769)
      ·
        refine ⟨10147333262349726081017077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13529777683132968108022769 10147333262349726081017077)
        ·
          refine ⟨951312493345286820095351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10147333262349726081017077 951312493345286820095351)
          ·
            refine ⟨1426968740017930230143027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951312493345286820095351 1426968740017930230143027)
            ·
              refine ⟨2140453110026895345214541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426968740017930230143027 2140453110026895345214541)
              ·
                refine ⟨802669916260085754455453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2140453110026895345214541 802669916260085754455453)
                ·
                  refine ⟨301001218597532157920795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802669916260085754455453 301001218597532157920795)
                  ·
                    rfl

theorem cell21_1318945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_1318945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1318945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1318945 prefixEnd_1318945 := by exact prefixLift 1318945
  have htrace : WordTrace (prefixWord ++ tailWord_1318945) baseStart_1318945 baseEnd_1318945 := by
    simpa [prefixWord, tailWord_1318945, baseEnd_1318945] using wordTrace_append hprefix tailTrace_1318945
  have hstable : (prefixWord ++ tailWord_1318945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318945).length < 2 ^ (prefixWord ++ tailWord_1318945).sum := by decide
  have hdescent : baseEnd_1318945 < baseStart_1318945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319018 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_1319018 : Nat := 118140960795 + 1319018 * 2 ^ 59
def prefixEnd_1319018 : Nat := 4983230072969 + 3 ^ 40 * 1319018 * 2
def baseEnd_1319018 : Nat := 301017878192100253203979

theorem tailTrace_1319018 : CollatzResearch.WordTrace tailWord_1319018 prefixEnd_1319018 301017878192100253203979 := by
  unfold tailWord_1319018
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027134683857632796205427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32072359156953687456547805 12027134683857632796205427)
  ·
    refine ⟨18040702025786449194308141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12027134683857632796205427 18040702025786449194308141)
    ·
      refine ⟨6765263259669918447865553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18040702025786449194308141 6765263259669918447865553)
      ·
        refine ⟨5073947444752438835899165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6765263259669918447865553 5073947444752438835899165)
        ·
          refine ⟨1902730291782164563462187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5073947444752438835899165 1902730291782164563462187)
          ·
            refine ⟨2854095437673246845193281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902730291782164563462187 2854095437673246845193281)
            ·
              refine ⟨2140571578254935133894961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2854095437673246845193281 2140571578254935133894961)
              ·
                refine ⟨1605428683691201350421221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140571578254935133894961 1605428683691201350421221)
                ·
                  refine ⟨301017878192100253203979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605428683691201350421221 301017878192100253203979)
                  ·
                    rfl

theorem cell21_1319018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_1319018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319018 prefixEnd_1319018 := by exact prefixLift 1319018
  have htrace : WordTrace (prefixWord ++ tailWord_1319018) baseStart_1319018 baseEnd_1319018 := by
    simpa [prefixWord, tailWord_1319018, baseEnd_1319018] using wordTrace_append hprefix tailTrace_1319018
  have hstable : (prefixWord ++ tailWord_1319018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319018).length < 2 ^ (prefixWord ++ tailWord_1319018).sum := by decide
  have hdescent : baseEnd_1319018 < baseStart_1319018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319108 : List Nat := [2, 3, 3, 1, 2, 1, 4, 5]
def baseStart_1319108 : Nat := 118140960795 + 1319108 * 2 ^ 59
def prefixEnd_1319108 : Nat := 4983230072969 + 3 ^ 40 * 1319108 * 2
def baseEnd_1319108 : Nat := 100346139139426698901265

theorem tailTrace_1319108 : CollatzResearch.WordTrace tailWord_1319108 prefixEnd_1319108 100346139139426698901265 := by
  unfold tailWord_1319108
  simp only [CollatzResearch.WordTrace]
  refine ⟨24055910652552238277798989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32074547536736317703731985 24055910652552238277798989)
  ·
    refine ⟨9020966494707089354174621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24055910652552238277798989 9020966494707089354174621)
    ·
      refine ⟨3382862435515158507815483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9020966494707089354174621 3382862435515158507815483)
      ·
        refine ⟨5074293653272737761723225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3382862435515158507815483 5074293653272737761723225)
        ·
          refine ⟨3805720239954553321292419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5074293653272737761723225 3805720239954553321292419)
          ·
            refine ⟨5708580359931829981938629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3805720239954553321292419 5708580359931829981938629)
            ·
              refine ⟨1070358817487218121613493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5708580359931829981938629 1070358817487218121613493)
              ·
                refine ⟨100346139139426698901265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1070358817487218121613493 100346139139426698901265)
                ·
                  rfl

theorem cell21_1319108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_1319108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319108 prefixEnd_1319108 := by exact prefixLift 1319108
  have htrace : WordTrace (prefixWord ++ tailWord_1319108) baseStart_1319108 baseEnd_1319108 := by
    simpa [prefixWord, tailWord_1319108, baseEnd_1319108] using wordTrace_append hprefix tailTrace_1319108
  have hstable : (prefixWord ++ tailWord_1319108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319108).length < 2 ^ (prefixWord ++ tailWord_1319108).sum := by decide
  have hdescent : baseEnd_1319108 < baseStart_1319108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319119 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 8]
def baseStart_1319119 : Nat := 118140960795 + 1319119 * 2 ^ 59
def prefixEnd_1319119 : Nat := 4983230072969 + 3 ^ 40 * 1319119 * 2
def baseEnd_1319119 : Nat := 301040927768146522020439

theorem tailTrace_1319119 : CollatzResearch.WordTrace tailWord_1319119 prefixEnd_1319119 301040927768146522020439 := by
  unfold tailWord_1319119
  simp only [CollatzResearch.WordTrace]
  refine ⟨48112222508064625434248411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32074815005376416956165607 48112222508064625434248411)
  ·
    refine ⟨72168333762096938151372617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48112222508064625434248411 72168333762096938151372617)
    ·
      refine ⟨54126250321572703613529463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72168333762096938151372617 54126250321572703613529463)
      ·
        refine ⟨81189375482359055420294195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54126250321572703613529463 81189375482359055420294195)
        ·
          refine ⟨121784063223538583130441293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81189375482359055420294195 121784063223538583130441293)
          ·
            refine ⟨45669023708826968673915485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121784063223538583130441293 45669023708826968673915485)
            ·
              refine ⟨17125883890810113252718307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45669023708826968673915485 17125883890810113252718307)
              ·
                refine ⟨25688825836215169879077461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17125883890810113252718307 25688825836215169879077461)
                ·
                  refine ⟨301040927768146522020439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25688825836215169879077461 301040927768146522020439)
                  ·
                    rfl

theorem cell21_1319119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_1319119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319119 prefixEnd_1319119 := by exact prefixLift 1319119
  have htrace : WordTrace (prefixWord ++ tailWord_1319119) baseStart_1319119 baseEnd_1319119 := by
    simpa [prefixWord, tailWord_1319119, baseEnd_1319119] using wordTrace_append hprefix tailTrace_1319119
  have hstable : (prefixWord ++ tailWord_1319119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319119).length < 2 ^ (prefixWord ++ tailWord_1319119).sum := by decide
  have hdescent : baseEnd_1319119 < baseStart_1319119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319136 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_1319136 : Nat := 118140960795 + 1319136 * 2 ^ 59
def prefixEnd_1319136 : Nat := 4983230072969 + 3 ^ 40 * 1319136 * 2
def baseEnd_1319136 : Nat := 301044807399758270237071

theorem tailTrace_1319136 : CollatzResearch.WordTrace tailWord_1319136 prefixEnd_1319136 301044807399758270237071 := by
  unfold tailWord_1319136
  simp only [CollatzResearch.WordTrace]
  refine ⟨24056421274501518668808631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32075228366002024891744841 24056421274501518668808631)
  ·
    refine ⟨36084631911752278003212947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24056421274501518668808631 36084631911752278003212947)
    ·
      refine ⟨54126947867628417004819421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36084631911752278003212947 54126947867628417004819421)
      ·
        refine ⟨20297605450360656376807283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54126947867628417004819421 20297605450360656376807283)
        ·
          refine ⟨30446408175540984565210925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20297605450360656376807283 30446408175540984565210925)
          ·
            refine ⟨11417403065827869211954097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30446408175540984565210925 11417403065827869211954097)
            ·
              refine ⟨8563052299370901908965573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11417403065827869211954097 8563052299370901908965573)
              ·
                refine ⟨1605572306132044107931045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8563052299370901908965573 1605572306132044107931045)
                ·
                  refine ⟨301044807399758270237071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605572306132044107931045 301044807399758270237071)
                  ·
                    rfl

theorem cell21_1319136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_1319136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319136 prefixEnd_1319136 := by exact prefixLift 1319136
  have htrace : WordTrace (prefixWord ++ tailWord_1319136) baseStart_1319136 baseEnd_1319136 := by
    simpa [prefixWord, tailWord_1319136, baseEnd_1319136] using wordTrace_append hprefix tailTrace_1319136
  have hstable : (prefixWord ++ tailWord_1319136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319136).length < 2 ^ (prefixWord ++ tailWord_1319136).sum := by decide
  have hdescent : baseEnd_1319136 < baseStart_1319136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319153 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 4]
def baseStart_1319153 : Nat := 118140960795 + 1319153 * 2 ^ 59
def prefixEnd_1319153 : Nat := 4983230072969 + 3 ^ 40 * 1319153 * 2
def baseEnd_1319153 : Nat := 301048687031370018453703

theorem tailTrace_1319153 : CollatzResearch.WordTrace tailWord_1319153 prefixEnd_1319153 301048687031370018453703 := by
  unfold tailWord_1319153
  simp only [CollatzResearch.WordTrace]
  refine ⟨48113462589941449240986113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32075641726627632827324075 48113462589941449240986113)
  ·
    refine ⟨36085096942456086930739585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48113462589941449240986113 36085096942456086930739585)
    ·
      refine ⟨27063822706842065198054689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36085096942456086930739585 27063822706842065198054689)
      ·
        refine ⟨20297867030131548898541017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27063822706842065198054689 20297867030131548898541017)
        ·
          refine ⟨15223400272598661673905763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20297867030131548898541017 15223400272598661673905763)
          ·
            refine ⟨22835100408897992510858645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15223400272598661673905763 22835100408897992510858645)
            ·
              refine ⟨1070395331667093398946499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22835100408897992510858645 1070395331667093398946499)
              ·
                refine ⟨1605592997500640098419749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070395331667093398946499 1605592997500640098419749)
                ·
                  refine ⟨301048687031370018453703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605592997500640098419749 301048687031370018453703)
                  ·
                    rfl

theorem cell21_1319153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_1319153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319153 prefixEnd_1319153 := by exact prefixLift 1319153
  have htrace : WordTrace (prefixWord ++ tailWord_1319153) baseStart_1319153 baseEnd_1319153 := by
    simpa [prefixWord, tailWord_1319153, baseEnd_1319153] using wordTrace_append hprefix tailTrace_1319153
  have hstable : (prefixWord ++ tailWord_1319153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319153).length < 2 ^ (prefixWord ++ tailWord_1319153).sum := by decide
  have hdescent : baseEnd_1319153 < baseStart_1319153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319195 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 6]
def baseStart_1319195 : Nat := 118140960795 + 1319195 * 2 ^ 59
def prefixEnd_1319195 : Nat := 4983230072969 + 3 ^ 40 * 1319195 * 2
def baseEnd_1319195 : Nat := 301058272003587278753617

theorem tailTrace_1319195 : CollatzResearch.WordTrace tailWord_1319195 prefixEnd_1319195 301058272003587278753617 := by
  unfold tailWord_1319195
  simp only [CollatzResearch.WordTrace]
  refine ⟨48114994455789290414015039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32076662970526193609343359 48114994455789290414015039)
  ·
    refine ⟨72172491683683935621022559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48114994455789290414015039 72172491683683935621022559)
    ·
      refine ⟨108258737525525903431533839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72172491683683935621022559 108258737525525903431533839)
      ·
        refine ⟨162388106288288855147300759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108258737525525903431533839 162388106288288855147300759)
        ·
          refine ⟨243582159432433282720951139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162388106288288855147300759 243582159432433282720951139)
          ·
            refine ⟨365373239148649924081426709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243582159432433282720951139 365373239148649924081426709)
            ·
              refine ⟨17126870585092965191316877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 365373239148649924081426709 17126870585092965191316877)
              ·
                refine ⟨6422576469409861946743829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17126870585092965191316877 6422576469409861946743829)
                ·
                  refine ⟨301058272003587278753617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6422576469409861946743829 301058272003587278753617)
                  ·
                    rfl

theorem cell21_1319195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_1319195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319195 prefixEnd_1319195 := by exact prefixLift 1319195
  have htrace : WordTrace (prefixWord ++ tailWord_1319195) baseStart_1319195 baseEnd_1319195 := by
    simpa [prefixWord, tailWord_1319195, baseEnd_1319195] using wordTrace_append hprefix tailTrace_1319195
  have hstable : (prefixWord ++ tailWord_1319195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319195).length < 2 ^ (prefixWord ++ tailWord_1319195).sum := by decide
  have hdescent : baseEnd_1319195 < baseStart_1319195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319212 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_1319212 : Nat := 118140960795 + 1319212 * 2 ^ 59
def prefixEnd_1319212 : Nat := 4983230072969 + 3 ^ 40 * 1319212 * 2
def baseEnd_1319212 : Nat := 301062151635199026970249

theorem tailTrace_1319212 : CollatzResearch.WordTrace tailWord_1319212 prefixEnd_1319212 301062151635199026970249 := by
  unfold tailWord_1319212
  simp only [CollatzResearch.WordTrace]
  refine ⟨24057807248363851158691945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32077076331151801544922593 24057807248363851158691945)
  ·
    refine ⟨18043355436272888369018959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24057807248363851158691945 18043355436272888369018959)
    ·
      refine ⟨27065033154409332553528439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18043355436272888369018959 27065033154409332553528439)
      ·
        refine ⟨40597549731613998830292659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27065033154409332553528439 40597549731613998830292659)
        ·
          refine ⟨60896324597420998245438989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40597549731613998830292659 60896324597420998245438989)
          ·
            refine ⟨22836121724032874342039621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60896324597420998245438989 22836121724032874342039621)
            ·
              refine ⟨4281772823256163939132429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22836121724032874342039621 4281772823256163939132429)
              ·
                refine ⟨1605664808721061477174661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4281772823256163939132429 1605664808721061477174661)
                ·
                  refine ⟨301062151635199026970249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605664808721061477174661 301062151635199026970249)
                  ·
                    rfl

theorem cell21_1319212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_1319212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319212 prefixEnd_1319212 := by exact prefixLift 1319212
  have htrace : WordTrace (prefixWord ++ tailWord_1319212) baseStart_1319212 baseEnd_1319212 := by
    simpa [prefixWord, tailWord_1319212, baseEnd_1319212] using wordTrace_append hprefix tailTrace_1319212
  have hstable : (prefixWord ++ tailWord_1319212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319212).length < 2 ^ (prefixWord ++ tailWord_1319212).sum := by decide
  have hdescent : baseEnd_1319212 < baseStart_1319212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319274 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_1319274 : Nat := 118140960795 + 1319274 * 2 ^ 59
def prefixEnd_1319274 : Nat := 4983230072969 + 3 ^ 40 * 1319274 * 2
def baseEnd_1319274 : Nat := 301076300879900696936789

theorem tailTrace_1319274 : CollatzResearch.WordTrace tailWord_1319274 prefixEnd_1319274 301076300879900696936789 := by
  unfold tailWord_1319274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12029468955625771726535219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32078583881668724604093917 12029468955625771726535219)
  ·
    refine ⟨18044203433438657589802829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12029468955625771726535219 18044203433438657589802829)
    ·
      refine ⟨6766576287539496596176061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18044203433438657589802829 6766576287539496596176061)
      ·
        refine ⟨2537466107827311223566023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6766576287539496596176061 2537466107827311223566023)
        ·
          refine ⟨3806199161740966835349035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537466107827311223566023 3806199161740966835349035)
          ·
            refine ⟨5709298742611450253023553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806199161740966835349035 5709298742611450253023553)
            ·
              refine ⟨4281974056958587689767665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5709298742611450253023553 4281974056958587689767665)
              ·
                refine ⟨3211480542718940767325749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4281974056958587689767665 3211480542718940767325749)
                ·
                  refine ⟨301076300879900696936789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3211480542718940767325749 301076300879900696936789)
                  ·
                    rfl

theorem cell21_1319274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_1319274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319274 prefixEnd_1319274 := by exact prefixLift 1319274
  have htrace : WordTrace (prefixWord ++ tailWord_1319274) baseStart_1319274 baseEnd_1319274 := by
    simpa [prefixWord, tailWord_1319274, baseEnd_1319274] using wordTrace_append hprefix tailTrace_1319274
  have hstable : (prefixWord ++ tailWord_1319274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319274).length < 2 ^ (prefixWord ++ tailWord_1319274).sum := by decide
  have hdescent : baseEnd_1319274 < baseStart_1319274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319291 : List Nat := [1, 1, 1, 1, 1, 9, 1, 3, 3]
def baseStart_1319291 : Nat := 118140960795 + 1319291 * 2 ^ 59
def prefixEnd_1319291 : Nat := 4983230072969 + 3 ^ 40 * 1319291 * 2
def baseEnd_1319291 : Nat := 301080180511512445153421

theorem tailTrace_1319291 : CollatzResearch.WordTrace tailWord_1319291 prefixEnd_1319291 301080180511512445153421 := by
  unfold tailWord_1319291
  simp only [CollatzResearch.WordTrace]
  refine ⟨48118495863441498809509727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32078997242294332539673151 48118495863441498809509727)
  ·
    refine ⟨72177743795162248214264591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48118495863441498809509727 72177743795162248214264591)
    ·
      refine ⟨108266615692743372321396887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72177743795162248214264591 108266615692743372321396887)
      ·
        refine ⟨162399923539115058482095331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108266615692743372321396887 162399923539115058482095331)
        ·
          refine ⟨243599885308672587723142997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162399923539115058482095331 243599885308672587723142997)
          ·
            refine ⟨1427343077980503443690291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 243599885308672587723142997 1427343077980503443690291)
            ·
              refine ⟨2141014616970755165535437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427343077980503443690291 2141014616970755165535437)
              ·
                refine ⟨802880481364033187075789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2141014616970755165535437 802880481364033187075789)
                ·
                  refine ⟨301080180511512445153421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802880481364033187075789 301080180511512445153421)
                  ·
                    rfl

theorem cell21_1319291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 3].length) (baseStart_1319291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319291 prefixEnd_1319291 := by exact prefixLift 1319291
  have htrace : WordTrace (prefixWord ++ tailWord_1319291) baseStart_1319291 baseEnd_1319291 := by
    simpa [prefixWord, tailWord_1319291, baseEnd_1319291] using wordTrace_append hprefix tailTrace_1319291
  have hstable : (prefixWord ++ tailWord_1319291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319291).length < 2 ^ (prefixWord ++ tailWord_1319291).sum := by decide
  have hdescent : baseEnd_1319291 < baseStart_1319291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319322 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_1319322 : Nat := 118140960795 + 1319322 * 2 ^ 59
def prefixEnd_1319322 : Nat := 4983230072969 + 3 ^ 40 * 1319322 * 2
def baseEnd_1319322 : Nat := 301087255133863280136691

theorem tailTrace_1319322 : CollatzResearch.WordTrace tailWord_1319322 prefixEnd_1319322 301087255133863280136691 := by
  unfold tailWord_1319322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12029906631582297775972055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32079751017552794069258813 12029906631582297775972055)
  ·
    refine ⟨18044859947373446663958083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12029906631582297775972055 18044859947373446663958083)
    ·
      refine ⟨27067289921060169995937125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18044859947373446663958083 27067289921060169995937125)
      ·
        refine ⟨5075116860198781874238211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27067289921060169995937125 5075116860198781874238211)
        ·
          refine ⟨7612675290298172811357317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075116860198781874238211 7612675290298172811357317)
          ·
            refine ⟨1427376616930907402129497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7612675290298172811357317 1427376616930907402129497)
            ·
              refine ⟨1070532462698180551597123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1427376616930907402129497 1070532462698180551597123)
              ·
                refine ⟨1605798694047270827395685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070532462698180551597123 1605798694047270827395685)
                ·
                  refine ⟨301087255133863280136691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605798694047270827395685 301087255133863280136691)
                  ·
                    rfl

theorem cell21_1319322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_1319322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319322 prefixEnd_1319322 := by exact prefixLift 1319322
  have htrace : WordTrace (prefixWord ++ tailWord_1319322) baseStart_1319322 baseEnd_1319322 := by
    simpa [prefixWord, tailWord_1319322, baseEnd_1319322] using wordTrace_append hprefix tailTrace_1319322
  have hstable : (prefixWord ++ tailWord_1319322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319322).length < 2 ^ (prefixWord ++ tailWord_1319322).sum := by decide
  have hdescent : baseEnd_1319322 < baseStart_1319322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319367 : List Nat := [1, 1, 4, 1, 1, 4, 4, 2, 3]
def baseStart_1319367 : Nat := 118140960795 + 1319367 * 2 ^ 59
def prefixEnd_1319367 : Nat := 4983230072969 + 3 ^ 40 * 1319367 * 2
def baseEnd_1319367 : Nat := 301097524746953201886599

theorem tailTrace_1319367 : CollatzResearch.WordTrace tailWord_1319367 prefixEnd_1319367 301097524746953201886599 := by
  unfold tailWord_1319367
  simp only [CollatzResearch.WordTrace]
  refine ⟨48121267811166163789276355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32080845207444109192850903 48121267811166163789276355)
  ·
    refine ⟨72181901716749245683914533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48121267811166163789276355 72181901716749245683914533)
    ·
      refine ⟨13534106571890483565733975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72181901716749245683914533 13534106571890483565733975)
      ·
        refine ⟨20301159857835725348600963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13534106571890483565733975 20301159857835725348600963)
        ·
          refine ⟨30451739786753588022901445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20301159857835725348600963 30451739786753588022901445)
          ·
            refine ⟨5709701210016297754294021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30451739786753588022901445 5709701210016297754294021)
            ·
              refine ⟨1070568976878055828930129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5709701210016297754294021 1070568976878055828930129)
              ·
                refine ⟨802926732658541871697597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070568976878055828930129 802926732658541871697597)
                ·
                  refine ⟨301097524746953201886599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802926732658541871697597 301097524746953201886599)
                  ·
                    rfl

theorem cell21_1319367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 3].length) (baseStart_1319367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319367 prefixEnd_1319367 := by exact prefixLift 1319367
  have htrace : WordTrace (prefixWord ++ tailWord_1319367) baseStart_1319367 baseEnd_1319367 := by
    simpa [prefixWord, tailWord_1319367, baseEnd_1319367] using wordTrace_append hprefix tailTrace_1319367
  have hstable : (prefixWord ++ tailWord_1319367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319367).length < 2 ^ (prefixWord ++ tailWord_1319367).sum := by decide
  have hdescent : baseEnd_1319367 < baseStart_1319367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319423 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 6]
def baseStart_1319423 : Nat := 118140960795 + 1319423 * 2 ^ 59
def prefixEnd_1319423 : Nat := 4983230072969 + 3 ^ 40 * 1319423 * 2
def baseEnd_1319423 : Nat := 301110304709909548953151

theorem tailTrace_1319423 : CollatzResearch.WordTrace tailWord_1319423 prefixEnd_1319423 301110304709909548953151 := by
  unfold tailWord_1319423
  simp only [CollatzResearch.WordTrace]
  refine ⟨48123310298963285353314923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32082206865975523568876615 48123310298963285353314923)
  ·
    refine ⟨72184965448444928029972385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48123310298963285353314923 72184965448444928029972385)
    ·
      refine ⟨54138724086333696022479289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72184965448444928029972385 54138724086333696022479289)
      ·
        refine ⟨40604043064750272016859467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54138724086333696022479289 40604043064750272016859467)
        ·
          refine ⟨60906064597125408025289201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40604043064750272016859467 60906064597125408025289201)
          ·
            refine ⟨45679548447844056018966901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60906064597125408025289201 45679548447844056018966901)
            ·
              refine ⟨4282457666985380251778147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45679548447844056018966901 4282457666985380251778147)
              ·
                refine ⟨6423686500478070377667221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282457666985380251778147 6423686500478070377667221)
                ·
                  refine ⟨301110304709909548953151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6423686500478070377667221 301110304709909548953151)
                  ·
                    rfl

theorem cell21_1319423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_1319423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319423 prefixEnd_1319423 := by exact prefixLift 1319423
  have htrace : WordTrace (prefixWord ++ tailWord_1319423) baseStart_1319423 baseEnd_1319423 := by
    simpa [prefixWord, tailWord_1319423, baseEnd_1319423] using wordTrace_append hprefix tailTrace_1319423
  have hstable : (prefixWord ++ tailWord_1319423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319423).length < 2 ^ (prefixWord ++ tailWord_1319423).sum := by decide
  have hdescent : baseEnd_1319423 < baseStart_1319423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319468 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_1319468 : Nat := 118140960795 + 1319468 * 2 ^ 59
def prefixEnd_1319468 : Nat := 4983230072969 + 3 ^ 40 * 1319468 * 2
def baseEnd_1319468 : Nat := 301120574322999470703059

theorem tailTrace_1319468 : CollatzResearch.WordTrace tailWord_1319468 prefixEnd_1319468 301120574322999470703059 := by
  unfold tailWord_1319468
  simp only [CollatzResearch.WordTrace]
  refine ⟨24062475791900129019351529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32083301055866838692468705 24062475791900129019351529)
  ·
    refine ⟨18046856843925096764513647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24062475791900129019351529 18046856843925096764513647)
    ·
      refine ⟨27070285265887645146770471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18046856843925096764513647 27070285265887645146770471)
      ·
        refine ⟨40605427898831467720155707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27070285265887645146770471 40605427898831467720155707)
        ·
          refine ⟨60908141848247201580233561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40605427898831467720155707 60908141848247201580233561)
          ·
            refine ⟨45681106386185401185175171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60908141848247201580233561 45681106386185401185175171)
            ·
              refine ⟨68521659579278101777762757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45681106386185401185175171 68521659579278101777762757)
              ·
                refine ⟨12847811171114644083330517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68521659579278101777762757 12847811171114644083330517)
                ·
                  refine ⟨301120574322999470703059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12847811171114644083330517 301120574322999470703059)
                  ·
                    rfl

theorem cell21_1319468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_1319468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319468 prefixEnd_1319468 := by exact prefixLift 1319468
  have htrace : WordTrace (prefixWord ++ tailWord_1319468) baseStart_1319468 baseEnd_1319468 := by
    simpa [prefixWord, tailWord_1319468, baseEnd_1319468] using wordTrace_append hprefix tailTrace_1319468
  have hstable : (prefixWord ++ tailWord_1319468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319468).length < 2 ^ (prefixWord ++ tailWord_1319468).sum := by decide
  have hdescent : baseEnd_1319468 < baseStart_1319468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319533 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1319533 : Nat := 118140960795 + 1319533 * 2 ^ 59
def prefixEnd_1319533 : Nat := 4983230072969 + 3 ^ 40 * 1319533 * 2
def baseEnd_1319533 : Nat := 301135408208573802119593

theorem tailTrace_1319533 : CollatzResearch.WordTrace tailWord_1319533 prefixEnd_1319533 301135408208573802119593 := by
  unfold tailWord_1319533
  simp only [CollatzResearch.WordTrace]
  refine ⟨48127322328564774139819253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32084881552376516093212835 48127322328564774139819253)
  ·
    refine ⟨4511936468302947575608055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48127322328564774139819253 4511936468302947575608055)
    ·
      refine ⟨6767904702454421363412083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4511936468302947575608055 6767904702454421363412083)
      ·
        refine ⟨10151857053681632045118125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6767904702454421363412083 10151857053681632045118125)
        ·
          refine ⟨3806946395130612016919297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10151857053681632045118125 3806946395130612016919297)
          ·
            refine ⟨2855209796347959012689473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3806946395130612016919297 2855209796347959012689473)
            ·
              refine ⟨2141407347260969259517105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2855209796347959012689473 2141407347260969259517105)
              ·
                refine ⟨1606055510445726944637829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2141407347260969259517105 1606055510445726944637829)
                ·
                  refine ⟨301135408208573802119593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1606055510445726944637829 301135408208573802119593)
                  ·
                    rfl

theorem cell21_1319533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1319533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319533 prefixEnd_1319533 := by exact prefixLift 1319533
  have htrace : WordTrace (prefixWord ++ tailWord_1319533) baseStart_1319533 baseEnd_1319533 := by
    simpa [prefixWord, tailWord_1319533, baseEnd_1319533] using wordTrace_append hprefix tailTrace_1319533
  have hstable : (prefixWord ++ tailWord_1319533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319533).length < 2 ^ (prefixWord ++ tailWord_1319533).sum := by decide
  have hdescent : baseEnd_1319533 < baseStart_1319533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319536 : List Nat := [2, 1, 1, 1, 7, 2, 2, 2, 3]
def baseStart_1319536 : Nat := 118140960795 + 1319536 * 2 ^ 59
def prefixEnd_1319536 : Nat := 4983230072969 + 3 ^ 40 * 1319536 * 2
def baseEnd_1319536 : Nat := 301136092849446463569587

theorem tailTrace_1319536 : CollatzResearch.WordTrace tailWord_1319536 prefixEnd_1319536 301136092849446463569587 := by
  unfold tailWord_1319536
  simp only [CollatzResearch.WordTrace]
  refine ⟨24063715873776952826089231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32084954498369270434785641 24063715873776952826089231)
  ·
    refine ⟨36095573810665429239133847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24063715873776952826089231 36095573810665429239133847)
    ·
      refine ⟨54143360715998143858700771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36095573810665429239133847 54143360715998143858700771)
      ·
        refine ⟨81215041073997215788051157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54143360715998143858700771 81215041073997215788051157)
        ·
          refine ⟨1903477525171809745032449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 81215041073997215788051157 1903477525171809745032449)
          ·
            refine ⟨1427608143878857308774337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1903477525171809745032449 1427608143878857308774337)
            ·
              refine ⟨1070706107909142981580753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1427608143878857308774337 1070706107909142981580753)
              ·
                refine ⟨803029580931857236185565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070706107909142981580753 803029580931857236185565)
                ·
                  refine ⟨301136092849446463569587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803029580931857236185565 301136092849446463569587)
                  ·
                    rfl

theorem cell21_1319536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_1319536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319536 prefixEnd_1319536 := by exact prefixLift 1319536
  have htrace : WordTrace (prefixWord ++ tailWord_1319536) baseStart_1319536 baseEnd_1319536 := by
    simpa [prefixWord, tailWord_1319536, baseEnd_1319536] using wordTrace_append hprefix tailTrace_1319536
  have hstable : (prefixWord ++ tailWord_1319536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319536).length < 2 ^ (prefixWord ++ tailWord_1319536).sum := by decide
  have hdescent : baseEnd_1319536 < baseStart_1319536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319575 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 6]
def baseStart_1319575 : Nat := 118140960795 + 1319575 * 2 ^ 59
def prefixEnd_1319575 : Nat := 4983230072969 + 3 ^ 40 * 1319575 * 2
def baseEnd_1319575 : Nat := 301144993180791062419507

theorem tailTrace_1319575 : CollatzResearch.WordTrace tailWord_1319575 prefixEnd_1319575 301144993180791062419507 := by
  unfold tailWord_1319575
  simp only [CollatzResearch.WordTrace]
  refine ⟨48128854194412615312848179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32085902796275076875232119 48128854194412615312848179)
  ·
    refine ⟨72193281291618922969272269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48128854194412615312848179 72193281291618922969272269)
    ·
      refine ⟨27072480484357096113477101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72193281291618922969272269 27072480484357096113477101)
      ·
        refine ⟨10152180181633911042553913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27072480484357096113477101 10152180181633911042553913)
        ·
          refine ⟨7614135136225433281915435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10152180181633911042553913 7614135136225433281915435)
          ·
            refine ⟨11421202704338149922873153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7614135136225433281915435 11421202704338149922873153)
            ·
              refine ⟨8565902028253612442154865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11421202704338149922873153 8565902028253612442154865)
              ·
                refine ⟨6424426521190209331616149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8565902028253612442154865 6424426521190209331616149)
                ·
                  refine ⟨301144993180791062419507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6424426521190209331616149 301144993180791062419507)
                  ·
                    rfl

theorem cell21_1319575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_1319575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319575 prefixEnd_1319575 := by exact prefixLift 1319575
  have htrace : WordTrace (prefixWord ++ tailWord_1319575) baseStart_1319575 baseEnd_1319575 := by
    simpa [prefixWord, tailWord_1319575, baseEnd_1319575] using wordTrace_append hprefix tailTrace_1319575
  have hstable : (prefixWord ++ tailWord_1319575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319575).length < 2 ^ (prefixWord ++ tailWord_1319575).sum := by decide
  have hdescent : baseEnd_1319575 < baseStart_1319575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319629 : List Nat := [1, 6, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1319629 : Nat := 118140960795 + 1319629 * 2 ^ 59
def prefixEnd_1319629 : Nat := 4983230072969 + 3 ^ 40 * 1319629 * 2
def baseEnd_1319629 : Nat := 301157316716498968519397

theorem tailTrace_1319629 : CollatzResearch.WordTrace tailWord_1319629 prefixEnd_1319629 301157316716498968519397 := by
  unfold tailWord_1319629
  simp only [CollatzResearch.WordTrace]
  refine ⟨48130823736216982535313941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32087215824144655023542627 48130823736216982535313941)
  ·
    refine ⟨2256132362635171056342841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48130823736216982535313941 2256132362635171056342841)
    ·
      refine ⟨1692099271976378292257131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2256132362635171056342841 1692099271976378292257131)
      ·
        refine ⟨2538148907964567438385697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692099271976378292257131 2538148907964567438385697)
        ·
          refine ⟨1903611680973425578789273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2538148907964567438385697 1903611680973425578789273)
          ·
            refine ⟨1427708760730069184091955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1903611680973425578789273 1427708760730069184091955)
            ·
              refine ⟨2141563141095103776137933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427708760730069184091955 2141563141095103776137933)
              ·
                refine ⟨803086177910663916051725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2141563141095103776137933 803086177910663916051725)
                ·
                  refine ⟨301157316716498968519397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803086177910663916051725 301157316716498968519397)
                  ·
                    rfl

theorem cell21_1319629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1319629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319629 prefixEnd_1319629 := by exact prefixLift 1319629
  have htrace : WordTrace (prefixWord ++ tailWord_1319629) baseStart_1319629 baseEnd_1319629 := by
    simpa [prefixWord, tailWord_1319629, baseEnd_1319629] using wordTrace_append hprefix tailTrace_1319629
  have hstable : (prefixWord ++ tailWord_1319629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319629).length < 2 ^ (prefixWord ++ tailWord_1319629).sum := by decide
  have hdescent : baseEnd_1319629 < baseStart_1319629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319716 : List Nat := [2, 3, 1, 3, 4, 1, 1, 6]
def baseStart_1319716 : Nat := 118140960795 + 1319716 * 2 ^ 59
def prefixEnd_1319716 : Nat := 4983230072969 + 3 ^ 40 * 1319716 * 2
def baseEnd_1319716 : Nat := 100392390433935383523073

theorem tailTrace_1319716 : CollatzResearch.WordTrace tailWord_1319716 prefixEnd_1319716 100392390433935383523073 := by
  unfold tailWord_1319716
  simp only [CollatzResearch.WordTrace]
  refine ⟨24066998443450898196865501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32089331257934530929154001 24066998443450898196865501)
  ·
    refine ⟨9025124416294086823824563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24066998443450898196865501 9025124416294086823824563)
    ·
      refine ⟨13537686624441130235736845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9025124416294086823824563 13537686624441130235736845)
      ·
        refine ⟨5076632484165423838401317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13537686624441130235736845 5076632484165423838401317)
        ·
          refine ⟨951868590781016969700247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5076632484165423838401317 951868590781016969700247)
          ·
            refine ⟨1427802886171525454550371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951868590781016969700247 1427802886171525454550371)
            ·
              refine ⟨2141704329257288181825557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427802886171525454550371 2141704329257288181825557)
              ·
                refine ⟨100392390433935383523073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2141704329257288181825557 100392390433935383523073)
                ·
                  rfl

theorem cell21_1319716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_1319716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319716 prefixEnd_1319716 := by exact prefixLift 1319716
  have htrace : WordTrace (prefixWord ++ tailWord_1319716) baseStart_1319716 baseEnd_1319716 := by
    simpa [prefixWord, tailWord_1319716, baseEnd_1319716] using wordTrace_append hprefix tailTrace_1319716
  have hstable : (prefixWord ++ tailWord_1319716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319716).length < 2 ^ (prefixWord ++ tailWord_1319716).sum := by decide
  have hdescent : baseEnd_1319716 < baseStart_1319716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319761 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 4]
def baseStart_1319761 : Nat := 118140960795 + 1319761 * 2 ^ 59
def prefixEnd_1319761 : Nat := 4983230072969 + 3 ^ 40 * 1319761 * 2
def baseEnd_1319761 : Nat := 301187440914896072319127

theorem tailTrace_1319761 : CollatzResearch.WordTrace tailWord_1319761 prefixEnd_1319761 301187440914896072319127 := by
  unfold tailWord_1319761
  simp only [CollatzResearch.WordTrace]
  refine ⟨48135638171738769079119137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32090425447825846052746091 48135638171738769079119137)
  ·
    refine ⟨36101728628804076809339353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48135638171738769079119137 36101728628804076809339353)
    ·
      refine ⟨27076296471603057607004515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36101728628804076809339353 27076296471603057607004515)
      ·
        refine ⟨40614444707404586410506773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27076296471603057607004515 40614444707404586410506773)
        ·
          refine ⟨1903802095659589987992505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40614444707404586410506773 1903802095659589987992505)
          ·
            refine ⟨1427851571744692490994379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1903802095659589987992505 1427851571744692490994379)
            ·
              refine ⟨2141777357617038736491569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427851571744692490994379 2141777357617038736491569)
              ·
                refine ⟨1606333018212779052368677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2141777357617038736491569 1606333018212779052368677)
                ·
                  refine ⟨301187440914896072319127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1606333018212779052368677 301187440914896072319127)
                  ·
                    rfl

theorem cell21_1319761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_1319761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319761 prefixEnd_1319761 := by exact prefixLift 1319761
  have htrace : WordTrace (prefixWord ++ tailWord_1319761) baseStart_1319761 baseEnd_1319761 := by
    simpa [prefixWord, tailWord_1319761, baseEnd_1319761] using wordTrace_append hprefix tailTrace_1319761
  have hstable : (prefixWord ++ tailWord_1319761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319761).length < 2 ^ (prefixWord ++ tailWord_1319761).sum := by decide
  have hdescent : baseEnd_1319761 < baseStart_1319761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319778 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1319778 : Nat := 118140960795 + 1319778 * 2 ^ 59
def prefixEnd_1319778 : Nat := 4983230072969 + 3 ^ 40 * 1319778 * 2
def baseEnd_1319778 : Nat := 301191320546507820535759

theorem tailTrace_1319778 : CollatzResearch.WordTrace tailWord_1319778 prefixEnd_1319778 301191320546507820535759 := by
  unfold tailWord_1319778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12034064553169295245621997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32090838808451453988325325 12034064553169295245621997)
  ·
    refine ⟨4512774207438485717108249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12034064553169295245621997 4512774207438485717108249)
    ·
      refine ⟨3384580655578864287831187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4512774207438485717108249 3384580655578864287831187)
      ·
        refine ⟨5076870983368296431746781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3384580655578864287831187 5076870983368296431746781)
        ·
          refine ⟨1903826618763111161905043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5076870983368296431746781 1903826618763111161905043)
          ·
            refine ⟨2855739928144666742857565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903826618763111161905043 2855739928144666742857565)
            ·
              refine ⟨1070902473054250028571587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2855739928144666742857565 1070902473054250028571587)
              ·
                refine ⟨1606353709581375042857381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070902473054250028571587 1606353709581375042857381)
                ·
                  refine ⟨301191320546507820535759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1606353709581375042857381 301191320546507820535759)
                  ·
                    rfl

theorem cell21_1319778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1319778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319778 prefixEnd_1319778 := by exact prefixLift 1319778
  have htrace : WordTrace (prefixWord ++ tailWord_1319778) baseStart_1319778 baseEnd_1319778 := by
    simpa [prefixWord, tailWord_1319778, baseEnd_1319778] using wordTrace_append hprefix tailTrace_1319778
  have hstable : (prefixWord ++ tailWord_1319778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319778).length < 2 ^ (prefixWord ++ tailWord_1319778).sum := by decide
  have hdescent : baseEnd_1319778 < baseStart_1319778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319817 : List Nat := [1, 2, 1, 1, 5, 2, 9]
def baseStart_1319817 : Nat := 118140960795 + 1319817 * 2 ^ 59
def prefixEnd_1319817 : Nat := 4983230072969 + 3 ^ 40 * 1319817 * 2
def baseEnd_1319817 : Nat := 33466691208650268820631

theorem tailTrace_1319817 : CollatzResearch.WordTrace tailWord_1319817 prefixEnd_1319817 33466691208650268820631 := by
  unfold tailWord_1319817
  simp only [CollatzResearch.WordTrace]
  refine ⟨48137680659535890643157705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32091787106357260428771803 48137680659535890643157705)
  ·
    refine ⟨36103260494651917982368279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48137680659535890643157705 36103260494651917982368279)
    ·
      refine ⟨54154890741977876973552419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36103260494651917982368279 54154890741977876973552419)
      ·
        refine ⟨81232336112966815460328629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54154890741977876973552419 81232336112966815460328629)
        ·
          refine ⟨7615531510590638949405809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81232336112966815460328629 7615531510590638949405809)
          ·
            refine ⟨5711648632942979212054357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7615531510590638949405809 5711648632942979212054357)
            ·
              refine ⟨33466691208650268820631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5711648632942979212054357 33466691208650268820631)
              ·
                rfl

theorem cell21_1319817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 9].length) (baseStart_1319817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319817 prefixEnd_1319817 := by exact prefixLift 1319817
  have htrace : WordTrace (prefixWord ++ tailWord_1319817) baseStart_1319817 baseEnd_1319817 := by
    simpa [prefixWord, tailWord_1319817, baseEnd_1319817] using wordTrace_append hprefix tailTrace_1319817
  have hstable : (prefixWord ++ tailWord_1319817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319817).length < 2 ^ (prefixWord ++ tailWord_1319817).sum := by decide
  have hdescent : baseEnd_1319817 < baseStart_1319817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319879 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 4]
def baseStart_1319879 : Nat := 118140960795 + 1319879 * 2 ^ 59
def prefixEnd_1319879 : Nat := 4983230072969 + 3 ^ 40 * 1319879 * 2
def baseEnd_1319879 : Nat := 301214370122554089352219

theorem tailTrace_1319879 : CollatzResearch.WordTrace tailWord_1319879 prefixEnd_1319879 301214370122554089352219 := by
  unfold tailWord_1319879
  simp only [CollatzResearch.WordTrace]
  refine ⟨48139941985311275231914691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32093294656874183487943127 48139941985311275231914691)
  ·
    refine ⟨72209912977966912847872037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48139941985311275231914691 72209912977966912847872037)
    ·
      refine ⟨13539358683368796158976007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72209912977966912847872037 13539358683368796158976007)
      ·
        refine ⟨20309038025053194238464011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13539358683368796158976007 20309038025053194238464011)
        ·
          refine ⟨30463557037579791357696017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20309038025053194238464011 30463557037579791357696017)
          ·
            refine ⟨22847667778184843518272013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30463557037579791357696017 22847667778184843518272013)
            ·
              refine ⟨8567875416819316319352005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22847667778184843518272013 8567875416819316319352005)
              ·
                refine ⟨1606476640653621809878501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8567875416819316319352005 1606476640653621809878501)
                ·
                  refine ⟨301214370122554089352219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1606476640653621809878501 301214370122554089352219)
                  ·
                    rfl

theorem cell21_1319879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 4].length) (baseStart_1319879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319879 prefixEnd_1319879 := by exact prefixLift 1319879
  have htrace : WordTrace (prefixWord ++ tailWord_1319879) baseStart_1319879 baseEnd_1319879 := by
    simpa [prefixWord, tailWord_1319879, baseEnd_1319879] using wordTrace_append hprefix tailTrace_1319879
  have hstable : (prefixWord ++ tailWord_1319879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319879).length < 2 ^ (prefixWord ++ tailWord_1319879).sum := by decide
  have hdescent : baseEnd_1319879 < baseStart_1319879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319941 : List Nat := [1, 3, 1, 1, 2, 3, 1, 6, 3]
def baseStart_1319941 : Nat := 118140960795 + 1319941 * 2 ^ 59
def prefixEnd_1319941 : Nat := 4983230072969 + 3 ^ 40 * 1319941 * 2
def baseEnd_1319941 : Nat := 301228519367255759318759

theorem tailTrace_1319941 : CollatzResearch.WordTrace tailWord_1319941 prefixEnd_1319941 301228519367255759318759 := by
  unfold tailWord_1319941
  simp only [CollatzResearch.WordTrace]
  refine ⟨48142203311086659820671677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32094802207391106547114451 48142203311086659820671677)
  ·
    refine ⟨18053326241657497432751879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48142203311086659820671677 18053326241657497432751879)
    ·
      refine ⟨27079989362486246149127819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18053326241657497432751879 27079989362486246149127819)
      ·
        refine ⟨40619984043729369223691729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27079989362486246149127819 40619984043729369223691729)
        ·
          refine ⟨30464988032797026917768797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40619984043729369223691729 30464988032797026917768797)
          ·
            refine ⟨11424370512298885094163299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30464988032797026917768797 11424370512298885094163299)
            ·
              refine ⟨17136555768448327641244949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11424370512298885094163299 17136555768448327641244949)
              ·
                refine ⟨803276051646015358183357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17136555768448327641244949 803276051646015358183357)
                ·
                  refine ⟨301228519367255759318759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803276051646015358183357 301228519367255759318759)
                  ·
                    rfl

theorem cell21_1319941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_1319941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319941 prefixEnd_1319941 := by exact prefixLift 1319941
  have htrace : WordTrace (prefixWord ++ tailWord_1319941) baseStart_1319941 baseEnd_1319941 := by
    simpa [prefixWord, tailWord_1319941, baseEnd_1319941] using wordTrace_append hprefix tailTrace_1319941
  have hstable : (prefixWord ++ tailWord_1319941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319941).length < 2 ^ (prefixWord ++ tailWord_1319941).sum := by decide
  have hdescent : baseEnd_1319941 < baseStart_1319941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319975 : List Nat := [1, 1, 7, 1, 1, 1, 3, 3, 3]
def baseStart_1319975 : Nat := 118140960795 + 1319975 * 2 ^ 59
def prefixEnd_1319975 : Nat := 4983230072969 + 3 ^ 40 * 1319975 * 2
def baseEnd_1319975 : Nat := 301236278630479255752023

theorem tailTrace_1319975 : CollatzResearch.WordTrace tailWord_1319975 prefixEnd_1319975 301236278630479255752023 := by
  unfold tailWord_1319975
  simp only [CollatzResearch.WordTrace]
  refine ⟨48143443392963483627409379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32095628928642322418272919 48143443392963483627409379)
  ·
    refine ⟨72215165089445225441114069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48143443392963483627409379 72215165089445225441114069)
    ·
      refine ⟨1692542931783872471276111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 72215165089445225441114069 1692542931783872471276111)
      ·
        refine ⟨2538814397675808706914167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692542931783872471276111 2538814397675808706914167)
        ·
          refine ⟨3808221596513713060371251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538814397675808706914167 3808221596513713060371251)
          ·
            refine ⟨5712332394770569590556877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808221596513713060371251 5712332394770569590556877)
            ·
              refine ⟨2142124648038963596458829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5712332394770569590556877 2142124648038963596458829)
              ·
                refine ⟨803296743014611348672061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2142124648038963596458829 803296743014611348672061)
                ·
                  refine ⟨301236278630479255752023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803296743014611348672061 301236278630479255752023)
                  ·
                    rfl

theorem cell21_1319975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 3].length) (baseStart_1319975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1319975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1319975 prefixEnd_1319975 := by exact prefixLift 1319975
  have htrace : WordTrace (prefixWord ++ tailWord_1319975) baseStart_1319975 baseEnd_1319975 := by
    simpa [prefixWord, tailWord_1319975, baseEnd_1319975] using wordTrace_append hprefix tailTrace_1319975
  have hstable : (prefixWord ++ tailWord_1319975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319975).length < 2 ^ (prefixWord ++ tailWord_1319975).sum := by decide
  have hdescent : baseEnd_1319975 < baseStart_1319975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320006 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1320006 : Nat := 118140960795 + 1320006 * 2 ^ 59
def prefixEnd_1320006 : Nat := 4983230072969 + 3 ^ 40 * 1320006 * 2
def baseEnd_1320006 : Nat := 301243353252830090735293

theorem tailTrace_1320006 : CollatzResearch.WordTrace tailWord_1320006 prefixEnd_1320006 301243353252830090735293 := by
  unfold tailWord_1320006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504517939245349247555871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32096382703900783947858581 1504517939245349247555871)
  ·
    refine ⟨2256776908868023871333807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1504517939245349247555871 2256776908868023871333807)
    ·
      refine ⟨3385165363302035807000711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2256776908868023871333807 3385165363302035807000711)
      ·
        refine ⟨5077748044953053710501067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3385165363302035807000711 5077748044953053710501067)
        ·
          refine ⟨7616622067429580565751601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077748044953053710501067 7616622067429580565751601)
          ·
            refine ⟨5712466550572185424313701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7616622067429580565751601 5712466550572185424313701)
            ·
              refine ⟨1071087478232284767058819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5712466550572185424313701 1071087478232284767058819)
              ·
                refine ⟨1606631217348427150588229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071087478232284767058819 1606631217348427150588229)
                ·
                  refine ⟨301243353252830090735293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1606631217348427150588229 301243353252830090735293)
                  ·
                    rfl

theorem cell21_1320006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1320006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320006 prefixEnd_1320006 := by exact prefixLift 1320006
  have htrace : WordTrace (prefixWord ++ tailWord_1320006) baseStart_1320006 baseEnd_1320006 := by
    simpa [prefixWord, tailWord_1320006, baseEnd_1320006] using wordTrace_append hprefix tailTrace_1320006
  have hstable : (prefixWord ++ tailWord_1320006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320006).length < 2 ^ (prefixWord ++ tailWord_1320006).sum := by decide
  have hdescent : baseEnd_1320006 < baseStart_1320006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320045 : List Nat := [1, 5, 1, 1, 2, 11]
def baseStart_1320045 : Nat := 118140960795 + 1320045 * 2 ^ 59
def prefixEnd_1320045 : Nat := 4983230072969 + 3 ^ 40 * 1320045 * 2
def baseEnd_1320045 : Nat := 11157490873487951466119

theorem tailTrace_1320045 : CollatzResearch.WordTrace tailWord_1320045 prefixEnd_1320045 11157490873487951466119 := by
  unfold tailWord_1320045
  simp only [CollatzResearch.WordTrace]
  refine ⟨48145996502709885582457589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32097331001806590388305059 48145996502709885582457589)
  ·
    refine ⟨4513687172129051773355399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48145996502709885582457589 4513687172129051773355399)
    ·
      refine ⟨6770530758193577660033099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4513687172129051773355399 6770530758193577660033099)
      ·
        refine ⟨10155796137290366490049649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6770530758193577660033099 10155796137290366490049649)
        ·
          refine ⟨7616847102967774867537237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10155796137290366490049649 7616847102967774867537237)
          ·
            refine ⟨11157490873487951466119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7616847102967774867537237 11157490873487951466119)
            ·
              rfl

theorem cell21_1320045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 11].length) (baseStart_1320045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320045 prefixEnd_1320045 := by exact prefixLift 1320045
  have htrace : WordTrace (prefixWord ++ tailWord_1320045) baseStart_1320045 baseEnd_1320045 := by
    simpa [prefixWord, tailWord_1320045, baseEnd_1320045] using wordTrace_append hprefix tailTrace_1320045
  have hstable : (prefixWord ++ tailWord_1320045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320045).length < 2 ^ (prefixWord ++ tailWord_1320045).sum := by decide
  have hdescent : baseEnd_1320045 < baseStart_1320045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320059 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 9]
def baseStart_1320059 : Nat := 118140960795 + 1320059 * 2 ^ 59
def prefixEnd_1320059 : Nat := 4983230072969 + 3 ^ 40 * 1320059 * 2
def baseEnd_1320059 : Nat := 301255448574913776351851

theorem tailTrace_1320059 : CollatzResearch.WordTrace tailWord_1320059 prefixEnd_1320059 301255448574913776351851 := by
  unfold tailWord_1320059
  simp only [CollatzResearch.WordTrace]
  refine ⟨48146507124659165973467231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32097671416439443982311487 48146507124659165973467231)
  ·
    refine ⟨72219760686988748960200847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48146507124659165973467231 72219760686988748960200847)
    ·
      refine ⟨108329641030483123440301271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72219760686988748960200847 108329641030483123440301271)
      ·
        refine ⟨162494461545724685160451907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108329641030483123440301271 162494461545724685160451907)
        ·
          refine ⟨243741692318587027740677861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162494461545724685160451907 243741692318587027740677861)
          ·
            refine ⟨45701567309735067701377099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 243741692318587027740677861 45701567309735067701377099)
            ·
              refine ⟨68552350964602601552065649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45701567309735067701377099 68552350964602601552065649)
              ·
                refine ⟨51414263223451951164049237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68552350964602601552065649 51414263223451951164049237)
                ·
                  refine ⟨301255448574913776351851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51414263223451951164049237 301255448574913776351851)
                  ·
                    rfl

theorem cell21_1320059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_1320059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320059 prefixEnd_1320059 := by exact prefixLift 1320059
  have htrace : WordTrace (prefixWord ++ tailWord_1320059) baseStart_1320059 baseEnd_1320059 := by
    simpa [prefixWord, tailWord_1320059, baseEnd_1320059] using wordTrace_append hprefix tailTrace_1320059
  have hstable : (prefixWord ++ tailWord_1320059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320059).length < 2 ^ (prefixWord ++ tailWord_1320059).sum := by decide
  have hdescent : baseEnd_1320059 < baseStart_1320059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320130 : List Nat := [3, 5, 1, 1, 3, 1, 2, 5]
def baseStart_1320130 : Nat := 118140960795 + 1320130 * 2 ^ 59
def prefixEnd_1320130 : Nat := 4983230072969 + 3 ^ 40 * 1320130 * 2
def baseEnd_1320130 : Nat := 100423883914077810222791

theorem tailTrace_1320130 : CollatzResearch.WordTrace tailWord_1320130 prefixEnd_1320130 100423883914077810222791 := by
  unfold tailWord_1320130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037274176850486274825461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32099397804934630066201229 12037274176850486274825461)
  ·
    refine ⟨1128494454079733088264887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12037274176850486274825461 1128494454079733088264887)
    ·
      refine ⟨1692741681119599632397331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128494454079733088264887 1692741681119599632397331)
      ·
        refine ⟨2539112521679399448595997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692741681119599632397331 2539112521679399448595997)
        ·
          refine ⟨952167195629774793223499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2539112521679399448595997 952167195629774793223499)
          ·
            refine ⟨1428250793444662189835249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952167195629774793223499 1428250793444662189835249)
            ·
              refine ⟨1071188095083496642376437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428250793444662189835249 1071188095083496642376437)
              ·
                refine ⟨100423883914077810222791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1071188095083496642376437 100423883914077810222791)
                ·
                  rfl

theorem cell21_1320130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_1320130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320130 prefixEnd_1320130 := by exact prefixLift 1320130
  have htrace : WordTrace (prefixWord ++ tailWord_1320130) baseStart_1320130 baseEnd_1320130 := by
    simpa [prefixWord, tailWord_1320130, baseEnd_1320130] using wordTrace_append hprefix tailTrace_1320130
  have hstable : (prefixWord ++ tailWord_1320130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320130).length < 2 ^ (prefixWord ++ tailWord_1320130).sum := by decide
  have hdescent : baseEnd_1320130 < baseStart_1320130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320138 : List Nat := [3, 1, 2, 1, 3, 2, 4, 5]
def baseStart_1320138 : Nat := 118140960795 + 1320138 * 2 ^ 59
def prefixEnd_1320138 : Nat := 4983230072969 + 3 ^ 40 * 1320138 * 2
def baseEnd_1320138 : Nat := 100424492483742398178341

theorem tailTrace_1320138 : CollatzResearch.WordTrace tailWord_1320138 prefixEnd_1320138 100424492483742398178341 := by
  unfold tailWord_1320138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037347122843240616398267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32099592327581974977062045 12037347122843240616398267)
  ·
    refine ⟨18056020684264860924597401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12037347122843240616398267 18056020684264860924597401)
    ·
      refine ⟨13542015513198645693448051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18056020684264860924597401 13542015513198645693448051)
      ·
        refine ⟨20313023269797968540172077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13542015513198645693448051 20313023269797968540172077)
        ·
          refine ⟨7617383726174238202564529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20313023269797968540172077 7617383726174238202564529)
          ·
            refine ⟨5713037794630678651923397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7617383726174238202564529 5713037794630678651923397)
            ·
              refine ⟨1071194586493252247235637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5713037794630678651923397 1071194586493252247235637)
              ·
                refine ⟨100424492483742398178341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1071194586493252247235637 100424492483742398178341)
                ·
                  rfl

theorem cell21_1320138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_1320138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320138 prefixEnd_1320138 := by exact prefixLift 1320138
  have htrace : WordTrace (prefixWord ++ tailWord_1320138) baseStart_1320138 baseEnd_1320138 := by
    simpa [prefixWord, tailWord_1320138, baseEnd_1320138] using wordTrace_append hprefix tailTrace_1320138
  have hstable : (prefixWord ++ tailWord_1320138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320138).length < 2 ^ (prefixWord ++ tailWord_1320138).sum := by decide
  have hdescent : baseEnd_1320138 < baseStart_1320138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320228 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1320228 : Nat := 118140960795 + 1320228 * 2 ^ 59
def prefixEnd_1320228 : Nat := 4983230072969 + 3 ^ 40 * 1320228 * 2
def baseEnd_1320228 : Nat := 301294016677407038034839

theorem tailTrace_1320228 : CollatzResearch.WordTrace tailWord_1320228 prefixEnd_1320228 301294016677407038034839 := by
  unfold tailWord_1320228
  simp only [CollatzResearch.WordTrace]
  refine ⟨24076335530523453918184669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32101780707364605224246225 24076335530523453918184669)
  ·
    refine ⟨9028625823946295219319251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24076335530523453918184669 9028625823946295219319251)
    ·
      refine ⟨13542938735919442828978877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9028625823946295219319251 13542938735919442828978877)
      ·
        refine ⟨5078602025969791060867079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13542938735919442828978877 5078602025969791060867079)
        ·
          refine ⟨7617903038954686591300619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5078602025969791060867079 7617903038954686591300619)
          ·
            refine ⟨11426854558432029886950929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7617903038954686591300619 11426854558432029886950929)
            ·
              refine ⟨8570140918824022415213197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11426854558432029886950929 8570140918824022415213197)
              ·
                refine ⟨3213802844559008405704949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8570140918824022415213197 3213802844559008405704949)
                ·
                  refine ⟨301294016677407038034839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3213802844559008405704949 301294016677407038034839)
                  ·
                    rfl

theorem cell21_1320228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1320228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320228 prefixEnd_1320228 := by exact prefixLift 1320228
  have htrace : WordTrace (prefixWord ++ tailWord_1320228) baseStart_1320228 baseEnd_1320228 := by
    simpa [prefixWord, tailWord_1320228, baseEnd_1320228] using wordTrace_append hprefix tailTrace_1320228
  have hstable : (prefixWord ++ tailWord_1320228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320228).length < 2 ^ (prefixWord ++ tailWord_1320228).sum := by decide
  have hdescent : baseEnd_1320228 < baseStart_1320228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320349 : List Nat := [1, 4, 2, 1, 3, 1, 1, 8]
def baseStart_1320349 : Nat := 118140960795 + 1320349 * 2 ^ 59
def prefixEnd_1320349 : Nat := 4983230072969 + 3 ^ 40 * 1320349 * 2
def baseEnd_1320349 : Nat := 100440543508645905505975

theorem tailTrace_1320349 : CollatzResearch.WordTrace tailWord_1320349 prefixEnd_1320349 100440543508645905505975 := by
  unfold tailWord_1320349
  simp only [CollatzResearch.WordTrace]
  refine ⟨48157084293608545501524101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32104722862405697001016067 48157084293608545501524101)
  ·
    refine ⟨9029453305051602281535769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48157084293608545501524101 9029453305051602281535769)
    ·
      refine ⟨6772089978788701711151827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9029453305051602281535769 6772089978788701711151827)
      ·
        refine ⟨10158134968183052566727741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6772089978788701711151827 10158134968183052566727741)
        ·
          refine ⟨3809300613068644712522903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10158134968183052566727741 3809300613068644712522903)
          ·
            refine ⟨5713950919602967068784355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809300613068644712522903 5713950919602967068784355)
            ·
              refine ⟨8570926379404450603176533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5713950919602967068784355 8570926379404450603176533)
              ·
                refine ⟨100440543508645905505975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8570926379404450603176533 100440543508645905505975)
                ·
                  rfl

theorem cell21_1320349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 8].length) (baseStart_1320349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320349 prefixEnd_1320349 := by exact prefixLift 1320349
  have htrace : WordTrace (prefixWord ++ tailWord_1320349) baseStart_1320349 baseEnd_1320349 := by
    simpa [prefixWord, tailWord_1320349, baseEnd_1320349] using wordTrace_append hprefix tailTrace_1320349
  have hstable : (prefixWord ++ tailWord_1320349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320349).length < 2 ^ (prefixWord ++ tailWord_1320349).sum := by decide
  have hdescent : baseEnd_1320349 < baseStart_1320349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320501 : List Nat := [1, 3, 3, 1, 1, 5, 7]
def baseStart_1320501 : Nat := 118140960795 + 1320501 * 2 ^ 59
def prefixEnd_1320501 : Nat := 4983230072969 + 3 ^ 40 * 1320501 * 2
def baseEnd_1320501 : Nat := 33484035444091025553809

theorem tailTrace_1320501 : CollatzResearch.WordTrace tailWord_1320501 prefixEnd_1320501 33484035444091025553809 := by
  unfold tailWord_1320501
  simp only [CollatzResearch.WordTrace]
  refine ⟨48162628189057875461057357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32108418792705250307371571 48162628189057875461057357)
  ·
    refine ⟨18060985570896703297896509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48162628189057875461057357 18060985570896703297896509)
    ·
      refine ⟨6772869589086263736711191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18060985570896703297896509 6772869589086263736711191)
      ·
        refine ⟨10159304383629395605066787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6772869589086263736711191 10159304383629395605066787)
        ·
          refine ⟨15238956575444093407600181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10159304383629395605066787 15238956575444093407600181)
          ·
            refine ⟨1428652178947883756962517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15238956575444093407600181 1428652178947883756962517)
            ·
              refine ⟨33484035444091025553809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1428652178947883756962517 33484035444091025553809)
              ·
                rfl

theorem cell21_1320501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 7].length) (baseStart_1320501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320501 prefixEnd_1320501 := by exact prefixLift 1320501
  have htrace : WordTrace (prefixWord ++ tailWord_1320501) baseStart_1320501 baseEnd_1320501 := by
    simpa [prefixWord, tailWord_1320501, baseEnd_1320501] using wordTrace_append hprefix tailTrace_1320501
  have hstable : (prefixWord ++ tailWord_1320501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320501).length < 2 ^ (prefixWord ++ tailWord_1320501).sum := by decide
  have hdescent : baseEnd_1320501 < baseStart_1320501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320560 : List Nat := [2, 1, 1, 1, 6, 10]
def baseStart_1320560 : Nat := 118140960795 + 1320560 * 2 ^ 59
def prefixEnd_1320560 : Nat := 4983230072969 + 3 ^ 40 * 1320560 * 2
def baseEnd_1320560 : Nat := 11161843837061045870401

theorem tailTrace_1320560 : CollatzResearch.WordTrace tailWord_1320560 prefixEnd_1320560 11161843837061045870401 := by
  unfold tailWord_1320560
  simp only [CollatzResearch.WordTrace]
  refine ⟨24082390047922064268727567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32109853397229419024970089 24082390047922064268727567)
  ·
    refine ⟨36123585071883096403091351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24082390047922064268727567 36123585071883096403091351)
    ·
      refine ⟨54185377607824644604637027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36123585071883096403091351 54185377607824644604637027)
      ·
        refine ⟨81278066411736966906955541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54185377607824644604637027 81278066411736966906955541)
        ·
          refine ⟨3809909363050170323763541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81278066411736966906955541 3809909363050170323763541)
          ·
            refine ⟨11161843837061045870401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3809909363050170323763541 11161843837061045870401)
            ·
              rfl

theorem cell21_1320560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 10].length) (baseStart_1320560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320560 prefixEnd_1320560 := by exact prefixLift 1320560
  have htrace : WordTrace (prefixWord ++ tailWord_1320560) baseStart_1320560 baseEnd_1320560 := by
    simpa [prefixWord, tailWord_1320560, baseEnd_1320560] using wordTrace_append hprefix tailTrace_1320560
  have hstable : (prefixWord ++ tailWord_1320560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320560).length < 2 ^ (prefixWord ++ tailWord_1320560).sum := by decide
  have hdescent : baseEnd_1320560 < baseStart_1320560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320566 : List Nat := [5, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1320566 : Nat := 118140960795 + 1320566 * 2 ^ 59
def prefixEnd_1320566 : Nat := 4983230072969 + 3 ^ 40 * 1320566 * 2
def baseEnd_1320566 : Nat := 301371152882393561400815

theorem tailTrace_1320566 : CollatzResearch.WordTrace tailWord_1320566 prefixEnd_1320566 301371152882393561400815 := by
  unfold tailWord_1320566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010312433363899472635847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32109999289214927708115701 3010312433363899472635847)
  ·
    refine ⟨4515468650045849208953771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3010312433363899472635847 4515468650045849208953771)
    ·
      refine ⟨6773202975068773813430657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4515468650045849208953771 6773202975068773813430657)
      ·
        refine ⟨5079902231301580360072993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6773202975068773813430657 5079902231301580360072993)
        ·
          refine ⟨3809926673476185270054745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5079902231301580360072993 3809926673476185270054745)
          ·
            refine ⟨2857445005107138952541059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3809926673476185270054745 2857445005107138952541059)
            ·
              refine ⟨4286167507660708428811589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857445005107138952541059 4286167507660708428811589)
              ·
                refine ⟨803656407686382830402173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4286167507660708428811589 803656407686382830402173)
                ·
                  refine ⟨301371152882393561400815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803656407686382830402173 301371152882393561400815)
                  ·
                    rfl

theorem cell21_1320566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1320566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320566 prefixEnd_1320566 := by exact prefixLift 1320566
  have htrace : WordTrace (prefixWord ++ tailWord_1320566) baseStart_1320566 baseEnd_1320566 := by
    simpa [prefixWord, tailWord_1320566, baseEnd_1320566] using wordTrace_append hprefix tailTrace_1320566
  have hstable : (prefixWord ++ tailWord_1320566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320566).length < 2 ^ (prefixWord ++ tailWord_1320566).sum := by decide
  have hdescent : baseEnd_1320566 < baseStart_1320566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320577 : List Nat := [1, 2, 4, 2, 1, 2, 3, 6]
def baseStart_1320577 : Nat := 118140960795 + 1320577 * 2 ^ 59
def prefixEnd_1320577 : Nat := 4983230072969 + 3 ^ 40 * 1320577 * 2
def baseEnd_1320577 : Nat := 100457887744086662239153

theorem tailTrace_1320577 : CollatzResearch.WordTrace tailWord_1320577 prefixEnd_1320577 100457887744086662239153 := by
  unfold tailWord_1320577
  simp only [CollatzResearch.WordTrace]
  refine ⟨48165400136782540440823985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32110266757855026960549323 48165400136782540440823985)
  ·
    refine ⟨36124050102586905330617989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48165400136782540440823985 36124050102586905330617989)
    ·
      refine ⟨6773259394235044749490873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36124050102586905330617989 6773259394235044749490873)
      ·
        refine ⟨5079944545676283562118155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6773259394235044749490873 5079944545676283562118155)
        ·
          refine ⟨7619916818514425343177233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5079944545676283562118155 7619916818514425343177233)
          ·
            refine ⟨5714937613885819007382925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7619916818514425343177233 5714937613885819007382925)
            ·
              refine ⟨2143101605207182127768597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5714937613885819007382925 2143101605207182127768597)
              ·
                refine ⟨100457887744086662239153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2143101605207182127768597 100457887744086662239153)
                ·
                  rfl

theorem cell21_1320577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 6].length) (baseStart_1320577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320577 prefixEnd_1320577 := by exact prefixLift 1320577
  have htrace : WordTrace (prefixWord ++ tailWord_1320577) baseStart_1320577 baseEnd_1320577 := by
    simpa [prefixWord, tailWord_1320577, baseEnd_1320577] using wordTrace_append hprefix tailTrace_1320577
  have hstable : (prefixWord ++ tailWord_1320577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320577).length < 2 ^ (prefixWord ++ tailWord_1320577).sum := by decide
  have hdescent : baseEnd_1320577 < baseStart_1320577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320639 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 4]
def baseStart_1320639 : Nat := 118140960795 + 1320639 * 2 ^ 59
def prefixEnd_1320639 : Nat := 4983230072969 + 3 ^ 40 * 1320639 * 2
def baseEnd_1320639 : Nat := 301387812476961656683999

theorem tailTrace_1320639 : CollatzResearch.WordTrace tailWord_1320639 prefixEnd_1320639 301387812476961656683999 := by
  unfold tailWord_1320639
  simp only [CollatzResearch.WordTrace]
  refine ⟨48167661462557925029580971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32111774308371950019720647 48167661462557925029580971)
  ·
    refine ⟨72251492193836887544371457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48167661462557925029580971 72251492193836887544371457)
    ·
      refine ⟨54188619145377665658278593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72251492193836887544371457 54188619145377665658278593)
      ·
        refine ⟨40641464359033249243708945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54188619145377665658278593 40641464359033249243708945)
        ·
          refine ⟨30481098269274936932781709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40641464359033249243708945 30481098269274936932781709)
          ·
            refine ⟨11430411850978101349793141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30481098269274936932781709 11430411850978101349793141)
            ·
              refine ⟨1071601111029197001543107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11430411850978101349793141 1071601111029197001543107)
              ·
                refine ⟨1607401666543795502314661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071601111029197001543107 1607401666543795502314661)
                ·
                  refine ⟨301387812476961656683999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1607401666543795502314661 301387812476961656683999)
                  ·
                    rfl

theorem cell21_1320639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 4].length) (baseStart_1320639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320639 prefixEnd_1320639 := by exact prefixLift 1320639
  have htrace : WordTrace (prefixWord ++ tailWord_1320639) baseStart_1320639 baseEnd_1320639 := by
    simpa [prefixWord, tailWord_1320639, baseEnd_1320639] using wordTrace_append hprefix tailTrace_1320639
  have hstable : (prefixWord ++ tailWord_1320639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320639).length < 2 ^ (prefixWord ++ tailWord_1320639).sum := by decide
  have hdescent : baseEnd_1320639 < baseStart_1320639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320684 : List Nat := [2, 2, 1, 1, 2, 2, 2, 6, 3]
def baseStart_1320684 : Nat := 118140960795 + 1320684 * 2 ^ 59
def prefixEnd_1320684 : Nat := 4983230072969 + 3 ^ 40 * 1320684 * 2
def baseEnd_1320684 : Nat := 301398082090051578433907

theorem tailTrace_1320684 : CollatzResearch.WordTrace tailWord_1320684 prefixEnd_1320684 301398082090051578433907 := by
  unfold tailWord_1320684
  simp only [CollatzResearch.WordTrace]
  refine ⟨24084651373697448857484553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32112868498263265143312737 24084651373697448857484553)
  ·
    refine ⟨18063488530273086643113415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24084651373697448857484553 18063488530273086643113415)
    ·
      refine ⟨27095232795409629964670123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18063488530273086643113415 27095232795409629964670123)
      ·
        refine ⟨40642849193114444947005185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27095232795409629964670123 40642849193114444947005185)
        ·
          refine ⟨30482136894835833710253889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40642849193114444947005185 30482136894835833710253889)
          ·
            refine ⟨22861602671126875282690417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30482136894835833710253889 22861602671126875282690417)
            ·
              refine ⟨17146202003345156462017813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22861602671126875282690417 17146202003345156462017813)
              ·
                refine ⟨803728218906804209157085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17146202003345156462017813 803728218906804209157085)
                ·
                  refine ⟨301398082090051578433907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803728218906804209157085 301398082090051578433907)
                  ·
                    rfl

theorem cell21_1320684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_1320684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320684 prefixEnd_1320684 := by exact prefixLift 1320684
  have htrace : WordTrace (prefixWord ++ tailWord_1320684) baseStart_1320684 baseEnd_1320684 := by
    simpa [prefixWord, tailWord_1320684, baseEnd_1320684] using wordTrace_append hprefix tailTrace_1320684
  have hstable : (prefixWord ++ tailWord_1320684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320684).length < 2 ^ (prefixWord ++ tailWord_1320684).sum := by decide
  have hdescent : baseEnd_1320684 < baseStart_1320684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320712 : List Nat := [2, 1, 3, 2, 2, 1, 1, 9]
def baseStart_1320712 : Nat := 118140960795 + 1320712 * 2 ^ 59
def prefixEnd_1320712 : Nat := 4983230072969 + 3 ^ 40 * 1320712 * 2
def baseEnd_1320712 : Nat := 100468157357176583989061

theorem tailTrace_1320712 : CollatzResearch.WordTrace tailWord_1320712 prefixEnd_1320712 100468157357176583989061 := by
  unfold tailWord_1320712
  simp only [CollatzResearch.WordTrace]
  refine ⟨24085161995646729248494195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32113549327528972331325593 24085161995646729248494195)
  ·
    refine ⟨36127742993470093872741293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24085161995646729248494195 36127742993470093872741293)
    ·
      refine ⟨13547903622551285202277985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36127742993470093872741293 13547903622551285202277985)
      ·
        refine ⟨10160927716913463901708489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13547903622551285202277985 10160927716913463901708489)
        ·
          refine ⟨7620695787685097926281367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10160927716913463901708489 7620695787685097926281367)
          ·
            refine ⟨11431043681527646889422051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7620695787685097926281367 11431043681527646889422051)
            ·
              refine ⟨17146565522291470334133077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11431043681527646889422051 17146565522291470334133077)
              ·
                refine ⟨100468157357176583989061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17146565522291470334133077 100468157357176583989061)
                ·
                  rfl

theorem cell21_1320712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_1320712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320712 prefixEnd_1320712 := by exact prefixLift 1320712
  have htrace : WordTrace (prefixWord ++ tailWord_1320712) baseStart_1320712 baseEnd_1320712 := by
    simpa [prefixWord, tailWord_1320712, baseEnd_1320712] using wordTrace_append hprefix tailTrace_1320712
  have hstable : (prefixWord ++ tailWord_1320712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320712).length < 2 ^ (prefixWord ++ tailWord_1320712).sum := by decide
  have hdescent : baseEnd_1320712 < baseStart_1320712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320822 : List Nat := [5, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1320822 : Nat := 118140960795 + 1320822 * 2 ^ 59
def prefixEnd_1320822 : Nat := 4983230072969 + 3 ^ 40 * 1320822 * 2
def baseEnd_1320822 : Nat := 100476525190064668377875

theorem tailTrace_1320822 : CollatzResearch.WordTrace tailWord_1320822 prefixEnd_1320822 100476525190064668377875 := by
  unfold tailWord_1320822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010896001305934205218295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32116224013929964855661813 3010896001305934205218295)
  ·
    refine ⟨4516344001958901307827443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3010896001305934205218295 4516344001958901307827443)
    ·
      refine ⟨6774516002938351961741165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4516344001958901307827443 6774516002938351961741165)
      ·
        refine ⟨2540443501101881985652937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6774516002938351961741165 2540443501101881985652937)
        ·
          refine ⟨1905332625826411489239703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2540443501101881985652937 1905332625826411489239703)
          ·
            refine ⟨2857998938739617233859555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905332625826411489239703 2857998938739617233859555)
            ·
              refine ⟨4286998408109425850789333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857998938739617233859555 4286998408109425850789333)
              ·
                refine ⟨100476525190064668377875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4286998408109425850789333 100476525190064668377875)
                ·
                  rfl

theorem cell21_1320822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1320822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320822 prefixEnd_1320822 := by exact prefixLift 1320822
  have htrace : WordTrace (prefixWord ++ tailWord_1320822) baseStart_1320822 baseEnd_1320822 := by
    simpa [prefixWord, tailWord_1320822, baseEnd_1320822] using wordTrace_append hprefix tailTrace_1320822
  have hstable : (prefixWord ++ tailWord_1320822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320822).length < 2 ^ (prefixWord ++ tailWord_1320822).sum := by decide
  have hdescent : baseEnd_1320822 < baseStart_1320822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320853 : List Nat := [1, 3, 2, 1, 1, 3, 5, 2, 3]
def baseStart_1320853 : Nat := 118140960795 + 1320853 * 2 ^ 59
def prefixEnd_1320853 : Nat := 4983230072969 + 3 ^ 40 * 1320853 * 2
def baseEnd_1320853 : Nat := 301436650192544840116895

theorem tailTrace_1320853 : CollatzResearch.WordTrace tailWord_1320853 prefixEnd_1320853 301436650192544840116895 := by
  unfold tailWord_1320853
  simp only [CollatzResearch.WordTrace]
  refine ⟨48175466683782639577871213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32116977789188426385247475 48175466683782639577871213)
  ·
    refine ⟨18065800006418489841701705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48175466683782639577871213 18065800006418489841701705)
    ·
      refine ⟨13549350004813867381276279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18065800006418489841701705 13549350004813867381276279)
      ·
        refine ⟨20324025007220801071914419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13549350004813867381276279 20324025007220801071914419)
        ·
          refine ⟨30486037510831201607871629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20324025007220801071914419 30486037510831201607871629)
          ·
            refine ⟨11432264066561700602951861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30486037510831201607871629 11432264066561700602951861)
            ·
              refine ⟨1071774756240159431526737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11432264066561700602951861 1071774756240159431526737)
              ·
                refine ⟨803831067180119573645053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071774756240159431526737 803831067180119573645053)
                ·
                  refine ⟨301436650192544840116895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803831067180119573645053 301436650192544840116895)
                  ·
                    rfl

theorem cell21_1320853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_1320853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320853 prefixEnd_1320853 := by exact prefixLift 1320853
  have htrace : WordTrace (prefixWord ++ tailWord_1320853) baseStart_1320853 baseEnd_1320853 := by
    simpa [prefixWord, tailWord_1320853, baseEnd_1320853] using wordTrace_append hprefix tailTrace_1320853
  have hstable : (prefixWord ++ tailWord_1320853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320853).length < 2 ^ (prefixWord ++ tailWord_1320853).sum := by decide
  have hdescent : baseEnd_1320853 < baseStart_1320853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320971 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 5]
def baseStart_1320971 : Nat := 118140960795 + 1320971 * 2 ^ 59
def prefixEnd_1320971 : Nat := 4983230072969 + 3 ^ 40 * 1320971 * 2
def baseEnd_1320971 : Nat := 301463579400202857149987

theorem tailTrace_1320971 : CollatzResearch.WordTrace tailWord_1320971 prefixEnd_1320971 301463579400202857149987 := by
  unfold tailWord_1320971
  simp only [CollatzResearch.WordTrace]
  refine ⟨48179770497355145730666767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32119846998236763820444511 48179770497355145730666767)
  ·
    refine ⟨72269655746032718596000151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48179770497355145730666767 72269655746032718596000151)
    ·
      refine ⟨108404483619049077894000227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72269655746032718596000151 108404483619049077894000227)
      ·
        refine ⟨162606725428573616841000341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108404483619049077894000227 162606725428573616841000341)
        ·
          refine ⟨7622190254464388289421891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 162606725428573616841000341 7622190254464388289421891)
          ·
            refine ⟨11433285381696582434132837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7622190254464388289421891 11433285381696582434132837)
            ·
              refine ⟨2143741009068109206399907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11433285381696582434132837 2143741009068109206399907)
              ·
                refine ⟨3215611513602163809599861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143741009068109206399907 3215611513602163809599861)
                ·
                  refine ⟨301463579400202857149987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3215611513602163809599861 301463579400202857149987)
                  ·
                    rfl

theorem cell21_1320971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 5].length) (baseStart_1320971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1320971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1320971 prefixEnd_1320971 := by exact prefixLift 1320971
  have htrace : WordTrace (prefixWord ++ tailWord_1320971) baseStart_1320971 baseEnd_1320971 := by
    simpa [prefixWord, tailWord_1320971, baseEnd_1320971] using wordTrace_append hprefix tailTrace_1320971
  have hstable : (prefixWord ++ tailWord_1320971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320971).length < 2 ^ (prefixWord ++ tailWord_1320971).sum := by decide
  have hdescent : baseEnd_1320971 < baseStart_1320971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321002 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_1321002 : Nat := 118140960795 + 1321002 * 2 ^ 59
def prefixEnd_1321002 : Nat := 4983230072969 + 3 ^ 40 * 1321002 * 2
def baseEnd_1321002 : Nat := 301470654022553692133257

theorem tailTrace_1321002 : CollatzResearch.WordTrace tailWord_1321002 prefixEnd_1321002 301470654022553692133257 := by
  unfold tailWord_1321002
  simp only [CollatzResearch.WordTrace]
  refine ⟨12045225290060709506261315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32120600773495225350030173 12045225290060709506261315)
  ·
    refine ⟨18067837935091064259391973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12045225290060709506261315 18067837935091064259391973)
    ·
      refine ⟨3387719612829574548635995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18067837935091064259391973 3387719612829574548635995)
      ·
        refine ⟨5081579419244361822953993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3387719612829574548635995 5081579419244361822953993)
        ·
          refine ⟨3811184564433271367215495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5081579419244361822953993 3811184564433271367215495)
          ·
            refine ⟨5716776846649907050823243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811184564433271367215495 5716776846649907050823243)
            ·
              refine ⟨8575165269974860576234865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5716776846649907050823243 8575165269974860576234865)
              ·
                refine ⟨6431373952481145432176149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8575165269974860576234865 6431373952481145432176149)
                ·
                  refine ⟨301470654022553692133257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6431373952481145432176149 301470654022553692133257)
                  ·
                    rfl

theorem cell21_1321002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_1321002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321002 prefixEnd_1321002 := by exact prefixLift 1321002
  have htrace : WordTrace (prefixWord ++ tailWord_1321002) baseStart_1321002 baseEnd_1321002 := by
    simpa [prefixWord, tailWord_1321002, baseEnd_1321002] using wordTrace_append hprefix tailTrace_1321002
  have hstable : (prefixWord ++ tailWord_1321002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321002).length < 2 ^ (prefixWord ++ tailWord_1321002).sum := by decide
  have hdescent : baseEnd_1321002 < baseStart_1321002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321022 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_1321022 : Nat := 118140960795 + 1321022 * 2 ^ 59
def prefixEnd_1321022 : Nat := 4983230072969 + 3 ^ 40 * 1321022 * 2
def baseEnd_1321022 : Nat := 301475218295038101799883

theorem tailTrace_1321022 : CollatzResearch.WordTrace tailWord_1321022 prefixEnd_1321022 301475218295038101799883 := by
  unfold tailWord_1321022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6022703827521297680096665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32121087080113587627182213 6022703827521297680096665)
  ·
    refine ⟨4517027870640973260072499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6022703827521297680096665 4517027870640973260072499)
    ·
      refine ⟨6775541805961459890108749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4517027870640973260072499 6775541805961459890108749)
      ·
        refine ⟨2540828177235547458790781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6775541805961459890108749 2540828177235547458790781)
        ·
          refine ⟨952810566463330297046543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2540828177235547458790781 952810566463330297046543)
          ·
            refine ⟨1429215849694995445569815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952810566463330297046543 1429215849694995445569815)
            ·
              refine ⟨2143823774542493168354723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429215849694995445569815 2143823774542493168354723)
              ·
                refine ⟨3215735661813739752532085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143823774542493168354723 3215735661813739752532085)
                ·
                  refine ⟨301475218295038101799883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3215735661813739752532085 301475218295038101799883)
                  ·
                    rfl

theorem cell21_1321022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_1321022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321022 prefixEnd_1321022 := by exact prefixLift 1321022
  have htrace : WordTrace (prefixWord ++ tailWord_1321022) baseStart_1321022 baseEnd_1321022 := by
    simpa [prefixWord, tailWord_1321022, baseEnd_1321022] using wordTrace_append hprefix tailTrace_1321022
  have hstable : (prefixWord ++ tailWord_1321022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321022).length < 2 ^ (prefixWord ++ tailWord_1321022).sum := by decide
  have hdescent : baseEnd_1321022 < baseStart_1321022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321081 : List Nat := [1, 2, 1, 3, 4, 1, 4, 2, 3]
def baseStart_1321081 : Nat := 118140960795 + 1321081 * 2 ^ 59
def prefixEnd_1321081 : Nat := 4983230072969 + 3 ^ 40 * 1321081 * 2
def baseEnd_1321081 : Nat := 301488682898867110316429

theorem tailTrace_1321081 : CollatzResearch.WordTrace tailWord_1321081 prefixEnd_1321081 301488682898867110316429 := by
  unfold tailWord_1321081
  simp only [CollatzResearch.WordTrace]
  refine ⟨48183782526956634517171097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32122521684637756344780731 48183782526956634517171097)
  ·
    refine ⟨36137836895217475887878323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48183782526956634517171097 36137836895217475887878323)
    ·
      refine ⟨54206755342826213831817485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36137836895217475887878323 54206755342826213831817485)
      ·
        refine ⟨20327533253559830186931557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54206755342826213831817485 20327533253559830186931557)
        ·
          refine ⟨3811412485042468160049667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20327533253559830186931557 3811412485042468160049667)
          ·
            refine ⟨5717118727563702240074501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811412485042468160049667 5717118727563702240074501)
            ·
              refine ⟨1071959761418194170013969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5717118727563702240074501 1071959761418194170013969)
              ·
                refine ⟨803969821063645627510477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071959761418194170013969 803969821063645627510477)
                ·
                  refine ⟨301488682898867110316429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803969821063645627510477 301488682898867110316429)
                  ·
                    rfl

theorem cell21_1321081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_1321081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321081 prefixEnd_1321081 := by exact prefixLift 1321081
  have htrace : WordTrace (prefixWord ++ tailWord_1321081) baseStart_1321081 baseEnd_1321081 := by
    simpa [prefixWord, tailWord_1321081, baseEnd_1321081] using wordTrace_append hprefix tailTrace_1321081
  have hstable : (prefixWord ++ tailWord_1321081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321081).length < 2 ^ (prefixWord ++ tailWord_1321081).sum := by decide
  have hdescent : baseEnd_1321081 < baseStart_1321081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321151 : List Nat := [1, 1, 2, 2, 2, 2, 1, 10]
def baseStart_1321151 : Nat := 118140960795 + 1321151 * 2 ^ 59
def prefixEnd_1321151 : Nat := 4983230072969 + 3 ^ 40 * 1321151 * 2
def baseEnd_1321151 : Nat := 100501552617520848049873

theorem tailTrace_1321151 : CollatzResearch.WordTrace tailWord_1321151 prefixEnd_1321151 100501552617520848049873 := by
  unfold tailWord_1321151
  simp only [CollatzResearch.WordTrace]
  refine ⟨48186335636703036472219307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32124223757802024314812871 48186335636703036472219307)
  ·
    refine ⟨72279503455054554708328961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48186335636703036472219307 72279503455054554708328961)
    ·
      refine ⟨54209627591290916031246721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72279503455054554708328961 54209627591290916031246721)
      ·
        refine ⟨40657220693468187023435041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54209627591290916031246721 40657220693468187023435041)
        ·
          refine ⟨30492915520101140267576281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40657220693468187023435041 30492915520101140267576281)
          ·
            refine ⟨22869686640075855200682211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30492915520101140267576281 22869686640075855200682211)
            ·
              refine ⟨34304529960113782801023317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22869686640075855200682211 34304529960113782801023317)
              ·
                refine ⟨100501552617520848049873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34304529960113782801023317 100501552617520848049873)
                ·
                  rfl

theorem cell21_1321151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 10].length) (baseStart_1321151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321151 prefixEnd_1321151 := by exact prefixLift 1321151
  have htrace : WordTrace (prefixWord ++ tailWord_1321151) baseStart_1321151 baseEnd_1321151 := by
    simpa [prefixWord, tailWord_1321151, baseEnd_1321151] using wordTrace_append hprefix tailTrace_1321151
  have hstable : (prefixWord ++ tailWord_1321151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321151).length < 2 ^ (prefixWord ++ tailWord_1321151).sum := by decide
  have hdescent : baseEnd_1321151 < baseStart_1321151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321174 : List Nat := [5, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1321174 : Nat := 118140960795 + 1321174 * 2 ^ 59
def prefixEnd_1321174 : Nat := 4983230072969 + 3 ^ 40 * 1321174 * 2
def baseEnd_1321174 : Nat := 301509906765919615266239

theorem tailTrace_1321174 : CollatzResearch.WordTrace tailWord_1321174 prefixEnd_1321174 301509906765919615266239 := by
  unfold tailWord_1321174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011698407226231962519161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32124783010413140933537717 3011698407226231962519161)
  ·
    refine ⟨2258773805419673971889371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3011698407226231962519161 2258773805419673971889371)
    ·
      refine ⟨3388160708129510957834057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258773805419673971889371 3388160708129510957834057)
      ·
        refine ⟨2541120531097133218375543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3388160708129510957834057 2541120531097133218375543)
        ·
          refine ⟨3811680796645699827563315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541120531097133218375543 3811680796645699827563315)
          ·
            refine ⟨5717521194968549741344973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811680796645699827563315 5717521194968549741344973)
            ·
              refine ⟨2144070448113206153004365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5717521194968549741344973 2144070448113206153004365)
              ·
                refine ⟨804026418042452307376637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2144070448113206153004365 804026418042452307376637)
                ·
                  refine ⟨301509906765919615266239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804026418042452307376637 301509906765919615266239)
                  ·
                    rfl

theorem cell21_1321174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1321174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321174 prefixEnd_1321174 := by exact prefixLift 1321174
  have htrace : WordTrace (prefixWord ++ tailWord_1321174) baseStart_1321174 baseEnd_1321174 := by
    simpa [prefixWord, tailWord_1321174, baseEnd_1321174] using wordTrace_append hprefix tailTrace_1321174
  have hstable : (prefixWord ++ tailWord_1321174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321174).length < 2 ^ (prefixWord ++ tailWord_1321174).sum := by decide
  have hdescent : baseEnd_1321174 < baseStart_1321174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321199 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 5]
def baseStart_1321199 : Nat := 118140960795 + 1321199 * 2 ^ 59
def prefixEnd_1321199 : Nat := 4983230072969 + 3 ^ 40 * 1321199 * 2
def baseEnd_1321199 : Nat := 301515612106525127349521

theorem tailTrace_1321199 : CollatzResearch.WordTrace tailWord_1321199 prefixEnd_1321199 301515612106525127349521 := by
  unfold tailWord_1321199
  simp only [CollatzResearch.WordTrace]
  refine ⟨48188086340529140669966651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32125390893686093779977767 48188086340529140669966651)
  ·
    refine ⟨72282129510793711004949977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48188086340529140669966651 72282129510793711004949977)
    ·
      refine ⟨54211597133095283253712483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72282129510793711004949977 54211597133095283253712483)
      ·
        refine ⟨81317395699642924880568725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54211597133095283253712483 81317395699642924880568725)
        ·
          refine ⟨3811752923420762103776659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81317395699642924880568725 3811752923420762103776659)
          ·
            refine ⟨5717629385131143155664989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811752923420762103776659 5717629385131143155664989)
            ·
              refine ⟨2144111019424178683374371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5717629385131143155664989 2144111019424178683374371)
              ·
                refine ⟨3216166529136268025061557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144111019424178683374371 3216166529136268025061557)
                ·
                  refine ⟨301515612106525127349521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3216166529136268025061557 301515612106525127349521)
                  ·
                    rfl

theorem cell21_1321199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 5].length) (baseStart_1321199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321199 prefixEnd_1321199 := by exact prefixLift 1321199
  have htrace : WordTrace (prefixWord ++ tailWord_1321199) baseStart_1321199 baseEnd_1321199 := by
    simpa [prefixWord, tailWord_1321199, baseEnd_1321199] using wordTrace_append hprefix tailTrace_1321199
  have hstable : (prefixWord ++ tailWord_1321199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321199).length < 2 ^ (prefixWord ++ tailWord_1321199).sum := by decide
  have hdescent : baseEnd_1321199 < baseStart_1321199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321227 : List Nat := [1, 1, 1, 1, 5, 2, 1, 9]
def baseStart_1321227 : Nat := 118140960795 + 1321227 * 2 ^ 59
def prefixEnd_1321227 : Nat := 4983230072969 + 3 ^ 40 * 1321227 * 2
def baseEnd_1321227 : Nat := 100507334029334433627599

theorem tailTrace_1321227 : CollatzResearch.WordTrace tailWord_1321227 prefixEnd_1321227 100507334029334433627599 := by
  unfold tailWord_1321227
  simp only [CollatzResearch.WordTrace]
  refine ⟨48189107584427701451985935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32126071722951800967990623 48189107584427701451985935)
  ·
    refine ⟨72283661376641552177978903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48189107584427701451985935 72283661376641552177978903)
    ·
      refine ⟨108425492064962328266968355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72283661376641552177978903 108425492064962328266968355)
      ·
        refine ⟨162638238097443492400452533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108425492064962328266968355 162638238097443492400452533)
        ·
          refine ⟨15247334821635327412542425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162638238097443492400452533 15247334821635327412542425)
          ·
            refine ⟨11435501116226495559406819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15247334821635327412542425 11435501116226495559406819)
            ·
              refine ⟨17153251674339743339110229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11435501116226495559406819 17153251674339743339110229)
              ·
                refine ⟨100507334029334433627599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17153251674339743339110229 100507334029334433627599)
                ·
                  rfl

theorem cell21_1321227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 9].length) (baseStart_1321227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321227 prefixEnd_1321227 := by exact prefixLift 1321227
  have htrace : WordTrace (prefixWord ++ tailWord_1321227) baseStart_1321227 baseEnd_1321227 := by
    simpa [prefixWord, tailWord_1321227, baseEnd_1321227] using wordTrace_append hprefix tailTrace_1321227
  have hstable : (prefixWord ++ tailWord_1321227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321227).length < 2 ^ (prefixWord ++ tailWord_1321227).sum := by decide
  have hdescent : baseEnd_1321227 < baseStart_1321227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321250 : List Nat := [3, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1321250 : Nat := 118140960795 + 1321250 * 2 ^ 59
def prefixEnd_1321250 : Nat := 4983230072969 + 3 ^ 40 * 1321250 * 2
def baseEnd_1321250 : Nat := 301527251001360371999417

theorem tailTrace_1321250 : CollatzResearch.WordTrace tailWord_1321250 prefixEnd_1321250 301527251001360371999417 := by
  unfold tailWord_1321250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12047486615836094095018301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32126630975562917586715469 12047486615836094095018301)
  ·
    refine ⟨4517807480938535285631863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12047486615836094095018301 4517807480938535285631863)
    ·
      refine ⟨6776711221407802928447795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4517807480938535285631863 6776711221407802928447795)
      ·
        refine ⟨10165066832111704392671693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6776711221407802928447795 10165066832111704392671693)
        ·
          refine ⟨3811900062041889147251885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10165066832111704392671693 3811900062041889147251885)
          ·
            refine ⟨1429462523265708430219457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3811900062041889147251885 1429462523265708430219457)
            ·
              refine ⟨1072096892449281322664593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1429462523265708430219457 1072096892449281322664593)
              ·
                refine ⟨804072669336960991998445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072096892449281322664593 804072669336960991998445)
                ·
                  refine ⟨301527251001360371999417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804072669336960991998445 301527251001360371999417)
                  ·
                    rfl

theorem cell21_1321250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1321250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321250 prefixEnd_1321250 := by exact prefixLift 1321250
  have htrace : WordTrace (prefixWord ++ tailWord_1321250) baseStart_1321250 baseEnd_1321250 := by
    simpa [prefixWord, tailWord_1321250, baseEnd_1321250] using wordTrace_append hprefix tailTrace_1321250
  have hstable : (prefixWord ++ tailWord_1321250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321250).length < 2 ^ (prefixWord ++ tailWord_1321250).sum := by decide
  have hdescent : baseEnd_1321250 < baseStart_1321250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321292 : List Nat := [2, 2, 1, 3, 2, 1, 4, 3, 3]
def baseStart_1321292 : Nat := 118140960795 + 1321292 * 2 ^ 59
def prefixEnd_1321292 : Nat := 4983230072969 + 3 ^ 40 * 1321292 * 2
def baseEnd_1321292 : Nat := 301536835973577632299331

theorem tailTrace_1321292 : CollatzResearch.WordTrace tailWord_1321292 prefixEnd_1321292 301536835973577632299331 := by
  unfold tailWord_1321292
  simp only [CollatzResearch.WordTrace]
  refine ⟨24095739164596108776551065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32127652219461478368734753 24095739164596108776551065)
  ·
    refine ⟨18071804373447081582413299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24095739164596108776551065 18071804373447081582413299)
    ·
      refine ⟨27107706560170622373619949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18071804373447081582413299 27107706560170622373619949)
      ·
        refine ⟨10165389960063983390107481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27107706560170622373619949 10165389960063983390107481)
        ·
          refine ⟨7624042470047987542580611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10165389960063983390107481 7624042470047987542580611)
          ·
            refine ⟨11436063705071981313870917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7624042470047987542580611 11436063705071981313870917)
            ·
              refine ⟨2144261944700996496350797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11436063705071981313870917 2144261944700996496350797)
              ·
                refine ⟨804098229262873686131549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2144261944700996496350797 804098229262873686131549)
                ·
                  refine ⟨301536835973577632299331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804098229262873686131549 301536835973577632299331)
                  ·
                    rfl

theorem cell21_1321292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_1321292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321292 prefixEnd_1321292 := by exact prefixLift 1321292
  have htrace : WordTrace (prefixWord ++ tailWord_1321292) baseStart_1321292 baseEnd_1321292 := by
    simpa [prefixWord, tailWord_1321292, baseEnd_1321292] using wordTrace_append hprefix tailTrace_1321292
  have hstable : (prefixWord ++ tailWord_1321292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321292).length < 2 ^ (prefixWord ++ tailWord_1321292).sum := by decide
  have hdescent : baseEnd_1321292 < baseStart_1321292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321303 : List Nat := [1, 1, 3, 2, 3, 1, 10]
def baseStart_1321303 : Nat := 118140960795 + 1321303 * 2 ^ 59
def prefixEnd_1321303 : Nat := 4983230072969 + 3 ^ 40 * 1321303 * 2
def baseEnd_1321303 : Nat := 33504371813716006401775

theorem tailTrace_1321303 : CollatzResearch.WordTrace tailWord_1321303 prefixEnd_1321303 33504371813716006401775 := by
  unfold tailWord_1321303
  simp only [CollatzResearch.WordTrace]
  refine ⟨48191879532152366431752563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32127919688101577621168375 48191879532152366431752563)
  ·
    refine ⟨72287819298228549647628845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48191879532152366431752563 72287819298228549647628845)
    ·
      refine ⟨27107932236835706117860817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72287819298228549647628845 27107932236835706117860817)
      ·
        refine ⟨20330949177626779588395613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27107932236835706117860817 20330949177626779588395613)
        ·
          refine ⟨7624105941610042345648355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20330949177626779588395613 7624105941610042345648355)
          ·
            refine ⟨11436158912415063518472533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7624105941610042345648355 11436158912415063518472533)
            ·
              refine ⟨33504371813716006401775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11436158912415063518472533 33504371813716006401775)
              ·
                rfl

theorem cell21_1321303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 10].length) (baseStart_1321303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321303 prefixEnd_1321303 := by exact prefixLift 1321303
  have htrace : WordTrace (prefixWord ++ tailWord_1321303) baseStart_1321303 baseEnd_1321303 := by
    simpa [prefixWord, tailWord_1321303, baseEnd_1321303] using wordTrace_append hprefix tailTrace_1321303
  have hstable : (prefixWord ++ tailWord_1321303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321303).length < 2 ^ (prefixWord ++ tailWord_1321303).sum := by decide
  have hdescent : baseEnd_1321303 < baseStart_1321303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321354 : List Nat := [3, 1, 2, 5, 2, 1, 7]
def baseStart_1321354 : Nat := 118140960795 + 1321354 * 2 ^ 59
def prefixEnd_1321354 : Nat := 4983230072969 + 3 ^ 40 * 1321354 * 2
def baseEnd_1321354 : Nat := 33505665024253255807319

theorem tailTrace_1321354 : CollatzResearch.WordTrace tailWord_1321354 prefixEnd_1321354 33505665024253255807319 := by
  unfold tailWord_1321354
  simp only [CollatzResearch.WordTrace]
  refine ⟨12048434913741900535464779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32129159769978401427906077 12048434913741900535464779)
  ·
    refine ⟨18072652370612850803197169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12048434913741900535464779 18072652370612850803197169)
    ·
      refine ⟨13554489277959638102397877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18072652370612850803197169 13554489277959638102397877)
      ·
        refine ⟨1270733369808716072099801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13554489277959638102397877 1270733369808716072099801)
        ·
          refine ⟨953050027356537054074851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1270733369808716072099801 953050027356537054074851)
          ·
            refine ⟨1429575041034805581112277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953050027356537054074851 1429575041034805581112277)
            ·
              refine ⟨33505665024253255807319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1429575041034805581112277 33505665024253255807319)
              ·
                rfl

theorem cell21_1321354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 7].length) (baseStart_1321354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321354 prefixEnd_1321354 := by exact prefixLift 1321354
  have htrace : WordTrace (prefixWord ++ tailWord_1321354) baseStart_1321354 baseEnd_1321354 := by
    simpa [prefixWord, tailWord_1321354, baseEnd_1321354] using wordTrace_append hprefix tailTrace_1321354
  have hstable : (prefixWord ++ tailWord_1321354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321354).length < 2 ^ (prefixWord ++ tailWord_1321354).sum := by decide
  have hdescent : baseEnd_1321354 < baseStart_1321354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321365 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 4]
def baseStart_1321365 : Nat := 118140960795 + 1321365 * 2 ^ 59
def prefixEnd_1321365 : Nat := 4983230072969 + 3 ^ 40 * 1321365 * 2
def baseEnd_1321365 : Nat := 301553495568145727582515

theorem tailTrace_1321365 : CollatzResearch.WordTrace tailWord_1321365 prefixEnd_1321365 301553495568145727582515 := by
  unfold tailWord_1321365
  simp only [CollatzResearch.WordTrace]
  refine ⟨48194140857927751020509549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32129427238618500680339699 48194140857927751020509549)
  ·
    refine ⟨18072802821722906632691081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48194140857927751020509549 18072802821722906632691081)
    ·
      refine ⟨13554602116292179974518311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18072802821722906632691081 13554602116292179974518311)
      ·
        refine ⟨20331903174438269961777467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13554602116292179974518311 20331903174438269961777467)
        ·
          refine ⟨30497854761657404942666201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20331903174438269961777467 30497854761657404942666201)
          ·
            refine ⟨22873391071243053706999651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30497854761657404942666201 22873391071243053706999651)
            ·
              refine ⟨34310086606864580560499477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22873391071243053706999651 34310086606864580560499477)
              ·
                refine ⟨1608285309696777213773413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34310086606864580560499477 1608285309696777213773413)
                ·
                  refine ⟨301553495568145727582515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608285309696777213773413 301553495568145727582515)
                  ·
                    rfl

theorem cell21_1321365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_1321365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321365 prefixEnd_1321365 := by exact prefixLift 1321365
  have htrace : WordTrace (prefixWord ++ tailWord_1321365) baseStart_1321365 baseEnd_1321365 := by
    simpa [prefixWord, tailWord_1321365, baseEnd_1321365] using wordTrace_append hprefix tailTrace_1321365
  have hstable : (prefixWord ++ tailWord_1321365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321365).length < 2 ^ (prefixWord ++ tailWord_1321365).sum := by decide
  have hdescent : baseEnd_1321365 < baseStart_1321365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321368 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_1321368 : Nat := 118140960795 + 1321368 * 2 ^ 59
def prefixEnd_1321368 : Nat := 4983230072969 + 3 ^ 40 * 1321368 * 2
def baseEnd_1321368 : Nat := 301554180209018389032509

theorem tailTrace_1321368 : CollatzResearch.WordTrace tailWord_1321368 prefixEnd_1321368 301554180209018389032509 := by
  unfold tailWord_1321368
  simp only [CollatzResearch.WordTrace]
  refine ⟨24097125138458441266434379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32129500184611255021912505 24097125138458441266434379)
  ·
    refine ⟨36145687707687661899651569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24097125138458441266434379 36145687707687661899651569)
    ·
      refine ⟨27109265780765746424738677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36145687707687661899651569 27109265780765746424738677)
      ·
        refine ⟨2541493666946788727319251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27109265780765746424738677 2541493666946788727319251)
        ·
          refine ⟨3812240500420183090978877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541493666946788727319251 3812240500420183090978877)
          ·
            refine ⟨1429590187657568659117079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3812240500420183090978877 1429590187657568659117079)
            ·
              refine ⟨2144385281486352988675619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429590187657568659117079 2144385281486352988675619)
              ·
                refine ⟨3216577922229529483013429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144385281486352988675619 3216577922229529483013429)
                ·
                  refine ⟨301554180209018389032509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3216577922229529483013429 301554180209018389032509)
                  ·
                    rfl

theorem cell21_1321368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_1321368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321368 prefixEnd_1321368 := by exact prefixLift 1321368
  have htrace : WordTrace (prefixWord ++ tailWord_1321368) baseStart_1321368 baseEnd_1321368 := by
    simpa [prefixWord, tailWord_1321368, baseEnd_1321368] using wordTrace_append hprefix tailTrace_1321368
  have hstable : (prefixWord ++ tailWord_1321368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321368).length < 2 ^ (prefixWord ++ tailWord_1321368).sum := by decide
  have hdescent : baseEnd_1321368 < baseStart_1321368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321379 : List Nat := [1, 1, 1, 4, 1, 4, 1, 8]
def baseStart_1321379 : Nat := 118140960795 + 1321379 * 2 ^ 59
def prefixEnd_1321379 : Nat := 4983230072969 + 3 ^ 40 * 1321379 * 2
def baseEnd_1321379 : Nat := 100518896852961604783051

theorem tailTrace_1321379 : CollatzResearch.WordTrace tailWord_1321379 prefixEnd_1321379 100518896852961604783051 := by
  unfold tailWord_1321379
  simp only [CollatzResearch.WordTrace]
  refine ⟨48194651479877031411519191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32129767653251354274346127 48194651479877031411519191)
  ·
    refine ⟨72291977219815547117278787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48194651479877031411519191 72291977219815547117278787)
    ·
      refine ⟨108437965829723320675918181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72291977219815547117278787 108437965829723320675918181)
      ·
        refine ⟨20332118593073122626734659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108437965829723320675918181 20332118593073122626734659)
        ·
          refine ⟨30498177889609683940101989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20332118593073122626734659 30498177889609683940101989)
          ·
            refine ⟨5718408354301815738769123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30498177889609683940101989 5718408354301815738769123)
            ·
              refine ⟨8577612531452723608153685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5718408354301815738769123 8577612531452723608153685)
              ·
                refine ⟨100518896852961604783051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8577612531452723608153685 100518896852961604783051)
                ·
                  rfl

theorem cell21_1321379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 8].length) (baseStart_1321379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321379 prefixEnd_1321379 := by exact prefixLift 1321379
  have htrace : WordTrace (prefixWord ++ tailWord_1321379) baseStart_1321379 baseEnd_1321379 := by
    simpa [prefixWord, tailWord_1321379, baseEnd_1321379] using wordTrace_append hprefix tailTrace_1321379
  have hstable : (prefixWord ++ tailWord_1321379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321379).length < 2 ^ (prefixWord ++ tailWord_1321379).sum := by decide
  have hdescent : baseEnd_1321379 < baseStart_1321379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321441 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 4]
def baseStart_1321441 : Nat := 118140960795 + 1321441 * 2 ^ 59
def prefixEnd_1321441 : Nat := 4983230072969 + 3 ^ 40 * 1321441 * 2
def baseEnd_1321441 : Nat := 301570839803586484315693

theorem tailTrace_1321441 : CollatzResearch.WordTrace tailWord_1321441 prefixEnd_1321441 301570839803586484315693 := by
  unfold tailWord_1321441
  simp only [CollatzResearch.WordTrace]
  refine ⟨48196912805652416000276177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32131275203768277333517451 48196912805652416000276177)
  ·
    refine ⟨36147684604239312000207133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48196912805652416000276177 36147684604239312000207133)
    ·
      refine ⟨13555381726589742000077675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36147684604239312000207133 13555381726589742000077675)
      ·
        refine ⟨20333072589884613000116513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13555381726589742000077675 20333072589884613000116513)
        ·
          refine ⟨15249804442413459750087385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20333072589884613000116513 15249804442413459750087385)
          ·
            refine ⟨11437353331810094812565539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15249804442413459750087385 11437353331810094812565539)
            ·
              refine ⟨17156029997715142218848309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11437353331810094812565539 17156029997715142218848309)
              ·
                refine ⟨1608377812285794583017029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17156029997715142218848309 1608377812285794583017029)
                ·
                  refine ⟨301570839803586484315693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608377812285794583017029 301570839803586484315693)
                  ·
                    rfl

theorem cell21_1321441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_1321441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321441 prefixEnd_1321441 := by exact prefixLift 1321441
  have htrace : WordTrace (prefixWord ++ tailWord_1321441) baseStart_1321441 baseEnd_1321441 := by
    simpa [prefixWord, tailWord_1321441, baseEnd_1321441] using wordTrace_append hprefix tailTrace_1321441
  have hstable : (prefixWord ++ tailWord_1321441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321441).length < 2 ^ (prefixWord ++ tailWord_1321441).sum := by decide
  have hdescent : baseEnd_1321441 < baseStart_1321441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321478 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1321478 : Nat := 118140960795 + 1321478 * 2 ^ 59
def prefixEnd_1321478 : Nat := 4983230072969 + 3 ^ 40 * 1321478 * 2
def baseEnd_1321478 : Nat := 301579283707682642198951

theorem tailTrace_1321478 : CollatzResearch.WordTrace tailWord_1321478 prefixEnd_1321478 301579283707682642198951 := by
  unfold tailWord_1321478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506195697078699103730409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32132174871012247546248725 1506195697078699103730409)
  ·
    refine ⟨1129646772809024327797807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1506195697078699103730409 1129646772809024327797807)
    ·
      refine ⟨1694470159213536491696711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1129646772809024327797807 1694470159213536491696711)
      ·
        refine ⟨2541705238820304737545067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1694470159213536491696711 2541705238820304737545067)
        ·
          refine ⟨3812557858230457106317601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541705238820304737545067 3812557858230457106317601)
          ·
            refine ⟨2859418393672842829738201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3812557858230457106317601 2859418393672842829738201)
            ·
              refine ⟨2144563795254632122303651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2859418393672842829738201 2144563795254632122303651)
              ·
                refine ⟨3216845692881948183455477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144563795254632122303651 3216845692881948183455477)
                ·
                  refine ⟨301579283707682642198951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3216845692881948183455477 301579283707682642198951)
                  ·
                    rfl

theorem cell21_1321478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1321478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321478 prefixEnd_1321478 := by exact prefixLift 1321478
  have htrace : WordTrace (prefixWord ++ tailWord_1321478) baseStart_1321478 baseEnd_1321478 := by
    simpa [prefixWord, tailWord_1321478, baseEnd_1321478] using wordTrace_append hprefix tailTrace_1321478
  have hstable : (prefixWord ++ tailWord_1321478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321478).length < 2 ^ (prefixWord ++ tailWord_1321478).sum := by decide
  have hdescent : baseEnd_1321478 < baseStart_1321478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321492 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1321492 : Nat := 118140960795 + 1321492 * 2 ^ 59
def prefixEnd_1321492 : Nat := 4983230072969 + 3 ^ 40 * 1321492 * 2
def baseEnd_1321492 : Nat := 301582478698421728965589

theorem tailTrace_1321492 : CollatzResearch.WordTrace tailWord_1321492 prefixEnd_1321492 301582478698421728965589 := by
  unfold tailWord_1321492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24099386464233825855191365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32132515285645101140255153 24099386464233825855191365)
  ·
    refine ⟨4518634962043842347848381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24099386464233825855191365 4518634962043842347848381)
    ·
      refine ⟨1694488110766440880443143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4518634962043842347848381 1694488110766440880443143)
      ·
        refine ⟨2541732166149661320664715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1694488110766440880443143 2541732166149661320664715)
        ·
          refine ⟨3812598249224491980997073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541732166149661320664715 3812598249224491980997073)
          ·
            refine ⟨2859448686918368985747805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3812598249224491980997073 2859448686918368985747805)
            ·
              refine ⟨1072293257594388369655427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2859448686918368985747805 1072293257594388369655427)
              ·
                refine ⟨1608439886391582554483141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072293257594388369655427 1608439886391582554483141)
                ·
                  refine ⟨301582478698421728965589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608439886391582554483141 301582478698421728965589)
                  ·
                    rfl

theorem cell21_1321492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1321492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321492 prefixEnd_1321492 := by exact prefixLift 1321492
  have htrace : WordTrace (prefixWord ++ tailWord_1321492) baseStart_1321492 baseEnd_1321492 := by
    simpa [prefixWord, tailWord_1321492, baseEnd_1321492] using wordTrace_append hprefix tailTrace_1321492
  have hstable : (prefixWord ++ tailWord_1321492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321492).length < 2 ^ (prefixWord ++ tailWord_1321492).sum := by decide
  have hdescent : baseEnd_1321492 < baseStart_1321492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321537 : List Nat := [1, 2, 5, 1, 1, 3, 3, 2, 3]
def baseStart_1321537 : Nat := 118140960795 + 1321537 * 2 ^ 59
def prefixEnd_1321537 : Nat := 4983230072969 + 3 ^ 40 * 1321537 * 2
def baseEnd_1321537 : Nat := 301592748311511650715497

theorem tailTrace_1321537 : CollatzResearch.WordTrace tailWord_1321537 prefixEnd_1321537 301592748311511650715497 := by
  unfold tailWord_1321537
  simp only [CollatzResearch.WordTrace]
  refine ⟨48200414213304624395770865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32133609475536416263847243 48200414213304624395770865)
  ·
    refine ⟨36150310659978468296828149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48200414213304624395770865 36150310659978468296828149)
    ·
      refine ⟨3389091624372981402827639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36150310659978468296828149 3389091624372981402827639)
      ·
        refine ⟨5083637436559472104241459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389091624372981402827639 5083637436559472104241459)
        ·
          refine ⟨7625456154839208156362189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083637436559472104241459 7625456154839208156362189)
          ·
            refine ⟨2859546058064703058635821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7625456154839208156362189 2859546058064703058635821)
            ·
              refine ⟨1072329771774263646988433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2859546058064703058635821 1072329771774263646988433)
              ·
                refine ⟨804247328830697735241325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072329771774263646988433 804247328830697735241325)
                ·
                  refine ⟨301592748311511650715497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804247328830697735241325 301592748311511650715497)
                  ·
                    rfl

theorem cell21_1321537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_1321537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321537 prefixEnd_1321537 := by exact prefixLift 1321537
  have htrace : WordTrace (prefixWord ++ tailWord_1321537) baseStart_1321537 baseEnd_1321537 := by
    simpa [prefixWord, tailWord_1321537, baseEnd_1321537] using wordTrace_append hprefix tailTrace_1321537
  have hstable : (prefixWord ++ tailWord_1321537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321537).length < 2 ^ (prefixWord ++ tailWord_1321537).sum := by decide
  have hdescent : baseEnd_1321537 < baseStart_1321537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321593 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 4]
def baseStart_1321593 : Nat := 118140960795 + 1321593 * 2 ^ 59
def prefixEnd_1321593 : Nat := 4983230072969 + 3 ^ 40 * 1321593 * 2
def baseEnd_1321593 : Nat := 301605528274467997782049

theorem tailTrace_1321593 : CollatzResearch.WordTrace tailWord_1321593 prefixEnd_1321593 301605528274467997782049 := by
  unfold tailWord_1321593
  simp only [CollatzResearch.WordTrace]
  refine ⟨48202456701101745959809433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32134971134067830639872955 48202456701101745959809433)
  ·
    refine ⟨36151842525826309469857075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48202456701101745959809433 36151842525826309469857075)
    ·
      refine ⟨54227763788739464204785613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36151842525826309469857075 54227763788739464204785613)
      ·
        refine ⟨20335411420777299076794605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54227763788739464204785613 20335411420777299076794605)
        ·
          refine ⟨7625779282791487153797977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20335411420777299076794605 7625779282791487153797977)
          ·
            refine ⟨5719334462093615365348483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7625779282791487153797977 5719334462093615365348483)
            ·
              refine ⟨8579001693140423048022725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5719334462093615365348483 8579001693140423048022725)
              ·
                refine ⟨1608562817463829321504261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8579001693140423048022725 1608562817463829321504261)
                ·
                  refine ⟨301605528274467997782049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608562817463829321504261 301605528274467997782049)
                  ·
                    rfl

theorem cell21_1321593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_1321593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321593 prefixEnd_1321593 := by exact prefixLift 1321593
  have htrace : WordTrace (prefixWord ++ tailWord_1321593) baseStart_1321593 baseEnd_1321593 := by
    simpa [prefixWord, tailWord_1321593, baseEnd_1321593] using wordTrace_append hprefix tailTrace_1321593
  have hstable : (prefixWord ++ tailWord_1321593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321593).length < 2 ^ (prefixWord ++ tailWord_1321593).sum := by decide
  have hdescent : baseEnd_1321593 < baseStart_1321593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321596 : List Nat := [2, 2, 2, 1, 1, 2, 6, 2, 3]
def baseStart_1321596 : Nat := 118140960795 + 1321596 * 2 ^ 59
def prefixEnd_1321596 : Nat := 4983230072969 + 3 ^ 40 * 1321596 * 2
def baseEnd_1321596 : Nat := 301606212915340659232043

theorem tailTrace_1321596 : CollatzResearch.WordTrace tailWord_1321596 prefixEnd_1321596 301606212915340659232043 := by
  unfold tailWord_1321596
  simp only [CollatzResearch.WordTrace]
  refine ⟨24101283060045438736084321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32135044080060584981445761 24101283060045438736084321)
  ·
    refine ⟨18075962295034079052063241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24101283060045438736084321 18075962295034079052063241)
    ·
      refine ⟨13556971721275559289047431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18075962295034079052063241 13556971721275559289047431)
      ·
        refine ⟨20335457581913338933571147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13556971721275559289047431 20335457581913338933571147)
        ·
          refine ⟨30503186372870008400356721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20335457581913338933571147 30503186372870008400356721)
          ·
            refine ⟨22877389779652506300267541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30503186372870008400356721 22877389779652506300267541)
            ·
              refine ⟨1072377645921211232825041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22877389779652506300267541 1072377645921211232825041)
              ·
                refine ⟨804283234440908424618781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072377645921211232825041 804283234440908424618781)
                ·
                  refine ⟨301606212915340659232043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804283234440908424618781 301606212915340659232043)
                  ·
                    rfl

theorem cell21_1321596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_1321596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321596 prefixEnd_1321596 := by exact prefixLift 1321596
  have htrace : WordTrace (prefixWord ++ tailWord_1321596) baseStart_1321596 baseEnd_1321596 := by
    simpa [prefixWord, tailWord_1321596, baseEnd_1321596] using wordTrace_append hprefix tailTrace_1321596
  have hstable : (prefixWord ++ tailWord_1321596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321596).length < 2 ^ (prefixWord ++ tailWord_1321596).sum := by decide
  have hdescent : baseEnd_1321596 < baseStart_1321596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321624 : List Nat := [2, 1, 2, 4, 1, 1, 5, 5]
def baseStart_1321624 : Nat := 118140960795 + 1321624 * 2 ^ 59
def prefixEnd_1321624 : Nat := 4983230072969 + 3 ^ 40 * 1321624 * 2
def baseEnd_1321624 : Nat := 100537534298939610921773

theorem tailTrace_1321624 : CollatzResearch.WordTrace tailWord_1321624 prefixEnd_1321624 100537534298939610921773 := by
  unfold tailWord_1321624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24101793681994719127093963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32135724909326292169458617 24101793681994719127093963)
  ·
    refine ⟨36152690522992078690640945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24101793681994719127093963 36152690522992078690640945)
    ·
      refine ⟨27114517892244059017980709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36152690522992078690640945 27114517892244059017980709)
      ·
        refine ⟨5083972104795761065871383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27114517892244059017980709 5083972104795761065871383)
        ·
          refine ⟨7625958157193641598807075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083972104795761065871383 7625958157193641598807075)
          ·
            refine ⟨11438937235790462398210613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625958157193641598807075 11438937235790462398210613)
            ·
              refine ⟨1072400365855355849832245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11438937235790462398210613 1072400365855355849832245)
              ·
                refine ⟨100537534298939610921773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1072400365855355849832245 100537534298939610921773)
                ·
                  rfl

theorem cell21_1321624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_1321624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321624 prefixEnd_1321624 := by exact prefixLift 1321624
  have htrace : WordTrace (prefixWord ++ tailWord_1321624) baseStart_1321624 baseEnd_1321624 := by
    simpa [prefixWord, tailWord_1321624, baseEnd_1321624] using wordTrace_append hprefix tailTrace_1321624
  have hstable : (prefixWord ++ tailWord_1321624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321624).length < 2 ^ (prefixWord ++ tailWord_1321624).sum := by decide
  have hdescent : baseEnd_1321624 < baseStart_1321624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321655 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 5]
def baseStart_1321655 : Nat := 118140960795 + 1321655 * 2 ^ 59
def prefixEnd_1321655 : Nat := 4983230072969 + 3 ^ 40 * 1321655 * 2
def baseEnd_1321655 : Nat := 301619677519169667748589

theorem tailTrace_1321655 : CollatzResearch.WordTrace tailWord_1321655 prefixEnd_1321655 301619677519169667748589 := by
  unfold tailWord_1321655
  simp only [CollatzResearch.WordTrace]
  refine ⟨48204718026877130548566419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32136478684584753699044279 48204718026877130548566419)
  ·
    refine ⟨72307077040315695822849629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48204718026877130548566419 72307077040315695822849629)
    ·
      refine ⟨27115153890118385933568611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72307077040315695822849629 27115153890118385933568611)
      ·
        refine ⟨40672730835177578900352917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27115153890118385933568611 40672730835177578900352917)
        ·
          refine ⟨1906534257898949010954043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40672730835177578900352917 1906534257898949010954043)
          ·
            refine ⟨2859801386848423516431065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906534257898949010954043 2859801386848423516431065)
            ·
              refine ⟨2144851040136317637323299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2859801386848423516431065 2144851040136317637323299)
              ·
                refine ⟨3217276560204476455984949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144851040136317637323299 3217276560204476455984949)
                ·
                  refine ⟨301619677519169667748589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3217276560204476455984949 301619677519169667748589)
                  ·
                    rfl

theorem cell21_1321655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 5].length) (baseStart_1321655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321655 prefixEnd_1321655 := by exact prefixLift 1321655
  have htrace : WordTrace (prefixWord ++ tailWord_1321655) baseStart_1321655 baseEnd_1321655 := by
    simpa [prefixWord, tailWord_1321655, baseEnd_1321655] using wordTrace_append hprefix tailTrace_1321655
  have hstable : (prefixWord ++ tailWord_1321655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321655).length < 2 ^ (prefixWord ++ tailWord_1321655).sum := by decide
  have hdescent : baseEnd_1321655 < baseStart_1321655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321762 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1321762 : Nat := 118140960795 + 1321762 * 2 ^ 59
def prefixEnd_1321762 : Nat := 4983230072969 + 3 ^ 40 * 1321762 * 2
def baseEnd_1321762 : Nat := 301644096376961259465037

theorem tailTrace_1321762 : CollatzResearch.WordTrace tailWord_1321762 prefixEnd_1321762 301644096376961259465037 := by
  unfold tailWord_1321762
  simp only [CollatzResearch.WordTrace]
  refine ⟨12052155159372371955677885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32139080424992991881807693 12052155159372371955677885)
  ·
    refine ⟨4519558184764639483379207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12052155159372371955677885 4519558184764639483379207)
    ·
      refine ⟨6779337277146959225068811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4519558184764639483379207 6779337277146959225068811)
      ·
        refine ⟨10169005915720438837603217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6779337277146959225068811 10169005915720438837603217)
        ·
          refine ⟨7626754436790329128202413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10169005915720438837603217 7626754436790329128202413)
          ·
            refine ⟨2860032913796373423075905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7626754436790329128202413 2860032913796373423075905)
            ·
              refine ⟨2145024685347280067306929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860032913796373423075905 2145024685347280067306929)
              ·
                refine ⟨1608768514010460050480197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2145024685347280067306929 1608768514010460050480197)
                ·
                  refine ⟨301644096376961259465037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608768514010460050480197 301644096376961259465037)
                  ·
                    rfl

theorem cell21_1321762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1321762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1321762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1321762 prefixEnd_1321762 := by exact prefixLift 1321762
  have htrace : WordTrace (prefixWord ++ tailWord_1321762) baseStart_1321762 baseEnd_1321762 := by
    simpa [prefixWord, tailWord_1321762, baseEnd_1321762] using wordTrace_append hprefix tailTrace_1321762
  have hstable : (prefixWord ++ tailWord_1321762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321762).length < 2 ^ (prefixWord ++ tailWord_1321762).sum := by decide
  have hdescent : baseEnd_1321762 < baseStart_1321762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322018 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1322018 : Nat := 118140960795 + 1322018 * 2 ^ 59
def prefixEnd_1322018 : Nat := 4983230072969 + 3 ^ 40 * 1322018 * 2
def baseEnd_1322018 : Nat := 301702519064761703197847

theorem tailTrace_1322018 : CollatzResearch.WordTrace tailWord_1322018 prefixEnd_1322018 301702519064761703197847 := by
  unfold tailWord_1322018
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054489431140510886007677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32145305149708029029353805 12054489431140510886007677)
  ·
    refine ⟨4520433536677691582252879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12054489431140510886007677 4520433536677691582252879)
    ·
      refine ⟨6780650305016537373379319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4520433536677691582252879 6780650305016537373379319)
      ·
        refine ⟨10170975457524806060068979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6780650305016537373379319 10170975457524806060068979)
        ·
          refine ⟨15256463186287209090103469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10170975457524806060068979 15256463186287209090103469)
          ·
            refine ⟨5721173694857703408788801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15256463186287209090103469 5721173694857703408788801)
            ·
              refine ⟨4290880271143277556591601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5721173694857703408788801 4290880271143277556591601)
              ·
                refine ⟨3218160203357458167443701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4290880271143277556591601 3218160203357458167443701)
                ·
                  refine ⟨301702519064761703197847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3218160203357458167443701 301702519064761703197847)
                  ·
                    rfl

theorem cell21_1322018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1322018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322018 prefixEnd_1322018 := by exact prefixLift 1322018
  have htrace : WordTrace (prefixWord ++ tailWord_1322018) baseStart_1322018 baseEnd_1322018 := by
    simpa [prefixWord, tailWord_1322018, baseEnd_1322018] using wordTrace_append hprefix tailTrace_1322018
  have hstable : (prefixWord ++ tailWord_1322018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322018).length < 2 ^ (prefixWord ++ tailWord_1322018).sum := by decide
  have hdescent : baseEnd_1322018 < baseStart_1322018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322066 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_1322066 : Nat := 118140960795 + 1322066 * 2 ^ 59
def prefixEnd_1322066 : Nat := 4983230072969 + 3 ^ 40 * 1322066 * 2
def baseEnd_1322066 : Nat := 301713473318724286397749

theorem tailTrace_1322066 : CollatzResearch.WordTrace tailWord_1322066 prefixEnd_1322066 301713473318724286397749 := by
  unfold tailWord_1322066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054927107097036935444513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32146472285592098494518701 12054927107097036935444513)
  ·
    refine ⟨9041195330322777701583385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12054927107097036935444513 9041195330322777701583385)
    ·
      refine ⟨6780896497742083276187539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9041195330322777701583385 6780896497742083276187539)
      ·
        refine ⟨10171344746613124914281309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6780896497742083276187539 10171344746613124914281309)
        ·
          refine ⟨3814254279979921842855491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10171344746613124914281309 3814254279979921842855491)
          ·
            refine ⟨5721381419969882764283237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3814254279979921842855491 5721381419969882764283237)
            ·
              refine ⟨1072759016244353018303107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5721381419969882764283237 1072759016244353018303107)
              ·
                refine ⟨1609138524366529527454661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072759016244353018303107 1609138524366529527454661)
                ·
                  refine ⟨301713473318724286397749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1609138524366529527454661 301713473318724286397749)
                  ·
                    rfl

theorem cell21_1322066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_1322066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322066 prefixEnd_1322066 := by exact prefixLift 1322066
  have htrace : WordTrace (prefixWord ++ tailWord_1322066) baseStart_1322066 baseEnd_1322066 := by
    simpa [prefixWord, tailWord_1322066, baseEnd_1322066] using wordTrace_append hprefix tailTrace_1322066
  have hstable : (prefixWord ++ tailWord_1322066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322066).length < 2 ^ (prefixWord ++ tailWord_1322066).sum := by decide
  have hdescent : baseEnd_1322066 < baseStart_1322066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322184 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_1322184 : Nat := 118140960795 + 1322184 * 2 ^ 59
def prefixEnd_1322184 : Nat := 4983230072969 + 3 ^ 40 * 1322184 * 2
def baseEnd_1322184 : Nat := 301740402526382303430841

theorem tailTrace_1322184 : CollatzResearch.WordTrace tailWord_1322184 prefixEnd_1322184 301740402526382303430841 := by
  unfold tailWord_1322184
  simp only [CollatzResearch.WordTrace]
  refine ⟨24112006120980326947286803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32149341494640435929715737 24112006120980326947286803)
  ·
    refine ⟨36168009181470490420930205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24112006120980326947286803 36168009181470490420930205)
    ·
      refine ⟨13563003443051433907848827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36168009181470490420930205 13563003443051433907848827)
      ·
        refine ⟨20344505164577150861773241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13563003443051433907848827 20344505164577150861773241)
        ·
          refine ⟨15258378873432863146329931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20344505164577150861773241 15258378873432863146329931)
          ·
            refine ⟨22887568310149294719494897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15258378873432863146329931 22887568310149294719494897)
            ·
              refine ⟨17165676232611971039621173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22887568310149294719494897 17165676232611971039621173)
              ·
                refine ⟨1609282146807372284964485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17165676232611971039621173 1609282146807372284964485)
                ·
                  refine ⟨301740402526382303430841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1609282146807372284964485 301740402526382303430841)
                  ·
                    rfl

theorem cell21_1322184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_1322184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322184 prefixEnd_1322184 := by exact prefixLift 1322184
  have htrace : WordTrace (prefixWord ++ tailWord_1322184) baseStart_1322184 baseEnd_1322184 := by
    simpa [prefixWord, tailWord_1322184, baseEnd_1322184] using wordTrace_append hprefix tailTrace_1322184
  have hstable : (prefixWord ++ tailWord_1322184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322184).length < 2 ^ (prefixWord ++ tailWord_1322184).sum := by decide
  have hdescent : baseEnd_1322184 < baseStart_1322184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322274 : List Nat := [3, 3, 1, 1, 13]
def baseStart_1322274 : Nat := 118140960795 + 1322274 * 2 ^ 59
def prefixEnd_1322274 : Nat := 4983230072969 + 3 ^ 40 * 1322274 * 2
def baseEnd_1322274 : Nat := 3725443725340273418897

theorem tailTrace_1322274 : CollatzResearch.WordTrace tailWord_1322274 prefixEnd_1322274 3725443725340273418897 := by
  unfold tailWord_1322274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056823702908649816337469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32151529874423066176899917 12056823702908649816337469)
  ·
    refine ⟨4521308888590743681126551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12056823702908649816337469 4521308888590743681126551)
    ·
      refine ⟨6781963332886115521689827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4521308888590743681126551 6781963332886115521689827)
      ·
        refine ⟨10172944999329173282534741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6781963332886115521689827 10172944999329173282534741)
        ·
          refine ⟨3725443725340273418897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10172944999329173282534741 3725443725340273418897)
          ·
            rfl

theorem cell21_1322274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 13].length) (baseStart_1322274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322274 prefixEnd_1322274 := by exact prefixLift 1322274
  have htrace : WordTrace (prefixWord ++ tailWord_1322274) baseStart_1322274 baseEnd_1322274 := by
    simpa [prefixWord, tailWord_1322274, baseEnd_1322274] using wordTrace_append hprefix tailTrace_1322274
  have hstable : (prefixWord ++ tailWord_1322274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322274).length < 2 ^ (prefixWord ++ tailWord_1322274).sum := by decide
  have hdescent : baseEnd_1322274 < baseStart_1322274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322277 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 4]
def baseStart_1322277 : Nat := 118140960795 + 1322277 * 2 ^ 59
def prefixEnd_1322277 : Nat := 4983230072969 + 3 ^ 40 * 1322277 * 2
def baseEnd_1322277 : Nat := 301761626393434808380651

theorem tailTrace_1322277 : CollatzResearch.WordTrace tailWord_1322277 prefixEnd_1322277 301761626393434808380651 := by
  unfold tailWord_1322277
  simp only [CollatzResearch.WordTrace]
  refine ⟨48227404230623730777709085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32151602820415820518472723 48227404230623730777709085)
  ·
    refine ⟨18085276586483899041640907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48227404230623730777709085 18085276586483899041640907)
    ·
      refine ⟨27127914879725848562461361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18085276586483899041640907 27127914879725848562461361)
      ·
        refine ⟨20345936159794386421846021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27127914879725848562461361 20345936159794386421846021)
        ·
          refine ⟨3814863029961447454096129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20345936159794386421846021 3814863029961447454096129)
          ·
            refine ⟨2861147272471085590572097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3814863029961447454096129 2861147272471085590572097)
            ·
              refine ⟨2145860454353314192929073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2861147272471085590572097 2145860454353314192929073)
              ·
                refine ⟨1609395340764985644696805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2145860454353314192929073 1609395340764985644696805)
                ·
                  refine ⟨301761626393434808380651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1609395340764985644696805 301761626393434808380651)
                  ·
                    rfl

theorem cell21_1322277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_1322277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322277 prefixEnd_1322277 := by exact prefixLift 1322277
  have htrace : WordTrace (prefixWord ++ tailWord_1322277) baseStart_1322277 baseEnd_1322277 := by
    simpa [prefixWord, tailWord_1322277, baseEnd_1322277] using wordTrace_append hprefix tailTrace_1322277
  have hstable : (prefixWord ++ tailWord_1322277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322277).length < 2 ^ (prefixWord ++ tailWord_1322277).sum := by decide
  have hdescent : baseEnd_1322277 < baseStart_1322277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322280 : List Nat := [2, 1, 5, 1, 2, 1, 4, 2, 3]
def baseStart_1322280 : Nat := 118140960795 + 1322280 * 2 ^ 59
def prefixEnd_1322280 : Nat := 4983230072969 + 3 ^ 40 * 1322280 * 2
def baseEnd_1322280 : Nat := 301762311034307469830645

theorem tailTrace_1322280 : CollatzResearch.WordTrace tailWord_1322280 prefixEnd_1322280 301762311034307469830645 := by
  unfold tailWord_1322280
  simp only [CollatzResearch.WordTrace]
  refine ⟨24113756824806431145034147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32151675766408574860045529 24113756824806431145034147)
  ·
    refine ⟨36170635237209646717551221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24113756824806431145034147 36170635237209646717551221)
    ·
      refine ⟨3390997053488404379770427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36170635237209646717551221 3390997053488404379770427)
      ·
        refine ⟨5086495580232606569655641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3390997053488404379770427 5086495580232606569655641)
        ·
          refine ⟨3814871685174454927241731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5086495580232606569655641 3814871685174454927241731)
          ·
            refine ⟨5722307527761682390862597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3814871685174454927241731 5722307527761682390862597)
            ·
              refine ⟨1072932661455315448286737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5722307527761682390862597 1072932661455315448286737)
              ·
                refine ⟨804699496091486586215053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072932661455315448286737 804699496091486586215053)
                ·
                  refine ⟨301762311034307469830645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804699496091486586215053 301762311034307469830645)
                  ·
                    rfl

theorem cell21_1322280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_1322280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322280 prefixEnd_1322280 := by exact prefixLift 1322280
  have htrace : WordTrace (prefixWord ++ tailWord_1322280) baseStart_1322280 baseEnd_1322280 := by
    simpa [prefixWord, tailWord_1322280, baseEnd_1322280] using wordTrace_append hprefix tailTrace_1322280
  have hstable : (prefixWord ++ tailWord_1322280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322280).length < 2 ^ (prefixWord ++ tailWord_1322280).sum := by decide
  have hdescent : baseEnd_1322280 < baseStart_1322280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322291 : List Nat := [1, 1, 1, 2, 5, 4, 1, 6]
def baseStart_1322291 : Nat := 118140960795 + 1322291 * 2 ^ 59
def prefixEnd_1322291 : Nat := 4983230072969 + 3 ^ 40 * 1322291 * 2
def baseEnd_1322291 : Nat := 100588273794724631715763

theorem tailTrace_1322291 : CollatzResearch.WordTrace tailWord_1322291 prefixEnd_1322291 100588273794724631715763 := by
  unfold tailWord_1322291
  simp only [CollatzResearch.WordTrace]
  refine ⟨48227914852573011168718727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32151943235048674112479151 48227914852573011168718727)
  ·
    refine ⟨72341872278859516753078091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48227914852573011168718727 72341872278859516753078091)
    ·
      refine ⟨108512808418289275129617137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72341872278859516753078091 108512808418289275129617137)
      ·
        refine ⟨81384606313716956347212853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108512808418289275129617137 81384606313716956347212853)
        ·
          refine ⟨7629806841910964657551205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81384606313716956347212853 7629806841910964657551205)
          ·
            refine ⟨1430588782858305873290851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7629806841910964657551205 1430588782858305873290851)
            ·
              refine ⟨2145883174287458809936277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430588782858305873290851 2145883174287458809936277)
              ·
                refine ⟨100588273794724631715763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2145883174287458809936277 100588273794724631715763)
                ·
                  rfl

theorem cell21_1322291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 6].length) (baseStart_1322291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322291 prefixEnd_1322291 := by exact prefixLift 1322291
  have htrace : WordTrace (prefixWord ++ tailWord_1322291) baseStart_1322291 baseEnd_1322291 := by
    simpa [prefixWord, tailWord_1322291, baseEnd_1322291] using wordTrace_append hprefix tailTrace_1322291
  have hstable : (prefixWord ++ tailWord_1322291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322291).length < 2 ^ (prefixWord ++ tailWord_1322291).sum := by decide
  have hdescent : baseEnd_1322291 < baseStart_1322291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322336 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_1322336 : Nat := 118140960795 + 1322336 * 2 ^ 59
def prefixEnd_1322336 : Nat := 4983230072969 + 3 ^ 40 * 1322336 * 2
def baseEnd_1322336 : Nat := 301775090997263816897197

theorem tailTrace_1322336 : CollatzResearch.WordTrace tailWord_1322336 prefixEnd_1322336 301775090997263816897197 := by
  unfold tailWord_1322336
  simp only [CollatzResearch.WordTrace]
  refine ⟨24114778068704991927053431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32153037424939989236071241 24114778068704991927053431)
  ·
    refine ⟨36172167103057487890580147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24114778068704991927053431 36172167103057487890580147)
    ·
      refine ⟨54258250654586231835870221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36172167103057487890580147 54258250654586231835870221)
      ·
        refine ⟨20346843995469836938451333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54258250654586231835870221 20346843995469836938451333)
        ·
          refine ⟨3815033249150594425959625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20346843995469836938451333 3815033249150594425959625)
          ·
            refine ⟨2861274936862945819469719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3815033249150594425959625 2861274936862945819469719)
            ·
              refine ⟨4291912405294418729204579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2861274936862945819469719 4291912405294418729204579)
              ·
                refine ⟨6437868607941628093806869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4291912405294418729204579 6437868607941628093806869)
                ·
                  refine ⟨301775090997263816897197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6437868607941628093806869 301775090997263816897197)
                  ·
                    rfl

theorem cell21_1322336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_1322336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322336 prefixEnd_1322336 := by exact prefixLift 1322336
  have htrace : WordTrace (prefixWord ++ tailWord_1322336) baseStart_1322336 baseEnd_1322336 := by
    simpa [prefixWord, tailWord_1322336, baseEnd_1322336] using wordTrace_append hprefix tailTrace_1322336
  have hstable : (prefixWord ++ tailWord_1322336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322336).length < 2 ^ (prefixWord ++ tailWord_1322336).sum := by decide
  have hdescent : baseEnd_1322336 < baseStart_1322336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322474 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_1322474 : Nat := 118140960795 + 1322474 * 2 ^ 59
def prefixEnd_1322474 : Nat := 4983230072969 + 3 ^ 40 * 1322474 * 2
def baseEnd_1322474 : Nat := 301806584477406243596915

theorem tailTrace_1322474 : CollatzResearch.WordTrace tailWord_1322474 prefixEnd_1322474 301806584477406243596915 := by
  unfold tailWord_1322474
  simp only [CollatzResearch.WordTrace]
  refine ⟨12058647352727508355657619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32156392940606688948420317 12058647352727508355657619)
  ·
    refine ⟨18087971029091262533486429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12058647352727508355657619 18087971029091262533486429)
    ·
      refine ⟨6782989135909223450057411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18087971029091262533486429 6782989135909223450057411)
      ·
        refine ⟨10174483703863835175086117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6782989135909223450057411 10174483703863835175086117)
        ·
          refine ⟨1907715694474469095328647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10174483703863835175086117 1907715694474469095328647)
          ·
            refine ⟨2861573541711703642992971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907715694474469095328647 2861573541711703642992971)
            ·
              refine ⟨4292360312567555464489457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2861573541711703642992971 4292360312567555464489457)
              ·
                refine ⟨3219270234425666598367093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4292360312567555464489457 3219270234425666598367093)
                ·
                  refine ⟨301806584477406243596915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3219270234425666598367093 301806584477406243596915)
                  ·
                    rfl

theorem cell21_1322474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_1322474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322474 prefixEnd_1322474 := by exact prefixLift 1322474
  have htrace : WordTrace (prefixWord ++ tailWord_1322474) baseStart_1322474 baseEnd_1322474 := by
    simpa [prefixWord, tailWord_1322474, baseEnd_1322474] using wordTrace_append hprefix tailTrace_1322474
  have hstable : (prefixWord ++ tailWord_1322474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322474).length < 2 ^ (prefixWord ++ tailWord_1322474).sum := by decide
  have hdescent : baseEnd_1322474 < baseStart_1322474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322547 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 6]
def baseStart_1322547 : Nat := 118140960795 + 1322547 * 2 ^ 59
def prefixEnd_1322547 : Nat := 4983230072969 + 3 ^ 40 * 1322547 * 2
def baseEnd_1322547 : Nat := 301823244071974338880099

theorem tailTrace_1322547 : CollatzResearch.WordTrace tailWord_1322547 prefixEnd_1322547 301823244071974338880099 := by
  unfold tailWord_1322547
  simp only [CollatzResearch.WordTrace]
  refine ⟨48237251939645566890037895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32158167959763711260025263 48237251939645566890037895)
  ·
    refine ⟨72355877909468350335056843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48237251939645566890037895 72355877909468350335056843)
    ·
      refine ⟨108533816864202525502585265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72355877909468350335056843 108533816864202525502585265)
      ·
        refine ⟨81400362648151894126938949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108533816864202525502585265 81400362648151894126938949)
        ·
          refine ⟨15262567996528480148801053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81400362648151894126938949 15262567996528480148801053)
          ·
            refine ⟨5723462998698180055800395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15262567996528480148801053 5723462998698180055800395)
            ·
              refine ⟨8585194498047270083700593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5723462998698180055800395 8585194498047270083700593)
              ·
                refine ⟨6438895873535452562775445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8585194498047270083700593 6438895873535452562775445)
                ·
                  refine ⟨301823244071974338880099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6438895873535452562775445 301823244071974338880099)
                  ·
                    rfl

theorem cell21_1322547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_1322547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322547 prefixEnd_1322547 := by exact prefixLift 1322547
  have htrace : WordTrace (prefixWord ++ tailWord_1322547) baseStart_1322547 baseEnd_1322547 := by
    simpa [prefixWord, tailWord_1322547, baseEnd_1322547] using wordTrace_append hprefix tailTrace_1322547
  have hstable : (prefixWord ++ tailWord_1322547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322547).length < 2 ^ (prefixWord ++ tailWord_1322547).sum := by decide
  have hdescent : baseEnd_1322547 < baseStart_1322547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322567 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 5]
def baseStart_1322567 : Nat := 118140960795 + 1322567 * 2 ^ 59
def prefixEnd_1322567 : Nat := 4983230072969 + 3 ^ 40 * 1322567 * 2
def baseEnd_1322567 : Nat := 301827808344458748546725

theorem tailTrace_1322567 : CollatzResearch.WordTrace tailWord_1322567 prefixEnd_1322567 301827808344458748546725 := by
  unfold tailWord_1322567
  simp only [CollatzResearch.WordTrace]
  refine ⟨48237981399573110305765955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32158654266382073537177303 48237981399573110305765955)
  ·
    refine ⟨72356972099359665458648933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48237981399573110305765955 72356972099359665458648933)
    ·
      refine ⟨13566932268629937273496675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72356972099359665458648933 13566932268629937273496675)
      ·
        refine ⟨20350398402944905910245013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13566932268629937273496675 20350398402944905910245013)
        ·
          refine ⟨953924925138042464542735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20350398402944905910245013 953924925138042464542735)
          ·
            refine ⟨1430887387707063696814103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953924925138042464542735 1430887387707063696814103)
            ·
              refine ⟨2146331081560595545221155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430887387707063696814103 2146331081560595545221155)
              ·
                refine ⟨3219496622340893317831733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146331081560595545221155 3219496622340893317831733)
                ·
                  refine ⟨301827808344458748546725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3219496622340893317831733 301827808344458748546725)
                  ·
                    rfl

theorem cell21_1322567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 5].length) (baseStart_1322567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322567 prefixEnd_1322567 := by exact prefixLift 1322567
  have htrace : WordTrace (prefixWord ++ tailWord_1322567) baseStart_1322567 baseEnd_1322567 := by
    simpa [prefixWord, tailWord_1322567, baseEnd_1322567] using wordTrace_append hprefix tailTrace_1322567
  have hstable : (prefixWord ++ tailWord_1322567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322567).length < 2 ^ (prefixWord ++ tailWord_1322567).sum := by decide
  have hdescent : baseEnd_1322567 < baseStart_1322567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322578 : List Nat := [3, 2, 2, 1, 2, 2, 1, 8]
def baseStart_1322578 : Nat := 118140960795 + 1322578 * 2 ^ 59
def prefixEnd_1322578 : Nat := 4983230072969 + 3 ^ 40 * 1322578 * 2
def baseEnd_1322578 : Nat := 100610106231441724621123

theorem tailTrace_1322578 : CollatzResearch.WordTrace tailWord_1322578 prefixEnd_1322578 100610106231441724621123 := by
  unfold tailWord_1322578
  simp only [CollatzResearch.WordTrace]
  refine ⟨12059595650633314796104097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32158921735022172789610925 12059595650633314796104097)
  ·
    refine ⟨9044696737974986097078073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12059595650633314796104097 9044696737974986097078073)
    ·
      refine ⟨6783522553481239572808555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9044696737974986097078073 6783522553481239572808555)
      ·
        refine ⟨10175283830221859359212833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6783522553481239572808555 10175283830221859359212833)
        ·
          refine ⟨7631462872666394519409625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10175283830221859359212833 7631462872666394519409625)
          ·
            refine ⟨5723597154499795889557219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7631462872666394519409625 5723597154499795889557219)
            ·
              refine ⟨8585395731749693834335829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5723597154499795889557219 8585395731749693834335829)
              ·
                refine ⟨100610106231441724621123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8585395731749693834335829 100610106231441724621123)
                ·
                  rfl

theorem cell21_1322578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_1322578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322578 prefixEnd_1322578 := by exact prefixLift 1322578
  have htrace : WordTrace (prefixWord ++ tailWord_1322578) baseStart_1322578 baseEnd_1322578 := by
    simpa [prefixWord, tailWord_1322578, baseEnd_1322578] using wordTrace_append hprefix tailTrace_1322578
  have hstable : (prefixWord ++ tailWord_1322578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322578).length < 2 ^ (prefixWord ++ tailWord_1322578).sum := by decide
  have hdescent : baseEnd_1322578 < baseStart_1322578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322592 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_1322592 : Nat := 118140960795 + 1322592 * 2 ^ 59
def prefixEnd_1322592 : Nat := 4983230072969 + 3 ^ 40 * 1322592 * 2
def baseEnd_1322592 : Nat := 301833513685064260630007

theorem tailTrace_1322592 : CollatzResearch.WordTrace tailWord_1322592 prefixEnd_1322592 301833513685064260630007 := by
  unfold tailWord_1322592
  simp only [CollatzResearch.WordTrace]
  refine ⟨24119446612241269787713015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32159262149655026383617353 24119446612241269787713015)
  ·
    refine ⟨36179169918361904681569523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24119446612241269787713015 36179169918361904681569523)
    ·
      refine ⟨54268754877542857022354285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36179169918361904681569523 54268754877542857022354285)
      ·
        refine ⟨20350783079078571383382857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54268754877542857022354285 20350783079078571383382857)
        ·
          refine ⟨15263087309308928537537143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20350783079078571383382857 15263087309308928537537143)
          ·
            refine ⟨22894630963963392806305715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15263087309308928537537143 22894630963963392806305715)
            ·
              refine ⟨34341946445945089209458573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22894630963963392806305715 34341946445945089209458573)
              ·
                refine ⟨12878229917229408453546965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34341946445945089209458573 12878229917229408453546965)
                ·
                  refine ⟨301833513685064260630007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12878229917229408453546965 301833513685064260630007)
                  ·
                    rfl

theorem cell21_1322592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_1322592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322592 prefixEnd_1322592 := by exact prefixLift 1322592
  have htrace : WordTrace (prefixWord ++ tailWord_1322592) baseStart_1322592 baseEnd_1322592 := by
    simpa [prefixWord, tailWord_1322592, baseEnd_1322592] using wordTrace_append hprefix tailTrace_1322592
  have hstable : (prefixWord ++ tailWord_1322592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322592).length < 2 ^ (prefixWord ++ tailWord_1322592).sum := by decide
  have hdescent : baseEnd_1322592 < baseStart_1322592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322685 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1322685 : Nat := 118140960795 + 1322685 * 2 ^ 59
def prefixEnd_1322685 : Nat := 4983230072969 + 3 ^ 40 * 1322685 * 2
def baseEnd_1322685 : Nat := 301854737552116765579817

theorem tailTrace_1322685 : CollatzResearch.WordTrace tailWord_1322685 prefixEnd_1322685 301854737552116765579817 := by
  unfold tailWord_1322685
  simp only [CollatzResearch.WordTrace]
  refine ⟨48242285213145616458561509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32161523475430410972374339 48242285213145616458561509)
  ·
    refine ⟨9045428477464803085980283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48242285213145616458561509 9045428477464803085980283)
    ·
      refine ⟨13568142716197204628970425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9045428477464803085980283 13568142716197204628970425)
      ·
        refine ⟨10176107037147903471727819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13568142716197204628970425 10176107037147903471727819)
        ·
          refine ⟨15264160555721855207591729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10176107037147903471727819 15264160555721855207591729)
          ·
            refine ⟨11448120416791391405693797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15264160555721855207591729 11448120416791391405693797)
            ·
              refine ⟨2146522578148385888567587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11448120416791391405693797 2146522578148385888567587)
              ·
                refine ⟨3219783867222578832851381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146522578148385888567587 3219783867222578832851381)
                ·
                  refine ⟨301854737552116765579817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3219783867222578832851381 301854737552116765579817)
                  ·
                    rfl

theorem cell21_1322685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1322685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322685 prefixEnd_1322685 := by exact prefixLift 1322685
  have htrace : WordTrace (prefixWord ++ tailWord_1322685) baseStart_1322685 baseEnd_1322685 := by
    simpa [prefixWord, tailWord_1322685, baseEnd_1322685] using wordTrace_append hprefix tailTrace_1322685
  have hstable : (prefixWord ++ tailWord_1322685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322685).length < 2 ^ (prefixWord ++ tailWord_1322685).sum := by decide
  have hdescent : baseEnd_1322685 < baseStart_1322685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322699 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 4]
def baseStart_1322699 : Nat := 118140960795 + 1322699 * 2 ^ 59
def prefixEnd_1322699 : Nat := 4983230072969 + 3 ^ 40 * 1322699 * 2
def baseEnd_1322699 : Nat := 301857932542855852346455

theorem tailTrace_1322699 : CollatzResearch.WordTrace tailWord_1322699 prefixEnd_1322699 301857932542855852346455 := by
  unfold tailWord_1322699
  simp only [CollatzResearch.WordTrace]
  refine ⟨48242795835094896849571151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32161863890063264566380767 48242795835094896849571151)
  ·
    refine ⟨72364193752642345274356727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48242795835094896849571151 72364193752642345274356727)
    ·
      refine ⟨108546290628963517911535091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72364193752642345274356727 108546290628963517911535091)
      ·
        refine ⟨162819435943445276867302637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108546290628963517911535091 162819435943445276867302637)
        ·
          refine ⟨61057288478791978825238489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162819435943445276867302637 61057288478791978825238489)
          ·
            refine ⟨45792966359093984118928867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61057288478791978825238489 45792966359093984118928867)
            ·
              refine ⟨68689449538640976178393301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45792966359093984118928867 68689449538640976178393301)
              ·
                refine ⟨1609908973561897879181093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68689449538640976178393301 1609908973561897879181093)
                ·
                  refine ⟨301857932542855852346455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1609908973561897879181093 301857932542855852346455)
                  ·
                    rfl

theorem cell21_1322699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 4].length) (baseStart_1322699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322699 prefixEnd_1322699 := by exact prefixLift 1322699
  have htrace : WordTrace (prefixWord ++ tailWord_1322699) baseStart_1322699 baseEnd_1322699 := by
    simpa [prefixWord, tailWord_1322699, baseEnd_1322699] using wordTrace_append hprefix tailTrace_1322699
  have hstable : (prefixWord ++ tailWord_1322699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322699).length < 2 ^ (prefixWord ++ tailWord_1322699).sum := by decide
  have hdescent : baseEnd_1322699 < baseStart_1322699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322744 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_1322744 : Nat := 118140960795 + 1322744 * 2 ^ 59
def prefixEnd_1322744 : Nat := 4983230072969 + 3 ^ 40 * 1322744 * 2
def baseEnd_1322744 : Nat := 301868202155945774096363

theorem tailTrace_1322744 : CollatzResearch.WordTrace tailWord_1322744 prefixEnd_1322744 301868202155945774096363 := by
  unfold tailWord_1322744
  simp only [CollatzResearch.WordTrace]
  refine ⟨24122218559965934767479643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32162958079954579689972857 24122218559965934767479643)
  ·
    refine ⟨36183327839948902151219465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24122218559965934767479643 36183327839948902151219465)
    ·
      refine ⟨27137495879961676613414599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36183327839948902151219465 27137495879961676613414599)
      ·
        refine ⟨40706243819942514920121899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27137495879961676613414599 40706243819942514920121899)
        ·
          refine ⟨61059365729913772380182849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40706243819942514920121899 61059365729913772380182849)
          ·
            refine ⟨45794524297435329285137137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61059365729913772380182849 45794524297435329285137137)
            ·
              refine ⟨34345893223076496963852853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45794524297435329285137137 34345893223076496963852853)
              ·
                refine ⟨3219927489663421590361205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34345893223076496963852853 3219927489663421590361205)
                ·
                  refine ⟨301868202155945774096363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3219927489663421590361205 301868202155945774096363)
                  ·
                    rfl

theorem cell21_1322744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_1322744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322744 prefixEnd_1322744 := by exact prefixLift 1322744
  have htrace : WordTrace (prefixWord ++ tailWord_1322744) baseStart_1322744 baseEnd_1322744 := by
    simpa [prefixWord, tailWord_1322744, baseEnd_1322744] using wordTrace_append hprefix tailTrace_1322744
  have hstable : (prefixWord ++ tailWord_1322744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322744).length < 2 ^ (prefixWord ++ tailWord_1322744).sum := by decide
  have hdescent : baseEnd_1322744 < baseStart_1322744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322789 : List Nat := [1, 3, 1, 2, 3, 11]
def baseStart_1322789 : Nat := 118140960795 + 1322789 * 2 ^ 59
def prefixEnd_1322789 : Nat := 4983230072969 + 3 ^ 40 * 1322789 * 2
def baseEnd_1322789 : Nat := 11180684139593914660973

theorem tailTrace_1322789 : CollatzResearch.WordTrace tailWord_1322789 prefixEnd_1322789 11180684139593914660973 := by
  unfold tailWord_1322789
  simp only [CollatzResearch.WordTrace]
  refine ⟨48246078404768842220347421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32164052269845894813564947 48246078404768842220347421)
  ·
    refine ⟨18092279401788315832630283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48246078404768842220347421 18092279401788315832630283)
    ·
      refine ⟨27138419102682473748945425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18092279401788315832630283 27138419102682473748945425)
      ·
        refine ⟨20353814327011855311709069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27138419102682473748945425 20353814327011855311709069)
        ·
          refine ⟨7632680372629445741890901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20353814327011855311709069 7632680372629445741890901)
          ·
            refine ⟨11180684139593914660973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7632680372629445741890901 11180684139593914660973)
            ·
              rfl

theorem cell21_1322789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 11].length) (baseStart_1322789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322789 prefixEnd_1322789 := by exact prefixLift 1322789
  have htrace : WordTrace (prefixWord ++ tailWord_1322789) baseStart_1322789 baseEnd_1322789 := by
    simpa [prefixWord, tailWord_1322789, baseEnd_1322789] using wordTrace_append hprefix tailTrace_1322789
  have hstable : (prefixWord ++ tailWord_1322789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322789).length < 2 ^ (prefixWord ++ tailWord_1322789).sum := by decide
  have hdescent : baseEnd_1322789 < baseStart_1322789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322792 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_1322792 : Nat := 118140960795 + 1322792 * 2 ^ 59
def prefixEnd_1322792 : Nat := 4983230072969 + 3 ^ 40 * 1322792 * 2
def baseEnd_1322792 : Nat := 301879156409908357296265

theorem tailTrace_1322792 : CollatzResearch.WordTrace tailWord_1322792 prefixEnd_1322792 301879156409908357296265 := by
  unfold tailWord_1322792
  simp only [CollatzResearch.WordTrace]
  refine ⟨24123093911878986866353315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32164125215838649155137753 24123093911878986866353315)
  ·
    refine ⟨36184640867818480299529973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24123093911878986866353315 36184640867818480299529973)
    ·
      refine ⟨3392310081357982528080935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36184640867818480299529973 3392310081357982528080935)
      ·
        refine ⟨5088465122036973792121403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3392310081357982528080935 5088465122036973792121403)
        ·
          refine ⟨7632697683055460688182105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5088465122036973792121403 7632697683055460688182105)
          ·
            refine ⟨5724523262291595516136579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7632697683055460688182105 5724523262291595516136579)
            ·
              refine ⟨8586784893437393274204869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724523262291595516136579 8586784893437393274204869)
              ·
                refine ⟨1610022167519511238913413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8586784893437393274204869 1610022167519511238913413)
                ·
                  refine ⟨301879156409908357296265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610022167519511238913413 301879156409908357296265)
                  ·
                    rfl

theorem cell21_1322792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_1322792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322792 prefixEnd_1322792 := by exact prefixLift 1322792
  have htrace : WordTrace (prefixWord ++ tailWord_1322792) baseStart_1322792 baseEnd_1322792 := by
    simpa [prefixWord, tailWord_1322792, baseEnd_1322792] using wordTrace_append hprefix tailTrace_1322792
  have hstable : (prefixWord ++ tailWord_1322792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322792).length < 2 ^ (prefixWord ++ tailWord_1322792).sum := by decide
  have hdescent : baseEnd_1322792 < baseStart_1322792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322865 : List Nat := [1, 2, 2, 2, 1, 3, 2, 8]
def baseStart_1322865 : Nat := 118140960795 + 1322865 * 2 ^ 59
def prefixEnd_1322865 : Nat := 4983230072969 + 3 ^ 40 * 1322865 * 2
def baseEnd_1322865 : Nat := 100631938668158817526483

theorem tailTrace_1322865 : CollatzResearch.WordTrace tailWord_1322865 prefixEnd_1322865 100631938668158817526483 := by
  unfold tailWord_1322865
  simp only [CollatzResearch.WordTrace]
  refine ⟨48248850352493507200114049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32165900234995671466742699 48248850352493507200114049)
  ·
    refine ⟨36186637764370130400085537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48248850352493507200114049 36186637764370130400085537)
    ·
      refine ⟨27139978323277597800064153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36186637764370130400085537 27139978323277597800064153)
      ·
        refine ⟨20354983742458198350048115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27139978323277597800064153 20354983742458198350048115)
        ·
          refine ⟨30532475613687297525072173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20354983742458198350048115 30532475613687297525072173)
          ·
            refine ⟨11449678355132736571902065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30532475613687297525072173 11449678355132736571902065)
            ·
              refine ⟨8587258766349552428926549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11449678355132736571902065 8587258766349552428926549)
              ·
                refine ⟨100631938668158817526483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8587258766349552428926549 100631938668158817526483)
                ·
                  rfl

theorem cell21_1322865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 8].length) (baseStart_1322865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322865 prefixEnd_1322865 := by exact prefixLift 1322865
  have htrace : WordTrace (prefixWord ++ tailWord_1322865) baseStart_1322865 baseEnd_1322865 := by
    simpa [prefixWord, tailWord_1322865, baseEnd_1322865] using wordTrace_append hprefix tailTrace_1322865
  have hstable : (prefixWord ++ tailWord_1322865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322865).length < 2 ^ (prefixWord ++ tailWord_1322865).sum := by decide
  have hdescent : baseEnd_1322865 < baseStart_1322865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322888 : List Nat := [2, 1, 3, 3, 4, 1, 1, 3, 3]
def baseStart_1322888 : Nat := 118140960795 + 1322888 * 2 ^ 59
def prefixEnd_1322888 : Nat := 4983230072969 + 3 ^ 40 * 1322888 * 2
def baseEnd_1322888 : Nat := 301901064917833523696069

theorem tailTrace_1322888 : CollatzResearch.WordTrace tailWord_1322888 prefixEnd_1322888 301901064917833523696069 := by
  unfold tailWord_1322888
  simp only [CollatzResearch.WordTrace]
  refine ⟨24124844615705091064100659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32166459487606788085467545 24124844615705091064100659)
  ·
    refine ⟨36187266923557636596150989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24124844615705091064100659 36187266923557636596150989)
    ·
      refine ⟨13570225096334113723556621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36187266923557636596150989 13570225096334113723556621)
      ·
        refine ⟨5088834411125292646333733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13570225096334113723556621 5088834411125292646333733)
        ·
          refine ⟨954156452085992371187575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5088834411125292646333733 954156452085992371187575)
          ·
            refine ⟨1431234678128988556781363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954156452085992371187575 1431234678128988556781363)
            ·
              refine ⟨2146852017193482835172045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431234678128988556781363 2146852017193482835172045)
              ·
                refine ⟨805069506447556063189517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2146852017193482835172045 805069506447556063189517)
                ·
                  refine ⟨301901064917833523696069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805069506447556063189517 301901064917833523696069)
                  ·
                    rfl

theorem cell21_1322888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_1322888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322888 prefixEnd_1322888 := by exact prefixLift 1322888
  have htrace : WordTrace (prefixWord ++ tailWord_1322888) baseStart_1322888 baseEnd_1322888 := by
    simpa [prefixWord, tailWord_1322888, baseEnd_1322888] using wordTrace_append hprefix tailTrace_1322888
  have hstable : (prefixWord ++ tailWord_1322888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322888).length < 2 ^ (prefixWord ++ tailWord_1322888).sum := by decide
  have hdescent : baseEnd_1322888 < baseStart_1322888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322927 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 4]
def baseStart_1322927 : Nat := 118140960795 + 1322927 * 2 ^ 59
def prefixEnd_1322927 : Nat := 4983230072969 + 3 ^ 40 * 1322927 * 2
def baseEnd_1322927 : Nat := 301909965249178122545989

theorem tailTrace_1322927 : CollatzResearch.WordTrace tailWord_1322927 prefixEnd_1322927 301909965249178122545989 := by
  unfold tailWord_1322927
  simp only [CollatzResearch.WordTrace]
  refine ⟨48251111678268891788871035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32167407785512594525914023 48251111678268891788871035)
  ·
    refine ⟨72376667517403337683306553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48251111678268891788871035 72376667517403337683306553)
    ·
      refine ⟨54282500638052503262479915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72376667517403337683306553 54282500638052503262479915)
      ·
        refine ⟨81423750957078754893719873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54282500638052503262479915 81423750957078754893719873)
        ·
          refine ⟨61067813217809066170289905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81423750957078754893719873 61067813217809066170289905)
          ·
            refine ⟨45800859913356799627717429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61067813217809066170289905 45800859913356799627717429)
            ·
              refine ⟨4293830616877199965098509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45800859913356799627717429 4293830616877199965098509)
              ·
                refine ⟨1610186481328949986911941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4293830616877199965098509 1610186481328949986911941)
                ·
                  refine ⟨301909965249178122545989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610186481328949986911941 301909965249178122545989)
                  ·
                    rfl

theorem cell21_1322927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 4].length) (baseStart_1322927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1322927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1322927 prefixEnd_1322927 := by exact prefixLift 1322927
  have htrace : WordTrace (prefixWord ++ tailWord_1322927) baseStart_1322927 baseEnd_1322927 := by
    simpa [prefixWord, tailWord_1322927, baseEnd_1322927] using wordTrace_append hprefix tailTrace_1322927
  have hstable : (prefixWord ++ tailWord_1322927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322927).length < 2 ^ (prefixWord ++ tailWord_1322927).sum := by decide
  have hdescent : baseEnd_1322927 < baseStart_1322927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323037 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 4]
def baseStart_1323037 : Nat := 118140960795 + 1323037 * 2 ^ 59
def prefixEnd_1323037 : Nat := 4983230072969 + 3 ^ 40 * 1323037 * 2
def baseEnd_1323037 : Nat := 301935068747842375712431

theorem tailTrace_1323037 : CollatzResearch.WordTrace tailWord_1323037 prefixEnd_1323037 301935068747842375712431 := by
  unfold tailWord_1323037
  simp only [CollatzResearch.WordTrace]
  refine ⟨48255123707870380575375365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32170082471913587050250243 48255123707870380575375365)
  ·
    refine ⟨9047835695225696357882881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48255123707870380575375365 9047835695225696357882881)
    ·
      refine ⟨6785876771419272268412161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9047835695225696357882881 6785876771419272268412161)
      ·
        refine ⟨5089407578564454201309121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6785876771419272268412161 5089407578564454201309121)
        ·
          refine ⟨3817055683923340650981841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5089407578564454201309121 3817055683923340650981841)
          ·
            refine ⟨2862791762942505488236381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3817055683923340650981841 2862791762942505488236381)
            ·
              refine ⟨1073546911103439558088643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2862791762942505488236381 1073546911103439558088643)
              ·
                refine ⟨1610320366655159337132965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073546911103439558088643 1610320366655159337132965)
                ·
                  refine ⟨301935068747842375712431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610320366655159337132965 301935068747842375712431)
                  ·
                    rfl

theorem cell21_1323037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_1323037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323037 prefixEnd_1323037 := by exact prefixLift 1323037
  have htrace : WordTrace (prefixWord ++ tailWord_1323037) baseStart_1323037 baseEnd_1323037 := by
    simpa [prefixWord, tailWord_1323037, baseEnd_1323037] using wordTrace_append hprefix tailTrace_1323037
  have hstable : (prefixWord ++ tailWord_1323037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323037).length < 2 ^ (prefixWord ++ tailWord_1323037).sum := by decide
  have hdescent : baseEnd_1323037 < baseStart_1323037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323079 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 4]
def baseStart_1323079 : Nat := 118140960795 + 1323079 * 2 ^ 59
def prefixEnd_1323079 : Nat := 4983230072969 + 3 ^ 40 * 1323079 * 2
def baseEnd_1323079 : Nat := 301944653720059636012345

theorem tailTrace_1323079 : CollatzResearch.WordTrace tailWord_1323079 prefixEnd_1323079 301944653720059636012345 := by
  unfold tailWord_1323079
  simp only [CollatzResearch.WordTrace]
  refine ⟨48256655573718221748404291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32171103715812147832269527 48256655573718221748404291)
  ·
    refine ⟨72384983360577332622606437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48256655573718221748404291 72384983360577332622606437)
    ·
      refine ⟨13572184380108249866738707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72384983360577332622606437 13572184380108249866738707)
      ·
        refine ⟨20358276570162374800108061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13572184380108249866738707 20358276570162374800108061)
        ·
          refine ⟨7634353713810890550040523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20358276570162374800108061 7634353713810890550040523)
          ·
            refine ⟨11451530570716335825060785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7634353713810890550040523 11451530570716335825060785)
            ·
              refine ⟨8588647928037251868795589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11451530570716335825060785 8588647928037251868795589)
              ·
                refine ⟨1610371486506984725399173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8588647928037251868795589 1610371486506984725399173)
                ·
                  refine ⟨301944653720059636012345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610371486506984725399173 301944653720059636012345)
                  ·
                    rfl

theorem cell21_1323079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 4].length) (baseStart_1323079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323079 prefixEnd_1323079 := by exact prefixLift 1323079
  have htrace : WordTrace (prefixWord ++ tailWord_1323079) baseStart_1323079 baseEnd_1323079 := by
    simpa [prefixWord, tailWord_1323079, baseEnd_1323079] using wordTrace_append hprefix tailTrace_1323079
  have hstable : (prefixWord ++ tailWord_1323079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323079).length < 2 ^ (prefixWord ++ tailWord_1323079).sum := by decide
  have hdescent : baseEnd_1323079 < baseStart_1323079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323093 : List Nat := [1, 3, 2, 2, 1, 3, 1, 8]
def baseStart_1323093 : Nat := 118140960795 + 1323093 * 2 ^ 59
def prefixEnd_1323093 : Nat := 4983230072969 + 3 ^ 40 * 1323093 * 2
def baseEnd_1323093 : Nat := 100649282903599574259661

theorem tailTrace_1323093 : CollatzResearch.WordTrace tailWord_1323093 prefixEnd_1323093 100649282903599574259661 := by
  unfold tailWord_1323093
  simp only [CollatzResearch.WordTrace]
  refine ⟨48257166195667502139413933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32171444130445001426275955 48257166195667502139413933)
  ·
    refine ⟨18096437323375313302280225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48257166195667502139413933 18096437323375313302280225)
    ·
      refine ⟨13572327992531484976710169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18096437323375313302280225 13572327992531484976710169)
      ·
        refine ⟨10179245994398613732532627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13572327992531484976710169 10179245994398613732532627)
        ·
          refine ⟨15268868991597920598798941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10179245994398613732532627 15268868991597920598798941)
          ·
            refine ⟨5725825871849220224549603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15268868991597920598798941 5725825871849220224549603)
            ·
              refine ⟨8588738807773830336824405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5725825871849220224549603 8588738807773830336824405)
              ·
                refine ⟨100649282903599574259661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8588738807773830336824405 100649282903599574259661)
                ·
                  rfl

theorem cell21_1323093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 8].length) (baseStart_1323093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323093 prefixEnd_1323093 := by exact prefixLift 1323093
  have htrace : WordTrace (prefixWord ++ tailWord_1323093) baseStart_1323093 baseEnd_1323093 := by
    simpa [prefixWord, tailWord_1323093, baseEnd_1323093] using wordTrace_append hprefix tailTrace_1323093
  have hstable : (prefixWord ++ tailWord_1323093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323093).length < 2 ^ (prefixWord ++ tailWord_1323093).sum := by decide
  have hdescent : baseEnd_1323093 < baseStart_1323093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323096 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_1323096 : Nat := 118140960795 + 1323096 * 2 ^ 59
def prefixEnd_1323096 : Nat := 4983230072969 + 3 ^ 40 * 1323096 * 2
def baseEnd_1323096 : Nat := 301948533351671384228977

theorem tailTrace_1323096 : CollatzResearch.WordTrace tailWord_1323096 prefixEnd_1323096 301948533351671384228977 := by
  unfold tailWord_1323096
  simp only [CollatzResearch.WordTrace]
  refine ⟨24128637807328316825886571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32171517076437755767848761 24128637807328316825886571)
  ·
    refine ⟨36192956710992475238829857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24128637807328316825886571 36192956710992475238829857)
    ·
      refine ⟨27144717533244356429122393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36192956710992475238829857 27144717533244356429122393)
      ·
        refine ⟨20358538149933267321841795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27144717533244356429122393 20358538149933267321841795)
        ·
          refine ⟨30537807224899900982762693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20358538149933267321841795 30537807224899900982762693)
          ·
            refine ⟨5725838854668731434268005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30537807224899900982762693 5725838854668731434268005)
            ·
              refine ⟨1073594785250387143925251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5725838854668731434268005 1073594785250387143925251)
              ·
                refine ⟨1610392177875580715887877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073594785250387143925251 1610392177875580715887877)
                ·
                  refine ⟨301948533351671384228977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610392177875580715887877 301948533351671384228977)
                  ·
                    rfl

theorem cell21_1323096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_1323096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323096 prefixEnd_1323096 := by exact prefixLift 1323096
  have htrace : WordTrace (prefixWord ++ tailWord_1323096) baseStart_1323096 baseEnd_1323096 := by
    simpa [prefixWord, tailWord_1323096, baseEnd_1323096] using wordTrace_append hprefix tailTrace_1323096
  have hstable : (prefixWord ++ tailWord_1323096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323096).length < 2 ^ (prefixWord ++ tailWord_1323096).sum := by decide
  have hdescent : baseEnd_1323096 < baseStart_1323096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323175 : List Nat := [1, 1, 6, 2, 2, 1, 2, 3, 3]
def baseStart_1323175 : Nat := 118140960795 + 1323175 * 2 ^ 59
def prefixEnd_1323175 : Nat := 4983230072969 + 3 ^ 40 * 1323175 * 2
def baseEnd_1323175 : Nat := 301966562227984802412149

theorem tailTrace_1323175 : CollatzResearch.WordTrace tailWord_1323175 prefixEnd_1323175 301966562227984802412149 := by
  unfold tailWord_1323175
  simp only [CollatzResearch.WordTrace]
  refine ⟨48260156981370430143898979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32173437987580286762599319 48260156981370430143898979)
  ·
    refine ⟨72390235472055645215848469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48260156981370430143898979 72390235472055645215848469)
    ·
      refine ⟨3393292287752608369492897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72390235472055645215848469 3393292287752608369492897)
      ·
        refine ⟨2544969215814456277119673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3393292287752608369492897 2544969215814456277119673)
        ·
          refine ⟨1908726911860842207839755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2544969215814456277119673 1908726911860842207839755)
          ·
            refine ⟨2863090367791263311759633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908726911860842207839755 2863090367791263311759633)
            ·
              refine ⟨2147317775843447483819725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863090367791263311759633 2147317775843447483819725)
              ·
                refine ⟨805244165941292806432397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2147317775843447483819725 805244165941292806432397)
                ·
                  refine ⟨301966562227984802412149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805244165941292806432397 301966562227984802412149)
                  ·
                    rfl

theorem cell21_1323175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 3].length) (baseStart_1323175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323175 prefixEnd_1323175 := by exact prefixLift 1323175
  have htrace : WordTrace (prefixWord ++ tailWord_1323175) baseStart_1323175 baseEnd_1323175 := by
    simpa [prefixWord, tailWord_1323175, baseEnd_1323175] using wordTrace_append hprefix tailTrace_1323175
  have hstable : (prefixWord ++ tailWord_1323175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323175).length < 2 ^ (prefixWord ++ tailWord_1323175).sum := by decide
  have hdescent : baseEnd_1323175 < baseStart_1323175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323183 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 9]
def baseStart_1323183 : Nat := 118140960795 + 1323183 * 2 ^ 59
def prefixEnd_1323183 : Nat := 4983230072969 + 3 ^ 40 * 1323183 * 2
def baseEnd_1323183 : Nat := 301968387936978566278799

theorem tailTrace_1323183 : CollatzResearch.WordTrace tailWord_1323183 prefixEnd_1323183 301968387936978566278799 := by
  unfold tailWord_1323183
  simp only [CollatzResearch.WordTrace]
  refine ⟨48260448765341447510190203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32173632510227631673460135 48260448765341447510190203)
  ·
    refine ⟨72390673148012171265285305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48260448765341447510190203 72390673148012171265285305)
    ·
      refine ⟨54293004861009128448963979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72390673148012171265285305 54293004861009128448963979)
      ·
        refine ⟨81439507291513692673445969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54293004861009128448963979 81439507291513692673445969)
        ·
          refine ⟨61079630468635269505084477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81439507291513692673445969 61079630468635269505084477)
          ·
            refine ⟨22904861425738226064406679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61079630468635269505084477 22904861425738226064406679)
            ·
              refine ⟨34357292138607339096610019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22904861425738226064406679 34357292138607339096610019)
              ·
                refine ⟨51535938207911008644915029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34357292138607339096610019 51535938207911008644915029)
                ·
                  refine ⟨301968387936978566278799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51535938207911008644915029 301968387936978566278799)
                  ·
                    rfl

theorem cell21_1323183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_1323183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323183 prefixEnd_1323183 := by exact prefixLift 1323183
  have htrace : WordTrace (prefixWord ++ tailWord_1323183) baseStart_1323183 baseEnd_1323183 := by
    simpa [prefixWord, tailWord_1323183, baseEnd_1323183] using wordTrace_append hprefix tailTrace_1323183
  have hstable : (prefixWord ++ tailWord_1323183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323183).length < 2 ^ (prefixWord ++ tailWord_1323183).sum := by decide
  have hdescent : baseEnd_1323183 < baseStart_1323183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323200 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_1323200 : Nat := 118140960795 + 1323200 * 2 ^ 59
def prefixEnd_1323200 : Nat := 4983230072969 + 3 ^ 40 * 1323200 * 2
def baseEnd_1323200 : Nat := 301972267568590314495431

theorem tailTrace_1323200 : CollatzResearch.WordTrace tailWord_1323200 prefixEnd_1323200 301972267568590314495431 := by
  unfold tailWord_1323200
  simp only [CollatzResearch.WordTrace]
  refine ⟨24130534403139929706779527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32174045870853239609039369 24130534403139929706779527)
  ·
    refine ⟨36195801604709894560169291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24130534403139929706779527 36195801604709894560169291)
    ·
      refine ⟨54293702407064841840253937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36195801604709894560169291 54293702407064841840253937)
      ·
        refine ⟨40720276805298631380190453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54293702407064841840253937 40720276805298631380190453)
        ·
          refine ⟨3817525950496746691892855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40720276805298631380190453 3817525950496746691892855)
          ·
            refine ⟨5726288925745120037839283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817525950496746691892855 5726288925745120037839283)
            ·
              refine ⟨8589433388617680056758925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5726288925745120037839283 8589433388617680056758925)
              ·
                refine ⟨3221037520731630021284597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8589433388617680056758925 3221037520731630021284597)
                ·
                  refine ⟨301972267568590314495431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3221037520731630021284597 301972267568590314495431)
                  ·
                    rfl

theorem cell21_1323200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_1323200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323200 prefixEnd_1323200 := by exact prefixLift 1323200
  have htrace : WordTrace (prefixWord ++ tailWord_1323200) baseStart_1323200 baseEnd_1323200 := by
    simpa [prefixWord, tailWord_1323200, baseEnd_1323200] using wordTrace_append hprefix tailTrace_1323200
  have hstable : (prefixWord ++ tailWord_1323200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323200).length < 2 ^ (prefixWord ++ tailWord_1323200).sum := by decide
  have hdescent : baseEnd_1323200 < baseStart_1323200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323262 : List Nat := [4, 2, 2, 1, 1, 1, 4, 6]
def baseStart_1323262 : Nat := 118140960795 + 1323262 * 2 ^ 59
def prefixEnd_1323262 : Nat := 4983230072969 + 3 ^ 40 * 1323262 * 2
def baseEnd_1323262 : Nat := 100662138937763994820657

theorem tailTrace_1323262 : CollatzResearch.WordTrace tailWord_1323262 prefixEnd_1323262 100662138937763994820657 := by
  unfold tailWord_1323262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6032916266506905500289505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32175553421370162668210693 6032916266506905500289505)
  ·
    refine ⟨4524687199880179125217129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6032916266506905500289505 4524687199880179125217129)
    ·
      refine ⟨3393515399910134343912847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4524687199880179125217129 3393515399910134343912847)
      ·
        refine ⟨5090273099865201515869271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3393515399910134343912847 5090273099865201515869271)
        ·
          refine ⟨7635409649797802273803907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5090273099865201515869271 7635409649797802273803907)
          ·
            refine ⟨11453114474696703410705861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7635409649797802273803907 11453114474696703410705861)
            ·
              refine ⟨2147458964005631889507349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11453114474696703410705861 2147458964005631889507349)
              ·
                refine ⟨100662138937763994820657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2147458964005631889507349 100662138937763994820657)
                ·
                  rfl

theorem cell21_1323262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_1323262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323262 prefixEnd_1323262 := by exact prefixLift 1323262
  have htrace : WordTrace (prefixWord ++ tailWord_1323262) baseStart_1323262 baseEnd_1323262 := by
    simpa [prefixWord, tailWord_1323262, baseEnd_1323262] using wordTrace_append hprefix tailTrace_1323262
  have hstable : (prefixWord ++ tailWord_1323262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323262).length < 2 ^ (prefixWord ++ tailWord_1323262).sum := by decide
  have hdescent : baseEnd_1323262 < baseStart_1323262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323428 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1323428 : Nat := 118140960795 + 1323428 * 2 ^ 59
def prefixEnd_1323428 : Nat := 4983230072969 + 3 ^ 40 * 1323428 * 2
def baseEnd_1323428 : Nat := 302024300274912584694965

theorem tailTrace_1323428 : CollatzResearch.WordTrace tailWord_1323428 prefixEnd_1323428 302024300274912584694965 := by
  unfold tailWord_1323428
  simp only [CollatzResearch.WordTrace]
  refine ⟨24134692324726927176429469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32179589766302569568572625 24134692324726927176429469)
  ·
    refine ⟨9050509621772597691161051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24134692324726927176429469 9050509621772597691161051)
    ·
      refine ⟨13575764432658896536741577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9050509621772597691161051 13575764432658896536741577)
      ·
        refine ⟨10181823324494172402556183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13575764432658896536741577 10181823324494172402556183)
        ·
          refine ⟨15272734986741258603834275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10181823324494172402556183 15272734986741258603834275)
          ·
            refine ⟨22909102480111887905751413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15272734986741258603834275 22909102480111887905751413)
            ·
              refine ⟨2147728357510489491164195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22909102480111887905751413 2147728357510489491164195)
              ·
                refine ⟨3221592536265734236746293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2147728357510489491164195 3221592536265734236746293)
                ·
                  refine ⟨302024300274912584694965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3221592536265734236746293 302024300274912584694965)
                  ·
                    rfl

theorem cell21_1323428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1323428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323428 prefixEnd_1323428 := by exact prefixLift 1323428
  have htrace : WordTrace (prefixWord ++ tailWord_1323428) baseStart_1323428 baseEnd_1323428 := by
    simpa [prefixWord, tailWord_1323428, baseEnd_1323428] using wordTrace_append hprefix tailTrace_1323428
  have hstable : (prefixWord ++ tailWord_1323428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323428).length < 2 ^ (prefixWord ++ tailWord_1323428).sum := by decide
  have hdescent : baseEnd_1323428 < baseStart_1323428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323434 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_1323434 : Nat := 118140960795 + 1323434 * 2 ^ 59
def prefixEnd_1323434 : Nat := 4983230072969 + 3 ^ 40 * 1323434 * 2
def baseEnd_1323434 : Nat := 302025669556657907594953

theorem tailTrace_1323434 : CollatzResearch.WordTrace tailWord_1323434 prefixEnd_1323434 302025669556657907594953 := by
  unfold tailWord_1323434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12067400871858029344394339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32179735658288078251718237 12067400871858029344394339)
  ·
    refine ⟨18101101307787044016591509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12067400871858029344394339 18101101307787044016591509)
    ·
      refine ⟨848489123802517688277727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18101101307787044016591509 848489123802517688277727)
      ·
        refine ⟨1272733685703776532416591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848489123802517688277727 1272733685703776532416591)
        ·
          refine ⟨1909100528555664798624887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272733685703776532416591 1909100528555664798624887)
          ·
            refine ⟨2863650792833497197937331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909100528555664798624887 2863650792833497197937331)
            ·
              refine ⟨4295476189250245796905997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2863650792833497197937331 4295476189250245796905997)
              ·
                refine ⟨1610803570968842173839749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4295476189250245796905997 1610803570968842173839749)
                ·
                  refine ⟨302025669556657907594953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610803570968842173839749 302025669556657907594953)
                  ·
                    rfl

theorem cell21_1323434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_1323434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323434 prefixEnd_1323434 := by exact prefixLift 1323434
  have htrace : WordTrace (prefixWord ++ tailWord_1323434) baseStart_1323434 baseEnd_1323434 := by
    simpa [prefixWord, tailWord_1323434, baseEnd_1323434] using wordTrace_append hprefix tailTrace_1323434
  have hstable : (prefixWord ++ tailWord_1323434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323434).length < 2 ^ (prefixWord ++ tailWord_1323434).sum := by decide
  have hdescent : baseEnd_1323434 < baseStart_1323434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323476 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1323476 : Nat := 118140960795 + 1323476 * 2 ^ 59
def prefixEnd_1323476 : Nat := 4983230072969 + 3 ^ 40 * 1323476 * 2
def baseEnd_1323476 : Nat := 302035254528875167894867

theorem tailTrace_1323476 : CollatzResearch.WordTrace tailWord_1323476 prefixEnd_1323476 302035254528875167894867 := by
  unfold tailWord_1323476
  simp only [CollatzResearch.WordTrace]
  refine ⟨24135567676639979275303141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32180756902186639033737521 24135567676639979275303141)
  ·
    refine ⟨4525418939369996114119339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24135567676639979275303141 4525418939369996114119339)
    ·
      refine ⟨6788128409054994171179009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4525418939369996114119339 6788128409054994171179009)
      ·
        refine ⟨5091096306791245628384257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6788128409054994171179009 5091096306791245628384257)
        ·
          refine ⟨3818322230093434221288193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5091096306791245628384257 3818322230093434221288193)
          ·
            refine ⟨2863741672570075665966145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3818322230093434221288193 2863741672570075665966145)
            ·
              refine ⟨2147806254427556749474609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863741672570075665966145 2147806254427556749474609)
              ·
                refine ⟨1610854690820667562105957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2147806254427556749474609 1610854690820667562105957)
                ·
                  refine ⟨302035254528875167894867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610854690820667562105957 302035254528875167894867)
                  ·
                    rfl

theorem cell21_1323476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1323476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323476 prefixEnd_1323476 := by exact prefixLift 1323476
  have htrace : WordTrace (prefixWord ++ tailWord_1323476) baseStart_1323476 baseEnd_1323476 := by
    simpa [prefixWord, tailWord_1323476, baseEnd_1323476] using wordTrace_append hprefix tailTrace_1323476
  have hstable : (prefixWord ++ tailWord_1323476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323476).length < 2 ^ (prefixWord ++ tailWord_1323476).sum := by decide
  have hdescent : baseEnd_1323476 < baseStart_1323476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323521 : List Nat := [1, 2, 4, 1, 3, 1, 1, 5, 3]
def baseStart_1323521 : Nat := 118140960795 + 1323521 * 2 ^ 59
def prefixEnd_1323521 : Nat := 4983230072969 + 3 ^ 40 * 1323521 * 2
def baseEnd_1323521 : Nat := 302045524141965089644775

theorem tailTrace_1323521 : CollatzResearch.WordTrace tailWord_1323521 prefixEnd_1323521 302045524141965089644775 := by
  unfold tailWord_1323521
  simp only [CollatzResearch.WordTrace]
  refine ⟨48272776638116931235994417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32181851092077954157329611 48272776638116931235994417)
  ·
    refine ⟨36204582478587698426995813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48272776638116931235994417 36204582478587698426995813)
    ·
      refine ⟨6788359214735193455061715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36204582478587698426995813 6788359214735193455061715)
      ·
        refine ⟨10182538822102790182592573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6788359214735193455061715 10182538822102790182592573)
        ·
          refine ⟨3818452058288546318472215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10182538822102790182592573 3818452058288546318472215)
          ·
            refine ⟨5727678087432819477708323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818452058288546318472215 5727678087432819477708323)
            ·
              refine ⟨8591517131149229216562485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727678087432819477708323 8591517131149229216562485)
              ·
                refine ⟨805454731045240239052733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8591517131149229216562485 805454731045240239052733)
                ·
                  refine ⟨302045524141965089644775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805454731045240239052733 302045524141965089644775)
                  ·
                    rfl

theorem cell21_1323521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_1323521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323521 prefixEnd_1323521 := by exact prefixLift 1323521
  have htrace : WordTrace (prefixWord ++ tailWord_1323521) baseStart_1323521 baseEnd_1323521 := by
    simpa [prefixWord, tailWord_1323521, baseEnd_1323521] using wordTrace_append hprefix tailTrace_1323521
  have hstable : (prefixWord ++ tailWord_1323521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323521).length < 2 ^ (prefixWord ++ tailWord_1323521).sum := by decide
  have hdescent : baseEnd_1323521 < baseStart_1323521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323566 : List Nat := [4, 1, 3, 1, 3, 1, 1, 7]
def baseStart_1323566 : Nat := 118140960795 + 1323566 * 2 ^ 59
def prefixEnd_1323566 : Nat := 4983230072969 + 3 ^ 40 * 1323566 * 2
def baseEnd_1323566 : Nat := 100685264585018337131561

theorem tailTrace_1323566 : CollatzResearch.WordTrace tailWord_1323566 prefixEnd_1323566 100685264585018337131561 := by
  unfold tailWord_1323566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034302240369237990172819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32182945281969269280921701 6034302240369237990172819)
  ·
    refine ⟨9051453360553856985259229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6034302240369237990172819 9051453360553856985259229)
    ·
      refine ⟨3394295010207696369472211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9051453360553856985259229 3394295010207696369472211)
      ·
        refine ⟨5091442515311544554208317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3394295010207696369472211 5091442515311544554208317)
        ·
          refine ⟨1909290943241829207828119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5091442515311544554208317 1909290943241829207828119)
          ·
            refine ⟨2863936414862743811742179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909290943241829207828119 2863936414862743811742179)
            ·
              refine ⟨4295904622294115717613269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2863936414862743811742179 4295904622294115717613269)
              ·
                refine ⟨100685264585018337131561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4295904622294115717613269 100685264585018337131561)
                ·
                  rfl

theorem cell21_1323566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_1323566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323566 prefixEnd_1323566 := by exact prefixLift 1323566
  have htrace : WordTrace (prefixWord ++ tailWord_1323566) baseStart_1323566 baseEnd_1323566 := by
    simpa [prefixWord, tailWord_1323566, baseEnd_1323566] using wordTrace_append hprefix tailTrace_1323566
  have hstable : (prefixWord ++ tailWord_1323566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323566).length < 2 ^ (prefixWord ++ tailWord_1323566).sum := by decide
  have hdescent : baseEnd_1323566 < baseStart_1323566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323572 : List Nat := [2, 5, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1323572 : Nat := 118140960795 + 1323572 * 2 ^ 59
def prefixEnd_1323572 : Nat := 4983230072969 + 3 ^ 40 * 1323572 * 2
def baseEnd_1323572 : Nat := 302057163036800334294671

theorem tailTrace_1323572 : CollatzResearch.WordTrace tailWord_1323572 prefixEnd_1323572 302057163036800334294671 := by
  unfold tailWord_1323572
  simp only [CollatzResearch.WordTrace]
  refine ⟨24137318380466083473050485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32183091173954777964067313 24137318380466083473050485)
  ·
    refine ⟨2262873598168695325598483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24137318380466083473050485 2262873598168695325598483)
    ·
      refine ⟨3394310397253042988397725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262873598168695325598483 3394310397253042988397725)
      ·
        refine ⟨1272866398969891120649147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3394310397253042988397725 1272866398969891120649147)
        ·
          refine ⟨1909299598454836680973721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272866398969891120649147 1909299598454836680973721)
          ·
            refine ⟨1431974698841127510730291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1909299598454836680973721 1431974698841127510730291)
            ·
              refine ⟨2147962048261691266095437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431974698841127510730291 2147962048261691266095437)
              ·
                refine ⟨805485768098134224785789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2147962048261691266095437 805485768098134224785789)
                ·
                  refine ⟨302057163036800334294671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805485768098134224785789 302057163036800334294671)
                  ·
                    rfl

theorem cell21_1323572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1323572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323572 prefixEnd_1323572 := by exact prefixLift 1323572
  have htrace : WordTrace (prefixWord ++ tailWord_1323572) baseStart_1323572 baseEnd_1323572 := by
    simpa [prefixWord, tailWord_1323572, baseEnd_1323572] using wordTrace_append hprefix tailTrace_1323572
  have hstable : (prefixWord ++ tailWord_1323572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323572).length < 2 ^ (prefixWord ++ tailWord_1323572).sum := by decide
  have hdescent : baseEnd_1323572 < baseStart_1323572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323594 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_1323594 : Nat := 118140960795 + 1323594 * 2 ^ 59
def prefixEnd_1323594 : Nat := 4983230072969 + 3 ^ 40 * 1323594 * 2
def baseEnd_1323594 : Nat := 302062183736533184927959

theorem tailTrace_1323594 : CollatzResearch.WordTrace tailWord_1323594 prefixEnd_1323594 302062183736533184927959 := by
  unfold tailWord_1323594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12068859791713116175850459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32183626111234976468934557 12068859791713116175850459)
  ·
    refine ⟨18103289687569674263775689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12068859791713116175850459 18103289687569674263775689)
    ·
      refine ⟨13577467265677255697831767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18103289687569674263775689 13577467265677255697831767)
      ·
        refine ⟨20366200898515883546747651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13577467265677255697831767 20366200898515883546747651)
        ·
          refine ⟨30549301347773825320121477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20366200898515883546747651 30549301347773825320121477)
          ·
            refine ⟨5727994002707592247522777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30549301347773825320121477 5727994002707592247522777)
            ·
              refine ⟨4295995502030694185642083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5727994002707592247522777 4295995502030694185642083)
              ·
                refine ⟨6443993253046041278463125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4295995502030694185642083 6443993253046041278463125)
                ·
                  refine ⟨302062183736533184927959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6443993253046041278463125 302062183736533184927959)
                  ·
                    rfl

theorem cell21_1323594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_1323594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323594 prefixEnd_1323594 := by exact prefixLift 1323594
  have htrace : WordTrace (prefixWord ++ tailWord_1323594) baseStart_1323594 baseEnd_1323594 := by
    simpa [prefixWord, tailWord_1323594, baseEnd_1323594] using wordTrace_append hprefix tailTrace_1323594
  have hstable : (prefixWord ++ tailWord_1323594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323594).length < 2 ^ (prefixWord ++ tailWord_1323594).sum := by decide
  have hdescent : baseEnd_1323594 < baseStart_1323594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323597 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1323597 : Nat := 118140960795 + 1323597 * 2 ^ 59
def prefixEnd_1323597 : Nat := 4983230072969 + 3 ^ 40 * 1323597 * 2
def baseEnd_1323597 : Nat := 302062868377405846377953

theorem tailTrace_1323597 : CollatzResearch.WordTrace tailWord_1323597 prefixEnd_1323597 302062868377405846377953 := by
  unfold tailWord_1323597
  simp only [CollatzResearch.WordTrace]
  refine ⟨48275548585841596215761045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32183699057227730810507363 48275548585841596215761045)
  ·
    refine ⟨2262916339961324822613799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48275548585841596215761045 2262916339961324822613799)
    ·
      refine ⟨3394374509941987233920699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262916339961324822613799 3394374509941987233920699)
      ·
        refine ⟨5091561764912980850881049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3394374509941987233920699 5091561764912980850881049)
        ·
          refine ⟨3818671323684735638160787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5091561764912980850881049 3818671323684735638160787)
          ·
            refine ⟨5728006985527103457241181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818671323684735638160787 5728006985527103457241181)
            ·
              refine ⟨2148002619572663796465443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5728006985527103457241181 2148002619572663796465443)
              ·
                refine ⟨3222003929358995694698165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148002619572663796465443 3222003929358995694698165)
                ·
                  refine ⟨302062868377405846377953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3222003929358995694698165 302062868377405846377953)
                  ·
                    rfl

theorem cell21_1323597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1323597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323597 prefixEnd_1323597 := by exact prefixLift 1323597
  have htrace : WordTrace (prefixWord ++ tailWord_1323597) baseStart_1323597 baseEnd_1323597 := by
    simpa [prefixWord, tailWord_1323597, baseEnd_1323597] using wordTrace_append hprefix tailTrace_1323597
  have hstable : (prefixWord ++ tailWord_1323597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323597).length < 2 ^ (prefixWord ++ tailWord_1323597).sum := by decide
  have hdescent : baseEnd_1323597 < baseStart_1323597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323608 : List Nat := [2, 1, 2, 2, 1, 2, 3, 8]
def baseStart_1323608 : Nat := 118140960795 + 1323608 * 2 ^ 59
def prefixEnd_1323608 : Nat := 4983230072969 + 3 ^ 40 * 1323608 * 2
def baseEnd_1323608 : Nat := 100688459575757423898199

theorem tailTrace_1323608 : CollatzResearch.WordTrace tailWord_1323608 prefixEnd_1323608 100688459575757423898199 := by
  unfold tailWord_1323608
  simp only [CollatzResearch.WordTrace]
  refine ⟨24137974894400872547205739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32183966525867830062940985 24137974894400872547205739)
  ·
    refine ⟨36206962341601308820808609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24137974894400872547205739 36206962341601308820808609)
    ·
      refine ⟨27155221756200981615606457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36206962341601308820808609 27155221756200981615606457)
      ·
        refine ⟨20366416317150736211704843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27155221756200981615606457 20366416317150736211704843)
        ·
          refine ⟨30549624475726104317557265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20366416317150736211704843 30549624475726104317557265)
          ·
            refine ⟨22912218356794578238167949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30549624475726104317557265 22912218356794578238167949)
            ·
              refine ⟨8592081883797966839312981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22912218356794578238167949 8592081883797966839312981)
              ·
                refine ⟨100688459575757423898199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8592081883797966839312981 100688459575757423898199)
                ·
                  rfl

theorem cell21_1323608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_1323608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323608 prefixEnd_1323608 := by exact prefixLift 1323608
  have htrace : WordTrace (prefixWord ++ tailWord_1323608) baseStart_1323608 baseEnd_1323608 := by
    simpa [prefixWord, tailWord_1323608, baseEnd_1323608] using wordTrace_append hprefix tailTrace_1323608
  have hstable : (prefixWord ++ tailWord_1323608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323608).length < 2 ^ (prefixWord ++ tailWord_1323608).sum := by decide
  have hdescent : baseEnd_1323608 < baseStart_1323608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323701 : List Nat := [1, 3, 3, 3, 1, 2, 8]
def baseStart_1323701 : Nat := 118140960795 + 1323701 * 2 ^ 59
def prefixEnd_1323701 : Nat := 4983230072969 + 3 ^ 40 * 1323701 * 2
def baseEnd_1323701 : Nat := 33565178066036086293823

theorem tailTrace_1323701 : CollatzResearch.WordTrace tailWord_1323701 prefixEnd_1323701 33565178066036086293823 := by
  unfold tailWord_1323701
  simp only [CollatzResearch.WordTrace]
  refine ⟨48279341777464821977546957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32186227851643214651697971 48279341777464821977546957)
  ·
    refine ⟨18104753166549308241580109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48279341777464821977546957 18104753166549308241580109)
    ·
      refine ⟨6789282437455990590592541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18104753166549308241580109 6789282437455990590592541)
      ·
        refine ⟨2545980914045996471472203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6789282437455990590592541 2545980914045996471472203)
        ·
          refine ⟨3818971371068994707208305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2545980914045996471472203 3818971371068994707208305)
          ·
            refine ⟨2864228528301746030406229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3818971371068994707208305 2864228528301746030406229)
            ·
              refine ⟨33565178066036086293823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2864228528301746030406229 33565178066036086293823)
              ·
                rfl

theorem cell21_1323701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 8].length) (baseStart_1323701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323701 prefixEnd_1323701 := by exact prefixLift 1323701
  have htrace : WordTrace (prefixWord ++ tailWord_1323701) baseStart_1323701 baseEnd_1323701 := by
    simpa [prefixWord, tailWord_1323701, baseEnd_1323701] using wordTrace_append hprefix tailTrace_1323701
  have hstable : (prefixWord ++ tailWord_1323701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323701).length < 2 ^ (prefixWord ++ tailWord_1323701).sum := by decide
  have hdescent : baseEnd_1323701 < baseStart_1323701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323749 : List Nat := [1, 3, 1, 4, 1, 2, 3, 3, 3]
def baseStart_1323749 : Nat := 118140960795 + 1323749 * 2 ^ 59
def prefixEnd_1323749 : Nat := 4983230072969 + 3 ^ 40 * 1323749 * 2
def baseEnd_1323749 : Nat := 302097556848287359844309

theorem tailTrace_1323749 : CollatzResearch.WordTrace tailWord_1323749 prefixEnd_1323749 302097556848287359844309 := by
  unfold tailWord_1323749
  simp only [CollatzResearch.WordTrace]
  refine ⟨48281092481290926175294301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32187394987527284116862867 48281092481290926175294301)
  ·
    refine ⟨18105409680484097315735363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48281092481290926175294301 18105409680484097315735363)
    ·
      refine ⟨27158114520726145973603045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18105409680484097315735363 27158114520726145973603045)
      ·
        refine ⟨5092146472636152370050571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27158114520726145973603045 5092146472636152370050571)
        ·
          refine ⟨7638219708954228555075857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5092146472636152370050571 7638219708954228555075857)
          ·
            refine ⟨5728664781715671416306893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7638219708954228555075857 5728664781715671416306893)
            ·
              refine ⟨2148249293143376781115085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5728664781715671416306893 2148249293143376781115085)
              ·
                refine ⟨805593484928766292918157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2148249293143376781115085 805593484928766292918157)
                ·
                  refine ⟨302097556848287359844309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805593484928766292918157 302097556848287359844309)
                  ·
                    rfl

theorem cell21_1323749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_1323749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323749 prefixEnd_1323749 := by exact prefixLift 1323749
  have htrace : WordTrace (prefixWord ++ tailWord_1323749) baseStart_1323749 baseEnd_1323749 := by
    simpa [prefixWord, tailWord_1323749, baseEnd_1323749] using wordTrace_append hprefix tailTrace_1323749
  have hstable : (prefixWord ++ tailWord_1323749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323749).length < 2 ^ (prefixWord ++ tailWord_1323749).sum := by decide
  have hdescent : baseEnd_1323749 < baseStart_1323749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323766 : List Nat := [5, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1323766 : Nat := 118140960795 + 1323766 * 2 ^ 59
def prefixEnd_1323766 : Nat := 4983230072969 + 3 ^ 40 * 1323766 * 2
def baseEnd_1323766 : Nat := 302101436479899108060941

theorem tailTrace_1323766 : CollatzResearch.WordTrace tailWord_1323766 prefixEnd_1323766 302101436479899108060941 := by
  unfold tailWord_1323766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3017607032639333629916447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32187808348152892052442101 3017607032639333629916447)
  ·
    refine ⟨4526410548959000444874671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3017607032639333629916447 4526410548959000444874671)
    ·
      refine ⟨6789615823438500667312007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4526410548959000444874671 6789615823438500667312007)
      ·
        refine ⟨10184423735157751000968011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6789615823438500667312007 10184423735157751000968011)
        ·
          refine ⟨15276635602736626501452017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10184423735157751000968011 15276635602736626501452017)
          ·
            refine ⟨11457476702052469876089013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15276635602736626501452017 11457476702052469876089013)
            ·
              refine ⟨1074138440817419050883345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11457476702052469876089013 1074138440817419050883345)
              ·
                refine ⟨805603830613064288162509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074138440817419050883345 805603830613064288162509)
                ·
                  refine ⟨302101436479899108060941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805603830613064288162509 302101436479899108060941)
                  ·
                    rfl

theorem cell21_1323766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1323766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323766 prefixEnd_1323766 := by exact prefixLift 1323766
  have htrace : WordTrace (prefixWord ++ tailWord_1323766) baseStart_1323766 baseEnd_1323766 := by
    simpa [prefixWord, tailWord_1323766, baseEnd_1323766] using wordTrace_append hprefix tailTrace_1323766
  have hstable : (prefixWord ++ tailWord_1323766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323766).length < 2 ^ (prefixWord ++ tailWord_1323766).sum := by decide
  have hdescent : baseEnd_1323766 < baseStart_1323766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323884 : List Nat := [2, 2, 1, 1, 4, 1, 1, 6, 3]
def baseStart_1323884 : Nat := 118140960795 + 1323884 * 2 ^ 59
def prefixEnd_1323884 : Nat := 4983230072969 + 3 ^ 40 * 1323884 * 2
def baseEnd_1323884 : Nat := 302128365687557125094033

theorem tailTrace_1323884 : CollatzResearch.WordTrace tailWord_1323884 prefixEnd_1323884 302128365687557125094033 := by
  unfold tailWord_1323884
  simp only [CollatzResearch.WordTrace]
  refine ⟨24143008167900922115729353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32190677557201229487639137 24143008167900922115729353)
  ·
    refine ⟨18107256125925691586797015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24143008167900922115729353 18107256125925691586797015)
    ·
      refine ⟨27160884188888537380195523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18107256125925691586797015 27160884188888537380195523)
      ·
        refine ⟨40741326283332806070293285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27160884188888537380195523 40741326283332806070293285)
        ·
          refine ⟨7638998678124901138179991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40741326283332806070293285 7638998678124901138179991)
          ·
            refine ⟨11458498017187351707269987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7638998678124901138179991 11458498017187351707269987)
            ·
              refine ⟨17187747025781027560904981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11458498017187351707269987 17187747025781027560904981)
              ·
                refine ⟨805675641833485666917421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17187747025781027560904981 805675641833485666917421)
                ·
                  refine ⟨302128365687557125094033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805675641833485666917421 302128365687557125094033)
                  ·
                    rfl

theorem cell21_1323884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_1323884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323884 prefixEnd_1323884 := by exact prefixLift 1323884
  have htrace : WordTrace (prefixWord ++ tailWord_1323884) baseStart_1323884 baseEnd_1323884 := by
    simpa [prefixWord, tailWord_1323884, baseEnd_1323884] using wordTrace_append hprefix tailTrace_1323884
  have hstable : (prefixWord ++ tailWord_1323884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323884).length < 2 ^ (prefixWord ++ tailWord_1323884).sum := by decide
  have hdescent : baseEnd_1323884 < baseStart_1323884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323988 : List Nat := [2, 4, 1, 2, 1, 11]
def baseStart_1323988 : Nat := 118140960795 + 1323988 * 2 ^ 59
def prefixEnd_1323988 : Nat := 4983230072969 + 3 ^ 40 * 1323988 * 2
def baseEnd_1323988 : Nat := 11190818514980594642981

theorem tailTrace_1323988 : CollatzResearch.WordTrace tailWord_1323988 prefixEnd_1323988 11190818514980594642981 := by
  unfold tailWord_1323988
  simp only [CollatzResearch.WordTrace]
  refine ⟨24144904763712534996622309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32193206351616713328829745 24144904763712534996622309)
  ·
    refine ⟨4527169643196100311866683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24144904763712534996622309 4527169643196100311866683)
    ·
      refine ⟨6790754464794150467800025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4527169643196100311866683 6790754464794150467800025)
      ·
        refine ⟨5093065848595612850850019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6790754464794150467800025 5093065848595612850850019)
        ·
          refine ⟨7639598772893419276275029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5093065848595612850850019 7639598772893419276275029)
          ·
            refine ⟨11190818514980594642981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7639598772893419276275029 11190818514980594642981)
            ·
              rfl

theorem cell21_1323988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 11].length) (baseStart_1323988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323988 prefixEnd_1323988 := by exact prefixLift 1323988
  have htrace : WordTrace (prefixWord ++ tailWord_1323988) baseStart_1323988 baseEnd_1323988 := by
    simpa [prefixWord, tailWord_1323988, baseEnd_1323988] using wordTrace_append hprefix tailTrace_1323988
  have hstable : (prefixWord ++ tailWord_1323988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323988).length < 2 ^ (prefixWord ++ tailWord_1323988).sum := by decide
  have hdescent : baseEnd_1323988 < baseStart_1323988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323994 : List Nat := [3, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_1323994 : Nat := 118140960795 + 1323994 * 2 ^ 59
def prefixEnd_1323994 : Nat := 4983230072969 + 3 ^ 40 * 1323994 * 2
def baseEnd_1323994 : Nat := 302153469186221378260475

theorem tailTrace_1323994 : CollatzResearch.WordTrace tailWord_1323994 prefixEnd_1323994 302153469186221378260475 := by
  unfold tailWord_1323994
  simp only [CollatzResearch.WordTrace]
  refine ⟨12072507091350833254490759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32193352243602222011975357 12072507091350833254490759)
  ·
    refine ⟨18108760637026249881736139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12072507091350833254490759 18108760637026249881736139)
    ·
      refine ⟨27163140955539374822604209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18108760637026249881736139 27163140955539374822604209)
      ·
        refine ⟨20372355716654531116953157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27163140955539374822604209 20372355716654531116953157)
        ·
          refine ⟨3819816696872724584428717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20372355716654531116953157 3819816696872724584428717)
          ·
            refine ⟨1432431261327271719160769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3819816696872724584428717 1432431261327271719160769)
            ·
              refine ⟨1074323445995453789370577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432431261327271719160769 1074323445995453789370577)
              ·
                refine ⟨805742584496590342027933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074323445995453789370577 805742584496590342027933)
                ·
                  refine ⟨302153469186221378260475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805742584496590342027933 302153469186221378260475)
                  ·
                    rfl

theorem cell21_1323994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_1323994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1323994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1323994 prefixEnd_1323994 := by exact prefixLift 1323994
  have htrace : WordTrace (prefixWord ++ tailWord_1323994) baseStart_1323994 baseEnd_1323994 := by
    simpa [prefixWord, tailWord_1323994, baseEnd_1323994] using wordTrace_append hprefix tailTrace_1323994
  have hstable : (prefixWord ++ tailWord_1323994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323994).length < 2 ^ (prefixWord ++ tailWord_1323994).sum := by decide
  have hdescent : baseEnd_1323994 < baseStart_1323994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324022 : List Nat := [5, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1324022 : Nat := 118140960795 + 1324022 * 2 ^ 59
def prefixEnd_1324022 : Nat := 4983230072969 + 3 ^ 40 * 1324022 * 2
def baseEnd_1324022 : Nat := 100719953055899850597917

theorem tailTrace_1324022 : CollatzResearch.WordTrace tailWord_1324022 prefixEnd_1324022 100719953055899850597917 := by
  unfold tailWord_1324022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018190600581368362498895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32194033072867929199988213 3018190600581368362498895)
  ·
    refine ⟨4527285900872052543748343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3018190600581368362498895 4527285900872052543748343)
    ·
      refine ⟨6790928851308078815622515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4527285900872052543748343 6790928851308078815622515)
      ·
        refine ⟨10186393276962118223433773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6790928851308078815622515 10186393276962118223433773)
        ·
          refine ⟨3819897478860794333787665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10186393276962118223433773 3819897478860794333787665)
          ·
            refine ⟨2864923109145595750340749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3819897478860794333787665 2864923109145595750340749)
            ·
              refine ⟨1074346165929598406377781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2864923109145595750340749 1074346165929598406377781)
              ·
                refine ⟨100719953055899850597917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1074346165929598406377781 100719953055899850597917)
                ·
                  rfl

theorem cell21_1324022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1324022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324022 prefixEnd_1324022 := by exact prefixLift 1324022
  have htrace : WordTrace (prefixWord ++ tailWord_1324022) baseStart_1324022 baseEnd_1324022 := by
    simpa [prefixWord, tailWord_1324022, baseEnd_1324022] using wordTrace_append hprefix tailTrace_1324022
  have hstable : (prefixWord ++ tailWord_1324022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324022).length < 2 ^ (prefixWord ++ tailWord_1324022).sum := by decide
  have hdescent : baseEnd_1324022 < baseStart_1324022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324067 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 4]
def baseStart_1324067 : Nat := 118140960795 + 1324067 * 2 ^ 59
def prefixEnd_1324067 : Nat := 4983230072969 + 3 ^ 40 * 1324067 * 2
def baseEnd_1324067 : Nat := 302170128780789473543659

theorem tailTrace_1324067 : CollatzResearch.WordTrace tailWord_1324067 prefixEnd_1324067 302170128780789473543659 := by
  unfold tailWord_1324067
  simp only [CollatzResearch.WordTrace]
  refine ⟨48292690894138866485370455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32195127262759244323580303 48292690894138866485370455)
  ·
    refine ⟨72439036341208299728055683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48292690894138866485370455 72439036341208299728055683)
    ·
      refine ⟨108658554511812449592083525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72439036341208299728055683 108658554511812449592083525)
      ·
        refine ⟨20373478970964834298515661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108658554511812449592083525 20373478970964834298515661)
        ·
          refine ⟨7640054614111812861943373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20373478970964834298515661 7640054614111812861943373)
          ·
            refine ⟨2865020480291929823228765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7640054614111812861943373 2865020480291929823228765)
            ·
              refine ⟨1074382680109473683710787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2865020480291929823228765 1074382680109473683710787)
              ·
                refine ⟨1611574020164210525566181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074382680109473683710787 1611574020164210525566181)
                ·
                  refine ⟨302170128780789473543659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611574020164210525566181 302170128780789473543659)
                  ·
                    rfl

theorem cell21_1324067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 4].length) (baseStart_1324067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324067 prefixEnd_1324067 := by exact prefixLift 1324067
  have htrace : WordTrace (prefixWord ++ tailWord_1324067) baseStart_1324067 baseEnd_1324067 := by
    simpa [prefixWord, tailWord_1324067, baseEnd_1324067] using wordTrace_append hprefix tailTrace_1324067
  have hstable : (prefixWord ++ tailWord_1324067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324067).length < 2 ^ (prefixWord ++ tailWord_1324067).sum := by decide
  have hdescent : baseEnd_1324067 < baseStart_1324067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324118 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1324118 : Nat := 118140960795 + 1324118 * 2 ^ 59
def prefixEnd_1324118 : Nat := 4983230072969 + 3 ^ 40 * 1324118 * 2
def baseEnd_1324118 : Nat := 302181767675624718193555

theorem tailTrace_1324118 : CollatzResearch.WordTrace tailWord_1324118 prefixEnd_1324118 302181767675624718193555 := by
  unfold tailWord_1324118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018409438559631387217313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32196367344636068130318005 3018409438559631387217313)
  ·
    refine ⟨2263807078919723540412985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3018409438559631387217313 2263807078919723540412985)
    ·
      refine ⟨1697855309189792655309739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2263807078919723540412985 1697855309189792655309739)
      ·
        refine ⟨2546782963784688982964609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1697855309189792655309739 2546782963784688982964609)
        ·
          refine ⟨1910087222838516737223457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2546782963784688982964609 1910087222838516737223457)
          ·
            refine ⟨1432565417128887552917593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1910087222838516737223457 1432565417128887552917593)
            ·
              refine ⟨1074424062846665664688195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432565417128887552917593 1074424062846665664688195)
              ·
                refine ⟨1611636094269998497032293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074424062846665664688195 1611636094269998497032293)
                ·
                  refine ⟨302181767675624718193555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611636094269998497032293 302181767675624718193555)
                  ·
                    rfl

theorem cell21_1324118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1324118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324118 prefixEnd_1324118 := by exact prefixLift 1324118
  have htrace : WordTrace (prefixWord ++ tailWord_1324118) baseStart_1324118 baseEnd_1324118 := by
    simpa [prefixWord, tailWord_1324118, baseEnd_1324118] using wordTrace_append hprefix tailTrace_1324118
  have hstable : (prefixWord ++ tailWord_1324118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324118).length < 2 ^ (prefixWord ++ tailWord_1324118).sum := by decide
  have hdescent : baseEnd_1324118 < baseStart_1324118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324275 : List Nat := [1, 1, 1, 2, 2, 5, 9]
def baseStart_1324275 : Nat := 118140960795 + 1324275 * 2 ^ 59
def prefixEnd_1324275 : Nat := 4983230072969 + 3 ^ 40 * 1324275 * 2
def baseEnd_1324275 : Nat := 33579733023847481564063

theorem tailTrace_1324275 : CollatzResearch.WordTrace tailWord_1324275 prefixEnd_1324275 33579733023847481564063 := by
  unfold tailWord_1324275
  simp only [CollatzResearch.WordTrace]
  refine ⟨48300277277385318008942279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32200184851590212005961519 48300277277385318008942279)
  ·
    refine ⟨72450415916077977013413419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48300277277385318008942279 72450415916077977013413419)
    ·
      refine ⟨108675623874116965520120129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72450415916077977013413419 108675623874116965520120129)
      ·
        refine ⟨81506717905587724140090097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108675623874116965520120129 81506717905587724140090097)
        ·
          refine ⟨61130038429190793105067573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81506717905587724140090097 61130038429190793105067573)
          ·
            refine ⟨5730941102736636853600085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61130038429190793105067573 5730941102736636853600085)
            ·
              refine ⟨33579733023847481564063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5730941102736636853600085 33579733023847481564063)
              ·
                rfl

theorem cell21_1324275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 9].length) (baseStart_1324275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324275 prefixEnd_1324275 := by exact prefixLift 1324275
  have htrace : WordTrace (prefixWord ++ tailWord_1324275) baseStart_1324275 baseEnd_1324275 := by
    simpa [prefixWord, tailWord_1324275, baseEnd_1324275] using wordTrace_append hprefix tailTrace_1324275
  have hstable : (prefixWord ++ tailWord_1324275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324275).length < 2 ^ (prefixWord ++ tailWord_1324275).sum := by decide
  have hdescent : baseEnd_1324275 < baseStart_1324275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
