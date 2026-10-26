import V185TrunkScan22Chunk361

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3228836 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 5]
def baseStart_3228836 : Nat := 118140960795 + 3228836 * 2 ^ 59
def prefixEnd_3228836 : Nat := 4983230072969 + 3 ^ 40 * 3228836 * 2
def baseEnd_3228836 : Nat := 368432182786807644000191

theorem tailTrace_3228836 : CollatzResearch.WordTrace tailWord_3228836 prefixEnd_3228836 368432182786807644000191 := by
  unfold tailWord_3228836
  simp only [CollatzResearch.WordTrace]
  refine ⟨58882661865243044065713181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78510215820324058754284241 58882661865243044065713181)
  ·
    refine ⟨22080998199466141524642443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58882661865243044065713181 22080998199466141524642443)
    ·
      refine ⟨33121497299199212286963665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22080998199466141524642443 33121497299199212286963665)
      ·
        refine ⟨24841122974399409215222749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33121497299199212286963665 24841122974399409215222749)
        ·
          refine ⟨9315421115399778455708531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24841122974399409215222749 9315421115399778455708531)
          ·
            refine ⟨13973131673099667683562797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315421115399778455708531 13973131673099667683562797)
            ·
              refine ⟨5239924377412375381336049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13973131673099667683562797 5239924377412375381336049)
              ·
                refine ⟨3929943283059281536002037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239924377412375381336049 3929943283059281536002037)
                ·
                  refine ⟨368432182786807644000191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3929943283059281536002037 368432182786807644000191)
                  ·
                    rfl

theorem cell22_3228836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_3228836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228836 prefixEnd_3228836 := by exact prefixLift 3228836
  have htrace : WordTrace (prefixWord ++ tailWord_3228836) baseStart_3228836 baseEnd_3228836 := by
    simpa [prefixWord, tailWord_3228836, baseEnd_3228836] using wordTrace_append hprefix tailTrace_3228836
  have hstable : (prefixWord ++ tailWord_3228836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228836).length < 2 ^ (prefixWord ++ tailWord_3228836).sum := by decide
  have hdescent : baseEnd_3228836 < baseStart_3228836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228896 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 4, 3]
def baseStart_3228896 : Nat := 118140960795 + 3228896 * 2 ^ 59
def prefixEnd_3228896 : Nat := 4983230072969 + 3 ^ 40 * 3228896 * 2
def baseEnd_3228896 : Nat := 1105317087586602775500389

theorem tailTrace_3228896 : CollatzResearch.WordTrace tailWord_3228896 prefixEnd_3228896 1105317087586602775500389 := by
  unfold tailWord_3228896
  simp only [CollatzResearch.WordTrace]
  refine ⟨58883756055134359189305271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78511674740179145585740361 58883756055134359189305271)
  ·
    refine ⟨88325634082701538783957907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58883756055134359189305271 88325634082701538783957907)
    ·
      refine ⟨132488451124052308175936861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88325634082701538783957907 132488451124052308175936861)
      ·
        refine ⟨49683169171519615565976323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132488451124052308175936861 49683169171519615565976323)
        ·
          refine ⟨74524753757279423348964485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49683169171519615565976323 74524753757279423348964485)
          ·
            refine ⟨13973391329489891877930841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74524753757279423348964485 13973391329489891877930841)
            ·
              refine ⟨10480043497117418908448131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13973391329489891877930841 10480043497117418908448131)
              ·
                refine ⟨15720065245676128362672197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10480043497117418908448131 15720065245676128362672197)
                ·
                  refine ⟨2947512233564274068001037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15720065245676128362672197 2947512233564274068001037)
                  ·
                    refine ⟨1105317087586602775500389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2947512233564274068001037 1105317087586602775500389)
                    ·
                      rfl

theorem cell22_3228896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_3228896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228896 prefixEnd_3228896 := by exact prefixLift 3228896
  have htrace : WordTrace (prefixWord ++ tailWord_3228896) baseStart_3228896 baseEnd_3228896 := by
    simpa [prefixWord, tailWord_3228896, baseEnd_3228896] using wordTrace_append hprefix tailTrace_3228896
  have hstable : (prefixWord ++ tailWord_3228896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228896).length < 2 ^ (prefixWord ++ tailWord_3228896).sum := by decide
  have hdescent : baseEnd_3228896 < baseStart_3228896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228926 : List Nat := [4, 2, 2, 1, 1, 2, 2, 8]
def baseStart_3228926 : Nat := 118140960795 + 3228926 * 2 ^ 59
def prefixEnd_3228926 : Nat := 4983230072969 + 3 ^ 40 * 3228926 * 2
def baseEnd_3228926 : Nat := 122814150799965855250033

theorem tailTrace_3228926 : CollatzResearch.WordTrace tailWord_3228926 prefixEnd_3228926 122814150799965855250033 := by
  unfold tailWord_3228926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721075787520004187775329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78512404200106689001468421 14721075787520004187775329)
  ·
    refine ⟨11040806840640003140831497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14721075787520004187775329 11040806840640003140831497)
    ·
      refine ⟨8280605130480002355623623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11040806840640003140831497 8280605130480002355623623)
      ·
        refine ⟨12420907695720003533435435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8280605130480002355623623 12420907695720003533435435)
        ·
          refine ⟨18631361543580005300153153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12420907695720003533435435 18631361543580005300153153)
          ·
            refine ⟨13973521157685003975114865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18631361543580005300153153 13973521157685003975114865)
            ·
              refine ⟨10480140868263752981336149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13973521157685003975114865 10480140868263752981336149)
              ·
                refine ⟨122814150799965855250033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10480140868263752981336149 122814150799965855250033)
                ·
                  rfl

theorem cell22_3228926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_3228926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3228926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3228926 prefixEnd_3228926 := by exact prefixLift 3228926
  have htrace : WordTrace (prefixWord ++ tailWord_3228926) baseStart_3228926 baseEnd_3228926 := by
    simpa [prefixWord, tailWord_3228926, baseEnd_3228926] using wordTrace_append hprefix tailTrace_3228926
  have hstable : (prefixWord ++ tailWord_3228926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228926).length < 2 ^ (prefixWord ++ tailWord_3228926).sum := by decide
  have hdescent : baseEnd_3228926 < baseStart_3228926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229005 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3229005 : Nat := 118140960795 + 3229005 * 2 ^ 59
def prefixEnd_3229005 : Nat := 4983230072969 + 3 ^ 40 * 3229005 * 2
def baseEnd_3229005 : Nat := 368451466838054274841685

theorem tailTrace_3229005 : CollatzResearch.WordTrace tailWord_3229005 prefixEnd_3229005 368451466838054274841685 := by
  unfold tailWord_3229005
  simp only [CollatzResearch.WordTrace]
  refine ⟨117771487666873829994328469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78514325111249219996218979 117771487666873829994328469)
  ·
    refine ⟨5520538484384710780984147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117771487666873829994328469 5520538484384710780984147)
    ·
      refine ⟨8280807726577066171476221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5520538484384710780984147 8280807726577066171476221)
      ·
        refine ⟨3105302897466399814303583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8280807726577066171476221 3105302897466399814303583)
        ·
          refine ⟨4657954346199599721455375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105302897466399814303583 4657954346199599721455375)
          ·
            refine ⟨6986931519299399582183063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657954346199599721455375 6986931519299399582183063)
            ·
              refine ⟨10480397278949099373274595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986931519299399582183063 10480397278949099373274595)
              ·
                refine ⟨15720595918423649059911893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10480397278949099373274595 15720595918423649059911893)
                ·
                  refine ⟨368451466838054274841685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15720595918423649059911893 368451466838054274841685)
                  ·
                    rfl

theorem cell22_3229005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3229005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229005 prefixEnd_3229005 := by exact prefixLift 3229005
  have htrace : WordTrace (prefixWord ++ tailWord_3229005) baseStart_3229005 baseEnd_3229005 := by
    simpa [prefixWord, tailWord_3229005, baseEnd_3229005] using wordTrace_append hprefix tailTrace_3229005
  have hstable : (prefixWord ++ tailWord_3229005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229005).length < 2 ^ (prefixWord ++ tailWord_3229005).sum := by decide
  have hdescent : baseEnd_3229005 < baseStart_3229005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229016 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 6]
def baseStart_3229016 : Nat := 118140960795 + 3229016 * 2 ^ 59
def prefixEnd_3229016 : Nat := 4983230072969 + 3 ^ 40 * 3229016 * 2
def baseEnd_3229016 : Nat := 368452722012987487500007

theorem tailTrace_3229016 : CollatzResearch.WordTrace tailWord_3229016 prefixEnd_3229016 368452722012987487500007 := by
  unfold tailWord_3229016
  simp only [CollatzResearch.WordTrace]
  refine ⟨58885944434916989436489451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78514592579889319248652601 58885944434916989436489451)
  ·
    refine ⟨88328916652375484154734177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58885944434916989436489451 88328916652375484154734177)
    ·
      refine ⟨66246687489281613116050633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88328916652375484154734177 66246687489281613116050633)
      ·
        refine ⟨49685015616961209837037975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66246687489281613116050633 49685015616961209837037975)
        ·
          refine ⟨74527523425441814755556963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49685015616961209837037975 74527523425441814755556963)
          ·
            refine ⟨111791285138162722133335445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74527523425441814755556963 111791285138162722133335445)
            ·
              refine ⟨5240216490851377600000099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111791285138162722133335445 5240216490851377600000099)
              ·
                refine ⟨7860324736277066400000149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240216490851377600000099 7860324736277066400000149)
                ·
                  refine ⟨368452722012987487500007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7860324736277066400000149 368452722012987487500007)
                  ·
                    rfl

theorem cell22_3229016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_3229016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229016 prefixEnd_3229016 := by exact prefixLift 3229016
  have htrace : WordTrace (prefixWord ++ tailWord_3229016) baseStart_3229016 baseEnd_3229016 := by
    simpa [prefixWord, tailWord_3229016, baseEnd_3229016] using wordTrace_append hprefix tailTrace_3229016
  have hstable : (prefixWord ++ tailWord_3229016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229016).length < 2 ^ (prefixWord ++ tailWord_3229016).sum := by decide
  have hdescent : baseEnd_3229016 < baseStart_3229016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229063 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3229063 : Nat := 118140960795 + 3229063 * 2 ^ 59
def prefixEnd_3229063 : Nat := 4983230072969 + 3 ^ 40 * 3229063 * 2
def baseEnd_3229063 : Nat := 1105374255099470006574877

theorem tailTrace_3229063 : CollatzResearch.WordTrace tailWord_3229063 prefixEnd_3229063 1105374255099470006574877 := by
  unfold tailWord_3229063
  simp only [CollatzResearch.WordTrace]
  refine ⟨117773603100663705899939843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78515735400442470599959895 117773603100663705899939843)
  ·
    refine ⟨176660404650995558849909765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117773603100663705899939843 176660404650995558849909765)
    ·
      refine ⟨33123825872061667284358081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176660404650995558849909765 33123825872061667284358081)
      ·
        refine ⟨24842869404046250463268561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33123825872061667284358081 24842869404046250463268561)
        ·
          refine ⟨18632152053034687847451421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24842869404046250463268561 18632152053034687847451421)
          ·
            refine ⟨6987057019888007942794283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18632152053034687847451421 6987057019888007942794283)
            ·
              refine ⟨10480585529832011914191425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987057019888007942794283 10480585529832011914191425)
              ·
                refine ⟨7860439147374008935643569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10480585529832011914191425 7860439147374008935643569)
                ·
                  refine ⟨5895329360530506701732677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7860439147374008935643569 5895329360530506701732677)
                  ·
                    refine ⟨1105374255099470006574877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5895329360530506701732677 1105374255099470006574877)
                    ·
                      rfl

theorem cell22_3229063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3229063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229063 prefixEnd_3229063 := by exact prefixLift 3229063
  have htrace : WordTrace (prefixWord ++ tailWord_3229063) baseStart_3229063 baseEnd_3229063 := by
    simpa [prefixWord, tailWord_3229063, baseEnd_3229063] using wordTrace_append hprefix tailTrace_3229063
  have hstable : (prefixWord ++ tailWord_3229063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229063).length < 2 ^ (prefixWord ++ tailWord_3229063).sum := by decide
  have hdescent : baseEnd_3229063 < baseStart_3229063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229106 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_3229106 : Nat := 118140960795 + 3229106 * 2 ^ 59
def prefixEnd_3229106 : Nat := 4983230072969 + 3 ^ 40 * 3229106 * 2
def baseEnd_3229106 : Nat := 368462991626077409249915

theorem tailTrace_3229106 : CollatzResearch.WordTrace tailWord_3229106 prefixEnd_3229106 368462991626077409249915 := by
  unfold tailWord_3229106
  simp only [CollatzResearch.WordTrace]
  refine ⟨29443792859876981060938793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78516780959671949495836781 29443792859876981060938793)
  ·
    refine ⟨22082844644907735795704095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29443792859876981060938793 22082844644907735795704095)
    ·
      refine ⟨33124266967361603693556143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22082844644907735795704095 33124266967361603693556143)
      ·
        refine ⟨49686400451042405540334215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33124266967361603693556143 49686400451042405540334215)
        ·
          refine ⟨74529600676563608310501323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49686400451042405540334215 74529600676563608310501323)
          ·
            refine ⟨111794401014845412465751985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74529600676563608310501323 111794401014845412465751985)
            ·
              refine ⟨83845800761134059349313989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111794401014845412465751985 83845800761134059349313989)
              ·
                refine ⟨15721087642712636127996373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83845800761134059349313989 15721087642712636127996373)
                ·
                  refine ⟨368462991626077409249915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15721087642712636127996373 368462991626077409249915)
                  ·
                    rfl

theorem cell22_3229106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_3229106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229106 prefixEnd_3229106 := by exact prefixLift 3229106
  have htrace : WordTrace (prefixWord ++ tailWord_3229106) baseStart_3229106 baseEnd_3229106 := by
    simpa [prefixWord, tailWord_3229106, baseEnd_3229106] using wordTrace_append hprefix tailTrace_3229106
  have hstable : (prefixWord ++ tailWord_3229106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229106).length < 2 ^ (prefixWord ++ tailWord_3229106).sum := by decide
  have hdescent : baseEnd_3229106 < baseStart_3229106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229153 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3229153 : Nat := 118140960795 + 3229153 * 2 ^ 59
def prefixEnd_3229153 : Nat := 4983230072969 + 3 ^ 40 * 3229153 * 2
def baseEnd_3229153 : Nat := 1105405063938739771824601

theorem tailTrace_3229153 : CollatzResearch.WordTrace tailWord_3229153 prefixEnd_3229153 1105405063938739771824601 := by
  unfold tailWord_3229153
  simp only [CollatzResearch.WordTrace]
  refine ⟨117776885670337651270716113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78517923780225100847144075 117776885670337651270716113)
  ·
    refine ⟨88332664252753238453037085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117776885670337651270716113 88332664252753238453037085)
    ·
      refine ⟨33124749094782464419888907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88332664252753238453037085 33124749094782464419888907)
      ·
        refine ⟨49687123642173696629833361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33124749094782464419888907 49687123642173696629833361)
        ·
          refine ⟨37265342731630272472375021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49687123642173696629833361 37265342731630272472375021)
          ·
            refine ⟨13974503524361352177140633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37265342731630272472375021 13974503524361352177140633)
            ·
              refine ⟨10480877643271014132855475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13974503524361352177140633 10480877643271014132855475)
              ·
                refine ⟨15721316464906521199283213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10480877643271014132855475 15721316464906521199283213)
                ·
                  refine ⟨5895493674339945449731205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15721316464906521199283213 5895493674339945449731205)
                  ·
                    refine ⟨1105405063938739771824601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5895493674339945449731205 1105405063938739771824601)
                    ·
                      rfl

theorem cell22_3229153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3229153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229153 prefixEnd_3229153 := by exact prefixLift 3229153
  have htrace : WordTrace (prefixWord ++ tailWord_3229153) baseStart_3229153 baseEnd_3229153 := by
    simpa [prefixWord, tailWord_3229153, baseEnd_3229153] using wordTrace_append hprefix tailTrace_3229153
  have hstable : (prefixWord ++ tailWord_3229153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229153).length < 2 ^ (prefixWord ++ tailWord_3229153).sum := by decide
  have hdescent : baseEnd_3229153 < baseStart_3229153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229185 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 6]
def baseStart_3229185 : Nat := 118140960795 + 3229185 * 2 ^ 59
def prefixEnd_3229185 : Nat := 4983230072969 + 3 ^ 40 * 3229185 * 2
def baseEnd_3229185 : Nat := 368472006064234118341501

theorem tailTrace_3229185 : CollatzResearch.WordTrace tailWord_3229185 prefixEnd_3229185 368472006064234118341501 := by
  unfold tailWord_3229185
  simp only [CollatzResearch.WordTrace]
  refine ⟨117778052806221720735881009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78518701870814480490587339 117778052806221720735881009)
  ·
    refine ⟨88333539604666290551910757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117778052806221720735881009 88333539604666290551910757)
    ·
      refine ⟨16562538675874929478483267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88333539604666290551910757 16562538675874929478483267)
      ·
        refine ⟨24843808013812394217724901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16562538675874929478483267 24843808013812394217724901)
        ·
          refine ⟨4658214002589823915823419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24843808013812394217724901 4658214002589823915823419)
          ·
            refine ⟨6987321003884735873735129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658214002589823915823419 6987321003884735873735129)
            ·
              refine ⟨5240490752913551905301347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6987321003884735873735129 5240490752913551905301347)
              ·
                refine ⟨7860736129370327857952021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240490752913551905301347 7860736129370327857952021)
                ·
                  refine ⟨368472006064234118341501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7860736129370327857952021 368472006064234118341501)
                  ·
                    rfl

theorem cell22_3229185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_3229185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229185 prefixEnd_3229185 := by exact prefixLift 3229185
  have htrace : WordTrace (prefixWord ++ tailWord_3229185) baseStart_3229185 baseEnd_3229185 := by
    simpa [prefixWord, tailWord_3229185, baseEnd_3229185] using wordTrace_append hprefix tailTrace_3229185
  have hstable : (prefixWord ++ tailWord_3229185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229185).length < 2 ^ (prefixWord ++ tailWord_3229185).sum := by decide
  have hdescent : baseEnd_3229185 < baseStart_3229185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229204 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3229204 : Nat := 118140960795 + 3229204 * 2 ^ 59
def prefixEnd_3229204 : Nat := 4983230072969 + 3 ^ 40 * 3229204 * 2
def baseEnd_3229204 : Nat := 1105422522280992638799445

theorem tailTrace_3229204 : CollatzResearch.WordTrace tailWord_3229204 prefixEnd_3229204 1105422522280992638799445 := by
  unfold tailWord_3229204
  simp only [CollatzResearch.WordTrace]
  refine ⟨58889372896576443490411333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78519163862101924653881777 58889372896576443490411333)
  ·
    refine ⟨11041757418108083154452125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58889372896576443490411333 11041757418108083154452125)
    ·
      refine ⟨4140659031790531182919547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11041757418108083154452125 4140659031790531182919547)
      ·
        refine ⟨6210988547685796774379321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140659031790531182919547 6210988547685796774379321)
        ·
          refine ⟨4658241410764347580784491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6210988547685796774379321 4658241410764347580784491)
          ·
            refine ⟨6987362116146521371176737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658241410764347580784491 6987362116146521371176737)
            ·
              refine ⟨5240521587109891028382553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6987362116146521371176737 5240521587109891028382553)
              ·
                refine ⟨3930391190332418271286915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5240521587109891028382553 3930391190332418271286915)
                ·
                  refine ⟨5895586785498627406930373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930391190332418271286915 5895586785498627406930373)
                  ·
                    refine ⟨1105422522280992638799445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5895586785498627406930373 1105422522280992638799445)
                    ·
                      rfl

theorem cell22_3229204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3229204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229204 prefixEnd_3229204 := by exact prefixLift 3229204
  have htrace : WordTrace (prefixWord ++ tailWord_3229204) baseStart_3229204 baseEnd_3229204 := by
    simpa [prefixWord, tailWord_3229204, baseEnd_3229204] using wordTrace_append hprefix tailTrace_3229204
  have hstable : (prefixWord ++ tailWord_3229204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229204).length < 2 ^ (prefixWord ++ tailWord_3229204).sum := by decide
  have hdescent : baseEnd_3229204 < baseStart_3229204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229213 : List Nat := [1, 4, 2, 2, 1, 1, 3, 8]
def baseStart_3229213 : Nat := 118140960795 + 3229213 * 2 ^ 59
def prefixEnd_3229213 : Nat := 4983230072969 + 3 ^ 40 * 3229213 * 2
def baseEnd_3229213 : Nat := 122825067018324401702713

theorem tailTrace_3229213 : CollatzResearch.WordTrace tailWord_3229213 prefixEnd_3229213 122825067018324401702713 := by
  unfold tailWord_3229213
  simp only [CollatzResearch.WordTrace]
  refine ⟨117779074050120281517900293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78519382700080187678600195 117779074050120281517900293)
  ·
    refine ⟨22083576384397552784606305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117779074050120281517900293 22083576384397552784606305)
    ·
      refine ⟨16562682288298164588454729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22083576384397552784606305 16562682288298164588454729)
      ·
        refine ⟨12422011716223623441341047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16562682288298164588454729 12422011716223623441341047)
        ·
          refine ⟨18633017574335435162011571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12422011716223623441341047 18633017574335435162011571)
          ·
            refine ⟨27949526361503152743017357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18633017574335435162011571 27949526361503152743017357)
            ·
              refine ⟨10481072385563682278631509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27949526361503152743017357 10481072385563682278631509)
              ·
                refine ⟨122825067018324401702713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10481072385563682278631509 122825067018324401702713)
                ·
                  rfl

theorem cell22_3229213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 8].length) (baseStart_3229213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229213 prefixEnd_3229213 := by exact prefixLift 3229213
  have htrace : WordTrace (prefixWord ++ tailWord_3229213) baseStart_3229213 baseEnd_3229213 := by
    simpa [prefixWord, tailWord_3229213, baseEnd_3229213] using wordTrace_append hprefix tailTrace_3229213
  have hstable : (prefixWord ++ tailWord_3229213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229213).length < 2 ^ (prefixWord ++ tailWord_3229213).sum := by decide
  have hdescent : baseEnd_3229213 < baseStart_3229213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229219 : List Nat := [1, 1, 1, 4, 6, 1, 1, 3, 4]
def baseStart_3229219 : Nat := 118140960795 + 3229219 * 2 ^ 59
def prefixEnd_3229219 : Nat := 4983230072969 + 3 ^ 40 * 3229219 * 2
def baseEnd_3229219 : Nat := 368475885695845866558133

theorem tailTrace_3229219 : CollatzResearch.WordTrace tailWord_3229219 prefixEnd_3229219 368475885695845866558133 := by
  unfold tailWord_3229219
  simp only [CollatzResearch.WordTrace]
  refine ⟨117779292888098544542618711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78519528592065696361745807 117779292888098544542618711)
  ·
    refine ⟨176668939332147816813928067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117779292888098544542618711 176668939332147816813928067)
    ·
      refine ⟨265003408998221725220892101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176668939332147816813928067 265003408998221725220892101)
      ·
        refine ⟨49688139187166573478917269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265003408998221725220892101 49688139187166573478917269)
        ·
          refine ⟨2329131524398433131824247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49688139187166573478917269 2329131524398433131824247)
          ·
            refine ⟨3493697286597649697736371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329131524398433131824247 3493697286597649697736371)
            ·
              refine ⟨5240545929896474546604557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493697286597649697736371 5240545929896474546604557)
              ·
                refine ⟨1965204723711177954976709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5240545929896474546604557 1965204723711177954976709)
                ·
                  refine ⟨368475885695845866558133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1965204723711177954976709 368475885695845866558133)
                  ·
                    rfl

theorem cell22_3229219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 4].length) (baseStart_3229219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229219 prefixEnd_3229219 := by exact prefixLift 3229219
  have htrace : WordTrace (prefixWord ++ tailWord_3229219) baseStart_3229219 baseEnd_3229219 := by
    simpa [prefixWord, tailWord_3229219, baseEnd_3229219] using wordTrace_append hprefix tailTrace_3229219
  have hstable : (prefixWord ++ tailWord_3229219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229219).length < 2 ^ (prefixWord ++ tailWord_3229219).sum := by decide
  have hdescent : baseEnd_3229219 < baseStart_3229219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229230 : List Nat := [4, 1, 3, 1, 2, 3, 8]
def baseStart_3229230 : Nat := 118140960795 + 3229230 * 2 ^ 59
def prefixEnd_3229230 : Nat := 4983230072969 + 3 ^ 40 * 3229230 * 2
def baseEnd_3229230 : Nat := 40941904541197675468495

theorem tailTrace_3229230 : CollatzResearch.WordTrace tailWord_3229230 prefixEnd_3229230 40941904541197675468495 := by
  unfold tailWord_3229230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14722461761382336677658643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78519796060705795614179429 14722461761382336677658643)
  ·
    refine ⟨22083692642073505016487965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14722461761382336677658643 22083692642073505016487965)
    ·
      refine ⟨8281384740777564381182987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22083692642073505016487965 8281384740777564381182987)
      ·
        refine ⟨12422077111166346571774481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8281384740777564381182987 12422077111166346571774481)
        ·
          refine ⟨9316557833374759928830861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12422077111166346571774481 9316557833374759928830861)
          ·
            refine ⟨3493709187515534973311573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9316557833374759928830861 3493709187515534973311573)
            ·
              refine ⟨40941904541197675468495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3493709187515534973311573 40941904541197675468495)
              ·
                rfl

theorem cell22_3229230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 8].length) (baseStart_3229230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229230 prefixEnd_3229230 := by exact prefixLift 3229230
  have htrace : WordTrace (prefixWord ++ tailWord_3229230) baseStart_3229230 baseEnd_3229230 := by
    simpa [prefixWord, tailWord_3229230, baseEnd_3229230] using wordTrace_append hprefix tailTrace_3229230
  have hstable : (prefixWord ++ tailWord_3229230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229230).length < 2 ^ (prefixWord ++ tailWord_3229230).sum := by decide
  have hdescent : baseEnd_3229230 < baseStart_3229230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229296 : List Nat := [2, 1, 1, 1, 6, 3, 2, 2, 1, 3]
def baseStart_3229296 : Nat := 118140960795 + 3229296 * 2 ^ 59
def prefixEnd_3229296 : Nat := 4983230072969 + 3 ^ 40 * 3229296 * 2
def baseEnd_3229296 : Nat := 1105454015761135065499163

theorem tailTrace_3229296 : CollatzResearch.WordTrace tailWord_3229296 prefixEnd_3229296 1105454015761135065499163 := by
  unfold tailWord_3229296
  simp only [CollatzResearch.WordTrace]
  refine ⟨58891050654409793346585871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78521400872546391128781161 58891050654409793346585871)
  ·
    refine ⟨88336575981614690019878807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58891050654409793346585871 88336575981614690019878807)
    ·
      refine ⟨132504863972422035029818211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88336575981614690019878807 132504863972422035029818211)
      ·
        refine ⟨198757295958633052544727317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132504863972422035029818211 198757295958633052544727317)
        ·
          refine ⟨9316748248060924338034093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198757295958633052544727317 9316748248060924338034093)
          ·
            refine ⟨3493780593022846626762785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9316748248060924338034093 3493780593022846626762785)
            ·
              refine ⟨2620335444767134970072089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3493780593022846626762785 2620335444767134970072089)
              ·
                refine ⟨1965251583575351227554067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2620335444767134970072089 1965251583575351227554067)
                ·
                  refine ⟨2947877375363026841331101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965251583575351227554067 2947877375363026841331101)
                  ·
                    refine ⟨1105454015761135065499163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2947877375363026841331101 1105454015761135065499163)
                    ·
                      rfl

theorem cell22_3229296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 3].length) (baseStart_3229296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229296 prefixEnd_3229296 := by exact prefixLift 3229296
  have htrace : WordTrace (prefixWord ++ tailWord_3229296) baseStart_3229296 baseEnd_3229296 := by
    simpa [prefixWord, tailWord_3229296, baseEnd_3229296] using wordTrace_append hprefix tailTrace_3229296
  have hstable : (prefixWord ++ tailWord_3229296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229296).length < 2 ^ (prefixWord ++ tailWord_3229296).sum := by decide
  have hdescent : baseEnd_3229296 < baseStart_3229296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229303 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 6]
def baseStart_3229303 : Nat := 118140960795 + 3229303 * 2 ^ 59
def prefixEnd_3229303 : Nat := 4983230072969 + 3 ^ 40 * 3229303 * 2
def baseEnd_3229303 : Nat := 368485470668063126858047

theorem tailTrace_3229303 : CollatzResearch.WordTrace tailWord_3229303 prefixEnd_3229303 368485470668063126858047 := by
  unfold tailWord_3229303
  simp only [CollatzResearch.WordTrace]
  refine ⟨117782356619794226888676563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78521571079862817925784375 117782356619794226888676563)
  ·
    refine ⟨176673534929691340333014845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117782356619794226888676563 176673534929691340333014845)
    ·
      refine ⟨66252575598634252624880567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176673534929691340333014845 66252575598634252624880567)
      ·
        refine ⟨99378863397951378937320851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66252575598634252624880567 99378863397951378937320851)
        ·
          refine ⟨149068295096927068405981277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99378863397951378937320851 149068295096927068405981277)
          ·
            refine ⟨55900610661347650652242979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149068295096927068405981277 55900610661347650652242979)
            ·
              refine ⟨83850915992021475978364469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55900610661347650652242979 83850915992021475978364469)
              ·
                refine ⟨7861023374252013372971669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83850915992021475978364469 7861023374252013372971669)
                ·
                  refine ⟨368485470668063126858047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7861023374252013372971669 368485470668063126858047)
                  ·
                    rfl

theorem cell22_3229303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 6].length) (baseStart_3229303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229303 prefixEnd_3229303 := by exact prefixLift 3229303
  have htrace : WordTrace (prefixWord ++ tailWord_3229303) baseStart_3229303 baseEnd_3229303 := by
    simpa [prefixWord, tailWord_3229303, baseEnd_3229303] using wordTrace_append hprefix tailTrace_3229303
  have hstable : (prefixWord ++ tailWord_3229303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229303).length < 2 ^ (prefixWord ++ tailWord_3229303).sum := by decide
  have hdescent : baseEnd_3229303 < baseStart_3229303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229335 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 1, 5]
def baseStart_3229335 : Nat := 118140960795 + 3229335 * 2 ^ 59
def prefixEnd_3229335 : Nat := 4983230072969 + 3 ^ 40 * 3229335 * 2
def baseEnd_3229335 : Nat := 1105467366258151963774043

theorem tailTrace_3229335 : CollatzResearch.WordTrace tailWord_3229335 prefixEnd_3229335 1105467366258151963774043 := by
  unfold tailWord_3229335
  simp only [CollatzResearch.WordTrace]
  refine ⟨117783523755678296353841459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78522349170452197569227639 117783523755678296353841459)
  ·
    refine ⟨176675285633517444530762189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117783523755678296353841459 176675285633517444530762189)
    ·
      refine ⟨66253232112569041699035821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176675285633517444530762189 66253232112569041699035821)
      ·
        refine ⟨24844962042213390637138433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66253232112569041699035821 24844962042213390637138433)
        ·
          refine ⟨18633721531660042977853825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24844962042213390637138433 18633721531660042977853825)
          ·
            refine ⟨13975291148745032233390369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18633721531660042977853825 13975291148745032233390369)
            ·
              refine ⟨10481468361558774175042777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13975291148745032233390369 10481468361558774175042777)
              ·
                refine ⟨7861101271169080631282083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10481468361558774175042777 7861101271169080631282083)
                ·
                  refine ⟨11791651906753620946923125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7861101271169080631282083 11791651906753620946923125)
                  ·
                    refine ⟨1105467366258151963774043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11791651906753620946923125 1105467366258151963774043)
                    ·
                      rfl

theorem cell22_3229335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_3229335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229335 prefixEnd_3229335 := by exact prefixLift 3229335
  have htrace : WordTrace (prefixWord ++ tailWord_3229335) baseStart_3229335 baseEnd_3229335 := by
    simpa [prefixWord, tailWord_3229335, baseEnd_3229335] using wordTrace_append hprefix tailTrace_3229335
  have hstable : (prefixWord ++ tailWord_3229335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229335).length < 2 ^ (prefixWord ++ tailWord_3229335).sum := by decide
  have hdescent : baseEnd_3229335 < baseStart_3229335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229380 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3229380 : Nat := 118140960795 + 3229380 * 2 ^ 59
def prefixEnd_3229380 : Nat := 4983230072969 + 3 ^ 40 * 3229380 * 2
def baseEnd_3229380 : Nat := 1105482770677786846398905

theorem tailTrace_3229380 : CollatzResearch.WordTrace tailWord_3229380 prefixEnd_3229380 1105482770677786846398905 := by
  unfold tailWord_3229380
  simp only [CollatzResearch.WordTrace]
  refine ⟨58892582520257634519614797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78523443360343512692819729 58892582520257634519614797)
  ·
    refine ⟨22084718445096612944855549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58892582520257634519614797 22084718445096612944855549)
    ·
      refine ⟨8281769416911229854320831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22084718445096612944855549 8281769416911229854320831)
      ·
        refine ⟨12422654125366844781481247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8281769416911229854320831 12422654125366844781481247)
        ·
          refine ⟨18633981188050267172221871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12422654125366844781481247 18633981188050267172221871)
          ·
            refine ⟨27950971782075400758332807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18633981188050267172221871 27950971782075400758332807)
            ·
              refine ⟨41926457673113101137499211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27950971782075400758332807 41926457673113101137499211)
              ·
                refine ⟨62889686509669651706248817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41926457673113101137499211 62889686509669651706248817)
                ·
                  refine ⟨47167264882252238779686613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62889686509669651706248817 47167264882252238779686613)
                  ·
                    refine ⟨1105482770677786846398905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47167264882252238779686613 1105482770677786846398905)
                    ·
                      rfl

theorem cell22_3229380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3229380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229380 prefixEnd_3229380 := by exact prefixLift 3229380
  have htrace : WordTrace (prefixWord ++ tailWord_3229380) baseStart_3229380 baseEnd_3229380 := by
    simpa [prefixWord, tailWord_3229380, baseEnd_3229380] using wordTrace_append hprefix tailTrace_3229380
  have hstable : (prefixWord ++ tailWord_3229380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229380).length < 2 ^ (prefixWord ++ tailWord_3229380).sum := by decide
  have hdescent : baseEnd_3229380 < baseStart_3229380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229427 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 5]
def baseStart_3229427 : Nat := 118140960795 + 3229427 * 2 ^ 59
def prefixEnd_3229427 : Nat := 4983230072969 + 3 ^ 40 * 3229427 * 2
def baseEnd_3229427 : Nat := 368499619912764796824587

theorem tailTrace_3229427 : CollatzResearch.WordTrace tailWord_3229427 prefixEnd_3229427 368499619912764796824587 := by
  unfold tailWord_3229427
  simp only [CollatzResearch.WordTrace]
  refine ⟨117786879271344996066190535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78524586180896664044127023 117786879271344996066190535)
  ·
    refine ⟨176680318907017494099285803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117786879271344996066190535 176680318907017494099285803)
    ·
      refine ⟨265020478360526241148928705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176680318907017494099285803 265020478360526241148928705)
      ·
        refine ⟨198765358770394680861696529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265020478360526241148928705 198765358770394680861696529)
        ·
          refine ⟨149074019077796010646272397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198765358770394680861696529 149074019077796010646272397)
          ·
            refine ⟨55902757154173503992352149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149074019077796010646272397 55902757154173503992352149)
            ·
              refine ⟨2620441741601882999641507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55902757154173503992352149 2620441741601882999641507)
              ·
                refine ⟨3930662612402824499462261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620441741601882999641507 3930662612402824499462261)
                ·
                  refine ⟨368499619912764796824587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3930662612402824499462261 368499619912764796824587)
                  ·
                    rfl

theorem cell22_3229427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 5].length) (baseStart_3229427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229427 prefixEnd_3229427 := by exact prefixLift 3229427
  have htrace : WordTrace (prefixWord ++ tailWord_3229427) baseStart_3229427 baseEnd_3229427 := by
    simpa [prefixWord, tailWord_3229427, baseEnd_3229427] using wordTrace_append hprefix tailTrace_3229427
  have hstable : (prefixWord ++ tailWord_3229427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229427).length < 2 ^ (prefixWord ++ tailWord_3229427).sum := by decide
  have hdescent : baseEnd_3229427 < baseStart_3229427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229440 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_3229440 : Nat := 118140960795 + 3229440 * 2 ^ 59
def prefixEnd_3229440 : Nat := 4983230072969 + 3 ^ 40 * 3229440 * 2
def baseEnd_3229440 : Nat := 1105503309903966689898721

theorem tailTrace_3229440 : CollatzResearch.WordTrace tailWord_3229440 prefixEnd_3229440 1105503309903966689898721 := by
  unfold tailWord_3229440
  simp only [CollatzResearch.WordTrace]
  refine ⟨58893676710148949643206887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78524902280198599524275849 58893676710148949643206887)
  ·
    refine ⟨88340515065223424464810331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58893676710148949643206887 88340515065223424464810331)
    ·
      refine ⟨132510772597835136697215497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88340515065223424464810331 132510772597835136697215497)
      ·
        refine ⟨99383079448376352522911623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132510772597835136697215497 99383079448376352522911623)
        ·
          refine ⟨149074619172564528784367435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99383079448376352522911623 149074619172564528784367435)
          ·
            refine ⟨223611928758846793176551153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149074619172564528784367435 223611928758846793176551153)
            ·
              refine ⟨167708946569135094882413365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223611928758846793176551153 167708946569135094882413365)
              ·
                refine ⟨15722713740856415145226253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167708946569135094882413365 15722713740856415145226253)
                ·
                  refine ⟨5896017652821155679459845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15722713740856415145226253 5896017652821155679459845)
                  ·
                    refine ⟨1105503309903966689898721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5896017652821155679459845 1105503309903966689898721)
                    ·
                      rfl

theorem cell22_3229440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_3229440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229440 prefixEnd_3229440 := by exact prefixLift 3229440
  have htrace : WordTrace (prefixWord ++ tailWord_3229440) baseStart_3229440 baseEnd_3229440 := by
    simpa [prefixWord, tailWord_3229440, baseEnd_3229440] using wordTrace_append hprefix tailTrace_3229440
  have hstable : (prefixWord ++ tailWord_3229440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229440).length < 2 ^ (prefixWord ++ tailWord_3229440).sum := by decide
  have hdescent : baseEnd_3229440 < baseStart_3229440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229500 : List Nat := [2, 2, 2, 2, 1, 1, 2, 10]
def baseStart_3229500 : Nat := 118140960795 + 3229500 * 2 ^ 59
def prefixEnd_3229500 : Nat := 4983230072969 + 3 ^ 40 * 3229500 * 2
def baseEnd_3229500 : Nat := 122835983236682948155393

theorem tailTrace_3229500 : CollatzResearch.WordTrace tailWord_3229500 prefixEnd_3229500 122835983236682948155393 := by
  unfold tailWord_3229500
  simp only [CollatzResearch.WordTrace]
  refine ⟨58894770900040264766798977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78526361200053686355731969 58894770900040264766798977)
  ·
    refine ⟨44171078175030198575099233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58894770900040264766798977 44171078175030198575099233)
    ·
      refine ⟨33128308631272648931324425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44171078175030198575099233 33128308631272648931324425)
      ·
        refine ⟨24846231473454486698493319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33128308631272648931324425 24846231473454486698493319)
        ·
          refine ⟨37269347210181730047739979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24846231473454486698493319 37269347210181730047739979)
          ·
            refine ⟨55904020815272595071609969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37269347210181730047739979 55904020815272595071609969)
            ·
              refine ⟨41928015611454446303707477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55904020815272595071609969 41928015611454446303707477)
              ·
                refine ⟨122835983236682948155393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41928015611454446303707477 122835983236682948155393)
                ·
                  rfl

theorem cell22_3229500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 10].length) (baseStart_3229500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229500 prefixEnd_3229500 := by exact prefixLift 3229500
  have htrace : WordTrace (prefixWord ++ tailWord_3229500) baseStart_3229500 baseEnd_3229500 := by
    simpa [prefixWord, tailWord_3229500, baseEnd_3229500] using wordTrace_append hprefix tailTrace_3229500
  have hstable : (prefixWord ++ tailWord_3229500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229500).length < 2 ^ (prefixWord ++ tailWord_3229500).sum := by decide
  have hdescent : baseEnd_3229500 < baseStart_3229500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229521 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 2, 3]
def baseStart_3229521 : Nat := 118140960795 + 3229521 * 2 ^ 59
def prefixEnd_3229521 : Nat := 4983230072969 + 3 ^ 40 * 3229521 * 2
def baseEnd_3229521 : Nat := 1105531037859309478623473

theorem tailTrace_3229521 : CollatzResearch.WordTrace tailWord_3229521 prefixEnd_3229521 1105531037859309478623473 := by
  unfold tailWord_3229521
  simp only [CollatzResearch.WordTrace]
  refine ⟨117790307733004450120112417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78526871822002966746741611 117790307733004450120112417)
  ·
    refine ⟨88342730799753337590084313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117790307733004450120112417 88342730799753337590084313)
    ·
      refine ⟨66257048099815003192563235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88342730799753337590084313 66257048099815003192563235)
      ·
        refine ⟨99385572149722504788844853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66257048099815003192563235 99385572149722504788844853)
        ·
          refine ⟨9317397389036484823954205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99385572149722504788844853 9317397389036484823954205)
          ·
            refine ⟨3494024020888681808982827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9317397389036484823954205 3494024020888681808982827)
            ·
              refine ⟨5241036031333022713474241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494024020888681808982827 5241036031333022713474241)
              ·
                refine ⟨3930777023499767035105681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5241036031333022713474241 3930777023499767035105681)
                ·
                  refine ⟨2948082767624825276329261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3930777023499767035105681 2948082767624825276329261)
                  ·
                    refine ⟨1105531037859309478623473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2948082767624825276329261 1105531037859309478623473)
                    ·
                      rfl

theorem cell22_3229521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_3229521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229521 prefixEnd_3229521 := by exact prefixLift 3229521
  have htrace : WordTrace (prefixWord ++ tailWord_3229521) baseStart_3229521 baseEnd_3229521 := by
    simpa [prefixWord, tailWord_3229521, baseEnd_3229521] using wordTrace_append hprefix tailTrace_3229521
  have hstable : (prefixWord ++ tailWord_3229521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229521).length < 2 ^ (prefixWord ++ tailWord_3229521).sum := by decide
  have hdescent : baseEnd_3229521 < baseStart_3229521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229538 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3229538 : Nat := 118140960795 + 3229538 * 2 ^ 59
def prefixEnd_3229538 : Nat := 4983230072969 + 3 ^ 40 * 3229538 * 2
def baseEnd_3229538 : Nat := 1105536857306727100948421

theorem tailTrace_3229538 : CollatzResearch.WordTrace tailWord_3229538 prefixEnd_3229538 1105536857306727100948421 := by
  unfold tailWord_3229538
  simp only [CollatzResearch.WordTrace]
  refine ⟨29447731943485715505870317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78527285182628574682320845 29447731943485715505870317)
  ·
    refine ⟨11042899478807143314701369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29447731943485715505870317 11042899478807143314701369)
    ·
      refine ⟨8282174609105357486026027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11042899478807143314701369 8282174609105357486026027)
      ·
        refine ⟨12423261913658036229039041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8282174609105357486026027 12423261913658036229039041)
        ·
          refine ⟨9317446435243527171779281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12423261913658036229039041 9317446435243527171779281)
          ·
            refine ⟨6988084826432645378834461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9317446435243527171779281 6988084826432645378834461)
            ·
              refine ⟨2620531809912242017062923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6988084826432645378834461 2620531809912242017062923)
              ·
                refine ⟨3930797714868363025594385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620531809912242017062923 3930797714868363025594385)
                ·
                  refine ⟨2948098286151272269195789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3930797714868363025594385 2948098286151272269195789)
                  ·
                    refine ⟨1105536857306727100948421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2948098286151272269195789 1105536857306727100948421)
                    ·
                      rfl

theorem cell22_3229538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3229538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229538 prefixEnd_3229538 := by exact prefixLift 3229538
  have htrace : WordTrace (prefixWord ++ tailWord_3229538) baseStart_3229538 baseEnd_3229538 := by
    simpa [prefixWord, tailWord_3229538, baseEnd_3229538] using wordTrace_append hprefix tailTrace_3229538
  have hstable : (prefixWord ++ tailWord_3229538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229538).length < 2 ^ (prefixWord ++ tailWord_3229538).sum := by decide
  have hdescent : baseEnd_3229538 < baseStart_3229538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229549 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_3229549 : Nat := 118140960795 + 3229549 * 2 ^ 59
def prefixEnd_3229549 : Nat := 4983230072969 + 3 ^ 40 * 3229549 * 2
def baseEnd_3229549 : Nat := 1105540622831526738923387

theorem tailTrace_3229549 : CollatzResearch.WordTrace tailWord_3229549 prefixEnd_3229549 1105540622831526738923387 := by
  unfold tailWord_3229549
  simp only [CollatzResearch.WordTrace]
  refine ⟨117791328976903010902131701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78527552651268673934754467 117791328976903010902131701)
  ·
    refine ⟨11042937091584657272074847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117791328976903010902131701 11042937091584657272074847)
    ·
      refine ⟨16564405637376985908112271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11042937091584657272074847 16564405637376985908112271)
      ·
        refine ⟨24846608456065478862168407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16564405637376985908112271 24846608456065478862168407)
        ·
          refine ⟨37269912684098218293252611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24846608456065478862168407 37269912684098218293252611)
          ·
            refine ⟨55904869026147327439878917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37269912684098218293252611 55904869026147327439878917)
            ·
              refine ⟨10482162942402623894977297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55904869026147327439878917 10482162942402623894977297)
              ·
                refine ⟨7861622206801967921232973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10482162942402623894977297 7861622206801967921232973)
                ·
                  refine ⟨2948108327550737970462365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7861622206801967921232973 2948108327550737970462365)
                  ·
                    refine ⟨1105540622831526738923387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2948108327550737970462365 1105540622831526738923387)
                    ·
                      rfl

theorem cell22_3229549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_3229549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229549 prefixEnd_3229549 := by exact prefixLift 3229549
  have htrace : WordTrace (prefixWord ++ tailWord_3229549) baseStart_3229549 baseEnd_3229549 := by
    simpa [prefixWord, tailWord_3229549, baseEnd_3229549] using wordTrace_append hprefix tailTrace_3229549
  have hstable : (prefixWord ++ tailWord_3229549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229549).length < 2 ^ (prefixWord ++ tailWord_3229549).sum := by decide
  have hdescent : baseEnd_3229549 < baseStart_3229549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229596 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 5]
def baseStart_3229596 : Nat := 118140960795 + 3229596 * 2 ^ 59
def prefixEnd_3229596 : Nat := 4983230072969 + 3 ^ 40 * 3229596 * 2
def baseEnd_3229596 : Nat := 368518903964011427666081

theorem tailTrace_3229596 : CollatzResearch.WordTrace tailWord_3229596 prefixEnd_3229596 368518903964011427666081 := by
  unfold tailWord_3229596
  simp only [CollatzResearch.WordTrace]
  refine ⟨58896521603866368964546321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78528695471821825286061761 58896521603866368964546321)
  ·
    refine ⟨44172391202899776723409741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58896521603866368964546321 44172391202899776723409741)
    ·
      refine ⟨16564646701087416271278653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44172391202899776723409741 16564646701087416271278653)
      ·
        refine ⟨6211742512907781101729495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16564646701087416271278653 6211742512907781101729495)
        ·
          refine ⟨9317613769361671652594243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6211742512907781101729495 9317613769361671652594243)
          ·
            refine ⟨13976420654042507478891365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9317613769361671652594243 13976420654042507478891365)
            ·
              refine ⟨2620578872632970152292131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13976420654042507478891365 2620578872632970152292131)
              ·
                refine ⟨3930868308949455228438197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620578872632970152292131 3930868308949455228438197)
                ·
                  refine ⟨368518903964011427666081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3930868308949455228438197 368518903964011427666081)
                  ·
                    rfl

theorem cell22_3229596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_3229596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229596 prefixEnd_3229596 := by exact prefixLift 3229596
  have htrace : WordTrace (prefixWord ++ tailWord_3229596) baseStart_3229596 baseEnd_3229596 := by
    simpa [prefixWord, tailWord_3229596, baseEnd_3229596] using wordTrace_append hprefix tailTrace_3229596
  have hstable : (prefixWord ++ tailWord_3229596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229596).length < 2 ^ (prefixWord ++ tailWord_3229596).sum := by decide
  have hdescent : baseEnd_3229596 < baseStart_3229596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229624 : List Nat := [2, 1, 2, 1, 2, 3, 2, 5, 4]
def baseStart_3229624 : Nat := 118140960795 + 3229624 * 2 ^ 59
def prefixEnd_3229624 : Nat := 4983230072969 + 3 ^ 40 * 3229624 * 2
def baseEnd_3229624 : Nat := 368522098954750514432719

theorem tailTrace_3229624 : CollatzResearch.WordTrace tailWord_3229624 prefixEnd_3229624 368522098954750514432719 := by
  unfold tailWord_3229624
  simp only [CollatzResearch.WordTrace]
  refine ⟨58897032225815649355555963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78529376301087532474074617 58897032225815649355555963)
  ·
    refine ⟨88345548338723474033333945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58897032225815649355555963 88345548338723474033333945)
    ·
      refine ⟨66259161254042605525000459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88345548338723474033333945 66259161254042605525000459)
      ·
        refine ⟨99388741881063908287500689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66259161254042605525000459 99388741881063908287500689)
        ·
          refine ⟨74541556410797931215625517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99388741881063908287500689 74541556410797931215625517)
          ·
            refine ⟨27953083654049224205859569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74541556410797931215625517 27953083654049224205859569)
            ·
              refine ⟨20964812740536918154394677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27953083654049224205859569 20964812740536918154394677)
              ·
                refine ⟨1965451194425336076974501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20964812740536918154394677 1965451194425336076974501)
                ·
                  refine ⟨368522098954750514432719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1965451194425336076974501 368522098954750514432719)
                  ·
                    rfl

theorem cell22_3229624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 4].length) (baseStart_3229624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229624 prefixEnd_3229624 := by exact prefixLift 3229624
  have htrace : WordTrace (prefixWord ++ tailWord_3229624) baseStart_3229624 baseEnd_3229624 := by
    simpa [prefixWord, tailWord_3229624, baseEnd_3229624] using wordTrace_append hprefix tailTrace_3229624
  have hstable : (prefixWord ++ tailWord_3229624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229624).length < 2 ^ (prefixWord ++ tailWord_3229624).sum := by decide
  have hdescent : baseEnd_3229624 < baseStart_3229624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229637 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_3229637 : Nat := 118140960795 + 3229637 * 2 ^ 59
def prefixEnd_3229637 : Nat := 4983230072969 + 3 ^ 40 * 3229637 * 2
def baseEnd_3229637 : Nat := 1105570747029923842723117

theorem tailTrace_3229637 : CollatzResearch.WordTrace tailWord_3229637 prefixEnd_3229637 1105570747029923842723117 := by
  unfold tailWord_3229637
  simp only [CollatzResearch.WordTrace]
  refine ⟨117794538600584201931335165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78529692400389467954223443 117794538600584201931335165)
  ·
    refine ⟨44172951975219075724250687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117794538600584201931335165 44172951975219075724250687)
    ·
      refine ⟨66259427962828613586376031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44172951975219075724250687 66259427962828613586376031)
      ·
        refine ⟨99389141944242920379564047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66259427962828613586376031 99389141944242920379564047)
        ·
          refine ⟨149083712916364380569346071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99389141944242920379564047 149083712916364380569346071)
          ·
            refine ⟨223625569374546570854019107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149083712916364380569346071 223625569374546570854019107)
            ·
              refine ⟨335438354061819856281028661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223625569374546570854019107 335438354061819856281028661)
              ·
                refine ⟨31447345693295611526346437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 335438354061819856281028661 31447345693295611526346437)
                ·
                  refine ⟨5896377317492927161189957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31447345693295611526346437 5896377317492927161189957)
                  ·
                    refine ⟨1105570747029923842723117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5896377317492927161189957 1105570747029923842723117)
                    ·
                      rfl

theorem cell22_3229637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_3229637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229637 prefixEnd_3229637 := by exact prefixLift 3229637
  have htrace : WordTrace (prefixWord ++ tailWord_3229637) baseStart_3229637 baseEnd_3229637 := by
    simpa [prefixWord, tailWord_3229637, baseEnd_3229637] using wordTrace_append hprefix tailTrace_3229637
  have hstable : (prefixWord ++ tailWord_3229637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229637).length < 2 ^ (prefixWord ++ tailWord_3229637).sum := by decide
  have hdescent : baseEnd_3229637 < baseStart_3229637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229677 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_3229677 : Nat := 118140960795 + 3229677 * 2 ^ 59
def prefixEnd_3229677 : Nat := 4983230072969 + 3 ^ 40 * 3229677 * 2
def baseEnd_3229677 : Nat := 1105584439847377071722995

theorem tailTrace_3229677 : CollatzResearch.WordTrace tailWord_3229677 prefixEnd_3229677 1105584439847377071722995 := by
  unfold tailWord_3229677
  simp only [CollatzResearch.WordTrace]
  refine ⟨117795997520439288762791285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78530665013626192508527523 117795997520439288762791285)
  ·
    refine ⟨11043374767541183321511683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117795997520439288762791285 11043374767541183321511683)
    ·
      refine ⟨16565062151311774982267525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11043374767541183321511683 16565062151311774982267525)
      ·
        refine ⟨3105949153370957809175161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16565062151311774982267525 3105949153370957809175161)
        ·
          refine ⟨2329461865028218356881371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3105949153370957809175161 2329461865028218356881371)
          ·
            refine ⟨3494192797542327535322057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329461865028218356881371 3494192797542327535322057)
            ·
              refine ⟨2620644598156745651491543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494192797542327535322057 2620644598156745651491543)
              ·
                refine ⟨3930966897235118477237315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620644598156745651491543 3930966897235118477237315)
                ·
                  refine ⟨5896450345852677715855973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930966897235118477237315 5896450345852677715855973)
                  ·
                    refine ⟨1105584439847377071722995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5896450345852677715855973 1105584439847377071722995)
                    ·
                      rfl

theorem cell22_3229677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_3229677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229677 prefixEnd_3229677 := by exact prefixLift 3229677
  have htrace : WordTrace (prefixWord ++ tailWord_3229677) baseStart_3229677 baseEnd_3229677 := by
    simpa [prefixWord, tailWord_3229677, baseEnd_3229677] using wordTrace_append hprefix tailTrace_3229677
  have hstable : (prefixWord ++ tailWord_3229677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229677).length < 2 ^ (prefixWord ++ tailWord_3229677).sum := by decide
  have hdescent : baseEnd_3229677 < baseStart_3229677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229701 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_3229701 : Nat := 118140960795 + 3229701 * 2 ^ 59
def prefixEnd_3229701 : Nat := 4983230072969 + 3 ^ 40 * 3229701 * 2
def baseEnd_3229701 : Nat := 1105592655537849009122921

theorem tailTrace_3229701 : CollatzResearch.WordTrace tailWord_3229701 prefixEnd_3229701 1105592655537849009122921 := by
  unfold tailWord_3229701
  simp only [CollatzResearch.WordTrace]
  refine ⟨117796872872352340861664957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78531248581568227241109971 117796872872352340861664957)
  ·
    refine ⟨44173827327132127823124359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117796872872352340861664957 44173827327132127823124359)
    ·
      refine ⟨66260740990698191734686539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44173827327132127823124359 66260740990698191734686539)
      ·
        refine ⟨99391111486047287602029809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66260740990698191734686539 99391111486047287602029809)
        ·
          refine ⟨74543333614535465701522357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99391111486047287602029809 74543333614535465701522357)
          ·
            refine ⟨6988437526362699909517721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74543333614535465701522357 6988437526362699909517721)
            ·
              refine ⟨5241328144772024932138291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988437526362699909517721 5241328144772024932138291)
              ·
                refine ⟨7861992217158037398207437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241328144772024932138291 7861992217158037398207437)
                ·
                  refine ⟨2948247081434264024327789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7861992217158037398207437 2948247081434264024327789)
                  ·
                    refine ⟨1105592655537849009122921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2948247081434264024327789 1105592655537849009122921)
                    ·
                      rfl

theorem cell22_3229701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_3229701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229701 prefixEnd_3229701 := by exact prefixLift 3229701
  have htrace : WordTrace (prefixWord ++ tailWord_3229701) baseStart_3229701 baseEnd_3229701 := by
    simpa [prefixWord, tailWord_3229701, baseEnd_3229701] using wordTrace_append hprefix tailTrace_3229701
  have hstable : (prefixWord ++ tailWord_3229701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229701).length < 2 ^ (prefixWord ++ tailWord_3229701).sum := by decide
  have hdescent : baseEnd_3229701 < baseStart_3229701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229759 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 6]
def baseStart_3229759 : Nat := 118140960795 + 3229759 * 2 ^ 59
def prefixEnd_3229759 : Nat := 4983230072969 + 3 ^ 40 * 3229759 * 2
def baseEnd_3229759 : Nat := 368537503374385397057581

theorem tailTrace_3229759 : CollatzResearch.WordTrace tailWord_3229759 prefixEnd_3229759 368537503374385397057581 := by
  unfold tailWord_3229759
  simp only [CollatzResearch.WordTrace]
  refine ⟨117798988306142216767276331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78532658870761477844850887 117798988306142216767276331)
  ·
    refine ⟨176698482459213325150914497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117798988306142216767276331 176698482459213325150914497)
    ·
      refine ⟨132523861844409993863185873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176698482459213325150914497 132523861844409993863185873)
      ·
        refine ⟨99392896383307495397389405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132523861844409993863185873 99392896383307495397389405)
        ·
          refine ⟨37272336143740310774021027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99392896383307495397389405 37272336143740310774021027)
          ·
            refine ⟨55908504215610466161031541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37272336143740310774021027 55908504215610466161031541)
            ·
              refine ⟨5241422270213481202596707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55908504215610466161031541 5241422270213481202596707)
              ·
                refine ⟨7862133405320221803895061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241422270213481202596707 7862133405320221803895061)
                ·
                  refine ⟨368537503374385397057581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7862133405320221803895061 368537503374385397057581)
                  ·
                    rfl

theorem cell22_3229759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 6].length) (baseStart_3229759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229759 prefixEnd_3229759 := by exact prefixLift 3229759
  have htrace : WordTrace (prefixWord ++ tailWord_3229759) baseStart_3229759 baseEnd_3229759 := by
    simpa [prefixWord, tailWord_3229759, baseEnd_3229759] using wordTrace_append hprefix tailTrace_3229759
  have hstable : (prefixWord ++ tailWord_3229759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229759).length < 2 ^ (prefixWord ++ tailWord_3229759).sum := by decide
  have hdescent : baseEnd_3229759 < baseStart_3229759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229806 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3229806 : Nat := 118140960795 + 3229806 * 2 ^ 59
def prefixEnd_3229806 : Nat := 4983230072969 + 3 ^ 40 * 3229806 * 2
def baseEnd_3229806 : Nat := 1105628599183663735247599

theorem tailTrace_3229806 : CollatzResearch.WordTrace tailWord_3229806 prefixEnd_3229806 1105628599183663735247599 := by
  unfold tailWord_3229806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725087817121492974279659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78533801691314629196158181 14725087817121492974279659)
  ·
    refine ⟨22087631725682239461419489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14725087817121492974279659 22087631725682239461419489)
    ·
      refine ⟨16565723794261679596064617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22087631725682239461419489 16565723794261679596064617)
      ·
        refine ⟨12424292845696259697048463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16565723794261679596064617 12424292845696259697048463)
        ·
          refine ⟨18636439268544389545572695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12424292845696259697048463 18636439268544389545572695)
          ·
            refine ⟨27954658902816584318359043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18636439268544389545572695 27954658902816584318359043)
            ·
              refine ⟨41931988354224876477538565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27954658902816584318359043 41931988354224876477538565)
              ·
                refine ⟨7862247816417164339538481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41931988354224876477538565 7862247816417164339538481)
                ·
                  refine ⟨5896685862312873254653861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862247816417164339538481 5896685862312873254653861)
                  ·
                    refine ⟨1105628599183663735247599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5896685862312873254653861 1105628599183663735247599)
                    ·
                      rfl

theorem cell22_3229806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3229806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229806 prefixEnd_3229806 := by exact prefixLift 3229806
  have htrace : WordTrace (prefixWord ++ tailWord_3229806) baseStart_3229806 baseEnd_3229806 := by
    simpa [prefixWord, tailWord_3229806, baseEnd_3229806] using wordTrace_append hprefix tailTrace_3229806
  have hstable : (prefixWord ++ tailWord_3229806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229806).length < 2 ^ (prefixWord ++ tailWord_3229806).sum := by decide
  have hdescent : baseEnd_3229806 < baseStart_3229806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229808 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 2, 3]
def baseStart_3229808 : Nat := 118140960795 + 3229808 * 2 ^ 59
def prefixEnd_3229808 : Nat := 4983230072969 + 3 ^ 40 * 3229808 * 2
def baseEnd_3229808 : Nat := 1105629283824536396697593

theorem tailTrace_3229808 : CollatzResearch.WordTrace tailWord_3229808 prefixEnd_3229808 1105629283824536396697593 := by
  unfold tailWord_3229808
  simp only [CollatzResearch.WordTrace]
  refine ⟨58900387741482349067905039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78533850321976465423873385 58900387741482349067905039)
  ·
    refine ⟨88350581612223523601857559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58900387741482349067905039 88350581612223523601857559)
    ·
      refine ⟨132525872418335285402786339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88350581612223523601857559 132525872418335285402786339)
      ·
        refine ⟨198788808627502928104179509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132525872418335285402786339 198788808627502928104179509)
        ·
          refine ⟨18636450808828399509766829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198788808627502928104179509 18636450808828399509766829)
          ·
            refine ⟨6988669053310649816162561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18636450808828399509766829 6988669053310649816162561)
            ·
              refine ⟨5241501789982987362121921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988669053310649816162561 5241501789982987362121921)
              ·
                refine ⟨3931126342487240521591441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5241501789982987362121921 3931126342487240521591441)
                ·
                  refine ⟨2948344756865430391193581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3931126342487240521591441 2948344756865430391193581)
                  ·
                    refine ⟨1105629283824536396697593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2948344756865430391193581 1105629283824536396697593)
                    ·
                      rfl

theorem cell22_3229808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_3229808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229808 prefixEnd_3229808 := by exact prefixLift 3229808
  have htrace : WordTrace (prefixWord ++ tailWord_3229808) baseStart_3229808 baseEnd_3229808 := by
    simpa [prefixWord, tailWord_3229808, baseEnd_3229808] using wordTrace_append hprefix tailTrace_3229808
  have hstable : (prefixWord ++ tailWord_3229808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229808).length < 2 ^ (prefixWord ++ tailWord_3229808).sum := by decide
  have hdescent : baseEnd_3229808 < baseStart_3229808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229810 : List Nat := [3, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_3229810 : Nat := 118140960795 + 3229810 * 2 ^ 59
def prefixEnd_3229810 : Nat := 4983230072969 + 3 ^ 40 * 3229810 * 2
def baseEnd_3229810 : Nat := 368543322821803019382529

theorem tailTrace_3229810 : CollatzResearch.WordTrace tailWord_3229810 prefixEnd_3229810 368543322821803019382529 := by
  unfold tailWord_3229810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29450212107239363119345721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78533898952638301651588589 29450212107239363119345721)
  ·
    refine ⟨22087659080429522339509291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29450212107239363119345721 22087659080429522339509291)
    ·
      refine ⟨33131488620644283509263937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22087659080429522339509291 33131488620644283509263937)
      ·
        refine ⟨24848616465483212631947953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33131488620644283509263937 24848616465483212631947953)
        ·
          refine ⟨18636462349112409473960965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24848616465483212631947953 18636462349112409473960965)
          ·
            refine ⟨3494336690458576776367681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18636462349112409473960965 3494336690458576776367681)
            ·
              refine ⟨2620752517843932582275761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494336690458576776367681 2620752517843932582275761)
              ·
                refine ⟨1965564388382949436706821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2620752517843932582275761 1965564388382949436706821)
                ·
                  refine ⟨368543322821803019382529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1965564388382949436706821 368543322821803019382529)
                  ·
                    rfl

theorem cell22_3229810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_3229810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229810 prefixEnd_3229810 := by exact prefixLift 3229810
  have htrace : WordTrace (prefixWord ++ tailWord_3229810) baseStart_3229810 baseEnd_3229810 := by
    simpa [prefixWord, tailWord_3229810, baseEnd_3229810] using wordTrace_append hprefix tailTrace_3229810
  have hstable : (prefixWord ++ tailWord_3229810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229810).length < 2 ^ (prefixWord ++ tailWord_3229810).sum := by decide
  have hdescent : baseEnd_3229810 < baseStart_3229810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229821 : List Nat := [1, 4, 1, 1, 3, 4, 1, 7]
def baseStart_3229821 : Nat := 118140960795 + 3229821 * 2 ^ 59
def prefixEnd_3229821 : Nat := 4983230072969 + 3 ^ 40 * 3229821 * 2
def baseEnd_3229821 : Nat := 122848192665578744013617

theorem tailTrace_3229821 : CollatzResearch.WordTrace tailWord_3229821 prefixEnd_3229821 122848192665578744013617 := by
  unfold tailWord_3229821
  simp only [CollatzResearch.WordTrace]
  refine ⟨117801249631917601356033317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78534166421278400904022211 117801249631917601356033317)
  ·
    refine ⟨22087734305984550254256247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117801249631917601356033317 22087734305984550254256247)
    ·
      refine ⟨33131601458976825381384371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22087734305984550254256247 33131601458976825381384371)
      ·
        refine ⟨49697402188465238072076557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33131601458976825381384371 49697402188465238072076557)
        ·
          refine ⟨18636525820674464277028709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49697402188465238072076557 18636525820674464277028709)
          ·
            refine ⟨3494348591376462051942883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18636525820674464277028709 3494348591376462051942883)
            ·
              refine ⟨5241522887064693077914325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494348591376462051942883 5241522887064693077914325)
              ·
                refine ⟨122848192665578744013617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5241522887064693077914325 122848192665578744013617)
                ·
                  rfl

theorem cell22_3229821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 7].length) (baseStart_3229821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229821 prefixEnd_3229821 := by exact prefixLift 3229821
  have htrace : WordTrace (prefixWord ++ tailWord_3229821) baseStart_3229821 baseEnd_3229821 := by
    simpa [prefixWord, tailWord_3229821, baseEnd_3229821] using wordTrace_append hprefix tailTrace_3229821
  have hstable : (prefixWord ++ tailWord_3229821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229821).length < 2 ^ (prefixWord ++ tailWord_3229821).sum := by decide
  have hdescent : baseEnd_3229821 < baseStart_3229821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229838 : List Nat := [4, 1, 1, 3, 3, 1, 3, 6]
def baseStart_3229838 : Nat := 118140960795 + 3229838 * 2 ^ 59
def prefixEnd_3229838 : Nat := 4983230072969 + 3 ^ 40 * 3229838 * 2
def baseEnd_3229838 : Nat := 122848839270847368716389

theorem tailTrace_3229838 : CollatzResearch.WordTrace tailWord_3229838 prefixEnd_3229838 122848839270847368716389 := by
  unfold tailWord_3229838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725233709107001657425271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78534579781904008839601445 14725233709107001657425271)
  ·
    refine ⟨22087850563660502486137907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14725233709107001657425271 22087850563660502486137907)
    ·
      refine ⟨33131775845490753729206861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22087850563660502486137907 33131775845490753729206861)
      ·
        refine ⟨12424415942059032648452573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33131775845490753729206861 12424415942059032648452573)
        ·
          refine ⟨4659155978272137243169715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12424415942059032648452573 4659155978272137243169715)
          ·
            refine ⟨6988733967408205864754573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659155978272137243169715 6988733967408205864754573)
            ·
              refine ⟨2620775237778077199282965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6988733967408205864754573 2620775237778077199282965)
              ·
                refine ⟨122848839270847368716389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2620775237778077199282965 122848839270847368716389)
                ·
                  rfl

theorem cell22_3229838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_3229838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229838 prefixEnd_3229838 := by exact prefixLift 3229838
  have htrace : WordTrace (prefixWord ++ tailWord_3229838) baseStart_3229838 baseEnd_3229838 := by
    simpa [prefixWord, tailWord_3229838, baseEnd_3229838] using wordTrace_append hprefix tailTrace_3229838
  have hstable : (prefixWord ++ tailWord_3229838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229838).length < 2 ^ (prefixWord ++ tailWord_3229838).sum := by decide
  have hdescent : baseEnd_3229838 < baseStart_3229838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229876 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3229876 : Nat := 118140960795 + 3229876 * 2 ^ 59
def prefixEnd_3229876 : Nat := 4983230072969 + 3 ^ 40 * 3229876 * 2
def baseEnd_3229876 : Nat := 1105652561614206885997385

theorem tailTrace_3229876 : CollatzResearch.WordTrace tailWord_3229876 prefixEnd_3229876 1105652561614206885997385 := by
  unfold tailWord_3229876
  simp only [CollatzResearch.WordTrace]
  refine ⟨58901627823359172874642741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78535503764478897166190321 58901627823359172874642741)
  ·
    refine ⟨5522027608439922456997757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58901627823359172874642741 5522027608439922456997757)
    ·
      refine ⟨2070760353164970921374159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5522027608439922456997757 2070760353164970921374159)
      ·
        refine ⟨3106140529747456382061239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070760353164970921374159 3106140529747456382061239)
        ·
          refine ⟨4659210794621184573091859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106140529747456382061239 4659210794621184573091859)
          ·
            refine ⟨6988816191931776859637789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659210794621184573091859 6988816191931776859637789)
            ·
              refine ⟨2620806071974416322364171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6988816191931776859637789 2620806071974416322364171)
              ·
                refine ⟨3931209107961624483546257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620806071974416322364171 3931209107961624483546257)
                ·
                  refine ⟨2948406830971218362659693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3931209107961624483546257 2948406830971218362659693)
                  ·
                    refine ⟨1105652561614206885997385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2948406830971218362659693 1105652561614206885997385)
                    ·
                      rfl

theorem cell22_3229876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3229876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229876 prefixEnd_3229876 := by exact prefixLift 3229876
  have htrace : WordTrace (prefixWord ++ tailWord_3229876) baseStart_3229876 baseEnd_3229876 := by
    simpa [prefixWord, tailWord_3229876, baseEnd_3229876] using wordTrace_append hprefix tailTrace_3229876
  have hstable : (prefixWord ++ tailWord_3229876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229876).length < 2 ^ (prefixWord ++ tailWord_3229876).sum := by decide
  have hdescent : baseEnd_3229876 < baseStart_3229876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229928 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 6]
def baseStart_3229928 : Nat := 118140960795 + 3229928 * 2 ^ 59
def prefixEnd_3229928 : Nat := 4983230072969 + 3 ^ 40 * 3229928 * 2
def baseEnd_3229928 : Nat := 368556787425632027899075

theorem tailTrace_3229928 : CollatzResearch.WordTrace tailWord_3229928 prefixEnd_3229928 368556787425632027899075 := by
  unfold tailWord_3229928
  simp only [CollatzResearch.WordTrace]
  refine ⟨58902576121264979315089219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78536768161686639086785625 58902576121264979315089219)
  ·
    refine ⟨88353864181897468972633829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58902576121264979315089219 88353864181897468972633829)
    ·
      refine ⟨16566349534105775432368843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88353864181897468972633829 16566349534105775432368843)
      ·
        refine ⟨24849524301158663148553265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16566349534105775432368843 24849524301158663148553265)
        ·
          refine ⟨18637143225868997361414949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24849524301158663148553265 18637143225868997361414949)
          ·
            refine ⟨3494464354850437005265303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18637143225868997361414949 3494464354850437005265303)
            ·
              refine ⟨5241696532275655507897955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494464354850437005265303 5241696532275655507897955)
              ·
                refine ⟨7862544798413483261846933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241696532275655507897955 7862544798413483261846933)
                ·
                  refine ⟨368556787425632027899075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7862544798413483261846933 368556787425632027899075)
                  ·
                    rfl

theorem cell22_3229928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_3229928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3229928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3229928 prefixEnd_3229928 := by exact prefixLift 3229928
  have htrace : WordTrace (prefixWord ++ tailWord_3229928) baseStart_3229928 baseEnd_3229928 := by
    simpa [prefixWord, tailWord_3229928, baseEnd_3229928] using wordTrace_append hprefix tailTrace_3229928
  have hstable : (prefixWord ++ tailWord_3229928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229928).length < 2 ^ (prefixWord ++ tailWord_3229928).sum := by decide
  have hdescent : baseEnd_3229928 < baseStart_3229928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230031 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 5, 4]
def baseStart_3230031 : Nat := 118140960795 + 3230031 * 2 ^ 59
def prefixEnd_3230031 : Nat := 4983230072969 + 3 ^ 40 * 3230031 * 2
def baseEnd_3230031 : Nat := 1105705621281838148371909

theorem tailTrace_3230031 : CollatzResearch.WordTrace tailWord_3230031 prefixEnd_3230031 1105705621281838148371909 := by
  unfold tailWord_3230031
  simp only [CollatzResearch.WordTrace]
  refine ⟨117808908961156807221177947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78539272640771204814118631 117808908961156807221177947)
  ·
    refine ⟨176713363441735210831766921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117808908961156807221177947 176713363441735210831766921)
    ·
      refine ⟨132535022581301408123825191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176713363441735210831766921 132535022581301408123825191)
      ·
        refine ⟨198802533871952112185737787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132535022581301408123825191 198802533871952112185737787)
        ·
          refine ⟨298203800807928168278606681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198802533871952112185737787 298203800807928168278606681)
          ·
            refine ⟨223652850605946126208955011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298203800807928168278606681 223652850605946126208955011)
            ·
              refine ⟨335479275908919189313432517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223652850605946126208955011 335479275908919189313432517)
              ·
                refine ⟨62902364232922347996268597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335479275908919189313432517 62902364232922347996268597)
                ·
                  refine ⟨5897096646836470124650181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62902364232922347996268597 5897096646836470124650181)
                  ·
                    refine ⟨1105705621281838148371909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5897096646836470124650181 1105705621281838148371909)
                    ·
                      rfl

theorem cell22_3230031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_3230031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230031 prefixEnd_3230031 := by exact prefixLift 3230031
  have htrace : WordTrace (prefixWord ++ tailWord_3230031) baseStart_3230031 baseEnd_3230031 := by
    simpa [prefixWord, tailWord_3230031, baseEnd_3230031] using wordTrace_append hprefix tailTrace_3230031
  have hstable : (prefixWord ++ tailWord_3230031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230031).length < 2 ^ (prefixWord ++ tailWord_3230031).sum := by decide
  have hdescent : baseEnd_3230031 < baseStart_3230031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230091 : List Nat := [1, 1, 1, 1, 4, 4, 10]
def baseStart_3230091 : Nat := 118140960795 + 3230091 * 2 ^ 59
def prefixEnd_3230091 : Nat := 4983230072969 + 3 ^ 40 * 3230091 * 2
def baseEnd_3230091 : Nat := 40952820759556221921175

theorem tailTrace_3230091 : CollatzResearch.WordTrace tailWord_3230091 prefixEnd_3230091 40952820759556221921175 := by
  unfold tailWord_3230091
  simp only [CollatzResearch.WordTrace]
  refine ⟨117811097340939437468362127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78540731560626291645574751 117811097340939437468362127)
  ·
    refine ⟨176716646011409156202543191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117811097340939437468362127 176716646011409156202543191)
    ·
      refine ⟨265074969017113734303814787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176716646011409156202543191 265074969017113734303814787)
      ·
        refine ⟨397612453525670601455722181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265074969017113734303814787 397612453525670601455722181)
        ·
          refine ⟨74552335036063237772947909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397612453525670601455722181 74552335036063237772947909)
          ·
            refine ⟨13978562819261857082427733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74552335036063237772947909 13978562819261857082427733)
            ·
              refine ⟨40952820759556221921175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13978562819261857082427733 40952820759556221921175)
              ·
                rfl

theorem cell22_3230091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 10].length) (baseStart_3230091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230091 prefixEnd_3230091 := by exact prefixLift 3230091
  have htrace : WordTrace (prefixWord ++ tailWord_3230091) baseStart_3230091 baseEnd_3230091 := by
    simpa [prefixWord, tailWord_3230091, baseEnd_3230091] using wordTrace_append hprefix tailTrace_3230091
  have hstable : (prefixWord ++ tailWord_3230091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230091).length < 2 ^ (prefixWord ++ tailWord_3230091).sum := by decide
  have hdescent : baseEnd_3230091 < baseStart_3230091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230112 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 2, 3]
def baseStart_3230112 : Nat := 118140960795 + 3230112 * 2 ^ 59
def prefixEnd_3230112 : Nat := 4983230072969 + 3 ^ 40 * 3230112 * 2
def baseEnd_3230112 : Nat := 1105733349237180937096661

theorem tailTrace_3230112 : CollatzResearch.WordTrace tailWord_3230112 prefixEnd_3230112 1105733349237180937096661 := by
  unfold tailWord_3230112
  simp only [CollatzResearch.WordTrace]
  refine ⟨58905931636931679027438295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78541242182575572036584393 58905931636931679027438295)
  ·
    refine ⟨88358897455397518541157443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58905931636931679027438295 88358897455397518541157443)
    ·
      refine ⟨132538346183096277811736165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88358897455397518541157443 132538346183096277811736165)
      ·
        refine ⟨24850939909330552089700531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132538346183096277811736165 24850939909330552089700531)
        ·
          refine ⟨37276409863995828134550797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24850939909330552089700531 37276409863995828134550797)
          ·
            refine ⟨13978653698998435550456549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37276409863995828134550797 13978653698998435550456549)
            ·
              refine ⟨2620997568562206665710603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13978653698998435550456549 2620997568562206665710603)
              ·
                refine ⟨3931496352843309998565905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620997568562206665710603 3931496352843309998565905)
                ·
                  refine ⟨2948622264632482498924429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3931496352843309998565905 2948622264632482498924429)
                  ·
                    refine ⟨1105733349237180937096661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2948622264632482498924429 1105733349237180937096661)
                    ·
                      rfl

theorem cell22_3230112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 3].length) (baseStart_3230112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230112 prefixEnd_3230112 := by exact prefixLift 3230112
  have htrace : WordTrace (prefixWord ++ tailWord_3230112) baseStart_3230112 baseEnd_3230112 := by
    simpa [prefixWord, tailWord_3230112, baseEnd_3230112] using wordTrace_append hprefix tailTrace_3230112
  have hstable : (prefixWord ++ tailWord_3230112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230112).length < 2 ^ (prefixWord ++ tailWord_3230112).sum := by decide
  have hdescent : baseEnd_3230112 < baseStart_3230112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230153 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 5]
def baseStart_3230153 : Nat := 118140960795 + 3230153 * 2 ^ 59
def prefixEnd_3230153 : Nat := 4983230072969 + 3 ^ 40 * 3230153 * 2
def baseEnd_3230153 : Nat := 368582461458356832273845

theorem tailTrace_3230153 : CollatzResearch.WordTrace tailWord_3230153 prefixEnd_3230153 368582461458356832273845 := by
  unfold tailWord_3230153
  simp only [CollatzResearch.WordTrace]
  refine ⟨117813358666714822057119113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78542239111143214704746075 117813358666714822057119113)
  ·
    refine ⟨88360019000036116542839335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117813358666714822057119113 88360019000036116542839335)
    ·
      refine ⟨132540028500054174814259003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88360019000036116542839335 132540028500054174814259003)
      ·
        refine ⟨198810042750081262221388505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132540028500054174814259003 198810042750081262221388505)
        ·
          refine ⟨149107532062560946666041379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198810042750081262221388505 149107532062560946666041379)
          ·
            refine ⟨223661298093841419999062069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149107532062560946666041379 223661298093841419999062069)
            ·
              refine ⟨20968246696297633124912069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223661298093841419999062069 20968246696297633124912069)
              ·
                refine ⟨3931546255555806210921013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20968246696297633124912069 3931546255555806210921013)
                ·
                  refine ⟨368582461458356832273845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3931546255555806210921013 368582461458356832273845)
                  ·
                    rfl

theorem cell22_3230153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_3230153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230153 prefixEnd_3230153 := by exact prefixLift 3230153
  have htrace : WordTrace (prefixWord ++ tailWord_3230153) baseStart_3230153 baseEnd_3230153 := by
    simpa [prefixWord, tailWord_3230153, baseEnd_3230153] using wordTrace_append hprefix tailTrace_3230153
  have hstable : (prefixWord ++ tailWord_3230153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230153).length < 2 ^ (prefixWord ++ tailWord_3230153).sum := by decide
  have hdescent : baseEnd_3230153 < baseStart_3230153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230200 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_3230200 : Nat := 118140960795 + 3230200 * 2 ^ 59
def prefixEnd_3230200 : Nat := 4983230072969 + 3 ^ 40 * 3230200 * 2
def baseEnd_3230200 : Nat := 1105763473435578040896391

theorem tailTrace_3230200 : CollatzResearch.WordTrace tailWord_3230200 prefixEnd_3230200 1105763473435578040896391 := by
  unfold tailWord_3230200
  simp only [CollatzResearch.WordTrace]
  refine ⟨58907536448772274542040027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78543381931696366056053369 58907536448772274542040027)
  ·
    refine ⟨88361304673158411813060041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58907536448772274542040027 88361304673158411813060041)
    ·
      refine ⟨66270978504868808859795031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88361304673158411813060041 66270978504868808859795031)
      ·
        refine ⟨99406467757303213289692547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66270978504868808859795031 99406467757303213289692547)
        ·
          refine ⟨149109701635954819934538821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99406467757303213289692547 149109701635954819934538821)
          ·
            refine ⟨27958069056741528737726029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149109701635954819934538821 27958069056741528737726029)
            ·
              refine ⟨10484275896278073276647261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27958069056741528737726029 10484275896278073276647261)
              ·
                refine ⟨3931603461104277478742723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10484275896278073276647261 3931603461104277478742723)
                ·
                  refine ⟨5897405191656416218114085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931603461104277478742723 5897405191656416218114085)
                  ·
                    refine ⟨1105763473435578040896391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5897405191656416218114085 1105763473435578040896391)
                    ·
                      rfl

theorem cell22_3230200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_3230200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230200 prefixEnd_3230200 := by exact prefixLift 3230200
  have htrace : WordTrace (prefixWord ++ tailWord_3230200) baseStart_3230200 baseEnd_3230200 := by
    simpa [prefixWord, tailWord_3230200, baseEnd_3230200] using wordTrace_append hprefix tailTrace_3230200
  have hstable : (prefixWord ++ tailWord_3230200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230200).length < 2 ^ (prefixWord ++ tailWord_3230200).sum := by decide
  have hdescent : baseEnd_3230200 < baseStart_3230200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230213 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_3230213 : Nat := 118140960795 + 3230213 * 2 ^ 59
def prefixEnd_3230213 : Nat := 4983230072969 + 3 ^ 40 * 3230213 * 2
def baseEnd_3230213 : Nat := 1105767923601250340321351

theorem tailTrace_3230213 : CollatzResearch.WordTrace tailWord_3230213 prefixEnd_3230213 1105767923601250340321351 := by
  unfold tailWord_3230213
  simp only [CollatzResearch.WordTrace]
  refine ⟨117815547046497452304303293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78543698030998301536202195 117815547046497452304303293)
  ·
    refine ⟨44180830142436544614113735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117815547046497452304303293 44180830142436544614113735)
    ·
      refine ⟨66271245213654816921170603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44180830142436544614113735 66271245213654816921170603)
      ·
        refine ⟨99406867820482225381755905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66271245213654816921170603 99406867820482225381755905)
        ·
          refine ⟨74555150865361669036316929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99406867820482225381755905 74555150865361669036316929)
          ·
            refine ⟨55916363149021251777237697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74555150865361669036316929 55916363149021251777237697)
            ·
              refine ⟨41937272361765938832928273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55916363149021251777237697 41937272361765938832928273)
              ·
                refine ⟨31452954271324454124696205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41937272361765938832928273 31452954271324454124696205)
                ·
                  refine ⟨11794857851746670296761077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31452954271324454124696205 11794857851746670296761077)
                  ·
                    refine ⟨1105767923601250340321351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11794857851746670296761077 1105767923601250340321351)
                    ·
                      rfl

theorem cell22_3230213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_3230213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230213 prefixEnd_3230213 := by exact prefixLift 3230213
  have htrace : WordTrace (prefixWord ++ tailWord_3230213) baseStart_3230213 baseEnd_3230213 := by
    simpa [prefixWord, tailWord_3230213, baseEnd_3230213] using wordTrace_append hprefix tailTrace_3230213
  have hstable : (prefixWord ++ tailWord_3230213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230213).length < 2 ^ (prefixWord ++ tailWord_3230213).sum := by decide
  have hdescent : baseEnd_3230213 < baseStart_3230213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230221 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3230221 : Nat := 118140960795 + 3230221 * 2 ^ 59
def prefixEnd_3230221 : Nat := 4983230072969 + 3 ^ 40 * 3230221 * 2
def baseEnd_3230221 : Nat := 368590220721580328707109

theorem tailTrace_3230221 : CollatzResearch.WordTrace tailWord_3230221 prefixEnd_3230221 368590220721580328707109 := by
  unfold tailWord_3230221
  simp only [CollatzResearch.WordTrace]
  refine ⟨117815838830468469670594517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78543892553645646447063011 117815838830468469670594517)
  ·
    refine ⟨2761308722589104757904559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 117815838830468469670594517 2761308722589104757904559)
    ·
      refine ⟨4141963083883657136856839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2761308722589104757904559 4141963083883657136856839)
      ·
        refine ⟨6212944625825485705285259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4141963083883657136856839 6212944625825485705285259)
        ·
          refine ⟨9319416938738228557927889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212944625825485705285259 9319416938738228557927889)
          ·
            refine ⟨6989562704053671418445917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9319416938738228557927889 6989562704053671418445917)
            ·
              refine ⟨2621086014020126781917219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6989562704053671418445917 2621086014020126781917219)
              ·
                refine ⟨3931629021030190172875829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621086014020126781917219 3931629021030190172875829)
                ·
                  refine ⟨368590220721580328707109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3931629021030190172875829 368590220721580328707109)
                  ·
                    rfl

theorem cell22_3230221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3230221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230221 prefixEnd_3230221 := by exact prefixLift 3230221
  have htrace : WordTrace (prefixWord ++ tailWord_3230221) baseStart_3230221 baseEnd_3230221 := by
    simpa [prefixWord, tailWord_3230221, baseEnd_3230221] using wordTrace_append hprefix tailTrace_3230221
  have hstable : (prefixWord ++ tailWord_3230221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230221).length < 2 ^ (prefixWord ++ tailWord_3230221).sum := by decide
  have hdescent : baseEnd_3230221 < baseStart_3230221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230262 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3230262 : Nat := 118140960795 + 3230262 * 2 ^ 59
def prefixEnd_3230262 : Nat := 4983230072969 + 3 ^ 40 * 3230262 * 2
def baseEnd_3230262 : Nat := 1105784697302630545846201

theorem tailTrace_3230262 : CollatzResearch.WordTrace tailWord_3230262 prefixEnd_3230262 1105784697302630545846201 := by
  unfold tailWord_3230262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7363583388957495854552315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78544889482213289115224693 7363583388957495854552315)
  ·
    refine ⟨11045375083436243781828473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7363583388957495854552315 11045375083436243781828473)
    ·
      refine ⟨8284031312577182836371355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11045375083436243781828473 8284031312577182836371355)
      ·
        refine ⟨12426046968865774254557033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8284031312577182836371355 12426046968865774254557033)
        ·
          refine ⟨9319535226649330690917775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12426046968865774254557033 9319535226649330690917775)
          ·
            refine ⟨13979302839973996036376663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9319535226649330690917775 13979302839973996036376663)
            ·
              refine ⟨20968954259960994054564995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13979302839973996036376663 20968954259960994054564995)
              ·
                refine ⟨31453431389941491081847493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20968954259960994054564995 31453431389941491081847493)
                ·
                  refine ⟨5897518385614029577846405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31453431389941491081847493 5897518385614029577846405)
                  ·
                    refine ⟨1105784697302630545846201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5897518385614029577846405 1105784697302630545846201)
                    ·
                      rfl

theorem cell22_3230262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3230262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230262 prefixEnd_3230262 := by exact prefixLift 3230262
  have htrace : WordTrace (prefixWord ++ tailWord_3230262) baseStart_3230262 baseEnd_3230262 := by
    simpa [prefixWord, tailWord_3230262, baseEnd_3230262] using wordTrace_append hprefix tailTrace_3230262
  have hstable : (prefixWord ++ tailWord_3230262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230262).length < 2 ^ (prefixWord ++ tailWord_3230262).sum := by decide
  have hdescent : baseEnd_3230262 < baseStart_3230262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230288 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 9]
def baseStart_3230288 : Nat := 118140960795 + 3230288 * 2 ^ 59
def prefixEnd_3230288 : Nat := 4983230072969 + 3 ^ 40 * 3230288 * 2
def baseEnd_3230288 : Nat := 368597865877991714898707

theorem tailTrace_3230288 : CollatzResearch.WordTrace tailWord_3230288 prefixEnd_3230288 368597865877991714898707 := by
  unfold tailWord_3230288
  simp only [CollatzResearch.WordTrace]
  refine ⟨58909141260612870056641759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78545521680817160075522345 58909141260612870056641759)
  ·
    refine ⟨88363711890919305084962639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58909141260612870056641759 88363711890919305084962639)
    ·
      refine ⟨132545567836378957627443959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88363711890919305084962639 132545567836378957627443959)
      ·
        refine ⟨198818351754568436441165939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132545567836378957627443959 198818351754568436441165939)
        ·
          refine ⟨298227527631852654661748909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198818351754568436441165939 298227527631852654661748909)
          ·
            refine ⟨111835322861944745498155841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298227527631852654661748909 111835322861944745498155841)
            ·
              refine ⟨83876492146458559123616881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111835322861944745498155841 83876492146458559123616881)
              ·
                refine ⟨62907369109843919342712661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83876492146458559123616881 62907369109843919342712661)
                ·
                  refine ⟨368597865877991714898707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62907369109843919342712661 368597865877991714898707)
                  ·
                    rfl

theorem cell22_3230288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_3230288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230288 prefixEnd_3230288 := by exact prefixLift 3230288
  have htrace : WordTrace (prefixWord ++ tailWord_3230288) baseStart_3230288 baseEnd_3230288 := by
    simpa [prefixWord, tailWord_3230288, baseEnd_3230288] using wordTrace_append hprefix tailTrace_3230288
  have hstable : (prefixWord ++ tailWord_3230288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230288).length < 2 ^ (prefixWord ++ tailWord_3230288).sum := by decide
  have hdescent : baseEnd_3230288 < baseStart_3230288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230369 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_3230369 : Nat := 118140960795 + 3230369 * 2 ^ 59
def prefixEnd_3230369 : Nat := 4983230072969 + 3 ^ 40 * 3230369 * 2
def baseEnd_3230369 : Nat := 1105821325589317933420873

theorem tailTrace_3230369 : CollatzResearch.WordTrace tailWord_3230369 prefixEnd_3230369 1105821325589317933420873 := by
  unfold tailWord_3230369
  simp only [CollatzResearch.WordTrace]
  refine ⟨117821236833932290946982161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78547491222621527297988107 117821236833932290946982161)
  ·
    refine ⟨88365927625449218210236621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117821236833932290946982161 88365927625449218210236621)
    ·
      refine ⟨33137222859543456828838733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88365927625449218210236621 33137222859543456828838733)
      ·
        refine ⟨12426458572328796310814525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33137222859543456828838733 12426458572328796310814525)
        ·
          refine ⟨4659921964623298616555447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12426458572328796310814525 4659921964623298616555447)
          ·
            refine ⟨6989882946934947924833171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659921964623298616555447 6989882946934947924833171)
            ·
              refine ⟨10484824420402421887249757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6989882946934947924833171 10484824420402421887249757)
              ·
                refine ⟨3931809157650908207718659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10484824420402421887249757 3931809157650908207718659)
                ·
                  refine ⟨5897713736476362311577989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931809157650908207718659 5897713736476362311577989)
                  ·
                    refine ⟨1105821325589317933420873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5897713736476362311577989 1105821325589317933420873)
                    ·
                      rfl

theorem cell22_3230369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_3230369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230369 prefixEnd_3230369 := by exact prefixLift 3230369
  have htrace : WordTrace (prefixWord ++ tailWord_3230369) baseStart_3230369 baseEnd_3230369 := by
    simpa [prefixWord, tailWord_3230369, baseEnd_3230369] using wordTrace_append hprefix tailTrace_3230369
  have hstable : (prefixWord ++ tailWord_3230369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230369).length < 2 ^ (prefixWord ++ tailWord_3230369).sum := by decide
  have hdescent : baseEnd_3230369 < baseStart_3230369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230412 : List Nat := [2, 2, 1, 5, 1, 2, 1, 8]
def baseStart_3230412 : Nat := 118140960795 + 3230412 * 2 ^ 59
def prefixEnd_3230412 : Nat := 4983230072969 + 3 ^ 40 * 3230412 * 2
def baseEnd_3230412 : Nat := 122870671707564461621749

theorem tailTrace_3230412 : CollatzResearch.WordTrace tailWord_3230412 prefixEnd_3230412 122870671707564461621749 := by
  unfold tailWord_3230412
  simp only [CollatzResearch.WordTrace]
  refine ⟨58911402586388254645398745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78548536781851006193864993 58911402586388254645398745)
  ·
    refine ⟨44183551939791190984049059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58911402586388254645398745 44183551939791190984049059)
    ·
      refine ⟨66275327909686786476073589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44183551939791190984049059 66275327909686786476073589)
      ·
        refine ⟨6213311991533136232131899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66275327909686786476073589 6213311991533136232131899)
        ·
          refine ⟨9319967987299704348197849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6213311991533136232131899 9319967987299704348197849)
          ·
            refine ⟨6989975990474778261148387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9319967987299704348197849 6989975990474778261148387)
            ·
              refine ⟨10484963985712167391722581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6989975990474778261148387 10484963985712167391722581)
              ·
                refine ⟨122870671707564461621749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10484963985712167391722581 122870671707564461621749)
                ·
                  rfl

theorem cell22_3230412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 8].length) (baseStart_3230412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230412 prefixEnd_3230412 := by exact prefixLift 3230412
  have htrace : WordTrace (prefixWord ++ tailWord_3230412) baseStart_3230412 baseEnd_3230412 := by
    simpa [prefixWord, tailWord_3230412, baseEnd_3230412] using wordTrace_append hprefix tailTrace_3230412
  have hstable : (prefixWord ++ tailWord_3230412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230412).length < 2 ^ (prefixWord ++ tailWord_3230412).sum := by decide
  have hdescent : baseEnd_3230412 < baseStart_3230412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230418 : List Nat := [3, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_3230418 : Nat := 118140960795 + 3230418 * 2 ^ 59
def prefixEnd_3230418 : Nat := 4983230072969 + 3 ^ 40 * 3230418 * 2
def baseEnd_3230418 : Nat := 368612699763566046315241

theorem tailTrace_3230418 : CollatzResearch.WordTrace tailWord_3230418 prefixEnd_3230418 368612699763566046315241 := by
  unfold tailWord_3230418
  simp only [CollatzResearch.WordTrace]
  refine ⟨29455756002688693078878977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78548682673836514877010605 29455756002688693078878977)
  ·
    refine ⟨22091817002016519809159233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29455756002688693078878977 22091817002016519809159233)
    ·
      refine ⟨16568862751512389856869425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22091817002016519809159233 16568862751512389856869425)
      ·
        refine ⟨12426647063634292392652069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16568862751512389856869425 12426647063634292392652069)
        ·
          refine ⟨2329996324431429823622263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12426647063634292392652069 2329996324431429823622263)
          ·
            refine ⟨3494994486647144735433395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329996324431429823622263 3494994486647144735433395)
            ·
              refine ⟨5242491729970717103150093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494994486647144735433395 5242491729970717103150093)
              ·
                refine ⟨1965934398739018913681285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5242491729970717103150093 1965934398739018913681285)
                ·
                  refine ⟨368612699763566046315241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1965934398739018913681285 368612699763566046315241)
                  ·
                    rfl

theorem cell22_3230418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_3230418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230418 prefixEnd_3230418 := by exact prefixLift 3230418
  have htrace : WordTrace (prefixWord ++ tailWord_3230418) baseStart_3230418 baseEnd_3230418 := by
    simpa [prefixWord, tailWord_3230418, baseEnd_3230418] using wordTrace_append hprefix tailTrace_3230418
  have hstable : (prefixWord ++ tailWord_3230418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230418).length < 2 ^ (prefixWord ++ tailWord_3230418).sum := by decide
  have hdescent : baseEnd_3230418 < baseStart_3230418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230455 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 1, 7]
def baseStart_3230455 : Nat := 118140960795 + 3230455 * 2 ^ 59
def prefixEnd_3230455 : Nat := 4983230072969 + 3 ^ 40 * 3230455 * 2
def baseEnd_3230455 : Nat := 1105850765146842375770609

theorem tailTrace_3230455 : CollatzResearch.WordTrace tailWord_3230455 prefixEnd_3230455 1105850765146842375770609 := by
  unfold tailWord_3230455
  simp only [CollatzResearch.WordTrace]
  refine ⟨117824373511620727634612819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78549582341080485089741879 117824373511620727634612819)
  ·
    refine ⟨176736560267431091451919229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117824373511620727634612819 176736560267431091451919229)
    ·
      refine ⟨66276210100286659294469711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176736560267431091451919229 66276210100286659294469711)
      ·
        refine ⟨99414315150429988941704567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66276210100286659294469711 99414315150429988941704567)
        ·
          refine ⟨149121472725644983412556851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99414315150429988941704567 149121472725644983412556851)
          ·
            refine ⟨223682209088467475118835277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149121472725644983412556851 223682209088467475118835277)
            ·
              refine ⟨83880828408175303169563229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223682209088467475118835277 83880828408175303169563229)
              ·
                refine ⟨31455310653065738688586211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83880828408175303169563229 31455310653065738688586211)
                ·
                  refine ⟨47182965979598608032879317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31455310653065738688586211 47182965979598608032879317)
                  ·
                    refine ⟨1105850765146842375770609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47182965979598608032879317 1105850765146842375770609)
                    ·
                      rfl

theorem cell22_3230455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_3230455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230455 prefixEnd_3230455 := by exact prefixLift 3230455
  have htrace : WordTrace (prefixWord ++ tailWord_3230455) baseStart_3230455 baseEnd_3230455 := by
    simpa [prefixWord, tailWord_3230455, baseEnd_3230455] using wordTrace_append hprefix tailTrace_3230455
  have hstable : (prefixWord ++ tailWord_3230455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230455).length < 2 ^ (prefixWord ++ tailWord_3230455).sum := by decide
  have hdescent : baseEnd_3230455 < baseStart_3230455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230506 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_3230506 : Nat := 118140960795 + 3230506 * 2 ^ 59
def prefixEnd_3230506 : Nat := 4983230072969 + 3 ^ 40 * 3230506 * 2
def baseEnd_3230506 : Nat := 1105868223489095242745453

theorem tailTrace_3230506 : CollatzResearch.WordTrace tailWord_3230506 prefixEnd_3230506 1105868223489095242745453 := by
  unfold tailWord_3230506
  simp only [CollatzResearch.WordTrace]
  refine ⟨29456558408608990836179843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78550822422957308896479581 29456558408608990836179843)
  ·
    refine ⟨44184837612913486254269765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29456558408608990836179843 44184837612913486254269765)
    ·
      refine ⟨8284657052421278672675581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44184837612913486254269765 8284657052421278672675581)
      ·
        refine ⟨3106746394657979502253343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8284657052421278672675581 3106746394657979502253343)
        ·
          refine ⟨4660119591986969253380015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106746394657979502253343 4660119591986969253380015)
          ·
            refine ⟨6990179387980453880070023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660119591986969253380015 6990179387980453880070023)
            ·
              refine ⟨10485269081970680820105035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990179387980453880070023 10485269081970680820105035)
              ·
                refine ⟨15727903622956021230157553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10485269081970680820105035 15727903622956021230157553)
                ·
                  refine ⟨11795927717217015922618165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15727903622956021230157553 11795927717217015922618165)
                  ·
                    refine ⟨1105868223489095242745453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11795927717217015922618165 1105868223489095242745453)
                    ·
                      rfl

theorem cell22_3230506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_3230506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230506 prefixEnd_3230506 := by exact prefixLift 3230506
  have htrace : WordTrace (prefixWord ++ tailWord_3230506) baseStart_3230506 baseEnd_3230506 := by
    simpa [prefixWord, tailWord_3230506, baseEnd_3230506] using wordTrace_append hprefix tailTrace_3230506
  have hstable : (prefixWord ++ tailWord_3230506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230506).length < 2 ^ (prefixWord ++ tailWord_3230506).sum := by decide
  have hdescent : baseEnd_3230506 < baseStart_3230506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230551 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 2, 3]
def baseStart_3230551 : Nat := 118140960795 + 3230551 * 2 ^ 59
def prefixEnd_3230551 : Nat := 4983230072969 + 3 ^ 40 * 3230551 * 2
def baseEnd_3230551 : Nat := 1105883627908730125370315

theorem tailTrace_3230551 : CollatzResearch.WordTrace tailWord_3230551 prefixEnd_3230551 1105883627908730125370315 := by
  unfold tailWord_3230551
  simp only [CollatzResearch.WordTrace]
  refine ⟨117827874919272936030107507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78551916612848624020071671 117827874919272936030107507)
  ·
    refine ⟨176741812378909404045161261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117827874919272936030107507 176741812378909404045161261)
    ·
      refine ⟨66278179642091026516935473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176741812378909404045161261 66278179642091026516935473)
      ·
        refine ⟨49708634731568269887701605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66278179642091026516935473 49708634731568269887701605)
        ·
          refine ⟨9320369012169050603944051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49708634731568269887701605 9320369012169050603944051)
          ·
            refine ⟨13980553518253575905916077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9320369012169050603944051 13980553518253575905916077)
            ·
              refine ⟨5242707569345090964718529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13980553518253575905916077 5242707569345090964718529)
              ·
                refine ⟨3932030677008818223538897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5242707569345090964718529 3932030677008818223538897)
                ·
                  refine ⟨2949023007756613667654173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3932030677008818223538897 2949023007756613667654173)
                  ·
                    refine ⟨1105883627908730125370315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949023007756613667654173 1105883627908730125370315)
                    ·
                      rfl

theorem cell22_3230551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_3230551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230551 prefixEnd_3230551 := by exact prefixLift 3230551
  have htrace : WordTrace (prefixWord ++ tailWord_3230551) baseStart_3230551 baseEnd_3230551 := by
    simpa [prefixWord, tailWord_3230551, baseEnd_3230551] using wordTrace_append hprefix tailTrace_3230551
  have hstable : (prefixWord ++ tailWord_3230551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230551).length < 2 ^ (prefixWord ++ tailWord_3230551).sum := by decide
  have hdescent : baseEnd_3230551 < baseStart_3230551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230568 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 2, 3]
def baseStart_3230568 : Nat := 118140960795 + 3230568 * 2 ^ 59
def prefixEnd_3230568 : Nat := 4983230072969 + 3 ^ 40 * 3230568 * 2
def baseEnd_3230568 : Nat := 1105889447356147747695263

theorem tailTrace_3230568 : CollatzResearch.WordTrace tailWord_3230568 prefixEnd_3230568 1105889447356147747695263 := by
  unfold tailWord_3230568
  simp only [CollatzResearch.WordTrace]
  refine ⟨58914247480105673966738179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78552329973474231955650905 58914247480105673966738179)
  ·
    refine ⟨88371371220158510950107269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58914247480105673966738179 88371371220158510950107269)
    ·
      refine ⟨16569632103779720803145113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88371371220158510950107269 16569632103779720803145113)
      ·
        refine ⟨12427224077834790602358835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16569632103779720803145113 12427224077834790602358835)
        ·
          refine ⟨18640836116752185903538253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12427224077834790602358835 18640836116752185903538253)
          ·
            refine ⟨6990313543782069713826845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18640836116752185903538253 6990313543782069713826845)
            ·
              refine ⟨2621367578918276142685067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6990313543782069713826845 2621367578918276142685067)
              ·
                refine ⟨3932051368377414214027601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621367578918276142685067 3932051368377414214027601)
                ·
                  refine ⟨2949038526283060660520701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3932051368377414214027601 2949038526283060660520701)
                  ·
                    refine ⟨1105889447356147747695263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949038526283060660520701 1105889447356147747695263)
                    ·
                      rfl

theorem cell22_3230568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_3230568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230568 prefixEnd_3230568 := by exact prefixLift 3230568
  have htrace : WordTrace (prefixWord ++ tailWord_3230568) baseStart_3230568 baseEnd_3230568 := by
    simpa [prefixWord, tailWord_3230568, baseEnd_3230568] using wordTrace_append hprefix tailTrace_3230568
  have hstable : (prefixWord ++ tailWord_3230568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230568).length < 2 ^ (prefixWord ++ tailWord_3230568).sum := by decide
  have hdescent : baseEnd_3230568 < baseStart_3230568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230579 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 3, 3]
def baseStart_3230579 : Nat := 118140960795 + 3230579 * 2 ^ 59
def prefixEnd_3230579 : Nat := 4983230072969 + 3 ^ 40 * 3230579 * 2
def baseEnd_3230579 : Nat := 1105893212880947385670229

theorem tailTrace_3230579 : CollatzResearch.WordTrace tailWord_3230579 prefixEnd_3230579 1105893212880947385670229 := by
  unfold tailWord_3230579
  simp only [CollatzResearch.WordTrace]
  refine ⟨117828896163171496812126791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78552597442114331208084527 117828896163171496812126791)
  ·
    refine ⟨176743344244757245218190187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117828896163171496812126791 176743344244757245218190187)
    ·
      refine ⟨265115016367135867827285281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176743344244757245218190187 265115016367135867827285281)
      ·
        refine ⟨198836262275351900870463961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265115016367135867827285281 198836262275351900870463961)
        ·
          refine ⟨149127196706513925652847971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198836262275351900870463961 149127196706513925652847971)
          ·
            refine ⟨223690795059770888479271957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149127196706513925652847971 223690795059770888479271957)
            ·
              refine ⟨10485506018426760397465873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 223690795059770888479271957 10485506018426760397465873)
              ·
                refine ⟨7864129513820070298099405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10485506018426760397465873 7864129513820070298099405)
                ·
                  refine ⟨2949048567682526361787277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7864129513820070298099405 2949048567682526361787277)
                  ·
                    refine ⟨1105893212880947385670229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949048567682526361787277 1105893212880947385670229)
                    ·
                      rfl

theorem cell22_3230579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 3].length) (baseStart_3230579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230579 prefixEnd_3230579 := by exact prefixLift 3230579
  have htrace : WordTrace (prefixWord ++ tailWord_3230579) baseStart_3230579 baseEnd_3230579 := by
    simpa [prefixWord, tailWord_3230579, baseEnd_3230579] using wordTrace_append hprefix tailTrace_3230579
  have hstable : (prefixWord ++ tailWord_3230579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230579).length < 2 ^ (prefixWord ++ tailWord_3230579).sum := by decide
  have hdescent : baseEnd_3230579 < baseStart_3230579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230581 : List Nat := [1, 3, 4, 1, 1, 4, 2, 6]
def baseStart_3230581 : Nat := 118140960795 + 3230581 * 2 ^ 59
def prefixEnd_3230581 : Nat := 4983230072969 + 3 ^ 40 * 3230581 * 2
def baseEnd_3230581 : Nat := 122877099724646671902247

theorem tailTrace_3230581 : CollatzResearch.WordTrace tailWord_3230581 prefixEnd_3230581 122877099724646671902247 := by
  unfold tailWord_3230581
  simp only [CollatzResearch.WordTrace]
  refine ⟨117828969109164251153699597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78552646072776167435799731 117828969109164251153699597)
  ·
    refine ⟨44185863415936594182637349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117828969109164251153699597 44185863415936594182637349)
    ·
      refine ⟨8284849390488111409244503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44185863415936594182637349 8284849390488111409244503)
      ·
        refine ⟨12427274085732167113866755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8284849390488111409244503 12427274085732167113866755)
        ·
          refine ⟨18640911128598250670800133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12427274085732167113866755 18640911128598250670800133)
          ·
            refine ⟨3495170836612172000775025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18640911128598250670800133 3495170836612172000775025)
            ·
              refine ⟨2621378127459129000581269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3495170836612172000775025 2621378127459129000581269)
              ·
                refine ⟨122877099724646671902247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2621378127459129000581269 122877099724646671902247)
                ·
                  rfl

theorem cell22_3230581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 6].length) (baseStart_3230581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230581 prefixEnd_3230581 := by exact prefixLift 3230581
  have htrace : WordTrace (prefixWord ++ tailWord_3230581) baseStart_3230581 baseEnd_3230581 := by
    simpa [prefixWord, tailWord_3230581, baseEnd_3230581] using wordTrace_append hprefix tailTrace_3230581
  have hstable : (prefixWord ++ tailWord_3230581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230581).length < 2 ^ (prefixWord ++ tailWord_3230581).sum := by decide
  have hdescent : baseEnd_3230581 < baseStart_3230581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230626 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_3230626 : Nat := 118140960795 + 3230626 * 2 ^ 59
def prefixEnd_3230626 : Nat := 4983230072969 + 3 ^ 40 * 3230626 * 2
def baseEnd_3230626 : Nat := 368636433980484976581695

theorem tailTrace_3230626 : CollatzResearch.WordTrace tailWord_3230626 prefixEnd_3230626 368636433980484976581695 := by
  unfold tailWord_3230626
  simp only [CollatzResearch.WordTrace]
  refine ⟨29457652598500305959771933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78553740262667482559391821 29457652598500305959771933)
  ·
    refine ⟨11046619724437614734914475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29457652598500305959771933 11046619724437614734914475)
    ·
      refine ⟨16569929586656422102371713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11046619724437614734914475 16569929586656422102371713)
      ·
        refine ⟨12427447189992316576778785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16569929586656422102371713 12427447189992316576778785)
        ·
          refine ⟨9320585392494237432584089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12427447189992316576778785 9320585392494237432584089)
          ·
            refine ⟨6990439044370678074438067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9320585392494237432584089 6990439044370678074438067)
            ·
              refine ⟨10485658566556017111657101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990439044370678074438067 10485658566556017111657101)
              ·
                refine ⟨3932121962458506416871413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10485658566556017111657101 3932121962458506416871413)
                ·
                  refine ⟨368636433980484976581695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3932121962458506416871413 368636433980484976581695)
                  ·
                    rfl

theorem cell22_3230626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_3230626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230626 prefixEnd_3230626 := by exact prefixLift 3230626
  have htrace : WordTrace (prefixWord ++ tailWord_3230626) baseStart_3230626 baseEnd_3230626 := by
    simpa [prefixWord, tailWord_3230626, baseEnd_3230626] using wordTrace_append hprefix tailTrace_3230626
  have hstable : (prefixWord ++ tailWord_3230626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230626).length < 2 ^ (prefixWord ++ tailWord_3230626).sum := by decide
  have hdescent : baseEnd_3230626 < baseStart_3230626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230639 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 1, 4]
def baseStart_3230639 : Nat := 118140960795 + 3230639 * 2 ^ 59
def prefixEnd_3230639 : Nat := 4983230072969 + 3 ^ 40 * 3230639 * 2
def baseEnd_3230639 : Nat := 1105913752107127229170045

theorem tailTrace_3230639 : CollatzResearch.WordTrace tailWord_3230639 prefixEnd_3230639 1105913752107127229170045 := by
  unfold tailWord_3230639
  simp only [CollatzResearch.WordTrace]
  refine ⟨117831084542954127059310971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78554056361969418039540647 117831084542954127059310971)
  ·
    refine ⟨176746626814431190588966457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117831084542954127059310971 176746626814431190588966457)
    ·
      refine ⟨132559970110823392941724843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176746626814431190588966457 132559970110823392941724843)
      ·
        refine ⟨198839955166235089412587265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132559970110823392941724843 198839955166235089412587265)
        ·
          refine ⟨149129966374676317059440449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198839955166235089412587265 149129966374676317059440449)
          ·
            refine ⟨111847474781007237794580337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149129966374676317059440449 111847474781007237794580337)
            ·
              refine ⟨83885606085755428345935253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111847474781007237794580337 83885606085755428345935253)
              ·
                refine ⟨3932137785269785703715715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83885606085755428345935253 3932137785269785703715715)
                ·
                  refine ⟨5898206677904678555573573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932137785269785703715715 5898206677904678555573573)
                  ·
                    refine ⟨1105913752107127229170045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5898206677904678555573573 1105913752107127229170045)
                    ·
                      rfl

theorem cell22_3230639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_3230639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230639 prefixEnd_3230639 := by exact prefixLift 3230639
  have htrace : WordTrace (prefixWord ++ tailWord_3230639) baseStart_3230639 baseEnd_3230639 := by
    simpa [prefixWord, tailWord_3230639, baseEnd_3230639] using wordTrace_append hprefix tailTrace_3230639
  have hstable : (prefixWord ++ tailWord_3230639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230639).length < 2 ^ (prefixWord ++ tailWord_3230639).sum := by decide
  have hdescent : baseEnd_3230639 < baseStart_3230639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230671 : List Nat := [1, 1, 2, 1, 1, 7, 1, 4, 4]
def baseStart_3230671 : Nat := 118140960795 + 3230671 * 2 ^ 59
def prefixEnd_3230671 : Nat := 4983230072969 + 3 ^ 40 * 3230671 * 2
def baseEnd_3230671 : Nat := 368641568787029937456649

theorem tailTrace_3230671 : CollatzResearch.WordTrace tailWord_3230671 prefixEnd_3230671 368641568787029937456649 := by
  unfold tailWord_3230671
  simp only [CollatzResearch.WordTrace]
  refine ⟨117832251678838196524475867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78554834452558797682983911 117832251678838196524475867)
  ·
    refine ⟨176748377518257294786713801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117832251678838196524475867 176748377518257294786713801)
    ·
      refine ⟨132561283138692971090035351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176748377518257294786713801 132561283138692971090035351)
      ·
        refine ⟨198841924708039456635053027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132561283138692971090035351 198841924708039456635053027)
        ·
          refine ⟨298262887062059184952579541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198841924708039456635053027 298262887062059184952579541)
          ·
            refine ⟨6990536415517012147326083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 298262887062059184952579541 6990536415517012147326083)
            ·
              refine ⟨10485804623275518220989125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990536415517012147326083 10485804623275518220989125)
              ·
                refine ⟨1966088366864159666435461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10485804623275518220989125 1966088366864159666435461)
                ·
                  refine ⟨368641568787029937456649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1966088366864159666435461 368641568787029937456649)
                  ·
                    rfl

theorem cell22_3230671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 4].length) (baseStart_3230671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230671 prefixEnd_3230671 := by exact prefixLift 3230671
  have htrace : WordTrace (prefixWord ++ tailWord_3230671) baseStart_3230671 baseEnd_3230671 := by
    simpa [prefixWord, tailWord_3230671, baseEnd_3230671] using wordTrace_append hprefix tailTrace_3230671
  have hstable : (prefixWord ++ tailWord_3230671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230671).length < 2 ^ (prefixWord ++ tailWord_3230671).sum := by decide
  have hdescent : baseEnd_3230671 < baseStart_3230671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230731 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 3, 3]
def baseStart_3230731 : Nat := 118140960795 + 3230731 * 2 ^ 59
def prefixEnd_3230731 : Nat := 4983230072969 + 3 ^ 40 * 3230731 * 2
def baseEnd_3230731 : Nat := 1105945245587269655869763

theorem tailTrace_3230731 : CollatzResearch.WordTrace tailWord_3230731 prefixEnd_3230731 1105945245587269655869763 := by
  unfold tailWord_3230731
  simp only [CollatzResearch.WordTrace]
  refine ⟨117834440058620826771660047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78556293372413884514440031 117834440058620826771660047)
  ·
    refine ⟨176751660087931240157490071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117834440058620826771660047 176751660087931240157490071)
    ·
      refine ⟨265127490131896860236235107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176751660087931240157490071 265127490131896860236235107)
      ·
        refine ⟨397691235197845290354352661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265127490131896860236235107 397691235197845290354352661)
        ·
          refine ⟨18641776649898997985360281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 397691235197845290354352661 18641776649898997985360281)
          ·
            refine ⟨13981332487424248489020211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18641776649898997985360281 13981332487424248489020211)
            ·
              refine ⟨20971998731136372733530317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13981332487424248489020211 20971998731136372733530317)
              ·
                refine ⟨7864499524176139775073869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20971998731136372733530317 7864499524176139775073869)
                ·
                  refine ⟨2949187321566052415652701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7864499524176139775073869 2949187321566052415652701)
                  ·
                    refine ⟨1105945245587269655869763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949187321566052415652701 1105945245587269655869763)
                    ·
                      rfl

theorem cell22_3230731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 3].length) (baseStart_3230731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230731 prefixEnd_3230731 := by exact prefixLift 3230731
  have htrace : WordTrace (prefixWord ++ tailWord_3230731) baseStart_3230731 baseEnd_3230731 := by
    simpa [prefixWord, tailWord_3230731, baseEnd_3230731] using wordTrace_append hprefix tailTrace_3230731
  have hstable : (prefixWord ++ tailWord_3230731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230731).length < 2 ^ (prefixWord ++ tailWord_3230731).sum := by decide
  have hdescent : baseEnd_3230731 < baseStart_3230731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230821 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_3230821 : Nat := 118140960795 + 3230821 * 2 ^ 59
def prefixEnd_3230821 : Nat := 4983230072969 + 3 ^ 40 * 3230821 * 2
def baseEnd_3230821 : Nat := 1105976054426539421119487

theorem tailTrace_3230821 : CollatzResearch.WordTrace tailWord_3230821 prefixEnd_3230821 1105976054426539421119487 := by
  unfold tailWord_3230821
  simp only [CollatzResearch.WordTrace]
  refine ⟨117837722628294772142436317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78558481752196514761624211 117837722628294772142436317)
  ·
    refine ⟨44189145985610539553413619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117837722628294772142436317 44189145985610539553413619)
    ·
      refine ⟨66283718978415809330120429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44189145985610539553413619 66283718978415809330120429)
      ·
        refine ⟨24856394616905928498795161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66283718978415809330120429 24856394616905928498795161)
        ·
          refine ⟨18642295962679446374096371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24856394616905928498795161 18642295962679446374096371)
          ·
            refine ⟨27963443944019169561144557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18642295962679446374096371 27963443944019169561144557)
            ·
              refine ⟨10486291479007188585429209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27963443944019169561144557 10486291479007188585429209)
              ·
                refine ⟨7864718609255391439071907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10486291479007188585429209 7864718609255391439071907)
                ·
                  refine ⟨11797077913883087158607861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7864718609255391439071907 11797077913883087158607861)
                  ·
                    refine ⟨1105976054426539421119487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11797077913883087158607861 1105976054426539421119487)
                    ·
                      rfl

theorem cell22_3230821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_3230821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230821 prefixEnd_3230821 := by exact prefixLift 3230821
  have htrace : WordTrace (prefixWord ++ tailWord_3230821) baseStart_3230821 baseEnd_3230821 := by
    simpa [prefixWord, tailWord_3230821, baseEnd_3230821] using wordTrace_append hprefix tailTrace_3230821
  have hstable : (prefixWord ++ tailWord_3230821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230821).length < 2 ^ (prefixWord ++ tailWord_3230821).sum := by decide
  have hdescent : baseEnd_3230821 < baseStart_3230821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230911 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 2, 5]
def baseStart_3230911 : Nat := 118140960795 + 3230911 * 2 ^ 59
def prefixEnd_3230911 : Nat := 4983230072969 + 3 ^ 40 * 3230911 * 2
def baseEnd_3230911 : Nat := 1106006863265809186369211

theorem tailTrace_3230911 : CollatzResearch.WordTrace tailWord_3230911 prefixEnd_3230911 1106006863265809186369211 := by
  unfold tailWord_3230911
  simp only [CollatzResearch.WordTrace]
  refine ⟨117841005197968717513212587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78560670131979145008808391 117841005197968717513212587)
  ·
    refine ⟨176761507796953076269818881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117841005197968717513212587 176761507796953076269818881)
    ·
      refine ⟨132571130847714807202364161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176761507796953076269818881 132571130847714807202364161)
      ·
        refine ⟨99428348135786105401773121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132571130847714807202364161 99428348135786105401773121)
        ·
          refine ⟨74571261101839579051329841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99428348135786105401773121 74571261101839579051329841)
          ·
            refine ⟨55928445826379684288497381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74571261101839579051329841 55928445826379684288497381)
            ·
              refine ⟨10486583592446190804093259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55928445826379684288497381 10486583592446190804093259)
              ·
                refine ⟨15729875388669286206139889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10486583592446190804093259 15729875388669286206139889)
                ·
                  refine ⟨11797406541501964654604917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15729875388669286206139889 11797406541501964654604917)
                  ·
                    refine ⟨1106006863265809186369211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11797406541501964654604917 1106006863265809186369211)
                    ·
                      rfl

theorem cell22_3230911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_3230911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230911 prefixEnd_3230911 := by exact prefixLift 3230911
  have htrace : WordTrace (prefixWord ++ tailWord_3230911) baseStart_3230911 baseEnd_3230911 := by
    simpa [prefixWord, tailWord_3230911, baseEnd_3230911] using wordTrace_append hprefix tailTrace_3230911
  have hstable : (prefixWord ++ tailWord_3230911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230911).length < 2 ^ (prefixWord ++ tailWord_3230911).sum := by decide
  have hdescent : baseEnd_3230911 < baseStart_3230911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230943 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 1, 4]
def baseStart_3230943 : Nat := 118140960795 + 3230943 * 2 ^ 59
def prefixEnd_3230943 : Nat := 4983230072969 + 3 ^ 40 * 3230943 * 2
def baseEnd_3230943 : Nat := 1106017817519771769569113

theorem tailTrace_3230943 : CollatzResearch.WordTrace tailWord_3230943 prefixEnd_3230943 1106017817519771769569113 := by
  unfold tailWord_3230943
  simp only [CollatzResearch.WordTrace]
  refine ⟨117842172333852786978377483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78561448222568524652251655 117842172333852786978377483)
  ·
    refine ⟨176763258500779180467566225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117842172333852786978377483 176763258500779180467566225)
    ·
      refine ⟨132572443875584385350674669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176763258500779180467566225 132572443875584385350674669)
      ·
        refine ⟨49714666453344144506503001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132572443875584385350674669 49714666453344144506503001)
        ·
          refine ⟨37285999840008108379877251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49714666453344144506503001 37285999840008108379877251)
          ·
            refine ⟨55928999760012162569815877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37285999840008108379877251 55928999760012162569815877)
            ·
              refine ⟨10486687455002280481840477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55928999760012162569815877 10486687455002280481840477)
              ·
                refine ⟨3932507795625855180690179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10486687455002280481840477 3932507795625855180690179)
                ·
                  refine ⟨5898761693438782771035269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932507795625855180690179 5898761693438782771035269)
                  ·
                    refine ⟨1106017817519771769569113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5898761693438782771035269 1106017817519771769569113)
                    ·
                      rfl

theorem cell22_3230943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_3230943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230943 prefixEnd_3230943 := by exact prefixLift 3230943
  have htrace : WordTrace (prefixWord ++ tailWord_3230943) baseStart_3230943 baseEnd_3230943 := by
    simpa [prefixWord, tailWord_3230943, baseEnd_3230943] using wordTrace_append hprefix tailTrace_3230943
  have hstable : (prefixWord ++ tailWord_3230943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230943).length < 2 ^ (prefixWord ++ tailWord_3230943).sum := by decide
  have hdescent : baseEnd_3230943 < baseStart_3230943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230958 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_3230958 : Nat := 118140960795 + 3230958 * 2 ^ 59
def prefixEnd_3230958 : Nat := 4983230072969 + 3 ^ 40 * 3230958 * 2
def baseEnd_3230958 : Nat := 368674317442105576814689

theorem tailTrace_3230958 : CollatzResearch.WordTrace tailWord_3230958 prefixEnd_3230958 368674317442105576814689 := by
  unfold tailWord_3230958
  simp only [CollatzResearch.WordTrace]
  refine ⟨14730339928599805567521691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78561812952532296360115685 14730339928599805567521691)
  ·
    refine ⟨22095509892899708351282537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14730339928599805567521691 22095509892899708351282537)
    ·
      refine ⟨16571632419674781263461903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22095509892899708351282537 16571632419674781263461903)
      ·
        refine ⟨24857448629512171895192855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16571632419674781263461903 24857448629512171895192855)
        ·
          refine ⟨37286172944268257842789283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24857448629512171895192855 37286172944268257842789283)
          ·
            refine ⟨55929259416402386764183925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37286172944268257842789283 55929259416402386764183925)
            ·
              refine ⟨5243368070287723759142243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55929259416402386764183925 5243368070287723759142243)
              ·
                refine ⟨7865052105431585638713365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5243368070287723759142243 7865052105431585638713365)
                ·
                  refine ⟨368674317442105576814689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7865052105431585638713365 368674317442105576814689)
                  ·
                    rfl

theorem cell22_3230958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_3230958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230958 prefixEnd_3230958 := by exact prefixLift 3230958
  have htrace : WordTrace (prefixWord ++ tailWord_3230958) baseStart_3230958 baseEnd_3230958 := by
    simpa [prefixWord, tailWord_3230958, baseEnd_3230958] using wordTrace_append hprefix tailTrace_3230958
  have hstable : (prefixWord ++ tailWord_3230958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230958).length < 2 ^ (prefixWord ++ tailWord_3230958).sum := by decide
  have hdescent : baseEnd_3230958 < baseStart_3230958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230964 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3230964 : Nat := 118140960795 + 3230964 * 2 ^ 59
def prefixEnd_3230964 : Nat := 4983230072969 + 3 ^ 40 * 3230964 * 2
def baseEnd_3230964 : Nat := 368675002082978238264683

theorem tailTrace_3230964 : CollatzResearch.WordTrace tailWord_3230964 prefixEnd_3230964 368675002082978238264683 := by
  unfold tailWord_3230964
  simp only [CollatzResearch.WordTrace]
  refine ⟨58921469133388353782445973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78561958844517805043261297 58921469133388353782445973)
  ·
    refine ⟨2761943865627579083552155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58921469133388353782445973 2761943865627579083552155)
    ·
      refine ⟨4142915798441368625328233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2761943865627579083552155 4142915798441368625328233)
      ·
        refine ⟨3107186848831026468996175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4142915798441368625328233 3107186848831026468996175)
        ·
          refine ⟨4660780273246539703494263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107186848831026468996175 4660780273246539703494263)
          ·
            refine ⟨6991170409869809555241395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660780273246539703494263 6991170409869809555241395)
            ·
              refine ⟨10486755614804714332862093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6991170409869809555241395 10486755614804714332862093)
              ·
                refine ⟨3932533355551767874823285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10486755614804714332862093 3932533355551767874823285)
                ·
                  refine ⟨368675002082978238264683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3932533355551767874823285 368675002082978238264683)
                  ·
                    rfl

theorem cell22_3230964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3230964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230964 prefixEnd_3230964 := by exact prefixLift 3230964
  have htrace : WordTrace (prefixWord ++ tailWord_3230964) baseStart_3230964 baseEnd_3230964 := by
    simpa [prefixWord, tailWord_3230964, baseEnd_3230964] using wordTrace_append hprefix tailTrace_3230964
  have hstable : (prefixWord ++ tailWord_3230964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230964).length < 2 ^ (prefixWord ++ tailWord_3230964).sum := by decide
  have hdescent : baseEnd_3230964 < baseStart_3230964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230988 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_3230988 : Nat := 118140960795 + 3230988 * 2 ^ 59
def prefixEnd_3230988 : Nat := 4983230072969 + 3 ^ 40 * 3230988 * 2
def baseEnd_3230988 : Nat := 1106033221939406652193975

theorem tailTrace_3230988 : CollatzResearch.WordTrace tailWord_3230988 prefixEnd_3230988 1106033221939406652193975 := by
  unfold tailWord_3230988
  simp only [CollatzResearch.WordTrace]
  refine ⟨58921906809344879831882809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78562542412459839775843745 58921906809344879831882809)
  ·
    refine ⟨44191430107008659873912107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58921906809344879831882809 44191430107008659873912107)
    ·
      refine ⟨66287145160512989810868161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44191430107008659873912107 66287145160512989810868161)
      ·
        refine ⟨49715358870384742358151121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66287145160512989810868161 49715358870384742358151121)
        ·
          refine ⟨37286519152788556768613341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49715358870384742358151121 37286519152788556768613341)
          ·
            refine ⟨13982444682295708788230003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37286519152788556768613341 13982444682295708788230003)
            ·
              refine ⟨20973667023443563182345005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13982444682295708788230003 20973667023443563182345005)
              ·
                refine ⟨7865125133791336193379377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20973667023443563182345005 7865125133791336193379377)
                ·
                  refine ⟨5898843850343502145034533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7865125133791336193379377 5898843850343502145034533)
                  ·
                    refine ⟨1106033221939406652193975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5898843850343502145034533 1106033221939406652193975)
                    ·
                      rfl

theorem cell22_3230988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_3230988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3230988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3230988 prefixEnd_3230988 := by exact prefixLift 3230988
  have htrace : WordTrace (prefixWord ++ tailWord_3230988) baseStart_3230988 baseEnd_3230988 := by
    simpa [prefixWord, tailWord_3230988, baseEnd_3230988] using wordTrace_append hprefix tailTrace_3230988
  have hstable : (prefixWord ++ tailWord_3230988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230988).length < 2 ^ (prefixWord ++ tailWord_3230988).sum := by decide
  have hdescent : baseEnd_3230988 < baseStart_3230988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231005 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_3231005 : Nat := 118140960795 + 3231005 * 2 ^ 59
def prefixEnd_3231005 : Nat := 4983230072969 + 3 ^ 40 * 3231005 * 2
def baseEnd_3231005 : Nat := 1106039041386824274518923

theorem tailTrace_3231005 : CollatzResearch.WordTrace tailWord_3231005 prefixEnd_3231005 1106039041386824274518923 := by
  unfold tailWord_3231005
  simp only [CollatzResearch.WordTrace]
  refine ⟨117844433659628171567134469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78562955773085447711422979 117844433659628171567134469)
  ·
    refine ⟨22095831311180282168837713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117844433659628171567134469 22095831311180282168837713)
    ·
      refine ⟨16571873483385211626628285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22095831311180282168837713 16571873483385211626628285)
      ·
        refine ⟨6214452556269454359985607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16571873483385211626628285 6214452556269454359985607)
        ·
          refine ⟨9321678834404181539978411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6214452556269454359985607 9321678834404181539978411)
          ·
            refine ⟨13982518251606272309967617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9321678834404181539978411 13982518251606272309967617)
            ·
              refine ⟨10486888688704704232475713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13982518251606272309967617 10486888688704704232475713)
              ·
                refine ⟨7865166516528528174356785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10486888688704704232475713 7865166516528528174356785)
                ·
                  refine ⟨5898874887396396130767589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7865166516528528174356785 5898874887396396130767589)
                  ·
                    refine ⟨1106039041386824274518923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5898874887396396130767589 1106039041386824274518923)
                    ·
                      rfl

theorem cell22_3231005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_3231005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231005 prefixEnd_3231005 := by exact prefixLift 3231005
  have htrace : WordTrace (prefixWord ++ tailWord_3231005) baseStart_3231005 baseEnd_3231005 := by
    simpa [prefixWord, tailWord_3231005, baseEnd_3231005] using wordTrace_append hprefix tailTrace_3231005
  have hstable : (prefixWord ++ tailWord_3231005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231005).length < 2 ^ (prefixWord ++ tailWord_3231005).sum := by decide
  have hdescent : baseEnd_3231005 < baseStart_3231005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231007 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 2, 3]
def baseStart_3231007 : Nat := 118140960795 + 3231007 * 2 ^ 59
def prefixEnd_3231007 : Nat := 4983230072969 + 3 ^ 40 * 3231007 * 2
def baseEnd_3231007 : Nat := 1106039726027696935968917

theorem tailTrace_3231007 : CollatzResearch.WordTrace tailWord_3231007 prefixEnd_3231007 1106039726027696935968917 := by
  unfold tailWord_3231007
  simp only [CollatzResearch.WordTrace]
  refine ⟨117844506605620925908707275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78563004403747283939138183 117844506605620925908707275)
  ·
    refine ⟨176766759908431388863060913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117844506605620925908707275 176766759908431388863060913)
    ·
      refine ⟨132575069931323541647295685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176766759908431388863060913 132575069931323541647295685)
      ·
        refine ⟨24857825612123164058867941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132575069931323541647295685 24857825612123164058867941)
        ·
          refine ⟨4660842302273093261037739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24857825612123164058867941 4660842302273093261037739)
          ·
            refine ⟨6991263453409639891556609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660842302273093261037739 6991263453409639891556609)
            ·
              refine ⟨5243447590057229918667457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6991263453409639891556609 5243447590057229918667457)
              ·
                refine ⟨3932585692542922439000593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5243447590057229918667457 3932585692542922439000593)
                ·
                  refine ⟨2949439269407191829250445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3932585692542922439000593 2949439269407191829250445)
                  ·
                    refine ⟨1106039726027696935968917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949439269407191829250445 1106039726027696935968917)
                    ·
                      rfl

theorem cell22_3231007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_3231007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231007 prefixEnd_3231007 := by exact prefixLift 3231007
  have htrace : WordTrace (prefixWord ++ tailWord_3231007) baseStart_3231007 baseEnd_3231007 := by
    simpa [prefixWord, tailWord_3231007, baseEnd_3231007] using wordTrace_append hprefix tailTrace_3231007
  have hstable : (prefixWord ++ tailWord_3231007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231007).length < 2 ^ (prefixWord ++ tailWord_3231007).sum := by decide
  have hdescent : baseEnd_3231007 < baseStart_3231007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231031 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 11]
def baseStart_3231031 : Nat := 118140960795 + 3231031 * 2 ^ 59
def prefixEnd_3231031 : Nat := 4983230072969 + 3 ^ 40 * 3231031 * 2
def baseEnd_3231031 : Nat := 368682647239389624456281

theorem tailTrace_3231031 : CollatzResearch.WordTrace tailWord_3231031 prefixEnd_3231031 368682647239389624456281 := by
  unfold tailWord_3231031
  simp only [CollatzResearch.WordTrace]
  refine ⟨117845381957533978007580947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78563587971689318671720631 117845381957533978007580947)
  ·
    refine ⟨176768072936300967011371421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117845381957533978007580947 176768072936300967011371421)
    ·
      refine ⟨66288027351112862629264283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176768072936300967011371421 66288027351112862629264283)
      ·
        refine ⟨99432041026669293943896425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66288027351112862629264283 99432041026669293943896425)
        ·
          refine ⟨74574030770001970457922319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99432041026669293943896425 74574030770001970457922319)
          ·
            refine ⟨111861046155002955686883479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74574030770001970457922319 111861046155002955686883479)
            ·
              refine ⟨167791569232504433530325219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111861046155002955686883479 167791569232504433530325219)
              ·
                refine ⟨251687353848756650295487829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167791569232504433530325219 251687353848756650295487829)
                ·
                  refine ⟨368682647239389624456281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 251687353848756650295487829 368682647239389624456281)
                  ·
                    rfl

theorem cell22_3231031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 11].length) (baseStart_3231031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231031 prefixEnd_3231031 := by exact prefixLift 3231031
  have htrace : WordTrace (prefixWord ++ tailWord_3231031) baseStart_3231031 baseEnd_3231031 := by
    simpa [prefixWord, tailWord_3231031, baseEnd_3231031] using wordTrace_append hprefix tailTrace_3231031
  have hstable : (prefixWord ++ tailWord_3231031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231031).length < 2 ^ (prefixWord ++ tailWord_3231031).sum := by decide
  have hdescent : baseEnd_3231031 < baseStart_3231031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231037 : List Nat := [1, 4, 1, 5, 1, 1, 3, 6]
def baseStart_3231037 : Nat := 118140960795 + 3231037 * 2 ^ 59
def prefixEnd_3231037 : Nat := 4983230072969 + 3 ^ 40 * 3231037 * 2
def baseEnd_3231037 : Nat := 122894443960087428635425

theorem tailTrace_3231037 : CollatzResearch.WordTrace tailWord_3231037 prefixEnd_3231037 122894443960087428635425 := by
  unfold tailWord_3231037
  simp only [CollatzResearch.WordTrace]
  refine ⟨117845600795512241032299365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78563733863674827354866243 117845600795512241032299365)
  ·
    refine ⟨22096050149158545193556131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117845600795512241032299365 22096050149158545193556131)
    ·
      refine ⟨33144075223737817790334197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22096050149158545193556131 33144075223737817790334197)
      ·
        refine ⟨3107257052225420417843831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33144075223737817790334197 3107257052225420417843831)
        ·
          refine ⟨4660885578338130626765747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107257052225420417843831 4660885578338130626765747)
          ·
            refine ⟨6991328367507195940148621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660885578338130626765747 6991328367507195940148621)
            ·
              refine ⟨2621748137815198477555733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6991328367507195940148621 2621748137815198477555733)
              ·
                refine ⟨122894443960087428635425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2621748137815198477555733 122894443960087428635425)
                ·
                  rfl

theorem cell22_3231037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 6].length) (baseStart_3231037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231037 prefixEnd_3231037 := by exact prefixLift 3231037
  have htrace : WordTrace (prefixWord ++ tailWord_3231037) baseStart_3231037 baseEnd_3231037 := by
    simpa [prefixWord, tailWord_3231037, baseEnd_3231037] using wordTrace_append hprefix tailTrace_3231037
  have hstable : (prefixWord ++ tailWord_3231037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231037).length < 2 ^ (prefixWord ++ tailWord_3231037).sum := by decide
  have hdescent : baseEnd_3231037 < baseStart_3231037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231052 : List Nat := [2, 2, 1, 3, 2, 2, 1, 5, 1, 3]
def baseStart_3231052 : Nat := 118140960795 + 3231052 * 2 ^ 59
def prefixEnd_3231052 : Nat := 4983230072969 + 3 ^ 40 * 3231052 * 2
def baseEnd_3231052 : Nat := 1106055130447331818593779

theorem tailTrace_3231052 : CollatzResearch.WordTrace tailWord_3231052 prefixEnd_3231052 1106055130447331818593779 := by
  unfold tailWord_3231052
  simp only [CollatzResearch.WordTrace]
  refine ⟨58923073945228949297047705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78564098593638599062730273 58923073945228949297047705)
  ·
    refine ⟨44192305458921711972785779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58923073945228949297047705 44192305458921711972785779)
    ·
      refine ⟨66288458188382567959178669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44192305458921711972785779 66288458188382567959178669)
      ·
        refine ⟨24858171820643462984692001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66288458188382567959178669 24858171820643462984692001)
        ·
          refine ⟨18643628865482597238519001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24858171820643462984692001 18643628865482597238519001)
          ·
            refine ⟨13982721649111947928889251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18643628865482597238519001 13982721649111947928889251)
            ·
              refine ⟨20974082473667921893333877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13982721649111947928889251 20974082473667921893333877)
              ·
                refine ⟨1966320231906367677500051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20974082473667921893333877 1966320231906367677500051)
                ·
                  refine ⟨2949480347859551516250077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966320231906367677500051 2949480347859551516250077)
                  ·
                    refine ⟨1106055130447331818593779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949480347859551516250077 1106055130447331818593779)
                    ·
                      rfl

theorem cell22_3231052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_3231052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231052 prefixEnd_3231052 := by exact prefixLift 3231052
  have htrace : WordTrace (prefixWord ++ tailWord_3231052) baseStart_3231052 baseEnd_3231052 := by
    simpa [prefixWord, tailWord_3231052, baseEnd_3231052] using wordTrace_append hprefix tailTrace_3231052
  have hstable : (prefixWord ++ tailWord_3231052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231052).length < 2 ^ (prefixWord ++ tailWord_3231052).sum := by decide
  have hdescent : baseEnd_3231052 < baseStart_3231052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231063 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 2, 5]
def baseStart_3231063 : Nat := 118140960795 + 3231063 * 2 ^ 59
def prefixEnd_3231063 : Nat := 4983230072969 + 3 ^ 40 * 3231063 * 2
def baseEnd_3231063 : Nat := 1106058895972131456568745

theorem tailTrace_3231063 : CollatzResearch.WordTrace tailWord_3231063 prefixEnd_3231063 1106058895972131456568745 := by
  unfold tailWord_3231063
  simp only [CollatzResearch.WordTrace]
  refine ⟨117846549093418047472745843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78564366062278698315163895 117846549093418047472745843)
  ·
    refine ⟨176769823640127071209118765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117846549093418047472745843 176769823640127071209118765)
    ·
      refine ⟨66288683865047651703419537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176769823640127071209118765 66288683865047651703419537)
      ·
        refine ⟨49716512898785738777564653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66288683865047651703419537 49716512898785738777564653)
        ·
          refine ⟨18643692337044652041586745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49716512898785738777564653 18643692337044652041586745)
          ·
            refine ⟨13982769252783489031190059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18643692337044652041586745 13982769252783489031190059)
            ·
              refine ⟨20974153879175233546785089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13982769252783489031190059 20974153879175233546785089)
              ·
                refine ⟨15730615409381425160088817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20974153879175233546785089 15730615409381425160088817)
                ·
                  refine ⟨11797961557036068870066613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15730615409381425160088817 11797961557036068870066613)
                  ·
                    refine ⟨1106058895972131456568745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11797961557036068870066613 1106058895972131456568745)
                    ·
                      rfl

theorem cell22_3231063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_3231063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231063 prefixEnd_3231063 := by exact prefixLift 3231063
  have htrace : WordTrace (prefixWord ++ tailWord_3231063) baseStart_3231063 baseEnd_3231063 := by
    simpa [prefixWord, tailWord_3231063, baseEnd_3231063] using wordTrace_append hprefix tailTrace_3231063
  have hstable : (prefixWord ++ tailWord_3231063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231063).length < 2 ^ (prefixWord ++ tailWord_3231063).sum := by decide
  have hdescent : baseEnd_3231063 < baseStart_3231063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231095 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 1, 4]
def baseStart_3231095 : Nat := 118140960795 + 3231095 * 2 ^ 59
def prefixEnd_3231095 : Nat := 4983230072969 + 3 ^ 40 * 3231095 * 2
def baseEnd_3231095 : Nat := 1106069850226094039768647

theorem tailTrace_3231095 : CollatzResearch.WordTrace tailWord_3231095 prefixEnd_3231095 1106069850226094039768647 := by
  unfold tailWord_3231095
  simp only [CollatzResearch.WordTrace]
  refine ⟨117847716229302116937910739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78565144152868077958607159 117847716229302116937910739)
  ·
    refine ⟨176771574343953175406866109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117847716229302116937910739 176771574343953175406866109)
    ·
      refine ⟨66289340378982440777574791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176771574343953175406866109 66289340378982440777574791)
      ·
        refine ⟨99434010568473661166362187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66289340378982440777574791 99434010568473661166362187)
        ·
          refine ⟨149151015852710491749543281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99434010568473661166362187 149151015852710491749543281)
          ·
            refine ⟨111863261889532868812157461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149151015852710491749543281 111863261889532868812157461)
            ·
              refine ⟨5243590401071853225569881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111863261889532868812157461 5243590401071853225569881)
              ·
                refine ⟨3932692800803889919177411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5243590401071853225569881 3932692800803889919177411)
                ·
                  refine ⟨5899039201205834878766117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932692800803889919177411 5899039201205834878766117)
                  ·
                    refine ⟨1106069850226094039768647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5899039201205834878766117 1106069850226094039768647)
                    ·
                      rfl

theorem cell22_3231095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_3231095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231095 prefixEnd_3231095 := by exact prefixLift 3231095
  have htrace : WordTrace (prefixWord ++ tailWord_3231095) baseStart_3231095 baseEnd_3231095 := by
    simpa [prefixWord, tailWord_3231095, baseEnd_3231095] using wordTrace_append hprefix tailTrace_3231095
  have hstable : (prefixWord ++ tailWord_3231095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231095).length < 2 ^ (prefixWord ++ tailWord_3231095).sum := by decide
  have hdescent : baseEnd_3231095 < baseStart_3231095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231125 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_3231125 : Nat := 118140960795 + 3231125 * 2 ^ 59
def prefixEnd_3231125 : Nat := 4983230072969 + 3 ^ 40 * 3231125 * 2
def baseEnd_3231125 : Nat := 1106080119839183961518555

theorem tailTrace_3231125 : CollatzResearch.WordTrace tailWord_3231125 prefixEnd_3231125 1106080119839183961518555 := by
  unfold tailWord_3231125
  simp only [CollatzResearch.WordTrace]
  refine ⟨117848810419193432061502829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78565873612795621374335219 117848810419193432061502829)
  ·
    refine ⟨44193303907197537023063561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117848810419193432061502829 44193303907197537023063561)
    ·
      refine ⟨33144977930398152767297671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44193303907197537023063561 33144977930398152767297671)
      ·
        refine ⟨49717466895597229150946507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33144977930398152767297671 49717466895597229150946507)
        ·
          refine ⟨74576200343395843726419761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49717466895597229150946507 74576200343395843726419761)
          ·
            refine ⟨55932150257546882794814821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74576200343395843726419761 55932150257546882794814821)
            ·
              refine ⟨10487278173290040524027779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55932150257546882794814821 10487278173290040524027779)
              ·
                refine ⟨15730917259935060786041669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10487278173290040524027779 15730917259935060786041669)
                ·
                  refine ⟨2949546986237823897382813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15730917259935060786041669 2949546986237823897382813)
                  ·
                    refine ⟨1106080119839183961518555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949546986237823897382813 1106080119839183961518555)
                    ·
                      rfl

theorem cell22_3231125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_3231125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231125 prefixEnd_3231125 := by exact prefixLift 3231125
  have htrace : WordTrace (prefixWord ++ tailWord_3231125) baseStart_3231125 baseEnd_3231125 := by
    simpa [prefixWord, tailWord_3231125, baseEnd_3231125] using wordTrace_append hprefix tailTrace_3231125
  have hstable : (prefixWord ++ tailWord_3231125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231125).length < 2 ^ (prefixWord ++ tailWord_3231125).sum := by decide
  have hdescent : baseEnd_3231125 < baseStart_3231125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231157 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3231157 : Nat := 118140960795 + 3231157 * 2 ^ 59
def prefixEnd_3231157 : Nat := 4983230072969 + 3 ^ 40 * 3231157 * 2
def baseEnd_3231157 : Nat := 1106091074093146544718457

theorem tailTrace_3231157 : CollatzResearch.WordTrace tailWord_3231157 prefixEnd_3231157 1106091074093146544718457 := by
  unfold tailWord_3231157
  simp only [CollatzResearch.WordTrace]
  refine ⟨117849977555077501526667725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78566651703385001017778483 117849977555077501526667725)
  ·
    refine ⟨44193741583154063072500397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117849977555077501526667725 44193741583154063072500397)
    ·
      refine ⟨16572653093682773652187649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44193741583154063072500397 16572653093682773652187649)
      ·
        refine ⟨12429489820262080239140737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16572653093682773652187649 12429489820262080239140737)
        ·
          refine ⟨9322117365196560179355553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12429489820262080239140737 9322117365196560179355553)
          ·
            refine ⟨6991588023897420134516665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9322117365196560179355553 6991588023897420134516665)
            ·
              refine ⟨5243691017923065100887499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6991588023897420134516665 5243691017923065100887499)
              ·
                refine ⟨7865536526884597651331249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5243691017923065100887499 7865536526884597651331249)
                ·
                  refine ⟨5899152395163448238498437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7865536526884597651331249 5899152395163448238498437)
                  ·
                    refine ⟨1106091074093146544718457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5899152395163448238498437 1106091074093146544718457)
                    ·
                      rfl

theorem cell22_3231157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3231157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231157 prefixEnd_3231157 := by exact prefixLift 3231157
  have htrace : WordTrace (prefixWord ++ tailWord_3231157) baseStart_3231157 baseEnd_3231157 := by
    simpa [prefixWord, tailWord_3231157, baseEnd_3231157] using wordTrace_append hprefix tailTrace_3231157
  have hstable : (prefixWord ++ tailWord_3231157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231157).length < 2 ^ (prefixWord ++ tailWord_3231157).sum := by decide
  have hdescent : baseEnd_3231157 < baseStart_3231157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231183 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 7]
def baseStart_3231183 : Nat := 118140960795 + 3231183 * 2 ^ 59
def prefixEnd_3231183 : Nat := 4983230072969 + 3 ^ 40 * 3231183 * 2
def baseEnd_3231183 : Nat := 368699991474830381189459

theorem tailTrace_3231183 : CollatzResearch.WordTrace tailWord_3231183 prefixEnd_3231183 368699991474830381189459 := by
  unfold tailWord_3231183
  simp only [CollatzResearch.WordTrace]
  refine ⟨117850925852983307967114203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78567283901988871978076135 117850925852983307967114203)
  ·
    refine ⟨176776388779474961950671305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117850925852983307967114203 176776388779474961950671305)
    ·
      refine ⟨132582291584606221463003479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176776388779474961950671305 132582291584606221463003479)
      ·
        refine ⟨198873437376909332194505219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132582291584606221463003479 198873437376909332194505219)
        ·
          refine ⟨298310156065363998291757829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198873437376909332194505219 298310156065363998291757829)
          ·
            refine ⟨55933154262255749679704593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298310156065363998291757829 55933154262255749679704593)
            ·
              refine ⟨41949865696691812259778445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55933154262255749679704593 41949865696691812259778445)
              ·
                refine ⟨15731199636259429597416917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41949865696691812259778445 15731199636259429597416917)
                ·
                  refine ⟨368699991474830381189459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15731199636259429597416917 368699991474830381189459)
                  ·
                    rfl

theorem cell22_3231183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 7].length) (baseStart_3231183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231183 prefixEnd_3231183 := by exact prefixLift 3231183
  have htrace : WordTrace (prefixWord ++ tailWord_3231183) baseStart_3231183 baseEnd_3231183 := by
    simpa [prefixWord, tailWord_3231183, baseEnd_3231183] using wordTrace_append hprefix tailTrace_3231183
  have hstable : (prefixWord ++ tailWord_3231183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231183).length < 2 ^ (prefixWord ++ tailWord_3231183).sum := by decide
  have hdescent : baseEnd_3231183 < baseStart_3231183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231221 : List Nat := [1, 3, 5, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3231221 : Nat := 118140960795 + 3231221 * 2 ^ 59
def prefixEnd_3231221 : Nat := 4983230072969 + 3 ^ 40 * 3231221 * 2
def baseEnd_3231221 : Nat := 1106112982601071711118261

theorem tailTrace_3231221 : CollatzResearch.WordTrace tailWord_3231221 prefixEnd_3231221 1106112982601071711118261 := by
  unfold tailWord_3231221
  simp only [CollatzResearch.WordTrace]
  refine ⟨117852311826845640456997517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78568207884563760304665011 117852311826845640456997517)
  ·
    refine ⟨44194616935067115171374069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117852311826845640456997517 44194616935067115171374069)
    ·
      refine ⟨4143245337662542047316319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44194616935067115171374069 4143245337662542047316319)
      ·
        refine ⟨6214868006493813070974479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4143245337662542047316319 6214868006493813070974479)
        ·
          refine ⟨9322302009740719606461719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6214868006493813070974479 9322302009740719606461719)
          ·
            refine ⟨13983453014611079409692579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9322302009740719606461719 13983453014611079409692579)
            ·
              refine ⟨20975179521916619114538869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13983453014611079409692579 20975179521916619114538869)
              ·
                refine ⟨1966423080179683041988019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20975179521916619114538869 1966423080179683041988019)
                ·
                  refine ⟨2949634620269524562982029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966423080179683041988019 2949634620269524562982029)
                  ·
                    refine ⟨1106112982601071711118261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949634620269524562982029 1106112982601071711118261)
                    ·
                      rfl

theorem cell22_3231221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3231221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231221 prefixEnd_3231221 := by exact prefixLift 3231221
  have htrace : WordTrace (prefixWord ++ tailWord_3231221) baseStart_3231221 baseEnd_3231221 := by
    simpa [prefixWord, tailWord_3231221, baseEnd_3231221] using wordTrace_append hprefix tailTrace_3231221
  have hstable : (prefixWord ++ tailWord_3231221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231221).length < 2 ^ (prefixWord ++ tailWord_3231221).sum := by decide
  have hdescent : baseEnd_3231221 < baseStart_3231221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231234 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_3231234 : Nat := 118140960795 + 3231234 * 2 ^ 59
def prefixEnd_3231234 : Nat := 4983230072969 + 3 ^ 40 * 3231234 * 2
def baseEnd_3231234 : Nat := 368705810922248003514407

theorem tailTrace_3231234 : CollatzResearch.WordTrace tailWord_3231234 prefixEnd_3231234 368705810922248003514407 := by
  unfold tailWord_3231234
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463196493949635919305189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78568523983865695784813837 29463196493949635919305189)
  ·
    refine ⟨5524349342615556734869723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29463196493949635919305189 5524349342615556734869723)
    ·
      refine ⟨8286524013923335102304585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5524349342615556734869723 8286524013923335102304585)
      ·
        refine ⟨6214893010442501326728439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8286524013923335102304585 6214893010442501326728439)
        ·
          refine ⟨9322339515663751990092659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6214893010442501326728439 9322339515663751990092659)
          ·
            refine ⟨13983509273495627985138989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9322339515663751990092659 13983509273495627985138989)
            ·
              refine ⟨5243815977560860494427121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13983509273495627985138989 5243815977560860494427121)
              ·
                refine ⟨3932861983170645370820341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5243815977560860494427121 3932861983170645370820341)
                ·
                  refine ⟨368705810922248003514407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3932861983170645370820341 368705810922248003514407)
                  ·
                    rfl

theorem cell22_3231234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_3231234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231234 prefixEnd_3231234 := by exact prefixLift 3231234
  have htrace : WordTrace (prefixWord ++ tailWord_3231234) baseStart_3231234 baseEnd_3231234 := by
    simpa [prefixWord, tailWord_3231234, baseEnd_3231234] using wordTrace_append hprefix tailTrace_3231234
  have hstable : (prefixWord ++ tailWord_3231234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231234).length < 2 ^ (prefixWord ++ tailWord_3231234).sum := by decide
  have hdescent : baseEnd_3231234 < baseStart_3231234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231264 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_3231264 : Nat := 118140960795 + 3231264 * 2 ^ 59
def prefixEnd_3231264 : Nat := 4983230072969 + 3 ^ 40 * 3231264 * 2
def baseEnd_3231264 : Nat := 1106127702379833932293129

theorem tailTrace_3231264 : CollatzResearch.WordTrace tailWord_3231264 prefixEnd_3231264 1106127702379833932293129 := by
  unfold tailWord_3231264
  simp only [CollatzResearch.WordTrace]
  refine ⟨58926940082844929400406423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78569253443793239200541897 58926940082844929400406423)
  ·
    refine ⟨88390410124267394100609635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58926940082844929400406423 88390410124267394100609635)
    ·
      refine ⟨132585615186401091150914453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88390410124267394100609635 132585615186401091150914453)
      ·
        refine ⟨6214950711862551147699115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132585615186401091150914453 6214950711862551147699115)
        ·
          refine ⟨9322426067793826721548673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6214950711862551147699115 9322426067793826721548673)
          ·
            refine ⟨6991819550845370041161505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9322426067793826721548673 6991819550845370041161505)
            ·
              refine ⟨5243864663134027530871129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6991819550845370041161505 5243864663134027530871129)
              ·
                refine ⟨3932898497350520648153347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5243864663134027530871129 3932898497350520648153347)
                ·
                  refine ⟨5899347746025780972230021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932898497350520648153347 5899347746025780972230021)
                  ·
                    refine ⟨1106127702379833932293129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5899347746025780972230021 1106127702379833932293129)
                    ·
                      rfl

theorem cell22_3231264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_3231264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231264 prefixEnd_3231264 := by exact prefixLift 3231264
  have htrace : WordTrace (prefixWord ++ tailWord_3231264) baseStart_3231264 baseEnd_3231264 := by
    simpa [prefixWord, tailWord_3231264, baseEnd_3231264] using wordTrace_append hprefix tailTrace_3231264
  have hstable : (prefixWord ++ tailWord_3231264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231264).length < 2 ^ (prefixWord ++ tailWord_3231264).sum := by decide
  have hdescent : baseEnd_3231264 < baseStart_3231264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231322 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_3231322 : Nat := 118140960795 + 3231322 * 2 ^ 59
def prefixEnd_3231322 : Nat := 4983230072969 + 3 ^ 40 * 3231322 * 2
def baseEnd_3231322 : Nat := 1106147556965141114342951

theorem tailTrace_3231322 : CollatzResearch.WordTrace tailWord_3231322 prefixEnd_3231322 1106147556965141114342951 := by
  unfold tailWord_3231322
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463998899869933676606055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78570663732986489804282813 29463998899869933676606055)
  ·
    refine ⟨44195998349804900514909083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29463998899869933676606055 44195998349804900514909083)
    ·
      refine ⟨66293997524707350772363625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44195998349804900514909083 66293997524707350772363625)
      ·
        refine ⟨49720498143530513079272719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66293997524707350772363625 49720498143530513079272719)
        ·
          refine ⟨74580747215295769618909079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49720498143530513079272719 74580747215295769618909079)
          ·
            refine ⟨111871120822943654428363619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74580747215295769618909079 111871120822943654428363619)
            ·
              refine ⟨167806681234415481642545429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111871120822943654428363619 167806681234415481642545429)
              ·
                refine ⟨7865938182863225701994317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167806681234415481642545429 7865938182863225701994317)
                ·
                  refine ⟨2949726818573709638247869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7865938182863225701994317 2949726818573709638247869)
                  ·
                    refine ⟨1106147556965141114342951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949726818573709638247869 1106147556965141114342951)
                    ·
                      rfl

theorem cell22_3231322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_3231322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231322 prefixEnd_3231322 := by exact prefixLift 3231322
  have htrace : WordTrace (prefixWord ++ tailWord_3231322) baseStart_3231322 baseEnd_3231322 := by
    simpa [prefixWord, tailWord_3231322, baseEnd_3231322] using wordTrace_append hprefix tailTrace_3231322
  have hstable : (prefixWord ++ tailWord_3231322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231322).length < 2 ^ (prefixWord ++ tailWord_3231322).sum := by decide
  have hdescent : baseEnd_3231322 < baseStart_3231322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231335 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 9]
def baseStart_3231335 : Nat := 118140960795 + 3231335 * 2 ^ 59
def prefixEnd_3231335 : Nat := 4983230072969 + 3 ^ 40 * 3231335 * 2
def baseEnd_3231335 : Nat := 368717335710271137922637

theorem tailTrace_3231335 : CollatzResearch.WordTrace tailWord_3231335 prefixEnd_3231335 368717335710271137922637 := by
  unfold tailWord_3231335
  simp only [CollatzResearch.WordTrace]
  refine ⟨117856469748432637926647459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78570979832288425284431639 117856469748432637926647459)
  ·
    refine ⟨176784704622648956889971189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117856469748432637926647459 176784704622648956889971189)
    ·
      refine ⟨16573566058373339708434799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176784704622648956889971189 16573566058373339708434799)
      ·
        refine ⟨24860349087560009562652199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16573566058373339708434799 24860349087560009562652199)
        ·
          refine ⟨37290523631340014343978299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24860349087560009562652199 37290523631340014343978299)
          ·
            refine ⟨55935785447010021515967449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37290523631340014343978299 55935785447010021515967449)
            ·
              refine ⟨41951839085257516136975587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55935785447010021515967449 41951839085257516136975587)
              ·
                refine ⟨62927758627886274205463381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41951839085257516136975587 62927758627886274205463381)
                ·
                  refine ⟨368717335710271137922637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62927758627886274205463381 368717335710271137922637)
                  ·
                    rfl

theorem cell22_3231335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 9].length) (baseStart_3231335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231335 prefixEnd_3231335 := by exact prefixLift 3231335
  have htrace : WordTrace (prefixWord ++ tailWord_3231335) baseStart_3231335 baseEnd_3231335 := by
    simpa [prefixWord, tailWord_3231335, baseEnd_3231335] using wordTrace_append hprefix tailTrace_3231335
  have hstable : (prefixWord ++ tailWord_3231335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231335).length < 2 ^ (prefixWord ++ tailWord_3231335).sum := by decide
  have hdescent : baseEnd_3231335 < baseStart_3231335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231367 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3231367 : Nat := 118140960795 + 3231367 * 2 ^ 59
def prefixEnd_3231367 : Nat := 4983230072969 + 3 ^ 40 * 3231367 * 2
def baseEnd_3231367 : Nat := 1106162961384775996967813

theorem tailTrace_3231367 : CollatzResearch.WordTrace tailWord_3231367 prefixEnd_3231367 1106162961384775996967813 := by
  unfold tailWord_3231367
  simp only [CollatzResearch.WordTrace]
  refine ⟨117857636884316707391812355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78571757922877804927874903 117857636884316707391812355)
  ·
    refine ⟨176786455326475061087718533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117857636884316707391812355 176786455326475061087718533)
    ·
      refine ⟨33147460373714073953947225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176786455326475061087718533 33147460373714073953947225)
      ·
        refine ⟨24860595280285555465460419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33147460373714073953947225 24860595280285555465460419)
        ·
          refine ⟨37290892920428333198190629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24860595280285555465460419 37290892920428333198190629)
          ·
            refine ⟨6992042422580312474660743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37290892920428333198190629 6992042422580312474660743)
            ·
              refine ⟨10488063633870468711991115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6992042422580312474660743 10488063633870468711991115)
              ·
                refine ⟨15732095450805703067986673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10488063633870468711991115 15732095450805703067986673)
                ·
                  refine ⟨11799071588104277300990005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15732095450805703067986673 11799071588104277300990005)
                  ·
                    refine ⟨1106162961384775996967813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11799071588104277300990005 1106162961384775996967813)
                    ·
                      rfl

theorem cell22_3231367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3231367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231367 prefixEnd_3231367 := by exact prefixLift 3231367
  have htrace : WordTrace (prefixWord ++ tailWord_3231367) baseStart_3231367 baseEnd_3231367 := by
    simpa [prefixWord, tailWord_3231367, baseEnd_3231367] using wordTrace_append hprefix tailTrace_3231367
  have hstable : (prefixWord ++ tailWord_3231367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231367).length < 2 ^ (prefixWord ++ tailWord_3231367).sum := by decide
  have hdescent : baseEnd_3231367 < baseStart_3231367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231444 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3231444 : Nat := 118140960795 + 3231444 * 2 ^ 59
def prefixEnd_3231444 : Nat := 4983230072969 + 3 ^ 40 * 3231444 * 2
def baseEnd_3231444 : Nat := 1106189320058373462792577

theorem tailTrace_3231444 : CollatzResearch.WordTrace tailWord_3231444 prefixEnd_3231444 1106189320058373462792577 := by
  unfold tailWord_3231444
  simp only [CollatzResearch.WordTrace]
  refine ⟨58930222652518874771182693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78573630203358499694910257 58930222652518874771182693)
  ·
    refine ⟨11049416747347289019596755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58930222652518874771182693 11049416747347289019596755)
    ·
      refine ⟨16574125121020933529395133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11049416747347289019596755 16574125121020933529395133)
      ·
        refine ⟨6215296920382850073523175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16574125121020933529395133 6215296920382850073523175)
        ·
          refine ⟨9322945380574275110284763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215296920382850073523175 9322945380574275110284763)
          ·
            refine ⟨13984418070861412665427145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9322945380574275110284763 13984418070861412665427145)
            ·
              refine ⟨10488313553146059499070359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13984418070861412665427145 10488313553146059499070359)
              ·
                refine ⟨15732470329719089248605539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10488313553146059499070359 15732470329719089248605539)
                ·
                  refine ⟨23598705494578633872908309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15732470329719089248605539 23598705494578633872908309)
                  ·
                    refine ⟨1106189320058373462792577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23598705494578633872908309 1106189320058373462792577)
                    ·
                      rfl

theorem cell22_3231444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3231444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231444 prefixEnd_3231444 := by exact prefixLift 3231444
  have htrace : WordTrace (prefixWord ++ tailWord_3231444) baseStart_3231444 baseEnd_3231444 := by
    simpa [prefixWord, tailWord_3231444, baseEnd_3231444] using wordTrace_append hprefix tailTrace_3231444
  have hstable : (prefixWord ++ tailWord_3231444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231444).length < 2 ^ (prefixWord ++ tailWord_3231444).sum := by decide
  have hdescent : baseEnd_3231444 < baseStart_3231444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231459 : List Nat := [1, 1, 1, 7, 2, 2, 8]
def baseStart_3231459 : Nat := 118140960795 + 3231459 * 2 ^ 59
def prefixEnd_3231459 : Nat := 4983230072969 + 3 ^ 40 * 3231459 * 2
def baseEnd_3231459 : Nat := 40970164994996978654353

theorem tailTrace_3231459 : CollatzResearch.WordTrace tailWord_3231459 prefixEnd_3231459 40970164994996978654353 := by
  unfold tailWord_3231459
  simp only [CollatzResearch.WordTrace]
  refine ⟨117860992399983407104161431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78573994933322271402774287 117860992399983407104161431)
  ·
    refine ⟨176791488599975110656242147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117860992399983407104161431 176791488599975110656242147)
    ·
      refine ⟨265187232899962665984363221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176791488599975110656242147 265187232899962665984363221)
      ·
        refine ⟨6215325771092874984008513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 265187232899962665984363221 6215325771092874984008513)
        ·
          refine ⟨4661494328319656238006385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6215325771092874984008513 4661494328319656238006385)
          ·
            refine ⟨3496120746239742178504789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4661494328319656238006385 3496120746239742178504789)
            ·
              refine ⟨40970164994996978654353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3496120746239742178504789 40970164994996978654353)
              ·
                rfl

theorem cell22_3231459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 8].length) (baseStart_3231459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231459 prefixEnd_3231459 := by exact prefixLift 3231459
  have htrace : WordTrace (prefixWord ++ tailWord_3231459) baseStart_3231459 baseEnd_3231459 := by
    simpa [prefixWord, tailWord_3231459, baseEnd_3231459] using wordTrace_append hprefix tailTrace_3231459
  have hstable : (prefixWord ++ tailWord_3231459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231459).length < 2 ^ (prefixWord ++ tailWord_3231459).sum := by decide
  have hdescent : baseEnd_3231459 < baseStart_3231459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231476 : List Nat := [2, 6, 1, 1, 1, 1, 1, 9]
def baseStart_3231476 : Nat := 118140960795 + 3231476 * 2 ^ 59
def prefixEnd_3231476 : Nat := 4983230072969 + 3 ^ 40 * 3231476 * 2
def baseEnd_3231476 : Nat := 122911141590259560665831

theorem tailTrace_3231476 : CollatzResearch.WordTrace tailWord_3231476 prefixEnd_3231476 122911141590259560665831 := by
  unfold tailWord_3231476
  simp only [CollatzResearch.WordTrace]
  refine ⟨58930806220460909503765141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78574408293947879338353521 58930806220460909503765141)
  ·
    refine ⟨2762381541584105132988991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58930806220460909503765141 2762381541584105132988991)
    ·
      refine ⟨4143572312376157699483487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2762381541584105132988991 4143572312376157699483487)
      ·
        refine ⟨6215358468564236549225231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4143572312376157699483487 6215358468564236549225231)
        ·
          refine ⟨9323037702846354823837847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215358468564236549225231 9323037702846354823837847)
          ·
            refine ⟨13984556554269532235756771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9323037702846354823837847 13984556554269532235756771)
            ·
              refine ⟨20976834831404298353635157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13984556554269532235756771 20976834831404298353635157)
              ·
                refine ⟨122911141590259560665831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20976834831404298353635157 122911141590259560665831)
                ·
                  rfl

theorem cell22_3231476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 9].length) (baseStart_3231476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231476 prefixEnd_3231476 := by exact prefixLift 3231476
  have htrace : WordTrace (prefixWord ++ tailWord_3231476) baseStart_3231476 baseEnd_3231476 := by
    simpa [prefixWord, tailWord_3231476, baseEnd_3231476] using wordTrace_append hprefix tailTrace_3231476
  have hstable : (prefixWord ++ tailWord_3231476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231476).length < 2 ^ (prefixWord ++ tailWord_3231476).sum := by decide
  have hdescent : baseEnd_3231476 < baseStart_3231476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231525 : List Nat := [1, 3, 1, 2, 3, 4, 2, 2, 1, 3]
def baseStart_3231525 : Nat := 118140960795 + 3231525 * 2 ^ 59
def prefixEnd_3231525 : Nat := 4983230072969 + 3 ^ 40 * 3231525 * 2
def baseEnd_3231525 : Nat := 1106217048013716251517329

theorem tailTrace_3231525 : CollatzResearch.WordTrace tailWord_3231525 prefixEnd_3231525 1106217048013716251517329 := by
  unfold tailWord_3231525
  simp only [CollatzResearch.WordTrace]
  refine ⟨117863399617744300376064029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78575599745162866917376019 117863399617744300376064029)
  ·
    refine ⟨44198774856654112641024011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117863399617744300376064029 44198774856654112641024011)
    ·
      refine ⟨66298162284981168961536017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44198774856654112641024011 66298162284981168961536017)
      ·
        refine ⟨49723621713735876721152013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66298162284981168961536017 49723621713735876721152013)
        ·
          refine ⟨18646358142650953770432005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49723621713735876721152013 18646358142650953770432005)
          ·
            refine ⟨3496192151747053831956001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18646358142650953770432005 3496192151747053831956001)
            ·
              refine ⟨2622144113810290373967001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3496192151747053831956001 2622144113810290373967001)
              ·
                refine ⟨1966608085357717780475251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622144113810290373967001 1966608085357717780475251)
                ·
                  refine ⟨2949912128036576670712877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966608085357717780475251 2949912128036576670712877)
                  ·
                    refine ⟨1106217048013716251517329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2949912128036576670712877 1106217048013716251517329)
                    ·
                      rfl

theorem cell22_3231525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_3231525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231525 prefixEnd_3231525 := by exact prefixLift 3231525
  have htrace : WordTrace (prefixWord ++ tailWord_3231525) baseStart_3231525 baseEnd_3231525 := by
    simpa [prefixWord, tailWord_3231525, baseEnd_3231525] using wordTrace_append hprefix tailTrace_3231525
  have hstable : (prefixWord ++ tailWord_3231525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231525).length < 2 ^ (prefixWord ++ tailWord_3231525).sum := by decide
  have hdescent : baseEnd_3231525 < baseStart_3231525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231549 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 8]
def baseStart_3231549 : Nat := 118140960795 + 3231549 * 2 ^ 59
def prefixEnd_3231549 : Nat := 4983230072969 + 3 ^ 40 * 3231549 * 2
def baseEnd_3231549 : Nat := 368741754568062729639085

theorem tailTrace_3231549 : CollatzResearch.WordTrace tailWord_3231549 prefixEnd_3231549 368741754568062729639085 := by
  unfold tailWord_3231549
  simp only [CollatzResearch.WordTrace]
  refine ⟨117864274969657352474937701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78576183313104901649958467 117864274969657352474937701)
  ·
    refine ⟨22099551556810753589050819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117864274969657352474937701 22099551556810753589050819)
    ·
      refine ⟨33149327335216130383576229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22099551556810753589050819 33149327335216130383576229)
      ·
        refine ⟨6215498875353024446920543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33149327335216130383576229 6215498875353024446920543)
        ·
          refine ⟨9323248313029536670380815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215498875353024446920543 9323248313029536670380815)
          ·
            refine ⟨13984872469544305005571223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9323248313029536670380815 13984872469544305005571223)
            ·
              refine ⟨20977308704316457508356835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13984872469544305005571223 20977308704316457508356835)
              ·
                refine ⟨31465963056474686262535253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20977308704316457508356835 31465963056474686262535253)
                ·
                  refine ⟨368741754568062729639085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31465963056474686262535253 368741754568062729639085)
                  ·
                    rfl

theorem cell22_3231549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_3231549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231549 prefixEnd_3231549 := by exact prefixLift 3231549
  have htrace : WordTrace (prefixWord ++ tailWord_3231549) baseStart_3231549 baseEnd_3231549 := by
    simpa [prefixWord, tailWord_3231549, baseEnd_3231549] using wordTrace_append hprefix tailTrace_3231549
  have hstable : (prefixWord ++ tailWord_3231549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231549).length < 2 ^ (prefixWord ++ tailWord_3231549).sum := by decide
  have hdescent : baseEnd_3231549 < baseStart_3231549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231577 : List Nat := [1, 2, 1, 2, 2, 3, 11]
def baseStart_3231577 : Nat := 118140960795 + 3231577 * 2 ^ 59
def prefixEnd_3231577 : Nat := 4983230072969 + 3 ^ 40 * 3231577 * 2
def baseEnd_3231577 : Nat := 40971661062089090711747

theorem tailTrace_3231577 : CollatzResearch.WordTrace tailWord_3231577 prefixEnd_3231577 40971661062089090711747 := by
  unfold tailWord_3231577
  simp only [CollatzResearch.WordTrace]
  refine ⟨117865296213555913256956985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78576864142370608837971323 117865296213555913256956985)
  ·
    refine ⟨88398972160166934942717739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117865296213555913256956985 88398972160166934942717739)
    ·
      refine ⟨132598458240250402414076609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88398972160166934942717739 132598458240250402414076609)
      ·
        refine ⟨99448843680187801810557457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132598458240250402414076609 99448843680187801810557457)
        ·
          refine ⟨74586632760140851357918093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99448843680187801810557457 74586632760140851357918093)
          ·
            refine ⟨27969987285052819259219285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74586632760140851357918093 27969987285052819259219285)
            ·
              refine ⟨40971661062089090711747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27969987285052819259219285 40971661062089090711747)
              ·
                rfl

theorem cell22_3231577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 11].length) (baseStart_3231577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231577 prefixEnd_3231577 := by exact prefixLift 3231577
  have htrace : WordTrace (prefixWord ++ tailWord_3231577) baseStart_3231577 baseEnd_3231577 := by
    simpa [prefixWord, tailWord_3231577, baseEnd_3231577] using wordTrace_append hprefix tailTrace_3231577
  have hstable : (prefixWord ++ tailWord_3231577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231577).length < 2 ^ (prefixWord ++ tailWord_3231577).sum := by decide
  have hdescent : baseEnd_3231577 < baseStart_3231577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231598 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3231598 : Nat := 118140960795 + 3231598 * 2 ^ 59
def prefixEnd_3231598 : Nat := 4983230072969 + 3 ^ 40 * 3231598 * 2
def baseEnd_3231598 : Nat := 1106242037405568394442105

theorem tailTrace_3231598 : CollatzResearch.WordTrace tailWord_3231598 prefixEnd_3231598 1106242037405568394442105 := by
  unfold tailWord_3231598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14733257768309979230433931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78577374764319889228980965 14733257768309979230433931)
  ·
    refine ⟨22099886652464968845650897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14733257768309979230433931 22099886652464968845650897)
    ·
      refine ⟨16574914989348726634238173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22099886652464968845650897 16574914989348726634238173)
      ·
        refine ⟨6215593121005772487839315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16574914989348726634238173 6215593121005772487839315)
        ·
          refine ⟨9323389681508658731758973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215593121005772487839315 9323389681508658731758973)
          ·
            refine ⟨3496271130565747024409615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9323389681508658731758973 3496271130565747024409615)
            ·
              refine ⟨5244406695848620536614423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496271130565747024409615 5244406695848620536614423)
              ·
                refine ⟨7866610043772930804921635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5244406695848620536614423 7866610043772930804921635)
                ·
                  refine ⟨11799915065659396207382453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7866610043772930804921635 11799915065659396207382453)
                  ·
                    refine ⟨1106242037405568394442105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11799915065659396207382453 1106242037405568394442105)
                    ·
                      rfl

theorem cell22_3231598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3231598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231598 prefixEnd_3231598 := by exact prefixLift 3231598
  have htrace : WordTrace (prefixWord ++ tailWord_3231598) baseStart_3231598 baseEnd_3231598 := by
    simpa [prefixWord, tailWord_3231598, baseEnd_3231598] using wordTrace_append hprefix tailTrace_3231598
  have hstable : (prefixWord ++ tailWord_3231598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231598).length < 2 ^ (prefixWord ++ tailWord_3231598).sum := by decide
  have hdescent : baseEnd_3231598 < baseStart_3231598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231617 : List Nat := [1, 2, 4, 4, 2, 1, 1, 3, 4]
def baseStart_3231617 : Nat := 118140960795 + 3231617 * 2 ^ 59
def prefixEnd_3231617 : Nat := 4983230072969 + 3 ^ 40 * 3231617 * 2
def baseEnd_3231617 : Nat := 368749513831286226072349

theorem tailTrace_3231617 : CollatzResearch.WordTrace tailWord_3231617 prefixEnd_3231617 368749513831286226072349 := by
  unfold tailWord_3231617
  simp only [CollatzResearch.WordTrace]
  refine ⟨117866755133411000088413105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78577836755607333392275403 117866755133411000088413105)
  ·
    refine ⟨88400066350058250066309829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117866755133411000088413105 88400066350058250066309829)
    ·
      refine ⟨16575012440635921887433093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88400066350058250066309829 16575012440635921887433093)
      ·
        refine ⟨3107814832619235353893705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16575012440635921887433093 3107814832619235353893705)
        ·
          refine ⟨2330861124464426515420279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3107814832619235353893705 2330861124464426515420279)
          ·
            refine ⟨3496291686696639773130419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330861124464426515420279 3496291686696639773130419)
            ·
              refine ⟨5244437530044959659695629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496291686696639773130419 5244437530044959659695629)
              ·
                refine ⟨1966664073766859872385861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5244437530044959659695629 1966664073766859872385861)
                ·
                  refine ⟨368749513831286226072349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1966664073766859872385861 368749513831286226072349)
                  ·
                    rfl

theorem cell22_3231617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 4].length) (baseStart_3231617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231617 prefixEnd_3231617 := by exact prefixLift 3231617
  have htrace : WordTrace (prefixWord ++ tailWord_3231617) baseStart_3231617 baseEnd_3231617 := by
    simpa [prefixWord, tailWord_3231617, baseEnd_3231617] using wordTrace_append hprefix tailTrace_3231617
  have hstable : (prefixWord ++ tailWord_3231617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231617).length < 2 ^ (prefixWord ++ tailWord_3231617).sum := by decide
  have hdescent : baseEnd_3231617 < baseStart_3231617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231639 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 7]
def baseStart_3231639 : Nat := 118140960795 + 3231639 * 2 ^ 59
def prefixEnd_3231639 : Nat := 4983230072969 + 3 ^ 40 * 3231639 * 2
def baseEnd_3231639 : Nat := 368752024181152651388993

theorem tailTrace_3231639 : CollatzResearch.WordTrace tailWord_3231639 prefixEnd_3231639 368752024181152651388993 := by
  unfold tailWord_3231639
  simp only [CollatzResearch.WordTrace]
  refine ⟨117867557539331297845713971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78578371692887531897142647 117867557539331297845713971)
  ·
    refine ⟨176801336308996946768570957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117867557539331297845713971 176801336308996946768570957)
    ·
      refine ⟨66300501115873855038214109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176801336308996946768570957 66300501115873855038214109)
      ·
        refine ⟨24862687918452695639330291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66300501115873855038214109 24862687918452695639330291)
        ·
          refine ⟨37294031877679043458995437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24862687918452695639330291 37294031877679043458995437)
          ·
            refine ⟨13985261954129641297123289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37294031877679043458995437 13985261954129641297123289)
            ·
              refine ⟨10488946465597230972842467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13985261954129641297123289 10488946465597230972842467)
              ·
                refine ⟨15733419698395846459263701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10488946465597230972842467 15733419698395846459263701)
                ·
                  refine ⟨368752024181152651388993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15733419698395846459263701 368752024181152651388993)
                  ·
                    rfl

theorem cell22_3231639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 7].length) (baseStart_3231639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231639 prefixEnd_3231639 := by exact prefixLift 3231639
  have htrace : WordTrace (prefixWord ++ tailWord_3231639) baseStart_3231639 baseEnd_3231639 := by
    simpa [prefixWord, tailWord_3231639, baseEnd_3231639] using wordTrace_append hprefix tailTrace_3231639
  have hstable : (prefixWord ++ tailWord_3231639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231639).length < 2 ^ (prefixWord ++ tailWord_3231639).sum := by decide
  have hdescent : baseEnd_3231639 < baseStart_3231639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231716 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_3231716 : Nat := 118140960795 + 3231716 * 2 ^ 59
def prefixEnd_3231716 : Nat := 4983230072969 + 3 ^ 40 * 3231716 * 2
def baseEnd_3231716 : Nat := 1106282431217055419991743

theorem tailTrace_3231716 : CollatzResearch.WordTrace tailWord_3231716 prefixEnd_3231716 1106282431217055419991743 := by
  unfold tailWord_3231716
  simp only [CollatzResearch.WordTrace]
  refine ⟨58935182980026169998133501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78580243973368226664178001 58935182980026169998133501)
  ·
    refine ⟨22100693617509813749300063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58935182980026169998133501 22100693617509813749300063)
    ·
      refine ⟨33151040426264720623950095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22100693617509813749300063 33151040426264720623950095)
      ·
        refine ⟨49726560639397080935925143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33151040426264720623950095 49726560639397080935925143)
        ·
          refine ⟨74589840959095621403887715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49726560639397080935925143 74589840959095621403887715)
          ·
            refine ⟨111884761438643432105831573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74589840959095621403887715 111884761438643432105831573)
            ·
              refine ⟨5244598192436410879960855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111884761438643432105831573 5244598192436410879960855)
              ·
                refine ⟨7866897288654616319941283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5244598192436410879960855 7866897288654616319941283)
                ·
                  refine ⟨11800345932981924479911925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7866897288654616319941283 11800345932981924479911925)
                  ·
                    refine ⟨1106282431217055419991743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11800345932981924479911925 1106282431217055419991743)
                    ·
                      rfl

theorem cell22_3231716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_3231716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231716 prefixEnd_3231716 := by exact prefixLift 3231716
  have htrace : WordTrace (prefixWord ++ tailWord_3231716) baseStart_3231716 baseEnd_3231716 := by
    simpa [prefixWord, tailWord_3231716, baseEnd_3231716] using wordTrace_append hprefix tailTrace_3231716
  have hstable : (prefixWord ++ tailWord_3231716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231716).length < 2 ^ (prefixWord ++ tailWord_3231716).sum := by decide
  have hdescent : baseEnd_3231716 < baseStart_3231716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231767 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 2, 3]
def baseStart_3231767 : Nat := 118140960795 + 3231767 * 2 ^ 59
def prefixEnd_3231767 : Nat := 4983230072969 + 3 ^ 40 * 3231767 * 2
def baseEnd_3231767 : Nat := 1106299889559308286966587

theorem tailTrace_3231767 : CollatzResearch.WordTrace tailWord_3231767 prefixEnd_3231767 1106299889559308286966587 := by
  unfold tailWord_3231767
  simp only [CollatzResearch.WordTrace]
  refine ⟨117872226082867575706373555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78581484055245050470915703 117872226082867575706373555)
  ·
    refine ⟨176808339124301363559560333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117872226082867575706373555 176808339124301363559560333)
    ·
      refine ⟨66303127171613011334835125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176808339124301363559560333 66303127171613011334835125)
      ·
        refine ⟨6215918172338719812640793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66303127171613011334835125 6215918172338719812640793)
        ·
          refine ⟨4661938629254039859480595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6215918172338719812640793 4661938629254039859480595)
          ·
            refine ⟨6992907943881059789220893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4661938629254039859480595 6992907943881059789220893)
            ·
              refine ⟨2622340478955397420957835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6992907943881059789220893 2622340478955397420957835)
              ·
                refine ⟨3933510718433096131436753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622340478955397420957835 3933510718433096131436753)
                ·
                  refine ⟨2950133038824822098577565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3933510718433096131436753 2950133038824822098577565)
                  ·
                    refine ⟨1106299889559308286966587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950133038824822098577565 1106299889559308286966587)
                    ·
                      rfl

theorem cell22_3231767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_3231767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231767 prefixEnd_3231767 := by exact prefixLift 3231767
  have htrace : WordTrace (prefixWord ++ tailWord_3231767) baseStart_3231767 baseEnd_3231767 := by
    simpa [prefixWord, tailWord_3231767, baseEnd_3231767] using wordTrace_append hprefix tailTrace_3231767
  have hstable : (prefixWord ++ tailWord_3231767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231767).length < 2 ^ (prefixWord ++ tailWord_3231767).sum := by decide
  have hdescent : baseEnd_3231767 < baseStart_3231767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231778 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_3231778 : Nat := 118140960795 + 3231778 * 2 ^ 59
def prefixEnd_3231778 : Nat := 4983230072969 + 3 ^ 40 * 3231778 * 2
def baseEnd_3231778 : Nat := 1106303655084107924941553

theorem tailTrace_3231778 : CollatzResearch.WordTrace tailWord_3231778 prefixEnd_3231778 1106303655084107924941553 := by
  unfold tailWord_3231778
  simp only [CollatzResearch.WordTrace]
  refine ⟨29468156821456931146255997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78581751523885149723349325 29468156821456931146255997)
  ·
    refine ⟨11050558808046349179845999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29468156821456931146255997 11050558808046349179845999)
    ·
      refine ⟨16575838212069523769768999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11050558808046349179845999 16575838212069523769768999)
      ·
        refine ⟨24863757318104285654653499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16575838212069523769768999 24863757318104285654653499)
        ·
          refine ⟨37295635977156428481980249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24863757318104285654653499 37295635977156428481980249)
          ·
            refine ⟨27971726982867321361485187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37295635977156428481980249 27971726982867321361485187)
            ·
              refine ⟨41957590474300982042227781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27971726982867321361485187 41957590474300982042227781)
              ·
                refine ⟨7867048213931434132917709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41957590474300982042227781 7867048213931434132917709)
                ·
                  refine ⟨2950143080224287799844141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7867048213931434132917709 2950143080224287799844141)
                  ·
                    refine ⟨1106303655084107924941553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950143080224287799844141 1106303655084107924941553)
                    ·
                      rfl

theorem cell22_3231778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_3231778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231778 prefixEnd_3231778 := by exact prefixLift 3231778
  have htrace : WordTrace (prefixWord ++ tailWord_3231778) baseStart_3231778 baseEnd_3231778 := by
    simpa [prefixWord, tailWord_3231778, baseEnd_3231778] using wordTrace_append hprefix tailTrace_3231778
  have hstable : (prefixWord ++ tailWord_3231778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231778).length < 2 ^ (prefixWord ++ tailWord_3231778).sum := by decide
  have hdescent : baseEnd_3231778 < baseStart_3231778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231780 : List Nat := [2, 3, 1, 4, 2, 2, 2, 6]
def baseStart_3231780 : Nat := 118140960795 + 3231780 * 2 ^ 59
def prefixEnd_3231780 : Nat := 4983230072969 + 3 ^ 40 * 3231780 * 2
def baseEnd_3231780 : Nat := 122922704413886731821283

theorem tailTrace_3231780 : CollatzResearch.WordTrace tailWord_3231780 prefixEnd_3231780 122922704413886731821283 := by
  unfold tailWord_3231780
  simp only [CollatzResearch.WordTrace]
  refine ⟨58936350115910239463298397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78581800154546985951064529 58936350115910239463298397)
  ·
    refine ⟨22101131293466339798736899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58936350115910239463298397 22101131293466339798736899)
    ·
      refine ⟨33151696940199509698105349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22101131293466339798736899 33151696940199509698105349)
      ·
        refine ⟨6215943176287408068394753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33151696940199509698105349 6215943176287408068394753)
        ·
          refine ⟨4661957382215556051296065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6215943176287408068394753 4661957382215556051296065)
          ·
            refine ⟨3496468036661667038472049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4661957382215556051296065 3496468036661667038472049)
            ·
              refine ⟨2622351027496250278854037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3496468036661667038472049 2622351027496250278854037)
              ·
                refine ⟨122922704413886731821283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2622351027496250278854037 122922704413886731821283)
                ·
                  rfl

theorem cell22_3231780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 6].length) (baseStart_3231780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231780 prefixEnd_3231780 := by exact prefixLift 3231780
  have htrace : WordTrace (prefixWord ++ tailWord_3231780) baseStart_3231780 baseEnd_3231780 := by
    simpa [prefixWord, tailWord_3231780, baseEnd_3231780] using wordTrace_append hprefix tailTrace_3231780
  have hstable : (prefixWord ++ tailWord_3231780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231780).length < 2 ^ (prefixWord ++ tailWord_3231780).sum := by decide
  have hdescent : baseEnd_3231780 < baseStart_3231780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231795 : List Nat := [1, 1, 1, 2, 4, 1, 5, 3, 1, 3]
def baseStart_3231795 : Nat := 118140960795 + 3231795 * 2 ^ 59
def prefixEnd_3231795 : Nat := 4983230072969 + 3 ^ 40 * 3231795 * 2
def baseEnd_3231795 : Nat := 1106309474531525547266501

theorem tailTrace_3231795 : CollatzResearch.WordTrace tailWord_3231795 prefixEnd_3231795 1106309474531525547266501 := by
  unfold tailWord_3231795
  simp only [CollatzResearch.WordTrace]
  refine ⟨117873247326766136488392839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78582164884510757658928559 117873247326766136488392839)
  ·
    refine ⟨176809870990149204732589259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117873247326766136488392839 176809870990149204732589259)
    ·
      refine ⟨265214806485223807098883889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176809870990149204732589259 265214806485223807098883889)
      ·
        refine ⟨198911104863917855324162917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265214806485223807098883889 198911104863917855324162917)
        ·
          refine ⟨37295832161984597873280547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198911104863917855324162917 37295832161984597873280547)
          ·
            refine ⟨55943748242976896809920821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37295832161984597873280547 55943748242976896809920821)
            ·
              refine ⟨5244726397779084075930077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55943748242976896809920821 5244726397779084075930077)
              ·
                refine ⟨1966772399167156528473779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5244726397779084075930077 1966772399167156528473779)
                ·
                  refine ⟨2950158598750734792710669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966772399167156528473779 2950158598750734792710669)
                  ·
                    refine ⟨1106309474531525547266501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950158598750734792710669 1106309474531525547266501)
                    ·
                      rfl

theorem cell22_3231795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 3].length) (baseStart_3231795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231795 prefixEnd_3231795 := by exact prefixLift 3231795
  have htrace : WordTrace (prefixWord ++ tailWord_3231795) baseStart_3231795 baseEnd_3231795 := by
    simpa [prefixWord, tailWord_3231795, baseEnd_3231795] using wordTrace_append hprefix tailTrace_3231795
  have hstable : (prefixWord ++ tailWord_3231795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231795).length < 2 ^ (prefixWord ++ tailWord_3231795).sum := by decide
  have hdescent : baseEnd_3231795 < baseStart_3231795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231855 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 1, 4]
def baseStart_3231855 : Nat := 118140960795 + 3231855 * 2 ^ 59
def prefixEnd_3231855 : Nat := 4983230072969 + 3 ^ 40 * 3231855 * 2
def baseEnd_3231855 : Nat := 1106330013757705390766317

theorem tailTrace_3231855 : CollatzResearch.WordTrace tailWord_3231855 prefixEnd_3231855 1106330013757705390766317 := by
  unfold tailWord_3231855
  simp only [CollatzResearch.WordTrace]
  refine ⟨117875435706548766735577019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78583623804365844490384679 117875435706548766735577019)
  ·
    refine ⟨176813153559823150103365529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117875435706548766735577019 176813153559823150103365529)
    ·
      refine ⟨132609865169867362577524147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176813153559823150103365529 132609865169867362577524147)
      ·
        refine ⟨198914797754801043866286221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132609865169867362577524147 198914797754801043866286221)
        ·
          refine ⟨74593049158050391449857333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198914797754801043866286221 74593049158050391449857333)
          ·
            refine ⟨6993098358567224198424125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74593049158050391449857333 6993098358567224198424125)
            ·
              refine ⟨2622411884462709074409047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6993098358567224198424125 2622411884462709074409047)
              ·
                refine ⟨3933617826694063611613571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622411884462709074409047 3933617826694063611613571)
                ·
                  refine ⟨5900426740041095417420357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933617826694063611613571 5900426740041095417420357)
                  ·
                    refine ⟨1106330013757705390766317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5900426740041095417420357 1106330013757705390766317)
                    ·
                      rfl

theorem cell22_3231855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 4].length) (baseStart_3231855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231855 prefixEnd_3231855 := by exact prefixLift 3231855
  have htrace : WordTrace (prefixWord ++ tailWord_3231855) baseStart_3231855 baseEnd_3231855 := by
    simpa [prefixWord, tailWord_3231855, baseEnd_3231855] using wordTrace_append hprefix tailTrace_3231855
  have hstable : (prefixWord ++ tailWord_3231855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231855).length < 2 ^ (prefixWord ++ tailWord_3231855).sum := by decide
  have hdescent : baseEnd_3231855 < baseStart_3231855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231981 : List Nat := [1, 5, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_3231981 : Nat := 118140960795 + 3231981 * 2 ^ 59
def prefixEnd_3231981 : Nat := 4983230072969 + 3 ^ 40 * 3231981 * 2
def baseEnd_3231981 : Nat := 1106373146132683062115931

theorem tailTrace_3231981 : CollatzResearch.WordTrace tailWord_3231981 prefixEnd_3231981 1106373146132683062115931 := by
  unfold tailWord_3231981
  simp only [CollatzResearch.WordTrace]
  refine ⟨117880031304092290254663797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78586687536061526836442531 117880031304092290254663797)
  ·
    refine ⟨11051252934758652211374731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117880031304092290254663797 11051252934758652211374731)
    ·
      refine ⟨16576879402137978317062097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11051252934758652211374731 16576879402137978317062097)
      ·
        refine ⟨12432659551603483737796573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16576879402137978317062097 12432659551603483737796573)
        ·
          refine ⟨4662247331851306401673715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12432659551603483737796573 4662247331851306401673715)
          ·
            refine ⟨6993370997776959602510573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662247331851306401673715 6993370997776959602510573)
            ·
              refine ⟨2622514124166359850941465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6993370997776959602510573 2622514124166359850941465)
              ·
                refine ⟨1966885593124769888206099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622514124166359850941465 1966885593124769888206099)
                ·
                  refine ⟨2950328389687154832309149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966885593124769888206099 2950328389687154832309149)
                  ·
                    refine ⟨1106373146132683062115931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950328389687154832309149 1106373146132683062115931)
                    ·
                      rfl

theorem cell22_3231981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_3231981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3231981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3231981 prefixEnd_3231981 := by exact prefixLift 3231981
  have htrace : WordTrace (prefixWord ++ tailWord_3231981) baseStart_3231981 baseEnd_3231981 := by
    simpa [prefixWord, tailWord_3231981, baseEnd_3231981] using wordTrace_append hprefix tailTrace_3231981
  have hstable : (prefixWord ++ tailWord_3231981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231981).length < 2 ^ (prefixWord ++ tailWord_3231981).sum := by decide
  have hdescent : baseEnd_3231981 < baseStart_3231981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232003 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 1, 5]
def baseStart_3232003 : Nat := 118140960795 + 3232003 * 2 ^ 59
def prefixEnd_3232003 : Nat := 4983230072969 + 3 ^ 40 * 3232003 * 2
def baseEnd_3232003 : Nat := 1106380677182282338065863

theorem tailTrace_3232003 : CollatzResearch.WordTrace tailWord_3232003 prefixEnd_3232003 1106380677182282338065863 := by
  unfold tailWord_3232003
  simp only [CollatzResearch.WordTrace]
  refine ⟨117880833710012588011964663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78587222473341725341309775 117880833710012588011964663)
  ·
    refine ⟨176821250565018882017946995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117880833710012588011964663 176821250565018882017946995)
    ·
      refine ⟨265231875847528323026920493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176821250565018882017946995 265231875847528323026920493)
      ·
        refine ⟨99461953442823121135095185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265231875847528323026920493 99461953442823121135095185)
        ·
          refine ⟨74596465082117340851321389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99461953442823121135095185 74596465082117340851321389)
          ·
            refine ⟨27973674405794002819245521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74596465082117340851321389 27973674405794002819245521)
            ·
              refine ⟨20980255804345502114434141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27973674405794002819245521 20980255804345502114434141)
              ·
                refine ⟨7867595926629563292912803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20980255804345502114434141 7867595926629563292912803)
                ·
                  refine ⟨11801393889944344939369205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7867595926629563292912803 11801393889944344939369205)
                  ·
                    refine ⟨1106380677182282338065863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11801393889944344939369205 1106380677182282338065863)
                    ·
                      rfl

theorem cell22_3232003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 5].length) (baseStart_3232003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232003 prefixEnd_3232003 := by exact prefixLift 3232003
  have htrace : WordTrace (prefixWord ++ tailWord_3232003) baseStart_3232003 baseEnd_3232003 := by
    simpa [prefixWord, tailWord_3232003, baseEnd_3232003] using wordTrace_append hprefix tailTrace_3232003
  have hstable : (prefixWord ++ tailWord_3232003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232003).length < 2 ^ (prefixWord ++ tailWord_3232003).sum := by decide
  have hdescent : baseEnd_3232003 < baseStart_3232003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232007 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 3, 4]
def baseStart_3232007 : Nat := 118140960795 + 3232007 * 2 ^ 59
def prefixEnd_3232007 : Nat := 4983230072969 + 3 ^ 40 * 3232007 * 2
def baseEnd_3232007 : Nat := 1106382046464027660965851

theorem tailTrace_3232007 : CollatzResearch.WordTrace tailWord_3232007 prefixEnd_3232007 1106382046464027660965851 := by
  unfold tailWord_3232007
  simp only [CollatzResearch.WordTrace]
  refine ⟨117880979601998096695110275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78587319734665397796740183 117880979601998096695110275)
  ·
    refine ⟨176821469402997145042665413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117880979601998096695110275 176821469402997145042665413)
    ·
      refine ⟨33154025513061964695499765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176821469402997145042665413 33154025513061964695499765)
      ·
        refine ⟨3108189891849559190203103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33154025513061964695499765 3108189891849559190203103)
        ·
          refine ⟨4662284837774338785304655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108189891849559190203103 4662284837774338785304655)
          ·
            refine ⟨6993427256661508177956983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662284837774338785304655 6993427256661508177956983)
            ·
              refine ⟨10490140884992262266935475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993427256661508177956983 10490140884992262266935475)
              ·
                refine ⟨15735211327488393400403213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10490140884992262266935475 15735211327488393400403213)
                ·
                  refine ⟨5900704247808147525151205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15735211327488393400403213 5900704247808147525151205)
                  ·
                    refine ⟨1106382046464027660965851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5900704247808147525151205 1106382046464027660965851)
                    ·
                      rfl

theorem cell22_3232007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_3232007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232007 prefixEnd_3232007 := by exact prefixLift 3232007
  have htrace : WordTrace (prefixWord ++ tailWord_3232007) baseStart_3232007 baseEnd_3232007 := by
    simpa [prefixWord, tailWord_3232007, baseEnd_3232007] using wordTrace_append hprefix tailTrace_3232007
  have hstable : (prefixWord ++ tailWord_3232007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232007).length < 2 ^ (prefixWord ++ tailWord_3232007).sum := by decide
  have hdescent : baseEnd_3232007 < baseStart_3232007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232063 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 2, 6]
def baseStart_3232063 : Nat := 118140960795 + 3232063 * 2 ^ 59
def prefixEnd_3232063 : Nat := 4983230072969 + 3 ^ 40 * 3232063 * 2
def baseEnd_3232063 : Nat := 1106401216408462181565679

theorem tailTrace_3232063 : CollatzResearch.WordTrace tailWord_3232063 prefixEnd_3232063 1106401216408462181565679 := by
  unfold tailWord_3232063
  simp only [CollatzResearch.WordTrace]
  refine ⟨117883022089795218259148843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78588681393196812172765895 117883022089795218259148843)
  ·
    refine ⟨176824533134692827388723265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117883022089795218259148843 176824533134692827388723265)
    ·
      refine ⟨132618399851019620541542449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176824533134692827388723265 132618399851019620541542449)
      ·
        refine ⟨99463799888264715406156837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132618399851019620541542449 99463799888264715406156837)
        ·
          refine ⟨18649462479049634138654407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99463799888264715406156837 18649462479049634138654407)
          ·
            refine ⟨27974193718574451207981611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18649462479049634138654407 27974193718574451207981611)
            ·
              refine ⟨41961290577861676811972417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27974193718574451207981611 41961290577861676811972417)
              ·
                refine ⟨31470967933396257608979313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41961290577861676811972417 31470967933396257608979313)
                ·
                  refine ⟨23603225950047193206734485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31470967933396257608979313 23603225950047193206734485)
                  ·
                    refine ⟨1106401216408462181565679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23603225950047193206734485 1106401216408462181565679)
                    ·
                      rfl

theorem cell22_3232063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_3232063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232063 prefixEnd_3232063 := by exact prefixLift 3232063
  have htrace : WordTrace (prefixWord ++ tailWord_3232063) baseStart_3232063 baseEnd_3232063 := by
    simpa [prefixWord, tailWord_3232063, baseEnd_3232063] using wordTrace_append hprefix tailTrace_3232063
  have hstable : (prefixWord ++ tailWord_3232063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232063).length < 2 ^ (prefixWord ++ tailWord_3232063).sum := by decide
  have hdescent : baseEnd_3232063 < baseStart_3232063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232095 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 5]
def baseStart_3232095 : Nat := 118140960795 + 3232095 * 2 ^ 59
def prefixEnd_3232095 : Nat := 4983230072969 + 3 ^ 40 * 3232095 * 2
def baseEnd_3232095 : Nat := 368804056887474921588527

theorem tailTrace_3232095 : CollatzResearch.WordTrace tailWord_3232095 prefixEnd_3232095 368804056887474921588527 := by
  unfold tailWord_3232095
  simp only [CollatzResearch.WordTrace]
  refine ⟨117884189225679287724313739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78589459483786191816209159 117884189225679287724313739)
  ·
    refine ⟨176826283838518931586470609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117884189225679287724313739 176826283838518931586470609)
    ·
      refine ⟨132619712878889198689852957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176826283838518931586470609 132619712878889198689852957)
      ·
        refine ⟨49732392329583449508694859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132619712878889198689852957 49732392329583449508694859)
        ·
          refine ⟨74598588494375174263042289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49732392329583449508694859 74598588494375174263042289)
          ·
            refine ⟨55948941370781380697281717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74598588494375174263042289 55948941370781380697281717)
            ·
              refine ⟨5245213253510754440370161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55948941370781380697281717 5245213253510754440370161)
              ·
                refine ⟨3933909940133065830277621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245213253510754440370161 3933909940133065830277621)
                ·
                  refine ⟨368804056887474921588527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3933909940133065830277621 368804056887474921588527)
                  ·
                    rfl

theorem cell22_3232095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 5].length) (baseStart_3232095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232095 prefixEnd_3232095 := by exact prefixLift 3232095
  have htrace : WordTrace (prefixWord ++ tailWord_3232095) baseStart_3232095 baseEnd_3232095 := by
    simpa [prefixWord, tailWord_3232095, baseEnd_3232095] using wordTrace_append hprefix tailTrace_3232095
  have hstable : (prefixWord ++ tailWord_3232095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232095).length < 2 ^ (prefixWord ++ tailWord_3232095).sum := by decide
  have hdescent : baseEnd_3232095 < baseStart_3232095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232112 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 5]
def baseStart_3232112 : Nat := 118140960795 + 3232112 * 2 ^ 59
def prefixEnd_3232112 : Nat := 4983230072969 + 3 ^ 40 * 3232112 * 2
def baseEnd_3232112 : Nat := 368805996703280795696843

theorem tailTrace_3232112 : CollatzResearch.WordTrace tailWord_3232112 prefixEnd_3232112 368805996703280795696843 := by
  unfold tailWord_3232112
  simp only [CollatzResearch.WordTrace]
  refine ⟨58942404633308849813841295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78589872844411799751788393 58942404633308849813841295)
  ·
    refine ⟨88413606949963274720761943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58942404633308849813841295 88413606949963274720761943)
    ·
      refine ⟨132620410424944912081142915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88413606949963274720761943 132620410424944912081142915)
      ·
        refine ⟨198930615637417368121714373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132620410424944912081142915 198930615637417368121714373)
        ·
          refine ⟨37299490432015756522821445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198930615637417368121714373 37299490432015756522821445)
          ·
            refine ⟨6993654456002954348029021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37299490432015756522821445 6993654456002954348029021)
            ·
              refine ⟨2622620421001107880510883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6993654456002954348029021 2622620421001107880510883)
              ·
                refine ⟨3933930631501661820766325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622620421001107880510883 3933930631501661820766325)
                ·
                  refine ⟨368805996703280795696843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3933930631501661820766325 368805996703280795696843)
                  ·
                    rfl

theorem cell22_3232112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 5].length) (baseStart_3232112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232112 prefixEnd_3232112 := by exact prefixLift 3232112
  have htrace : WordTrace (prefixWord ++ tailWord_3232112) baseStart_3232112 baseEnd_3232112 := by
    simpa [prefixWord, tailWord_3232112, baseEnd_3232112] using wordTrace_append hprefix tailTrace_3232112
  have hstable : (prefixWord ++ tailWord_3232112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232112).length < 2 ^ (prefixWord ++ tailWord_3232112).sum := by decide
  have hdescent : baseEnd_3232112 < baseStart_3232112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232150 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3232150 : Nat := 118140960795 + 3232150 * 2 ^ 59
def prefixEnd_3232150 : Nat := 4983230072969 + 3 ^ 40 * 3232150 * 2
def baseEnd_3232150 : Nat := 1106430998286422954640413

theorem tailTrace_3232150 : CollatzResearch.WordTrace tailWord_3232150 prefixEnd_3232150 1106430998286422954640413 := by
  unfold tailWord_3232150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7367887202530002007347869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78590796826986688078377269 7367887202530002007347869)
  ·
    refine ⟨2762957700948750752755451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7367887202530002007347869 2762957700948750752755451)
    ·
      refine ⟨4144436551423126129133177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2762957700948750752755451 4144436551423126129133177)
      ·
        refine ⟨3108327413567344596849883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4144436551423126129133177 3108327413567344596849883)
        ·
          refine ⟨4662491120351016895274825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108327413567344596849883 4662491120351016895274825)
          ·
            refine ⟨3496868340263262671456119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4662491120351016895274825 3496868340263262671456119)
            ·
              refine ⟨5245302510394894007184179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496868340263262671456119 5245302510394894007184179)
              ·
                refine ⟨7867953765592341010776269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5245302510394894007184179 7867953765592341010776269)
                ·
                  refine ⟨2950482662097127879041101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7867953765592341010776269 2950482662097127879041101)
                  ·
                    refine ⟨1106430998286422954640413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950482662097127879041101 1106430998286422954640413)
                    ·
                      rfl

theorem cell22_3232150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3232150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232150 prefixEnd_3232150 := by exact prefixLift 3232150
  have htrace : WordTrace (prefixWord ++ tailWord_3232150) baseStart_3232150 baseEnd_3232150 := by
    simpa [prefixWord, tailWord_3232150, baseEnd_3232150] using wordTrace_append hprefix tailTrace_3232150
  have hstable : (prefixWord ++ tailWord_3232150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232150).length < 2 ^ (prefixWord ++ tailWord_3232150).sum := by decide
  have hdescent : baseEnd_3232150 < baseStart_3232150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232185 : List Nat := [1, 2, 1, 4, 3, 1, 2, 8]
def baseStart_3232185 : Nat := 118140960795 + 3232185 * 2 ^ 59
def prefixEnd_3232185 : Nat := 4983230072969 + 3 ^ 40 * 3232185 * 2
def baseEnd_3232185 : Nat := 122938108833521614446145

theorem tailTrace_3232185 : CollatzResearch.WordTrace tailWord_3232185 prefixEnd_3232185 122938108833521614446145 := by
  unfold tailWord_3232185
  simp only [CollatzResearch.WordTrace]
  refine ⟨117887471795353233095090009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78591647863568822063393339 117887471795353233095090009)
  ·
    refine ⟨88415603846514924821317507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117887471795353233095090009 88415603846514924821317507)
    ·
      refine ⟨132623405769772387231976261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88415603846514924821317507 132623405769772387231976261)
      ·
        refine ⟨24866888581832322605995549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132623405769772387231976261 24866888581832322605995549)
        ·
          refine ⟨9325083218187120977248331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24866888581832322605995549 9325083218187120977248331)
          ·
            refine ⟨13987624827280681465872497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9325083218187120977248331 13987624827280681465872497)
            ·
              refine ⟨10490718620460511099404373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13987624827280681465872497 10490718620460511099404373)
              ·
                refine ⟨122938108833521614446145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10490718620460511099404373 122938108833521614446145)
                ·
                  rfl

theorem cell22_3232185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 8].length) (baseStart_3232185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232185 prefixEnd_3232185 := by exact prefixLift 3232185
  have htrace : WordTrace (prefixWord ++ tailWord_3232185) baseStart_3232185 baseEnd_3232185 := by
    simpa [prefixWord, tailWord_3232185, baseEnd_3232185] using wordTrace_append hprefix tailTrace_3232185
  have hstable : (prefixWord ++ tailWord_3232185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232185).length < 2 ^ (prefixWord ++ tailWord_3232185).sum := by decide
  have hdescent : baseEnd_3232185 < baseStart_3232185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232217 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 3, 3]
def baseStart_3232217 : Nat := 118140960795 + 3232217 * 2 ^ 59
def prefixEnd_3232217 : Nat := 4983230072969 + 3 ^ 40 * 3232217 * 2
def baseEnd_3232217 : Nat := 1106453933755657113215207

theorem tailTrace_3232217 : CollatzResearch.WordTrace tailWord_3232217 prefixEnd_3232217 1106453933755657113215207 := by
  unfold tailWord_3232217
  simp only [CollatzResearch.WordTrace]
  refine ⟨117888638931237302560254905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78592425954158201706836603 117888638931237302560254905)
  ·
    refine ⟨88416479198427976920191179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117888638931237302560254905 88416479198427976920191179)
    ·
      refine ⟨132624718797641965380286769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88416479198427976920191179 132624718797641965380286769)
      ·
        refine ⟨99468539098231474035215077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132624718797641965380286769 99468539098231474035215077)
        ·
          refine ⟨18650351080918401381602827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99468539098231474035215077 18650351080918401381602827)
          ·
            refine ⟨27975526621377602072404241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18650351080918401381602827 27975526621377602072404241)
            ·
              refine ⟨20981644966033201554303181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27975526621377602072404241 20981644966033201554303181)
              ·
                refine ⟨7868116862262450582863693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20981644966033201554303181 7868116862262450582863693)
                ·
                  refine ⟨2950543823348418968573885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7868116862262450582863693 2950543823348418968573885)
                  ·
                    refine ⟨1106453933755657113215207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950543823348418968573885 1106453933755657113215207)
                    ·
                      rfl

theorem cell22_3232217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_3232217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232217 prefixEnd_3232217 := by exact prefixLift 3232217
  have htrace : WordTrace (prefixWord ++ tailWord_3232217) baseStart_3232217 baseEnd_3232217 := by
    simpa [prefixWord, tailWord_3232217, baseEnd_3232217] using wordTrace_append hprefix tailTrace_3232217
  have hstable : (prefixWord ++ tailWord_3232217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232217).length < 2 ^ (prefixWord ++ tailWord_3232217).sum := by decide
  have hdescent : baseEnd_3232217 < baseStart_3232217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232234 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_3232234 : Nat := 118140960795 + 3232234 * 2 ^ 59
def prefixEnd_3232234 : Nat := 4983230072969 + 3 ^ 40 * 3232234 * 2
def baseEnd_3232234 : Nat := 1106459753203074735540155

theorem tailTrace_3232234 : CollatzResearch.WordTrace tailWord_3232234 prefixEnd_3232234 1106459753203074735540155 := by
  unfold tailWord_3232234
  simp only [CollatzResearch.WordTrace]
  refine ⟨29472314743043928615905939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78592839314783809642415837 29472314743043928615905939)
  ·
    refine ⟨44208472114565892923858909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29472314743043928615905939 44208472114565892923858909)
    ·
      refine ⟨16578177042962209846447091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44208472114565892923858909 16578177042962209846447091)
      ·
        refine ⟨24867265564443314769670637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16578177042962209846447091 24867265564443314769670637)
        ·
          refine ⟨9325224586666243038626489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24867265564443314769670637 9325224586666243038626489)
          ·
            refine ⟨6993918439999682278969867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9325224586666243038626489 6993918439999682278969867)
            ·
              refine ⟨10490877659999523418454801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993918439999682278969867 10490877659999523418454801)
              ·
                refine ⟨7868158244999642563841101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10490877659999523418454801 7868158244999642563841101)
                ·
                  refine ⟨2950559341874865961440413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7868158244999642563841101 2950559341874865961440413)
                  ·
                    refine ⟨1106459753203074735540155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950559341874865961440413 1106459753203074735540155)
                    ·
                      rfl

theorem cell22_3232234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_3232234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232234 prefixEnd_3232234 := by exact prefixLift 3232234
  have htrace : WordTrace (prefixWord ++ tailWord_3232234) baseStart_3232234 baseEnd_3232234 := by
    simpa [prefixWord, tailWord_3232234, baseEnd_3232234] using wordTrace_append hprefix tailTrace_3232234
  have hstable : (prefixWord ++ tailWord_3232234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232234).length < 2 ^ (prefixWord ++ tailWord_3232234).sum := by decide
  have hdescent : baseEnd_3232234 < baseStart_3232234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232307 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 6, 3]
def baseStart_3232307 : Nat := 118140960795 + 3232307 * 2 ^ 59
def prefixEnd_3232307 : Nat := 4983230072969 + 3 ^ 40 * 3232307 * 2
def baseEnd_3232307 : Nat := 1106484742594926878464931

theorem tailTrace_3232307 : CollatzResearch.WordTrace tailWord_3232307 prefixEnd_3232307 1106484742594926878464931 := by
  unfold tailWord_3232307
  simp only [CollatzResearch.WordTrace]
  refine ⟨117891921500911247931031175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78594614333940831954020783 117891921500911247931031175)
  ·
    refine ⟨176837882251366871896546763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117891921500911247931031175 176837882251366871896546763)
    ·
      refine ⟨265256823377050307844820145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176837882251366871896546763 265256823377050307844820145)
      ·
        refine ⟨198942617532787730883615109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265256823377050307844820145 198942617532787730883615109)
        ·
          refine ⟨37301740787397699540677833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198942617532787730883615109 37301740787397699540677833)
          ·
            refine ⟨27976305590548274655508375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37301740787397699540677833 27976305590548274655508375)
            ·
              refine ⟨41964458385822411983262563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27976305590548274655508375 41964458385822411983262563)
              ·
                refine ⟨62946687578733617974893845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41964458385822411983262563 62946687578733617974893845)
                ·
                  refine ⟨2950625980253138342573149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62946687578733617974893845 2950625980253138342573149)
                  ·
                    refine ⟨1106484742594926878464931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950625980253138342573149 1106484742594926878464931)
                    ·
                      rfl

theorem cell22_3232307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 3].length) (baseStart_3232307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232307 prefixEnd_3232307 := by exact prefixLift 3232307
  have htrace : WordTrace (prefixWord ++ tailWord_3232307) baseStart_3232307 baseEnd_3232307 := by
    simpa [prefixWord, tailWord_3232307, baseEnd_3232307] using wordTrace_append hprefix tailTrace_3232307
  have hstable : (prefixWord ++ tailWord_3232307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232307).length < 2 ^ (prefixWord ++ tailWord_3232307).sum := by decide
  have hdescent : baseEnd_3232307 < baseStart_3232307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232320 : List Nat := [2, 1, 1, 2, 2, 2, 12]
def baseStart_3232320 : Nat := 118140960795 + 3232320 * 2 ^ 59
def prefixEnd_3232320 : Nat := 4983230072969 + 3 ^ 40 * 3232320 * 2
def baseEnd_3232320 : Nat := 40981081213355525107033

theorem tailTrace_3232320 : CollatzResearch.WordTrace tailWord_3232320 prefixEnd_3232320 40981081213355525107033 := by
  unfold tailWord_3232320
  simp only [CollatzResearch.WordTrace]
  refine ⟨58946197824932075575627207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78594930433242767434169609 58946197824932075575627207)
  ·
    refine ⟨88419296737398113363440811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58946197824932075575627207 88419296737398113363440811)
    ·
      refine ⟨132628945106097170045161217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88419296737398113363440811 132628945106097170045161217)
      ·
        refine ⟨99471708829572877533870913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132628945106097170045161217 99471708829572877533870913)
        ·
          refine ⟨74603781622179658150403185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99471708829572877533870913 74603781622179658150403185)
          ·
            refine ⟨55952836216634743612802389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74603781622179658150403185 55952836216634743612802389)
            ·
              refine ⟨40981081213355525107033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 55952836216634743612802389 40981081213355525107033)
              ·
                rfl

theorem cell22_3232320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 12].length) (baseStart_3232320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232320 prefixEnd_3232320 := by exact prefixLift 3232320
  have htrace : WordTrace (prefixWord ++ tailWord_3232320) baseStart_3232320 baseEnd_3232320 := by
    simpa [prefixWord, tailWord_3232320, baseEnd_3232320] using wordTrace_append hprefix tailTrace_3232320
  have hstable : (prefixWord ++ tailWord_3232320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232320).length < 2 ^ (prefixWord ++ tailWord_3232320).sum := by decide
  have hdescent : baseEnd_3232320 < baseStart_3232320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232326 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3232326 : Nat := 118140960795 + 3232326 * 2 ^ 59
def prefixEnd_3232326 : Nat := 4983230072969 + 3 ^ 40 * 3232326 * 2
def baseEnd_3232326 : Nat := 368830415561072387413291

theorem tailTrace_3232326 : CollatzResearch.WordTrace tailWord_3232326 prefixEnd_3232326 368830415561072387413291 := by
  unfold tailWord_3232326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3684144202745075442999151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78595076325228276117315221 3684144202745075442999151)
  ·
    refine ⟨5526216304117613164498727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3684144202745075442999151 5526216304117613164498727)
    ·
      refine ⟨8289324456176419746748091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5526216304117613164498727 8289324456176419746748091)
      ·
        refine ⟨12433986684264629620122137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8289324456176419746748091 12433986684264629620122137)
        ·
          refine ⟨9325490013198472215091603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12433986684264629620122137 9325490013198472215091603)
          ·
            refine ⟨13988235019797708322637405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9325490013198472215091603 13988235019797708322637405)
            ·
              refine ⟨5245588132424140620989027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13988235019797708322637405 5245588132424140620989027)
              ·
                refine ⟨7868382198636210931483541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5245588132424140620989027 7868382198636210931483541)
                ·
                  refine ⟨368830415561072387413291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7868382198636210931483541 368830415561072387413291)
                  ·
                    rfl

theorem cell22_3232326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3232326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232326 prefixEnd_3232326 := by exact prefixLift 3232326
  have htrace : WordTrace (prefixWord ++ tailWord_3232326) baseStart_3232326 baseEnd_3232326 := by
    simpa [prefixWord, tailWord_3232326, baseEnd_3232326] using wordTrace_append hprefix tailTrace_3232326
  have hstable : (prefixWord ++ tailWord_3232326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232326).length < 2 ^ (prefixWord ++ tailWord_3232326).sum := by decide
  have hdescent : baseEnd_3232326 < baseStart_3232326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232337 : List Nat := [1, 2, 2, 1, 3, 4, 2, 7]
def baseStart_3232337 : Nat := 118140960795 + 3232337 * 2 ^ 59
def prefixEnd_3232337 : Nat := 4983230072969 + 3 ^ 40 * 3232337 * 2
def baseEnd_3232337 : Nat := 122943890245335200023871

theorem tailTrace_3232337 : CollatzResearch.WordTrace tailWord_3232337 prefixEnd_3232337 122943890245335200023871 := by
  unfold tailWord_3232337
  simp only [CollatzResearch.WordTrace]
  refine ⟨117893015690802563054623265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78595343793868375369748843 117893015690802563054623265)
  ·
    refine ⟨88419761768101922290967449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117893015690802563054623265 88419761768101922290967449)
    ·
      refine ⟨66314821326076441718225587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88419761768101922290967449 66314821326076441718225587)
      ·
        refine ⟨99472231989114662577338381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66314821326076441718225587 99472231989114662577338381)
        ·
          refine ⟨37302086995917998466501893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99472231989114662577338381 37302086995917998466501893)
          ·
            refine ⟨6994141311734624712469105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37302086995917998466501893 6994141311734624712469105)
            ·
              refine ⟨5245605983800968534351829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6994141311734624712469105 5245605983800968534351829)
              ·
                refine ⟨122943890245335200023871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5245605983800968534351829 122943890245335200023871)
                ·
                  rfl

theorem cell22_3232337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 7].length) (baseStart_3232337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232337 prefixEnd_3232337 := by exact prefixLift 3232337
  have htrace : WordTrace (prefixWord ++ tailWord_3232337) baseStart_3232337 baseEnd_3232337 := by
    simpa [prefixWord, tailWord_3232337, baseEnd_3232337] using wordTrace_append hprefix tailTrace_3232337
  have hstable : (prefixWord ++ tailWord_3232337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232337).length < 2 ^ (prefixWord ++ tailWord_3232337).sum := by decide
  have hdescent : baseEnd_3232337 < baseStart_3232337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232341 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 2, 3]
def baseStart_3232341 : Nat := 118140960795 + 3232341 * 2 ^ 59
def prefixEnd_3232341 : Nat := 4983230072969 + 3 ^ 40 * 3232341 * 2
def baseEnd_3232341 : Nat := 1106496381489762123114827

theorem tailTrace_3232341 : CollatzResearch.WordTrace tailWord_3232341 prefixEnd_3232341 1106496381489762123114827 := by
  unfold tailWord_3232341
  simp only [CollatzResearch.WordTrace]
  refine ⟨117893161582788071737768877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78595441055192047825179251 117893161582788071737768877)
  ·
    refine ⟨44209935593545526901663329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117893161582788071737768877 44209935593545526901663329)
    ·
      refine ⟨33157451695159145176247497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44209935593545526901663329 33157451695159145176247497)
      ·
        refine ⟨24868088771369358882185623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33157451695159145176247497 24868088771369358882185623)
        ·
          refine ⟨37302133157054038323278435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24868088771369358882185623 37302133157054038323278435)
          ·
            refine ⟨55953199735581057484917653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37302133157054038323278435 55953199735581057484917653)
            ·
              refine ⟨2622806237605362069605515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55953199735581057484917653 2622806237605362069605515)
              ·
                refine ⟨3934209356408043104408273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622806237605362069605515 3934209356408043104408273)
                ·
                  refine ⟨2950657017306032328306205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3934209356408043104408273 2950657017306032328306205)
                  ·
                    refine ⟨1106496381489762123114827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950657017306032328306205 1106496381489762123114827)
                    ·
                      rfl

theorem cell22_3232341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_3232341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232341 prefixEnd_3232341 := by exact prefixLift 3232341
  have htrace : WordTrace (prefixWord ++ tailWord_3232341) baseStart_3232341 baseEnd_3232341 := by
    simpa [prefixWord, tailWord_3232341, baseEnd_3232341] using wordTrace_append hprefix tailTrace_3232341
  have hstable : (prefixWord ++ tailWord_3232341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232341).length < 2 ^ (prefixWord ++ tailWord_3232341).sum := by decide
  have hdescent : baseEnd_3232341 < baseStart_3232341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232414 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3232414 : Nat := 118140960795 + 3232414 * 2 ^ 59
def prefixEnd_3232414 : Nat := 4983230072969 + 3 ^ 40 * 3232414 * 2
def baseEnd_3232414 : Nat := 1106521370881614266039603

theorem tailTrace_3232414 : CollatzResearch.WordTrace tailWord_3232414 prefixEnd_3232414 1106521370881614266039603 := by
  unfold tailWord_3232414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14736978013940450650647037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78597216074349070136784197 14736978013940450650647037)
  ·
    refine ⟨5526366755227668993992639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14736978013940450650647037 5526366755227668993992639)
    ·
      refine ⟨8289550132841503490988959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5526366755227668993992639 8289550132841503490988959)
      ·
        refine ⟨12434325199262255236483439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8289550132841503490988959 12434325199262255236483439)
        ·
          refine ⟨18651487798893382854725159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12434325199262255236483439 18651487798893382854725159)
          ·
            refine ⟨27977231698340074282087739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18651487798893382854725159 27977231698340074282087739)
            ·
              refine ⟨41965847547510111423131609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27977231698340074282087739 41965847547510111423131609)
              ·
                refine ⟨31474385660632583567348707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41965847547510111423131609 31474385660632583567348707)
                ·
                  refine ⟨47211578490948875351023061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31474385660632583567348707 47211578490948875351023061)
                  ·
                    refine ⟨1106521370881614266039603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47211578490948875351023061 1106521370881614266039603)
                    ·
                      rfl

theorem cell22_3232414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3232414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232414 prefixEnd_3232414 := by exact prefixLift 3232414
  have htrace : WordTrace (prefixWord ++ tailWord_3232414) baseStart_3232414 baseEnd_3232414 := by
    simpa [prefixWord, tailWord_3232414, baseEnd_3232414] using wordTrace_append hprefix tailTrace_3232414
  have hstable : (prefixWord ++ tailWord_3232414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232414).length < 2 ^ (prefixWord ++ tailWord_3232414).sum := by decide
  have hdescent : baseEnd_3232414 < baseStart_3232414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232433 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 5]
def baseStart_3232433 : Nat := 118140960795 + 3232433 * 2 ^ 59
def prefixEnd_3232433 : Nat := 4983230072969 + 3 ^ 40 * 3232433 * 2
def baseEnd_3232433 : Nat := 368842624989968183271515

theorem tailTrace_3232433 : CollatzResearch.WordTrace tailWord_3232433 prefixEnd_3232433 368842624989968183271515 := by
  unfold tailWord_3232433
  simp only [CollatzResearch.WordTrace]
  refine ⟨117896517098454771450117953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78597678065636514300078635 117896517098454771450117953)
  ·
    refine ⟨88422387823841078587588465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117896517098454771450117953 88422387823841078587588465)
    ·
      refine ⟨66316790867880808940691349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88422387823841078587588465 66316790867880808940691349)
      ·
        refine ⟨3108599571931912919094907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66316790867880808940691349 3108599571931912919094907)
        ·
          refine ⟨4662899357897869378642361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108599571931912919094907 4662899357897869378642361)
          ·
            refine ⟨3497174518423402033981771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4662899357897869378642361 3497174518423402033981771)
            ·
              refine ⟨5245761777635103050972657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497174518423402033981771 5245761777635103050972657)
              ·
                refine ⟨3934321333226327288229493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245761777635103050972657 3934321333226327288229493)
                ·
                  refine ⟨368842624989968183271515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3934321333226327288229493 368842624989968183271515)
                  ·
                    rfl

theorem cell22_3232433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_3232433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232433 prefixEnd_3232433 := by exact prefixLift 3232433
  have htrace : WordTrace (prefixWord ++ tailWord_3232433) baseStart_3232433 baseEnd_3232433 := by
    simpa [prefixWord, tailWord_3232433, baseEnd_3232433] using wordTrace_append hprefix tailTrace_3232433
  have hstable : (prefixWord ++ tailWord_3232433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232433).length < 2 ^ (prefixWord ++ tailWord_3232433).sum := by decide
  have hdescent : baseEnd_3232433 < baseStart_3232433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232444 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 6]
def baseStart_3232444 : Nat := 118140960795 + 3232444 * 2 ^ 59
def prefixEnd_3232444 : Nat := 4983230072969 + 3 ^ 40 * 3232444 * 2
def baseEnd_3232444 : Nat := 368843880164901395929837

theorem tailTrace_3232444 : CollatzResearch.WordTrace tailWord_3232444 prefixEnd_3232444 368843880164901395929837 := by
  unfold tailWord_3232444
  simp only [CollatzResearch.WordTrace]
  refine ⟨58948459150707460164384193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78597945534276613552512257 58948459150707460164384193)
  ·
    refine ⟨44211344363030595123288145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58948459150707460164384193 44211344363030595123288145)
    ·
      refine ⟨33158508272272946342466109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44211344363030595123288145 33158508272272946342466109)
      ·
        refine ⟨12434440602102354878424791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33158508272272946342466109 12434440602102354878424791)
        ·
          refine ⟨18651660903153532317637187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12434440602102354878424791 18651660903153532317637187)
          ·
            refine ⟨27977491354730298476455781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18651660903153532317637187 27977491354730298476455781)
            ·
              refine ⟨5245779629011930964335459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27977491354730298476455781 5245779629011930964335459)
              ·
                refine ⟨7868669443517896446503189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5245779629011930964335459 7868669443517896446503189)
                ·
                  refine ⟨368843880164901395929837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7868669443517896446503189 368843880164901395929837)
                  ·
                    rfl

theorem cell22_3232444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_3232444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232444 prefixEnd_3232444 := by exact prefixLift 3232444
  have htrace : WordTrace (prefixWord ++ tailWord_3232444) baseStart_3232444 baseEnd_3232444 := by
    simpa [prefixWord, tailWord_3232444, baseEnd_3232444] using wordTrace_append hprefix tailTrace_3232444
  have hstable : (prefixWord ++ tailWord_3232444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232444).length < 2 ^ (prefixWord ++ tailWord_3232444).sum := by decide
  have hdescent : baseEnd_3232444 < baseStart_3232444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232474 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_3232474 : Nat := 118140960795 + 3232474 * 2 ^ 59
def prefixEnd_3232474 : Nat := 4983230072969 + 3 ^ 40 * 3232474 * 2
def baseEnd_3232474 : Nat := 1106541910107794109539419

theorem tailTrace_3232474 : CollatzResearch.WordTrace tailWord_3232474 prefixEnd_3232474 1106541910107794109539419 := by
  unfold tailWord_3232474
  simp only [CollatzResearch.WordTrace]
  refine ⟨29474503122826558863090119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78598674994204156968240317 29474503122826558863090119)
  ·
    refine ⟨44211754684239838294635179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29474503122826558863090119 44211754684239838294635179)
    ·
      refine ⟨66317632026359757441952769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44211754684239838294635179 66317632026359757441952769)
      ·
        refine ⟨49738224019769818081464577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66317632026359757441952769 49738224019769818081464577)
        ·
          refine ⟨37303668014827363561098433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49738224019769818081464577 37303668014827363561098433)
          ·
            refine ⟨27977751011120522670823825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37303668014827363561098433 27977751011120522670823825)
            ·
              refine ⟨20983313258340392003117869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27977751011120522670823825 20983313258340392003117869)
              ·
                refine ⟨7868742471877647001169201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20983313258340392003117869 7868742471877647001169201)
                ·
                  refine ⟨5901556853908235250876901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7868742471877647001169201 5901556853908235250876901)
                  ·
                    refine ⟨1106541910107794109539419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5901556853908235250876901 1106541910107794109539419)
                    ·
                      rfl

theorem cell22_3232474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_3232474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232474 prefixEnd_3232474 := by exact prefixLift 3232474
  have htrace : WordTrace (prefixWord ++ tailWord_3232474) baseStart_3232474 baseEnd_3232474 := by
    simpa [prefixWord, tailWord_3232474, baseEnd_3232474] using wordTrace_append hprefix tailTrace_3232474
  have hstable : (prefixWord ++ tailWord_3232474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232474).length < 2 ^ (prefixWord ++ tailWord_3232474).sum := by decide
  have hdescent : baseEnd_3232474 < baseStart_3232474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232510 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3232510 : Nat := 118140960795 + 3232510 * 2 ^ 59
def prefixEnd_3232510 : Nat := 4983230072969 + 3 ^ 40 * 3232510 * 2
def baseEnd_3232510 : Nat := 1106554233643502015639309

theorem tailTrace_3232510 : CollatzResearch.WordTrace tailWord_3232510 prefixEnd_3232510 1106554233643502015639309 := by
  unfold tailWord_3232510
  simp only [CollatzResearch.WordTrace]
  refine ⟨14737415689896976700083873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78599550346117209067113989 14737415689896976700083873)
  ·
    refine ⟨11053061767422732525062905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14737415689896976700083873 11053061767422732525062905)
    ·
      refine ⟨8289796325567049393797179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11053061767422732525062905 8289796325567049393797179)
      ·
        refine ⟨12434694488350574090695769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8289796325567049393797179 12434694488350574090695769)
        ·
          refine ⟨9326020866262930568021827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12434694488350574090695769 9326020866262930568021827)
          ·
            refine ⟨13989031299394395852032741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9326020866262930568021827 13989031299394395852032741)
            ·
              refine ⟨2622943368636449222256139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13989031299394395852032741 2622943368636449222256139)
              ·
                refine ⟨3934415052954673833384209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622943368636449222256139 3934415052954673833384209)
                ·
                  refine ⟨2950811289716005375038157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3934415052954673833384209 2950811289716005375038157)
                  ·
                    refine ⟨1106554233643502015639309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950811289716005375038157 1106554233643502015639309)
                    ·
                      rfl

theorem cell22_3232510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3232510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232510 prefixEnd_3232510 := by exact prefixLift 3232510
  have htrace : WordTrace (prefixWord ++ tailWord_3232510) baseStart_3232510 baseEnd_3232510 := by
    simpa [prefixWord, tailWord_3232510, baseEnd_3232510] using wordTrace_append hprefix tailTrace_3232510
  have hstable : (prefixWord ++ tailWord_3232510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232510).length < 2 ^ (prefixWord ++ tailWord_3232510).sum := by decide
  have hdescent : baseEnd_3232510 < baseStart_3232510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232538 : List Nat := [3, 1, 1, 3, 2, 1, 2, 5, 1, 3]
def baseStart_3232538 : Nat := 118140960795 + 3232538 * 2 ^ 59
def prefixEnd_3232538 : Nat := 4983230072969 + 3 ^ 40 * 3232538 * 2
def baseEnd_3232538 : Nat := 1106563818615719275939223

theorem tailTrace_3232538 : CollatzResearch.WordTrace tailWord_3232538 prefixEnd_3232538 1106563818615719275939223 := by
  unfold tailWord_3232538
  simp only [CollatzResearch.WordTrace]
  refine ⟨29475086690768593595672567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78600231175382916255126845 29475086690768593595672567)
  ·
    refine ⟨44212630036152890393508851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29475086690768593595672567 44212630036152890393508851)
    ·
      refine ⟨66318945054229335590263277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44212630036152890393508851 66318945054229335590263277)
      ·
        refine ⟨24869604395336000846348729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66318945054229335590263277 24869604395336000846348729)
        ·
          refine ⟨18652203296502000634761547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24869604395336000846348729 18652203296502000634761547)
          ·
            refine ⟨27978304944753000952142321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18652203296502000634761547 27978304944753000952142321)
            ·
              refine ⟨20983728708564750714106741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27978304944753000952142321 20983728708564750714106741)
              ·
                refine ⟨1967224566427945379447507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20983728708564750714106741 1967224566427945379447507)
                ·
                  refine ⟨2950836849641918069171261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967224566427945379447507 2950836849641918069171261)
                  ·
                    refine ⟨1106563818615719275939223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950836849641918069171261 1106563818615719275939223)
                    ·
                      rfl

theorem cell22_3232538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_3232538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232538 prefixEnd_3232538 := by exact prefixLift 3232538
  have htrace : WordTrace (prefixWord ++ tailWord_3232538) baseStart_3232538 baseEnd_3232538 := by
    simpa [prefixWord, tailWord_3232538, baseEnd_3232538] using wordTrace_append hprefix tailTrace_3232538
  have hstable : (prefixWord ++ tailWord_3232538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232538).length < 2 ^ (prefixWord ++ tailWord_3232538).sum := by decide
  have hdescent : baseEnd_3232538 < baseStart_3232538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232549 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_3232549 : Nat := 118140960795 + 3232549 * 2 ^ 59
def prefixEnd_3232549 : Nat := 4983230072969 + 3 ^ 40 * 3232549 * 2
def baseEnd_3232549 : Nat := 1106567584140518913914189

theorem tailTrace_3232549 : CollatzResearch.WordTrace tailWord_3232549 prefixEnd_3232549 1106567584140518913914189 := by
  unfold tailWord_3232549
  simp only [CollatzResearch.WordTrace]
  refine ⟨117900747966034523261340701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78600498644023015507560467 117900747966034523261340701)
  ·
    refine ⟨44212780487262946223002763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117900747966034523261340701 44212780487262946223002763)
    ·
      refine ⟨66319170730894419334504145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44212780487262946223002763 66319170730894419334504145)
      ·
        refine ⟨49739378048170814500878109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66319170730894419334504145 49739378048170814500878109)
        ·
          refine ⟨18652266768064055437829291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49739378048170814500878109 18652266768064055437829291)
          ·
            refine ⟨27978400152096083156743937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18652266768064055437829291 27978400152096083156743937)
            ·
              refine ⟨20983800114072062367557953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27978400152096083156743937 20983800114072062367557953)
              ·
                refine ⟨15737850085554046775668465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20983800114072062367557953 15737850085554046775668465)
                ·
                  refine ⟨11803387564165535081751349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15737850085554046775668465 11803387564165535081751349)
                  ·
                    refine ⟨1106567584140518913914189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11803387564165535081751349 1106567584140518913914189)
                    ·
                      rfl

theorem cell22_3232549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_3232549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232549 prefixEnd_3232549 := by exact prefixLift 3232549
  have htrace : WordTrace (prefixWord ++ tailWord_3232549) baseStart_3232549 baseEnd_3232549 := by
    simpa [prefixWord, tailWord_3232549, baseEnd_3232549] using wordTrace_append hprefix tailTrace_3232549
  have hstable : (prefixWord ++ tailWord_3232549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232549).length < 2 ^ (prefixWord ++ tailWord_3232549).sum := by decide
  have hdescent : baseEnd_3232549 < baseStart_3232549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232579 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 6]
def baseStart_3232579 : Nat := 118140960795 + 3232579 * 2 ^ 59
def prefixEnd_3232579 : Nat := 4983230072969 + 3 ^ 40 * 3232579 * 2
def baseEnd_3232579 : Nat := 368859284584536278554699

theorem tailTrace_3232579 : CollatzResearch.WordTrace tailWord_3232579 prefixEnd_3232579 368859284584536278554699 := by
  unfold tailWord_3232579
  simp only [CollatzResearch.WordTrace]
  refine ⟨117901842155925838384932791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78601228103950558923288527 117901842155925838384932791)
  ·
    refine ⟨176852763233888757577399187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117901842155925838384932791 176852763233888757577399187)
    ·
      refine ⟨265279144850833136366098781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176852763233888757577399187 265279144850833136366098781)
      ·
        refine ⟨99479679319062426137287043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265279144850833136366098781 99479679319062426137287043)
        ·
          refine ⟨149219518978593639205930565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99479679319062426137287043 149219518978593639205930565)
          ·
            refine ⟨27978659808486307351111981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149219518978593639205930565 27978659808486307351111981)
            ·
              refine ⟨10491997428182365256666993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27978659808486307351111981 10491997428182365256666993)
              ·
                refine ⟨7868998071136773942500245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10491997428182365256666993 7868998071136773942500245)
                ·
                  refine ⟨368859284584536278554699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7868998071136773942500245 368859284584536278554699)
                  ·
                    rfl

theorem cell22_3232579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 6].length) (baseStart_3232579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232579 prefixEnd_3232579 := by exact prefixLift 3232579
  have htrace : WordTrace (prefixWord ++ tailWord_3232579) baseStart_3232579 baseEnd_3232579 := by
    simpa [prefixWord, tailWord_3232579, baseEnd_3232579] using wordTrace_append hprefix tailTrace_3232579
  have hstable : (prefixWord ++ tailWord_3232579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232579).length < 2 ^ (prefixWord ++ tailWord_3232579).sum := by decide
  have hdescent : baseEnd_3232579 < baseStart_3232579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232658 : List Nat := [3, 2, 3, 2, 2, 2, 8]
def baseStart_3232658 : Nat := 118140960795 + 3232658 * 2 ^ 59
def prefixEnd_3232658 : Nat := 4983230072969 + 3 ^ 40 * 3232658 * 2
def baseEnd_3232658 : Nat := 40985366558076998627365

theorem tailTrace_3232658 : CollatzResearch.WordTrace tailWord_3232658 prefixEnd_3232658 40985366558076998627365 := by
  unfold tailWord_3232658
  simp only [CollatzResearch.WordTrace]
  refine ⟨29476180880659908719264657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78603149015093089918039085 29476180880659908719264657)
  ·
    refine ⟨22107135660494931539448493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29476180880659908719264657 22107135660494931539448493)
    ·
      refine ⟨8290175872685599327293185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22107135660494931539448493 8290175872685599327293185)
      ·
        refine ⟨6217631904514199495469889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8290175872685599327293185 6217631904514199495469889)
        ·
          refine ⟨4663223928385649621602417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6217631904514199495469889 4663223928385649621602417)
          ·
            refine ⟨3497417946289237216201813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4663223928385649621602417 3497417946289237216201813)
            ·
              refine ⟨40985366558076998627365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3497417946289237216201813 40985366558076998627365)
              ·
                rfl

theorem cell22_3232658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 8].length) (baseStart_3232658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232658 prefixEnd_3232658 := by exact prefixLift 3232658
  have htrace : WordTrace (prefixWord ++ tailWord_3232658) baseStart_3232658 baseEnd_3232658 := by
    simpa [prefixWord, tailWord_3232658, baseEnd_3232658] using wordTrace_append hprefix tailTrace_3232658
  have hstable : (prefixWord ++ tailWord_3232658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232658).length < 2 ^ (prefixWord ++ tailWord_3232658).sum := by decide
  have hdescent : baseEnd_3232658 < baseStart_3232658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232662 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3232662 : Nat := 118140960795 + 3232662 * 2 ^ 59
def prefixEnd_3232662 : Nat := 4983230072969 + 3 ^ 40 * 3232662 * 2
def baseEnd_3232662 : Nat := 1106606266349824285838843

theorem tailTrace_3232662 : CollatzResearch.WordTrace tailWord_3232662 prefixEnd_3232662 1106606266349824285838843 := by
  unfold tailWord_3232662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369054338414071472512765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78603246276416762373469493 7369054338414071472512765)
  ·
    refine ⟨2763395376905276802192287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7369054338414071472512765 2763395376905276802192287)
    ·
      refine ⟨4145093065357915203288431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2763395376905276802192287 4145093065357915203288431)
      ·
        refine ⟨6217639598036872804932647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4145093065357915203288431 6217639598036872804932647)
        ·
          refine ⟨9326459397055309207398971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217639598036872804932647 9326459397055309207398971)
          ·
            refine ⟨13989689095582963811098457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9326459397055309207398971 13989689095582963811098457)
            ·
              refine ⟨10492266821687222858323843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13989689095582963811098457 10492266821687222858323843)
              ·
                refine ⟨15738400232530834287485765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10492266821687222858323843 15738400232530834287485765)
                ·
                  refine ⟨2950950043599531428903581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15738400232530834287485765 2950950043599531428903581)
                  ·
                    refine ⟨1106606266349824285838843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950950043599531428903581 1106606266349824285838843)
                    ·
                      rfl

theorem cell22_3232662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3232662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232662 prefixEnd_3232662 := by exact prefixLift 3232662
  have htrace : WordTrace (prefixWord ++ tailWord_3232662) baseStart_3232662 baseEnd_3232662 := by
    simpa [prefixWord, tailWord_3232662, baseEnd_3232662] using wordTrace_append hprefix tailTrace_3232662
  have hstable : (prefixWord ++ tailWord_3232662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232662).length < 2 ^ (prefixWord ++ tailWord_3232662).sum := by decide
  have hdescent : baseEnd_3232662 < baseStart_3232662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232679 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3232679 : Nat := 118140960795 + 3232679 * 2 ^ 59
def prefixEnd_3232679 : Nat := 4983230072969 + 3 ^ 40 * 3232679 * 2
def baseEnd_3232679 : Nat := 1106612085797241908163791

theorem tailTrace_3232679 : CollatzResearch.WordTrace tailWord_3232679 prefixEnd_3232679 1106612085797241908163791 := by
  unfold tailWord_3232679
  simp only [CollatzResearch.WordTrace]
  refine ⟨117905489455563555463573091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78603659637042370309048727 117905489455563555463573091)
  ·
    refine ⟨176858234183345333195359637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117905489455563555463573091 176858234183345333195359637)
    ·
      refine ⟨8290229727344312493532483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176858234183345333195359637 8290229727344312493532483)
      ·
        refine ⟨12435344591016468740298725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8290229727344312493532483 12435344591016468740298725)
        ·
          refine ⟨2331627110815587888806011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12435344591016468740298725 2331627110815587888806011)
          ·
            refine ⟨3497440666223381833209017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331627110815587888806011 3497440666223381833209017)
            ·
              refine ⟨2623080499667536374906763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3497440666223381833209017 2623080499667536374906763)
              ·
                refine ⟨3934620749501304562360145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623080499667536374906763 3934620749501304562360145)
                ·
                  refine ⟨2950965562125978421770109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3934620749501304562360145 2950965562125978421770109)
                  ·
                    refine ⟨1106612085797241908163791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2950965562125978421770109 1106612085797241908163791)
                    ·
                      rfl

theorem cell22_3232679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3232679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232679 prefixEnd_3232679 := by exact prefixLift 3232679
  have htrace : WordTrace (prefixWord ++ tailWord_3232679) baseStart_3232679 baseEnd_3232679 := by
    simpa [prefixWord, tailWord_3232679, baseEnd_3232679] using wordTrace_append hprefix tailTrace_3232679
  have hstable : (prefixWord ++ tailWord_3232679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232679).length < 2 ^ (prefixWord ++ tailWord_3232679).sum := by decide
  have hdescent : baseEnd_3232679 < baseStart_3232679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232694 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3232694 : Nat := 118140960795 + 3232694 * 2 ^ 59
def prefixEnd_3232694 : Nat := 4983230072969 + 3 ^ 40 * 3232694 * 2
def baseEnd_3232694 : Nat := 1106617220603786869038745

theorem tailTrace_3232694 : CollatzResearch.WordTrace tailWord_3232694 prefixEnd_3232694 1106617220603786869038745 := by
  unfold tailWord_3232694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369127284406825814085571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78604024367006142016912757 7369127284406825814085571)
  ·
    refine ⟨11053690926610238721128357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7369127284406825814085571 11053690926610238721128357)
    ·
      refine ⟨2072567048739419760211567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11053690926610238721128357 2072567048739419760211567)
      ·
        refine ⟨3108850573109129640317351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072567048739419760211567 3108850573109129640317351)
        ·
          refine ⟨4663275859663694460476027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108850573109129640317351 4663275859663694460476027)
          ·
            refine ⟨6994913789495541690714041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663275859663694460476027 6994913789495541690714041)
            ·
              refine ⟨5246185342121656268035531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6994913789495541690714041 5246185342121656268035531)
              ·
                refine ⟨7869278013182484402053297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246185342121656268035531 7869278013182484402053297)
                ·
                  refine ⟨5901958509886863301539973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7869278013182484402053297 5901958509886863301539973)
                  ·
                    refine ⟨1106617220603786869038745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5901958509886863301539973 1106617220603786869038745)
                    ·
                      rfl

theorem cell22_3232694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3232694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232694 prefixEnd_3232694 := by exact prefixLift 3232694
  have htrace : WordTrace (prefixWord ++ tailWord_3232694) baseStart_3232694 baseEnd_3232694 := by
    simpa [prefixWord, tailWord_3232694, baseEnd_3232694] using wordTrace_append hprefix tailTrace_3232694
  have hstable : (prefixWord ++ tailWord_3232694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232694).length < 2 ^ (prefixWord ++ tailWord_3232694).sum := by decide
  have hdescent : baseEnd_3232694 < baseStart_3232694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232724 : List Nat := [2, 4, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3232724 : Nat := 118140960795 + 3232724 * 2 ^ 59
def prefixEnd_3232724 : Nat := 4983230072969 + 3 ^ 40 * 3232724 * 2
def baseEnd_3232724 : Nat := 1106627490216876790788653

theorem tailTrace_3232724 : CollatzResearch.WordTrace tailWord_3232724 prefixEnd_3232724 1106627490216876790788653 := by
  unfold tailWord_3232724
  simp only [CollatzResearch.WordTrace]
  refine ⟨58953565370200264074480613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78604753826933685432640817 58953565370200264074480613)
  ·
    refine ⟨11053793506912549513965115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58953565370200264074480613 11053793506912549513965115)
    ·
      refine ⟨16580690260368824270947673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11053793506912549513965115 16580690260368824270947673)
      ·
        refine ⟨12435517695276618203210755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16580690260368824270947673 12435517695276618203210755)
        ·
          refine ⟨18653276542914927304816133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12435517695276618203210755 18653276542914927304816133)
          ·
            refine ⟨3497489351796548869653025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18653276542914927304816133 3497489351796548869653025)
            ·
              refine ⟨2623117013847411652239769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3497489351796548869653025 2623117013847411652239769)
              ·
                refine ⟨1967337760385558739179827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623117013847411652239769 1967337760385558739179827)
                ·
                  refine ⟨2951006640578338108769741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967337760385558739179827 2951006640578338108769741)
                  ·
                    refine ⟨1106627490216876790788653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951006640578338108769741 1106627490216876790788653)
                    ·
                      rfl

theorem cell22_3232724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3232724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232724 prefixEnd_3232724 := by exact prefixLift 3232724
  have htrace : WordTrace (prefixWord ++ tailWord_3232724) baseStart_3232724 baseEnd_3232724 := by
    simpa [prefixWord, tailWord_3232724, baseEnd_3232724] using wordTrace_append hprefix tailTrace_3232724
  have hstable : (prefixWord ++ tailWord_3232724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232724).length < 2 ^ (prefixWord ++ tailWord_3232724).sum := by decide
  have hdescent : baseEnd_3232724 < baseStart_3232724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232733 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3232733 : Nat := 118140960795 + 3232733 * 2 ^ 59
def prefixEnd_3232733 : Nat := 4983230072969 + 3 ^ 40 * 3232733 * 2
def baseEnd_3232733 : Nat := 1106630571100803767313625

theorem tailTrace_3232733 : CollatzResearch.WordTrace tailWord_3232733 prefixEnd_3232733 1106630571100803767313625 := by
  unfold tailWord_3232733
  simp only [CollatzResearch.WordTrace]
  refine ⟨117907458997367922686038853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78604972664911948457359235 117907458997367922686038853)
  ·
    refine ⟨22107648562006485503632285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117907458997367922686038853 22107648562006485503632285)
    ·
      refine ⟨8290368210752432063862107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22107648562006485503632285 8290368210752432063862107)
      ·
        refine ⟨12435552316128648095793161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8290368210752432063862107 12435552316128648095793161)
        ·
          refine ⟨9326664237096486071844871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12435552316128648095793161 9326664237096486071844871)
          ·
            refine ⟨13989996355644729107767307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9326664237096486071844871 13989996355644729107767307)
            ·
              refine ⟨20984994533467093661650961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13989996355644729107767307 20984994533467093661650961)
              ·
                refine ⟨15738745900100320246238221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20984994533467093661650961 15738745900100320246238221)
                ·
                  refine ⟨5902029712537620092339333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15738745900100320246238221 5902029712537620092339333)
                  ·
                    refine ⟨1106630571100803767313625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5902029712537620092339333 1106630571100803767313625)
                    ·
                      rfl

theorem cell22_3232733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3232733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232733 prefixEnd_3232733 := by exact prefixLift 3232733
  have htrace : WordTrace (prefixWord ++ tailWord_3232733) baseStart_3232733 baseEnd_3232733 := by
    simpa [prefixWord, tailWord_3232733, baseEnd_3232733] using wordTrace_append hprefix tailTrace_3232733
  have hstable : (prefixWord ++ tailWord_3232733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232733).length < 2 ^ (prefixWord ++ tailWord_3232733).sum := by decide
  have hdescent : baseEnd_3232733 < baseStart_3232733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232761 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_3232761 : Nat := 118140960795 + 3232761 * 2 ^ 59
def prefixEnd_3232761 : Nat := 4983230072969 + 3 ^ 40 * 3232761 * 2
def baseEnd_3232761 : Nat := 1106640156073021027613539

theorem tailTrace_3232761 : CollatzResearch.WordTrace tailWord_3232761 prefixEnd_3232761 1106640156073021027613539 := by
  unfold tailWord_3232761
  simp only [CollatzResearch.WordTrace]
  refine ⟨117908480241266483468058137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78605653494177655645372091 117908480241266483468058137)
  ·
    refine ⟨88431360180949862601043603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117908480241266483468058137 88431360180949862601043603)
    ·
      refine ⟨132647040271424793901565405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88431360180949862601043603 132647040271424793901565405)
      ·
        refine ⟨49742640101784297713087027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132647040271424793901565405 49742640101784297713087027)
        ·
          refine ⟨74613960152676446569630541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49742640101784297713087027 74613960152676446569630541)
          ·
            refine ⟨27980235057253667463611453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74613960152676446569630541 27980235057253667463611453)
            ·
              refine ⟨10492588146470125298854295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27980235057253667463611453 10492588146470125298854295)
              ·
                refine ⟨15738882219705187948281443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10492588146470125298854295 15738882219705187948281443)
                ·
                  refine ⟨23608323329557781922422165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15738882219705187948281443 23608323329557781922422165)
                  ·
                    refine ⟨1106640156073021027613539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23608323329557781922422165 1106640156073021027613539)
                    ·
                      rfl

theorem cell22_3232761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_3232761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232761 prefixEnd_3232761 := by exact prefixLift 3232761
  have htrace : WordTrace (prefixWord ++ tailWord_3232761) baseStart_3232761 baseEnd_3232761 := by
    simpa [prefixWord, tailWord_3232761, baseEnd_3232761] using wordTrace_append hprefix tailTrace_3232761
  have hstable : (prefixWord ++ tailWord_3232761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232761).length < 2 ^ (prefixWord ++ tailWord_3232761).sum := by decide
  have hdescent : baseEnd_3232761 < baseStart_3232761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232776 : List Nat := [2, 1, 3, 2, 1, 4, 9]
def baseStart_3232776 : Nat := 118140960795 + 3232776 * 2 ^ 59
def prefixEnd_3232776 : Nat := 4983230072969 + 3 ^ 40 * 3232776 * 2
def baseEnd_3232776 : Nat := 40986862625169110684759

theorem tailTrace_3232776 : CollatzResearch.WordTrace tailWord_3232776 prefixEnd_3232776 40986862625169110684759 := by
  unfold tailWord_3232776
  simp only [CollatzResearch.WordTrace]
  refine ⟨58954513668106070514927091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78606018224141427353236121 58954513668106070514927091)
  ·
    refine ⟨88431770502159105772390637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58954513668106070514927091 88431770502159105772390637)
    ·
      refine ⟨33161913938309664664646489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88431770502159105772390637 33161913938309664664646489)
      ·
        refine ⟨24871435453732248498484867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33161913938309664664646489 24871435453732248498484867)
        ·
          refine ⟨37307153180598372747727301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24871435453732248498484867 37307153180598372747727301)
          ·
            refine ⟨6995091221362194890198869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37307153180598372747727301 6995091221362194890198869)
            ·
              refine ⟨40986862625169110684759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6995091221362194890198869 40986862625169110684759)
              ·
                rfl

theorem cell22_3232776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 9].length) (baseStart_3232776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232776 prefixEnd_3232776 := by exact prefixLift 3232776
  have htrace : WordTrace (prefixWord ++ tailWord_3232776) baseStart_3232776 baseEnd_3232776 := by
    simpa [prefixWord, tailWord_3232776, baseEnd_3232776] using wordTrace_append hprefix tailTrace_3232776
  have hstable : (prefixWord ++ tailWord_3232776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232776).length < 2 ^ (prefixWord ++ tailWord_3232776).sum := by decide
  have hdescent : baseEnd_3232776 < baseStart_3232776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232780 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_3232780 : Nat := 118140960795 + 3232780 * 2 ^ 59
def prefixEnd_3232780 : Nat := 4983230072969 + 3 ^ 40 * 3232780 * 2
def baseEnd_3232780 : Nat := 1106646660161311311388481

theorem tailTrace_3232780 : CollatzResearch.WordTrace tailWord_3232780 prefixEnd_3232780 1106646660161311311388481 := by
  unfold tailWord_3232780
  simp only [CollatzResearch.WordTrace]
  refine ⟨58954586614098824856499897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78606115485465099808666529 58954586614098824856499897)
  ·
    refine ⟨44215939960574118642374923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58954586614098824856499897 44215939960574118642374923)
    ·
      refine ⟨66323909940861177963562385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44215939960574118642374923 66323909940861177963562385)
      ·
        refine ⟨49742932455645883472671789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66323909940861177963562385 49742932455645883472671789)
        ·
          refine ⟨18653599670867206302251921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49742932455645883472671789 18653599670867206302251921)
          ·
            refine ⟨13990199753150404726688941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18653599670867206302251921 13990199753150404726688941)
            ·
              refine ⟨5246324907431401772508353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13990199753150404726688941 5246324907431401772508353)
              ·
                refine ⟨3934743680573551329381265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5246324907431401772508353 3934743680573551329381265)
                ·
                  refine ⟨2951057760430163497035949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3934743680573551329381265 2951057760430163497035949)
                  ·
                    refine ⟨1106646660161311311388481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951057760430163497035949 1106646660161311311388481)
                    ·
                      rfl

theorem cell22_3232780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_3232780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232780 prefixEnd_3232780 := by exact prefixLift 3232780
  have htrace : WordTrace (prefixWord ++ tailWord_3232780) baseStart_3232780 baseEnd_3232780 := by
    simpa [prefixWord, tailWord_3232780, baseEnd_3232780] using wordTrace_append hprefix tailTrace_3232780
  have hstable : (prefixWord ++ tailWord_3232780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232780).length < 2 ^ (prefixWord ++ tailWord_3232780).sum := by decide
  have hdescent : baseEnd_3232780 < baseStart_3232780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232797 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_3232797 : Nat := 118140960795 + 3232797 * 2 ^ 59
def prefixEnd_3232797 : Nat := 4983230072969 + 3 ^ 40 * 3232797 * 2
def baseEnd_3232797 : Nat := 1106652479608728933713429

theorem tailTrace_3232797 : CollatzResearch.WordTrace tailWord_3232797 prefixEnd_3232797 1106652479608728933713429 := by
  unfold tailWord_3232797
  simp only [CollatzResearch.WordTrace]
  refine ⟨117909793269136061616368645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78606528846090707744245763 117909793269136061616368645)
  ·
    refine ⟨22108086237963011553069121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117909793269136061616368645 22108086237963011553069121)
    ·
      refine ⟨16581064678472258664801841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22108086237963011553069121 16581064678472258664801841)
      ·
        refine ⟨12435798508854193998601381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16581064678472258664801841 12435798508854193998601381)
        ·
          refine ⟨2331712220410161374737759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12435798508854193998601381 2331712220410161374737759)
          ·
            refine ⟨3497568330615242062106639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331712220410161374737759 3497568330615242062106639)
            ·
              refine ⟨5246352495922863093159959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497568330615242062106639 5246352495922863093159959)
              ·
                refine ⟨7869528743884294639739939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246352495922863093159959 7869528743884294639739939)
                ·
                  refine ⟨11804293115826441959609909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7869528743884294639739939 11804293115826441959609909)
                  ·
                    refine ⟨1106652479608728933713429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11804293115826441959609909 1106652479608728933713429)
                    ·
                      rfl

theorem cell22_3232797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_3232797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232797 prefixEnd_3232797 := by exact prefixLift 3232797
  have htrace : WordTrace (prefixWord ++ tailWord_3232797) baseStart_3232797 baseEnd_3232797 := by
    simpa [prefixWord, tailWord_3232797, baseEnd_3232797] using wordTrace_append hprefix tailTrace_3232797
  have hstable : (prefixWord ++ tailWord_3232797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232797).length < 2 ^ (prefixWord ++ tailWord_3232797).sum := by decide
  have hdescent : baseEnd_3232797 < baseStart_3232797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232915 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 2, 3]
def baseStart_3232915 : Nat := 118140960795 + 3232915 * 2 ^ 59
def prefixEnd_3232915 : Nat := 4983230072969 + 3 ^ 40 * 3232915 * 2
def baseEnd_3232915 : Nat := 1106692873420215959263067

theorem tailTrace_3232915 : CollatzResearch.WordTrace tailWord_3232915 prefixEnd_3232915 1106692873420215959263067 := by
  unfold tailWord_3232915
  simp only [CollatzResearch.WordTrace]
  refine ⟨117914097082708567769164199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78609398055139045179442799 117914097082708567769164199)
  ·
    refine ⟨176871145624062851653746299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117914097082708567769164199 176871145624062851653746299)
    ·
      refine ⟨265306718436094277480619449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176871145624062851653746299 265306718436094277480619449)
      ·
        refine ⟨198980038827070708110464587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265306718436094277480619449 198980038827070708110464587)
        ·
          refine ⟨298470058240606062165696881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198980038827070708110464587 298470058240606062165696881)
          ·
            refine ⟨223852543680454546624272661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298470058240606062165696881 223852543680454546624272661)
            ·
              refine ⟨10493087985021306873012781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 223852543680454546624272661 10493087985021306873012781)
              ·
                refine ⟨3934907994382990077379793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10493087985021306873012781 3934907994382990077379793)
                ·
                  refine ⟨2951180995787242558034845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3934907994382990077379793 2951180995787242558034845)
                  ·
                    refine ⟨1106692873420215959263067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951180995787242558034845 1106692873420215959263067)
                    ·
                      rfl

theorem cell22_3232915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 3].length) (baseStart_3232915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3232915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3232915 prefixEnd_3232915 := by exact prefixLift 3232915
  have htrace : WordTrace (prefixWord ++ tailWord_3232915) baseStart_3232915 baseEnd_3232915 := by
    simpa [prefixWord, tailWord_3232915, baseEnd_3232915] using wordTrace_append hprefix tailTrace_3232915
  have hstable : (prefixWord ++ tailWord_3232915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232915).length < 2 ^ (prefixWord ++ tailWord_3232915).sum := by decide
  have hdescent : baseEnd_3232915 < baseStart_3232915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233050 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_3233050 : Nat := 118140960795 + 3233050 * 2 ^ 59
def prefixEnd_3233050 : Nat := 4983230072969 + 3 ^ 40 * 3233050 * 2
def baseEnd_3233050 : Nat := 1106739086679120607137653

theorem tailTrace_3233050 : CollatzResearch.WordTrace tailWord_3233050 prefixEnd_3233050 1106739086679120607137653 := by
  unfold tailWord_3233050
  simp only [CollatzResearch.WordTrace]
  refine ⟨29479755234304871456332151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78612680624812990550219069 29479755234304871456332151)
  ·
    refine ⟨44219632851457307184498227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29479755234304871456332151 44219632851457307184498227)
    ·
      refine ⟨66329449277185960776747341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44219632851457307184498227 66329449277185960776747341)
      ·
        refine ⟨24873543478944735291280253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66329449277185960776747341 24873543478944735291280253)
        ·
          refine ⟨9327578804604275734230095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24873543478944735291280253 9327578804604275734230095)
          ·
            refine ⟨13991368206906413601345143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9327578804604275734230095 13991368206906413601345143)
            ·
              refine ⟨20987052310359620402017715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13991368206906413601345143 20987052310359620402017715)
              ·
                refine ⟨31480578465539430603026573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20987052310359620402017715 31480578465539430603026573)
                ·
                  refine ⟨11805216924577286476134965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31480578465539430603026573 11805216924577286476134965)
                  ·
                    refine ⟨1106739086679120607137653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11805216924577286476134965 1106739086679120607137653)
                    ·
                      rfl

theorem cell22_3233050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_3233050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233050 prefixEnd_3233050 := by exact prefixLift 3233050
  have htrace : WordTrace (prefixWord ++ tailWord_3233050) baseStart_3233050 baseEnd_3233050 := by
    simpa [prefixWord, tailWord_3233050, baseEnd_3233050] using wordTrace_append hprefix tailTrace_3233050
  have hstable : (prefixWord ++ tailWord_3233050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233050).length < 2 ^ (prefixWord ++ tailWord_3233050).sum := by decide
  have hdescent : baseEnd_3233050 < baseStart_3233050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233125 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 7]
def baseStart_3233125 : Nat := 118140960795 + 3233125 * 2 ^ 59
def prefixEnd_3233125 : Nat := 4983230072969 + 3 ^ 40 * 3233125 * 2
def baseEnd_3233125 : Nat := 368921586903948470504141

theorem tailTrace_3233125 : CollatzResearch.WordTrace tailWord_3233125 prefixEnd_3233125 368921586903948470504141 := by
  unfold tailWord_3233125
  simp only [CollatzResearch.WordTrace]
  refine ⟨117921756411947773634308829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78614504274631849089539219 117921756411947773634308829)
  ·
    refine ⟨44220658654480415112865811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117921756411947773634308829 44220658654480415112865811)
    ·
      refine ⟨66330987981720622669298717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44220658654480415112865811 66330987981720622669298717)
      ·
        refine ⟨24874120493145233500987019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66330987981720622669298717 24874120493145233500987019)
        ·
          refine ⟨37311180739717850251480529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24874120493145233500987019 37311180739717850251480529)
          ·
            refine ⟨27983385554788387688610397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37311180739717850251480529 27983385554788387688610397)
            ·
              refine ⟨10493769583045645383228899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27983385554788387688610397 10493769583045645383228899)
              ·
                refine ⟨15740654374568468074843349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10493769583045645383228899 15740654374568468074843349)
                ·
                  refine ⟨368921586903948470504141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15740654374568468074843349 368921586903948470504141)
                  ·
                    rfl

theorem cell22_3233125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_3233125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233125 prefixEnd_3233125 := by exact prefixLift 3233125
  have htrace : WordTrace (prefixWord ++ tailWord_3233125) baseStart_3233125 baseEnd_3233125 := by
    simpa [prefixWord, tailWord_3233125, baseEnd_3233125] using wordTrace_append hprefix tailTrace_3233125
  have hstable : (prefixWord ++ tailWord_3233125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233125).length < 2 ^ (prefixWord ++ tailWord_3233125).sum := by decide
  have hdescent : baseEnd_3233125 < baseStart_3233125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233180 : List Nat := [2, 2, 3, 4, 1, 1, 3, 2, 1, 3]
def baseStart_3233180 : Nat := 118140960795 + 3233180 * 2 ^ 59
def prefixEnd_3233180 : Nat := 4983230072969 + 3 ^ 40 * 3233180 * 2
def baseEnd_3233180 : Nat := 1106783588335843601387255

theorem tailTrace_3233180 : CollatzResearch.WordTrace tailWord_3233180 prefixEnd_3233180 1106783588335843601387255 := by
  unfold tailWord_3233180
  simp only [CollatzResearch.WordTrace]
  refine ⟨58961881213374259013780497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78615841617832345351707329 58961881213374259013780497)
  ·
    refine ⟨44221410910030694260335373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58961881213374259013780497 44221410910030694260335373)
    ·
      refine ⟨16583029091261510347625765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44221410910030694260335373 16583029091261510347625765)
      ·
        refine ⟨3109317954611533190179831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16583029091261510347625765 3109317954611533190179831)
        ·
          refine ⟨4663976931917299785269747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3109317954611533190179831 4663976931917299785269747)
          ·
            refine ⟨6995965397875949677904621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663976931917299785269747 6995965397875949677904621)
            ·
              refine ⟨2623487024203481129214233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6995965397875949677904621 2623487024203481129214233)
              ·
                refine ⟨1967615268152610846910675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623487024203481129214233 1967615268152610846910675)
                ·
                  refine ⟨2951422902228916270366013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967615268152610846910675 2951422902228916270366013)
                  ·
                    refine ⟨1106783588335843601387255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951422902228916270366013 1106783588335843601387255)
                    ·
                      rfl

theorem cell22_3233180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_3233180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233180 prefixEnd_3233180 := by exact prefixLift 3233180
  have htrace : WordTrace (prefixWord ++ tailWord_3233180) baseStart_3233180 baseEnd_3233180 := by
    simpa [prefixWord, tailWord_3233180, baseEnd_3233180] using wordTrace_append hprefix tailTrace_3233180
  have hstable : (prefixWord ++ tailWord_3233180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233180).length < 2 ^ (prefixWord ++ tailWord_3233180).sum := by decide
  have hdescent : baseEnd_3233180 < baseStart_3233180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233200 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_3233200 : Nat := 118140960795 + 3233200 * 2 ^ 59
def prefixEnd_3233200 : Nat := 4983230072969 + 3 ^ 40 * 3233200 * 2
def baseEnd_3233200 : Nat := 1106790434744570215887193

theorem tailTrace_3233200 : CollatzResearch.WordTrace tailWord_3233200 prefixEnd_3233200 1106790434744570215887193 := by
  unfold tailWord_3233200
  simp only [CollatzResearch.WordTrace]
  refine ⟨58962245943338030721644527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78616327924450707628859369 58962245943338030721644527)
  ·
    refine ⟨88443368915007046082466791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58962245943338030721644527 88443368915007046082466791)
    ·
      refine ⟨132665053372510569123700187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88443368915007046082466791 132665053372510569123700187)
      ·
        refine ⟨198997580058765853685550281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132665053372510569123700187 198997580058765853685550281)
        ·
          refine ⟨149248185044074390264162711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198997580058765853685550281 149248185044074390264162711)
          ·
            refine ⟨223872277566111585396244067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149248185044074390264162711 223872277566111585396244067)
            ·
              refine ⟨335808416349167378094366101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223872277566111585396244067 335808416349167378094366101)
              ·
                refine ⟨15741019516367220848173411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 335808416349167378094366101 15741019516367220848173411)
                ·
                  refine ⟨23611529274550831272260117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15741019516367220848173411 23611529274550831272260117)
                  ·
                    refine ⟨1106790434744570215887193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23611529274550831272260117 1106790434744570215887193)
                    ·
                      rfl

theorem cell22_3233200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_3233200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233200 prefixEnd_3233200 := by exact prefixLift 3233200
  have htrace : WordTrace (prefixWord ++ tailWord_3233200) baseStart_3233200 baseEnd_3233200 := by
    simpa [prefixWord, tailWord_3233200, baseEnd_3233200] using wordTrace_append hprefix tailTrace_3233200
  have hstable : (prefixWord ++ tailWord_3233200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233200).length < 2 ^ (prefixWord ++ tailWord_3233200).sum := by decide
  have hdescent : baseEnd_3233200 < baseStart_3233200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233202 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_3233202 : Nat := 118140960795 + 3233202 * 2 ^ 59
def prefixEnd_3233202 : Nat := 4983230072969 + 3 ^ 40 * 3233202 * 2
def baseEnd_3233202 : Nat := 1106791119385442877337187

theorem tailTrace_3233202 : CollatzResearch.WordTrace tailWord_3233202 prefixEnd_3233202 1106791119385442877337187 := by
  unfold tailWord_3233202
  simp only [CollatzResearch.WordTrace]
  refine ⟨29481141208167203946215465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78616376555112543856574573 29481141208167203946215465)
  ·
    refine ⟨22110855906125402959661599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29481141208167203946215465 22110855906125402959661599)
    ·
      refine ⟨33166283859188104439492399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22110855906125402959661599 33166283859188104439492399)
      ·
        refine ⟨49749425788782156659238599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33166283859188104439492399 49749425788782156659238599)
        ·
          refine ⟨74624138683173234988857899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49749425788782156659238599 74624138683173234988857899)
          ·
            refine ⟨111936208024759852483286849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74624138683173234988857899 111936208024759852483286849)
            ·
              refine ⟨83952156018569889362465137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111936208024759852483286849 83952156018569889362465137)
              ·
                refine ⟨62964117013927417021848853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83952156018569889362465137 62964117013927417021848853)
                ·
                  refine ⟨2951442985027847672899165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62964117013927417021848853 2951442985027847672899165)
                  ·
                    refine ⟨1106791119385442877337187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951442985027847672899165 1106791119385442877337187)
                    ·
                      rfl

theorem cell22_3233202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_3233202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233202 prefixEnd_3233202 := by exact prefixLift 3233202
  have htrace : WordTrace (prefixWord ++ tailWord_3233202) baseStart_3233202 baseEnd_3233202 := by
    simpa [prefixWord, tailWord_3233202, baseEnd_3233202] using wordTrace_append hprefix tailTrace_3233202
  have hstable : (prefixWord ++ tailWord_3233202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233202).length < 2 ^ (prefixWord ++ tailWord_3233202).sum := by decide
  have hdescent : baseEnd_3233202 < baseStart_3233202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233238 : List Nat := [5, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_3233238 : Nat := 118140960795 + 3233238 * 2 ^ 59
def prefixEnd_3233238 : Nat := 4983230072969 + 3 ^ 40 * 3233238 * 2
def baseEnd_3233238 : Nat := 368934480973716927812359

theorem tailTrace_3233238 : CollatzResearch.WordTrace tailWord_3233238 prefixEnd_3233238 368934480973716927812359 := by
  unfold tailWord_3233238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7370367366283649620823273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78617251907025595955448245 7370367366283649620823273)
  ·
    refine ⟨5527775524712737215617455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7370367366283649620823273 5527775524712737215617455)
    ·
      refine ⟨8291663287069105823426183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5527775524712737215617455 8291663287069105823426183)
      ·
        refine ⟨12437494930603658735139275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8291663287069105823426183 12437494930603658735139275)
        ·
          refine ⟨18656242395905488102708913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12437494930603658735139275 18656242395905488102708913)
          ·
            refine ⟨13992181796929116077031685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18656242395905488102708913 13992181796929116077031685)
            ·
              refine ⟨2623534086924209264443441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13992181796929116077031685 2623534086924209264443441)
              ·
                refine ⟨1967650565193156948332581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623534086924209264443441 1967650565193156948332581)
                ·
                  refine ⟨368934480973716927812359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1967650565193156948332581 368934480973716927812359)
                  ·
                    rfl

theorem cell22_3233238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_3233238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233238 prefixEnd_3233238 := by exact prefixLift 3233238
  have htrace : WordTrace (prefixWord ++ tailWord_3233238) baseStart_3233238 baseEnd_3233238 := by
    simpa [prefixWord, tailWord_3233238, baseEnd_3233238] using wordTrace_append hprefix tailTrace_3233238
  have hstable : (prefixWord ++ tailWord_3233238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233238).length < 2 ^ (prefixWord ++ tailWord_3233238).sum := by decide
  have hdescent : baseEnd_3233238 < baseStart_3233238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233262 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3233262 : Nat := 118140960795 + 3233262 * 2 ^ 59
def prefixEnd_3233262 : Nat := 4983230072969 + 3 ^ 40 * 3233262 * 2
def baseEnd_3233262 : Nat := 1106811658611622720837003

theorem tailTrace_3233262 : CollatzResearch.WordTrace tailWord_3233262 prefixEnd_3233262 1106811658611622720837003 := by
  unfold tailWord_3233262
  simp only [CollatzResearch.WordTrace]
  refine ⟨14740844151556430754005755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78617835474967630688030693 14740844151556430754005755)
  ·
    refine ⟨22111266227334646131008633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14740844151556430754005755 22111266227334646131008633)
    ·
      refine ⟨16583449670500984598256475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22111266227334646131008633 16583449670500984598256475)
      ·
        refine ⟨24875174505751476897384713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16583449670500984598256475 24875174505751476897384713)
        ·
          refine ⟨18656380879313607673038535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24875174505751476897384713 18656380879313607673038535)
          ·
            refine ⟨27984571318970411509557803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18656380879313607673038535 27984571318970411509557803)
            ·
              refine ⟨41976856978455617264336705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27984571318970411509557803 41976856978455617264336705)
              ·
                refine ⟨31482642733841712948252529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41976856978455617264336705 31482642733841712948252529)
                ·
                  refine ⟨23611982050381284711189397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31482642733841712948252529 23611982050381284711189397)
                  ·
                    refine ⟨1106811658611622720837003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23611982050381284711189397 1106811658611622720837003)
                    ·
                      rfl

theorem cell22_3233262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3233262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233262 prefixEnd_3233262 := by exact prefixLift 3233262
  have htrace : WordTrace (prefixWord ++ tailWord_3233262) baseStart_3233262 baseEnd_3233262 := by
    simpa [prefixWord, tailWord_3233262, baseEnd_3233262] using wordTrace_append hprefix tailTrace_3233262
  have hstable : (prefixWord ++ tailWord_3233262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233262).length < 2 ^ (prefixWord ++ tailWord_3233262).sum := by decide
  have hdescent : baseEnd_3233262 < baseStart_3233262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233264 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 3, 3]
def baseStart_3233264 : Nat := 118140960795 + 3233264 * 2 ^ 59
def prefixEnd_3233264 : Nat := 4983230072969 + 3 ^ 40 * 3233264 * 2
def baseEnd_3233264 : Nat := 1106812343252495382286997

theorem tailTrace_3233264 : CollatzResearch.WordTrace tailWord_3233264 prefixEnd_3233264 1106812343252495382286997 := by
  unfold tailWord_3233264
  simp only [CollatzResearch.WordTrace]
  refine ⟨58963413079222100186809423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78617884105629466915745897 58963413079222100186809423)
  ·
    refine ⟨88445119618833150280214135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58963413079222100186809423 88445119618833150280214135)
    ·
      refine ⟨132667679428249725420321203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88445119618833150280214135 132667679428249725420321203)
      ·
        refine ⟨199001519142374588130481805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132667679428249725420321203 199001519142374588130481805)
        ·
          refine ⟨74625569678390470548930677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199001519142374588130481805 74625569678390470548930677)
          ·
            refine ⟨6996147157349106613962251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74625569678390470548930677 6996147157349106613962251)
            ·
              refine ⟨10494220736023659920943377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996147157349106613962251 10494220736023659920943377)
              ·
                refine ⟨7870665552017744940707533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10494220736023659920943377 7870665552017744940707533)
                ·
                  refine ⟨2951499582006654352765325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7870665552017744940707533 2951499582006654352765325)
                  ·
                    refine ⟨1106812343252495382286997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951499582006654352765325 1106812343252495382286997)
                    ·
                      rfl

theorem cell22_3233264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_3233264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233264 prefixEnd_3233264 := by exact prefixLift 3233264
  have htrace : WordTrace (prefixWord ++ tailWord_3233264) baseStart_3233264 baseEnd_3233264 := by
    simpa [prefixWord, tailWord_3233264, baseEnd_3233264] using wordTrace_append hprefix tailTrace_3233264
  have hstable : (prefixWord ++ tailWord_3233264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233264).length < 2 ^ (prefixWord ++ tailWord_3233264).sum := by decide
  have hdescent : baseEnd_3233264 < baseStart_3233264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233294 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_3233294 : Nat := 118140960795 + 3233294 * 2 ^ 59
def prefixEnd_3233294 : Nat := 4983230072969 + 3 ^ 40 * 3233294 * 2
def baseEnd_3233294 : Nat := 368940870955195101345635

theorem tailTrace_3233294 : CollatzResearch.WordTrace tailWord_3233294 prefixEnd_3233294 368940870955195101345635 := by
  unfold tailWord_3233294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14740990043541939437151367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78618613565557010331473957 14740990043541939437151367)
  ·
    refine ⟨22111485065312909155727051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14740990043541939437151367 22111485065312909155727051)
    ·
      refine ⟨33167227597969363733590577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22111485065312909155727051 33167227597969363733590577)
      ·
        refine ⟨24875420698477022800192933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33167227597969363733590577 24875420698477022800192933)
        ·
          refine ⟨4664141380964441775036175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24875420698477022800192933 4664141380964441775036175)
          ·
            refine ⟨6996212071446662662554263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4664141380964441775036175 6996212071446662662554263)
            ·
              refine ⟨10494318107169993993831395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996212071446662662554263 10494318107169993993831395)
              ·
                refine ⟨15741477160754990990747093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10494318107169993993831395 15741477160754990990747093)
                ·
                  refine ⟨368940870955195101345635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15741477160754990990747093 368940870955195101345635)
                  ·
                    rfl

theorem cell22_3233294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_3233294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233294 prefixEnd_3233294 := by exact prefixLift 3233294
  have htrace : WordTrace (prefixWord ++ tailWord_3233294) baseStart_3233294 baseEnd_3233294 := by
    simpa [prefixWord, tailWord_3233294, baseEnd_3233294] using wordTrace_append hprefix tailTrace_3233294
  have hstable : (prefixWord ++ tailWord_3233294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233294).length < 2 ^ (prefixWord ++ tailWord_3233294).sum := by decide
  have hdescent : baseEnd_3233294 < baseStart_3233294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233354 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_3233354 : Nat := 118140960795 + 3233354 * 2 ^ 59
def prefixEnd_3233354 : Nat := 4983230072969 + 3 ^ 40 * 3233354 * 2
def baseEnd_3233354 : Nat := 1106843152091765147536721

theorem tailTrace_3233354 : CollatzResearch.WordTrace tailWord_3233354 prefixEnd_3233354 1106843152091765147536721 := by
  unfold tailWord_3233354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29482527182029536436098779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78620072485412097162930077 29482527182029536436098779)
  ·
    refine ⟨44223790773044304654148169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29482527182029536436098779 44223790773044304654148169)
    ·
      refine ⟨33167843079783228490611127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44223790773044304654148169 33167843079783228490611127)
      ·
        refine ⟨49751764619674842735916691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33167843079783228490611127 49751764619674842735916691)
        ·
          refine ⟨74627646929512264103875037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49751764619674842735916691 74627646929512264103875037)
          ·
            refine ⟨27985367598567099038953139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74627646929512264103875037 27985367598567099038953139)
            ·
              refine ⟨41978051397850648558429709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27985367598567099038953139 41978051397850648558429709)
              ·
                refine ⟨15741769274193993209411141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41978051397850648558429709 15741769274193993209411141)
                ·
                  refine ⟨2951581738911373726764589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15741769274193993209411141 2951581738911373726764589)
                  ·
                    refine ⟨1106843152091765147536721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951581738911373726764589 1106843152091765147536721)
                    ·
                      rfl

theorem cell22_3233354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_3233354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233354 prefixEnd_3233354 := by exact prefixLift 3233354
  have htrace : WordTrace (prefixWord ++ tailWord_3233354) baseStart_3233354 baseEnd_3233354 := by
    simpa [prefixWord, tailWord_3233354, baseEnd_3233354] using wordTrace_append hprefix tailTrace_3233354
  have hstable : (prefixWord ++ tailWord_3233354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233354).length < 2 ^ (prefixWord ++ tailWord_3233354).sum := by decide
  have hdescent : baseEnd_3233354 < baseStart_3233354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233367 : List Nat := [1, 1, 3, 2, 2, 3, 1, 9]
def baseStart_3233367 : Nat := 118140960795 + 3233367 * 2 ^ 59
def prefixEnd_3233367 : Nat := 4983230072969 + 3 ^ 40 * 3233367 * 2
def baseEnd_3233367 : Nat := 122983066917493049662409

theorem tailTrace_3233367 : CollatzResearch.WordTrace tailWord_3233367 prefixEnd_3233367 122983066917493049662409 := by
  unfold tailWord_3233367
  simp only [CollatzResearch.WordTrace]
  refine ⟨117930582877071048964618355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78620388584714032643078903 117930582877071048964618355)
  ·
    refine ⟨176895874315606573446927533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117930582877071048964618355 176895874315606573446927533)
    ·
      refine ⟨66335952868352465042597825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176895874315606573446927533 66335952868352465042597825)
      ·
        refine ⟨49751964651264348781948369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66335952868352465042597825 49751964651264348781948369)
        ·
          refine ⟨37313973488448261586461277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49751964651264348781948369 37313973488448261586461277)
          ·
            refine ⟨13992740058168098094922979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37313973488448261586461277 13992740058168098094922979)
            ·
              refine ⟨20989110087252147142384469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13992740058168098094922979 20989110087252147142384469)
              ·
                refine ⟨122983066917493049662409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20989110087252147142384469 122983066917493049662409)
                ·
                  rfl

theorem cell22_3233367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 9].length) (baseStart_3233367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233367 prefixEnd_3233367 := by exact prefixLift 3233367
  have htrace : WordTrace (prefixWord ++ tailWord_3233367) baseStart_3233367 baseEnd_3233367 := by
    simpa [prefixWord, tailWord_3233367, baseEnd_3233367] using wordTrace_append hprefix tailTrace_3233367
  have hstable : (prefixWord ++ tailWord_3233367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233367).length < 2 ^ (prefixWord ++ tailWord_3233367).sum := by decide
  have hdescent : baseEnd_3233367 < baseStart_3233367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233384 : List Nat := [2, 1, 4, 3, 1, 1, 2, 8]
def baseStart_3233384 : Nat := 118140960795 + 3233384 * 2 ^ 59
def prefixEnd_3233384 : Nat := 4983230072969 + 3 ^ 40 * 3233384 * 2
def baseEnd_3233384 : Nat := 122983713522761674365181

theorem tailTrace_3233384 : CollatzResearch.WordTrace tailWord_3233384 prefixEnd_3233384 122983713522761674365181 := by
  unfold tailWord_3233384
  simp only [CollatzResearch.WordTrace]
  refine ⟨58965601459004730433993603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78620801945339640578658137 58965601459004730433993603)
  ·
    refine ⟨88448402188507095650990405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58965601459004730433993603 88448402188507095650990405)
    ·
      refine ⟨16584075410345080434560701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88448402188507095650990405 16584075410345080434560701)
      ·
        refine ⟨6219028278879405162960263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16584075410345080434560701 6219028278879405162960263)
        ·
          refine ⟨9328542418319107744440395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6219028278879405162960263 9328542418319107744440395)
          ·
            refine ⟨13992813627478661616660593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9328542418319107744440395 13992813627478661616660593)
            ·
              refine ⟨10494610220608996212495445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13992813627478661616660593 10494610220608996212495445)
              ·
                refine ⟨122983713522761674365181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10494610220608996212495445 122983713522761674365181)
                ·
                  rfl

theorem cell22_3233384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 8].length) (baseStart_3233384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233384 prefixEnd_3233384 := by exact prefixLift 3233384
  have htrace : WordTrace (prefixWord ++ tailWord_3233384) baseStart_3233384 baseEnd_3233384 := by
    simpa [prefixWord, tailWord_3233384, baseEnd_3233384] using wordTrace_append hprefix tailTrace_3233384
  have hstable : (prefixWord ++ tailWord_3233384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233384).length < 2 ^ (prefixWord ++ tailWord_3233384).sum := by decide
  have hdescent : baseEnd_3233384 < baseStart_3233384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233386 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_3233386 : Nat := 118140960795 + 3233386 * 2 ^ 59
def prefixEnd_3233386 : Nat := 4983230072969 + 3 ^ 40 * 3233386 * 2
def baseEnd_3233386 : Nat := 1106854106345727730736623

theorem tailTrace_3233386 : CollatzResearch.WordTrace tailWord_3233386 prefixEnd_3233386 1106854106345727730736623 := by
  unfold tailWord_3233386
  simp only [CollatzResearch.WordTrace]
  refine ⟨29482818966000553802390003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78620850576001476806373341 29482818966000553802390003)
  ·
    refine ⟨44224228449000830703585005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29482818966000553802390003 44224228449000830703585005)
    ·
      refine ⟨16584085668375311513844377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44224228449000830703585005 16584085668375311513844377)
      ·
        refine ⟨12438064251281483635383283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16584085668375311513844377 12438064251281483635383283)
        ·
          refine ⟨18657096376922225453074925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12438064251281483635383283 18657096376922225453074925)
          ·
            refine ⟨6996411141345834544903097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18657096376922225453074925 6996411141345834544903097)
            ·
              refine ⟨5247308356009375908677323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6996411141345834544903097 5247308356009375908677323)
              ·
                refine ⟨7870962534014063863015985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5247308356009375908677323 7870962534014063863015985)
                ·
                  refine ⟨5903221900510547897261989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7870962534014063863015985 5903221900510547897261989)
                  ·
                    refine ⟨1106854106345727730736623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5903221900510547897261989 1106854106345727730736623)
                    ·
                      rfl

theorem cell22_3233386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_3233386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233386 prefixEnd_3233386 := by exact prefixLift 3233386
  have htrace : WordTrace (prefixWord ++ tailWord_3233386) baseStart_3233386 baseEnd_3233386 := by
    simpa [prefixWord, tailWord_3233386, baseEnd_3233386] using wordTrace_append hprefix tailTrace_3233386
  have hstable : (prefixWord ++ tailWord_3233386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233386).length < 2 ^ (prefixWord ++ tailWord_3233386).sum := by decide
  have hdescent : baseEnd_3233386 < baseStart_3233386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233504 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_3233504 : Nat := 118140960795 + 3233504 * 2 ^ 59
def prefixEnd_3233504 : Nat := 4983230072969 + 3 ^ 40 * 3233504 * 2
def baseEnd_3233504 : Nat := 1106894500157214756286261

theorem tailTrace_3233504 : CollatzResearch.WordTrace tailWord_3233504 prefixEnd_3233504 1106894500157214756286261 := by
  unfold tailWord_3233504
  simp only [CollatzResearch.WordTrace]
  refine ⟨58967789838787360681177783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78623719785049814241570377 58967789838787360681177783)
  ·
    refine ⟨88451684758181041021766675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58967789838787360681177783 88451684758181041021766675)
    ·
      refine ⟨132677527137271561532650013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88451684758181041021766675 132677527137271561532650013)
      ·
        refine ⟨49754072676476835574743755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132677527137271561532650013 49754072676476835574743755)
        ·
          refine ⟨74631109014715253362115633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49754072676476835574743755 74631109014715253362115633)
          ·
            refine ⟨55973331761036440021586725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74631109014715253362115633 55973331761036440021586725)
            ·
              refine ⟨10494999705194332504047511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55973331761036440021586725 10494999705194332504047511)
              ·
                refine ⟨15742499557791498756071267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10494999705194332504047511 15742499557791498756071267)
                ·
                  refine ⟨23613749336687248134106901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15742499557791498756071267 23613749336687248134106901)
                  ·
                    refine ⟨1106894500157214756286261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23613749336687248134106901 1106894500157214756286261)
                    ·
                      rfl

theorem cell22_3233504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_3233504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233504 prefixEnd_3233504 := by exact prefixLift 3233504
  have htrace : WordTrace (prefixWord ++ tailWord_3233504) baseStart_3233504 baseEnd_3233504 := by
    simpa [prefixWord, tailWord_3233504, baseEnd_3233504] using wordTrace_append hprefix tailTrace_3233504
  have hstable : (prefixWord ++ tailWord_3233504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233504).length < 2 ^ (prefixWord ++ tailWord_3233504).sum := by decide
  have hdescent : baseEnd_3233504 < baseStart_3233504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233521 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_3233521 : Nat := 118140960795 + 3233521 * 2 ^ 59
def prefixEnd_3233521 : Nat := 4983230072969 + 3 ^ 40 * 3233521 * 2
def baseEnd_3233521 : Nat := 1106900319604632378611209

theorem tailTrace_3233521 : CollatzResearch.WordTrace tailWord_3233521 prefixEnd_3233521 1106900319604632378611209 := by
  unfold tailWord_3233521
  simp only [CollatzResearch.WordTrace]
  refine ⟨117936199718513133265724417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78624133145675422177149611 117936199718513133265724417)
  ·
    refine ⟨88452149788884849949293313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117936199718513133265724417 88452149788884849949293313)
    ·
      refine ⟨66339112341663637461969985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88452149788884849949293313 66339112341663637461969985)
      ·
        refine ⟨49754334256247728096477489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66339112341663637461969985 49754334256247728096477489)
        ·
          refine ⟨37315750692185796072358117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49754334256247728096477489 37315750692185796072358117)
          ·
            refine ⟨6996703254784836763567147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37315750692185796072358117 6996703254784836763567147)
            ·
              refine ⟨10495054882177255145350721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996703254784836763567147 10495054882177255145350721)
              ·
                refine ⟨7871291161632941359013041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10495054882177255145350721 7871291161632941359013041)
                ·
                  refine ⟨5903468371224706019259781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7871291161632941359013041 5903468371224706019259781)
                  ·
                    refine ⟨1106900319604632378611209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5903468371224706019259781 1106900319604632378611209)
                    ·
                      rfl

theorem cell22_3233521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_3233521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233521 prefixEnd_3233521 := by exact prefixLift 3233521
  have htrace : WordTrace (prefixWord ++ tailWord_3233521) baseStart_3233521 baseEnd_3233521 := by
    simpa [prefixWord, tailWord_3233521, baseEnd_3233521] using wordTrace_append hprefix tailTrace_3233521
  have hstable : (prefixWord ++ tailWord_3233521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233521).length < 2 ^ (prefixWord ++ tailWord_3233521).sum := by decide
  have hdescent : baseEnd_3233521 < baseStart_3233521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233540 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_3233540 : Nat := 118140960795 + 3233540 * 2 ^ 59
def prefixEnd_3233540 : Nat := 4983230072969 + 3 ^ 40 * 3233540 * 2
def baseEnd_3233540 : Nat := 1106906823692922662386151

theorem tailTrace_3233540 : CollatzResearch.WordTrace tailWord_3233540 prefixEnd_3233540 1106906823692922662386151 := by
  unfold tailWord_3233540
  simp only [CollatzResearch.WordTrace]
  refine ⟨58968446352722149755333037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78624595136962866340444049 58968446352722149755333037)
  ·
    refine ⟨22113167382270806158249889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58968446352722149755333037 22113167382270806158249889)
    ·
      refine ⟨16584875536703104618687417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22113167382270806158249889 16584875536703104618687417)
      ·
        refine ⟨12438656652527328464015563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16584875536703104618687417 12438656652527328464015563)
        ·
          refine ⟨18657984978790992696023345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12438656652527328464015563 18657984978790992696023345)
          ·
            refine ⟨13993488734093244522017509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18657984978790992696023345 13993488734093244522017509)
            ·
              refine ⟨2623779137642483347878283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13993488734093244522017509 2623779137642483347878283)
              ·
                refine ⟨3935668706463725021817425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623779137642483347878283 3935668706463725021817425)
                ·
                  refine ⟨2951751529847793766363069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3935668706463725021817425 2951751529847793766363069)
                  ·
                    refine ⟨1106906823692922662386151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951751529847793766363069 1106906823692922662386151)
                    ·
                      rfl

theorem cell22_3233540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_3233540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233540 prefixEnd_3233540 := by exact prefixLift 3233540
  have htrace : WordTrace (prefixWord ++ tailWord_3233540) baseStart_3233540 baseEnd_3233540 := by
    simpa [prefixWord, tailWord_3233540, baseEnd_3233540] using wordTrace_append hprefix tailTrace_3233540
  have hstable : (prefixWord ++ tailWord_3233540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233540).length < 2 ^ (prefixWord ++ tailWord_3233540).sum := by decide
  have hdescent : baseEnd_3233540 < baseStart_3233540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233585 : List Nat := [1, 2, 2, 3, 2, 3, 1, 4, 1, 3]
def baseStart_3233585 : Nat := 118140960795 + 3233585 * 2 ^ 59
def prefixEnd_3233585 : Nat := 4983230072969 + 3 ^ 40 * 3233585 * 2
def baseEnd_3233585 : Nat := 1106922228112557545011013

theorem tailTrace_3233585 : CollatzResearch.WordTrace tailWord_3233585 prefixEnd_3233585 1106922228112557545011013 := by
  unfold tailWord_3233585
  simp only [CollatzResearch.WordTrace]
  refine ⟨117938533990281272196054209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78625689326854181464036139 117938533990281272196054209)
  ·
    refine ⟨88453900492710954147040657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117938533990281272196054209 88453900492710954147040657)
    ·
      refine ⟨66340425369533215610280493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88453900492710954147040657 66340425369533215610280493)
      ·
        refine ⟨24877659513574955853855185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66340425369533215610280493 24877659513574955853855185)
        ·
          refine ⟨18658244635181216890391389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24877659513574955853855185 18658244635181216890391389)
          ·
            refine ⟨6996841738192956333896771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18658244635181216890391389 6996841738192956333896771)
            ·
              refine ⟨10495262607289434500845157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996841738192956333896771 10495262607289434500845157)
              ·
                refine ⟨1967861738866768968908467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10495262607289434500845157 1967861738866768968908467)
                ·
                  refine ⟨2951792608300153453362701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967861738866768968908467 2951792608300153453362701)
                  ·
                    refine ⟨1106922228112557545011013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951792608300153453362701 1106922228112557545011013)
                    ·
                      rfl

theorem cell22_3233585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_3233585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233585 prefixEnd_3233585 := by exact prefixLift 3233585
  have htrace : WordTrace (prefixWord ++ tailWord_3233585) baseStart_3233585 baseEnd_3233585 := by
    simpa [prefixWord, tailWord_3233585, baseEnd_3233585] using wordTrace_append hprefix tailTrace_3233585
  have hstable : (prefixWord ++ tailWord_3233585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233585).length < 2 ^ (prefixWord ++ tailWord_3233585).sum := by decide
  have hdescent : baseEnd_3233585 < baseStart_3233585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233598 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_3233598 : Nat := 118140960795 + 3233598 * 2 ^ 59
def prefixEnd_3233598 : Nat := 4983230072969 + 3 ^ 40 * 3233598 * 2
def baseEnd_3233598 : Nat := 368975559426076614811991

theorem tailTrace_3233598 : CollatzResearch.WordTrace tailWord_3233598 prefixEnd_3233598 368975559426076614811991 := by
  unfold tailWord_3233598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742376017404271927034681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78626005426156116944184965 14742376017404271927034681)
  ·
    refine ⟨11056782013053203945276011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14742376017404271927034681 11056782013053203945276011)
    ·
      refine ⟨16585173019579805917914017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11056782013053203945276011 16585173019579805917914017)
      ·
        refine ⟨12438879764684854438435513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16585173019579805917914017 12438879764684854438435513)
        ·
          refine ⟨9329159823513640828826635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12438879764684854438435513 9329159823513640828826635)
          ·
            refine ⟨13993739735270461243239953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9329159823513640828826635 13993739735270461243239953)
            ·
              refine ⟨10495304801452845932429965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13993739735270461243239953 10495304801452845932429965)
              ·
                refine ⟨3935739300544817224661237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10495304801452845932429965 3935739300544817224661237)
                ·
                  refine ⟨368975559426076614811991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3935739300544817224661237 368975559426076614811991)
                  ·
                    rfl

theorem cell22_3233598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_3233598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233598 prefixEnd_3233598 := by exact prefixLift 3233598
  have htrace : WordTrace (prefixWord ++ tailWord_3233598) baseStart_3233598 baseEnd_3233598 := by
    simpa [prefixWord, tailWord_3233598, baseEnd_3233598] using wordTrace_append hprefix tailTrace_3233598
  have hstable : (prefixWord ++ tailWord_3233598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233598).length < 2 ^ (prefixWord ++ tailWord_3233598).sum := by decide
  have hdescent : baseEnd_3233598 < baseStart_3233598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233658 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_3233658 : Nat := 118140960795 + 3233658 * 2 ^ 59
def prefixEnd_3233658 : Nat := 4983230072969 + 3 ^ 40 * 3233658 * 2
def baseEnd_3233658 : Nat := 1106947217504409687935789

theorem tailTrace_3233658 : CollatzResearch.WordTrace tailWord_3233658 prefixEnd_3233658 1106947217504409687935789 := by
  unfold tailWord_3233658
  simp only [CollatzResearch.WordTrace]
  refine ⟨29485299129754201415865407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78627464346011203775641085 29485299129754201415865407)
  ·
    refine ⟨44227948694631302123798111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29485299129754201415865407 44227948694631302123798111)
    ·
      refine ⟨66341923041946953185697167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44227948694631302123798111 66341923041946953185697167)
      ·
        refine ⟨99512884562920429778545751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66341923041946953185697167 99512884562920429778545751)
        ·
          refine ⟨149269326844380644667818627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99512884562920429778545751 149269326844380644667818627)
          ·
            refine ⟨223903990266570967001727941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149269326844380644667818627 223903990266570967001727941)
            ·
              refine ⟨41981998174982056312823989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223903990266570967001727941 41981998174982056312823989)
              ·
                refine ⟨3935812328904567779327249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41981998174982056312823989 3935812328904567779327249)
                ·
                  refine ⟨2951859246678425834495437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3935812328904567779327249 2951859246678425834495437)
                  ·
                    refine ⟨1106947217504409687935789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2951859246678425834495437 1106947217504409687935789)
                    ·
                      rfl

theorem cell22_3233658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_3233658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233658 prefixEnd_3233658 := by exact prefixLift 3233658
  have htrace : WordTrace (prefixWord ++ tailWord_3233658) baseStart_3233658 baseEnd_3233658 := by
    simpa [prefixWord, tailWord_3233658, baseEnd_3233658] using wordTrace_append hprefix tailTrace_3233658
  have hstable : (prefixWord ++ tailWord_3233658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233658).length < 2 ^ (prefixWord ++ tailWord_3233658).sum := by decide
  have hdescent : baseEnd_3233658 < baseStart_3233658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233662 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3233662 : Nat := 118140960795 + 3233662 * 2 ^ 59
def prefixEnd_3233662 : Nat := 4983230072969 + 3 ^ 40 * 3233662 * 2
def baseEnd_3233662 : Nat := 1106948586786155010835777

theorem tailTrace_3233662 : CollatzResearch.WordTrace tailWord_3233662 prefixEnd_3233662 1106948586786155010835777 := by
  unfold tailWord_3233662
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742667801375289293325905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78627561607334876231071493 14742667801375289293325905)
  ·
    refine ⟨11057000851031466969994429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14742667801375289293325905 11057000851031466969994429)
    ·
      refine ⟨4146375319136800113747911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11057000851031466969994429 4146375319136800113747911)
      ·
        refine ⟨6219562978705200170621867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146375319136800113747911 6219562978705200170621867)
        ·
          refine ⟨9329344468057800255932801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6219562978705200170621867 9329344468057800255932801)
          ·
            refine ⟨6997008351043350191949601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9329344468057800255932801 6997008351043350191949601)
            ·
              refine ⟨5247756263282512643962201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6997008351043350191949601 5247756263282512643962201)
              ·
                refine ⟨3935817197461884482971651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5247756263282512643962201 3935817197461884482971651)
                ·
                  refine ⟨5903725796192826724457477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935817197461884482971651 5903725796192826724457477)
                  ·
                    refine ⟨1106948586786155010835777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5903725796192826724457477 1106948586786155010835777)
                    ·
                      rfl

theorem cell22_3233662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3233662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233662 prefixEnd_3233662 := by exact prefixLift 3233662
  have htrace : WordTrace (prefixWord ++ tailWord_3233662) baseStart_3233662 baseEnd_3233662 := by
    simpa [prefixWord, tailWord_3233662, baseEnd_3233662] using wordTrace_append hprefix tailTrace_3233662
  have hstable : (prefixWord ++ tailWord_3233662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233662).length < 2 ^ (prefixWord ++ tailWord_3233662).sum := by decide
  have hdescent : baseEnd_3233662 < baseStart_3233662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233694 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_3233694 : Nat := 118140960795 + 3233694 * 2 ^ 59
def prefixEnd_3233694 : Nat := 4983230072969 + 3 ^ 40 * 3233694 * 2
def baseEnd_3233694 : Nat := 368986513680039198011893

theorem tailTrace_3233694 : CollatzResearch.WordTrace tailWord_3233694 prefixEnd_3233694 368986513680039198011893 := by
  unfold tailWord_3233694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742813693360797976471517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78628339697924255874514757 14742813693360797976471517)
  ·
    refine ⟨5528555135010299241176819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14742813693360797976471517 5528555135010299241176819)
    ·
      refine ⟨8292832702515448861765229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528555135010299241176819 8292832702515448861765229)
      ·
        refine ⟨3109812263443293323161961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8292832702515448861765229 3109812263443293323161961)
        ·
          refine ⟨2332359197582469992371471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109812263443293323161961 2332359197582469992371471)
          ·
            refine ⟨3498538796373704988557207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332359197582469992371471 3498538796373704988557207)
            ·
              refine ⟨5247808194560557482835811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498538796373704988557207 5247808194560557482835811)
              ·
                refine ⟨7871712291840836224253717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5247808194560557482835811 7871712291840836224253717)
                ·
                  refine ⟨368986513680039198011893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7871712291840836224253717 368986513680039198011893)
                  ·
                    rfl

theorem cell22_3233694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_3233694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233694 prefixEnd_3233694 := by exact prefixLift 3233694
  have htrace : WordTrace (prefixWord ++ tailWord_3233694) baseStart_3233694 baseEnd_3233694 := by
    simpa [prefixWord, tailWord_3233694, baseEnd_3233694] using wordTrace_append hprefix tailTrace_3233694
  have hstable : (prefixWord ++ tailWord_3233694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233694).length < 2 ^ (prefixWord ++ tailWord_3233694).sum := by decide
  have hdescent : baseEnd_3233694 < baseStart_3233694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233748 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3233748 : Nat := 118140960795 + 3233748 * 2 ^ 59
def prefixEnd_3233748 : Nat := 4983230072969 + 3 ^ 40 * 3233748 * 2
def baseEnd_3233748 : Nat := 1106978026343679453185513

theorem tailTrace_3233748 : CollatzResearch.WordTrace tailWord_3233748 prefixEnd_3233748 1106978026343679453185513 := by
  unfold tailWord_3233748
  simp only [CollatzResearch.WordTrace]
  refine ⟨58972239544345375517118949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78629652725793834022825265 58972239544345375517118949)
  ·
    refine ⟨11057294914564757909459803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58972239544345375517118949 11057294914564757909459803)
    ·
      refine ⟨16585942371847136864189705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11057294914564757909459803 16585942371847136864189705)
      ·
        refine ⟨12439456778885352648142279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16585942371847136864189705 12439456778885352648142279)
        ·
          refine ⟨18659185168328028972213419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12439456778885352648142279 18659185168328028972213419)
          ·
            refine ⟨27988777752492043458320129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18659185168328028972213419 27988777752492043458320129)
            ·
              refine ⟨20991583314369032593740097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27988777752492043458320129 20991583314369032593740097)
              ·
                refine ⟨15743687485776774445305073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20991583314369032593740097 15743687485776774445305073)
                ·
                  refine ⟨11807765614332580833978805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15743687485776774445305073 11807765614332580833978805)
                  ·
                    refine ⟨1106978026343679453185513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11807765614332580833978805 1106978026343679453185513)
                    ·
                      rfl

theorem cell22_3233748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3233748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233748 prefixEnd_3233748 := by exact prefixLift 3233748
  have htrace : WordTrace (prefixWord ++ tailWord_3233748) baseStart_3233748 baseEnd_3233748 := by
    simpa [prefixWord, tailWord_3233748, baseEnd_3233748] using wordTrace_append hprefix tailTrace_3233748
  have hstable : (prefixWord ++ tailWord_3233748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233748).length < 2 ^ (prefixWord ++ tailWord_3233748).sum := by decide
  have hdescent : baseEnd_3233748 < baseStart_3233748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233763 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 3, 4]
def baseStart_3233763 : Nat := 118140960795 + 3233763 * 2 ^ 59
def prefixEnd_3233763 : Nat := 4983230072969 + 3 ^ 40 * 3233763 * 2
def baseEnd_3233763 : Nat := 1106983161150224414060467

theorem tailTrace_3233763 : CollatzResearch.WordTrace tailWord_3233763 prefixEnd_3233763 1106983161150224414060467 := by
  unfold tailWord_3233763
  simp only [CollatzResearch.WordTrace]
  refine ⟨117945026183636408596033943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78630017455757605730689295 117945026183636408596033943)
  ·
    refine ⟨176917539275454612894050915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117945026183636408596033943 176917539275454612894050915)
    ·
      refine ⟨265376308913181919341076373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176917539275454612894050915 265376308913181919341076373)
      ·
        refine ⟨12439514480305402469112955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 265376308913181919341076373 12439514480305402469112955)
        ·
          refine ⟨18659271720458103703669433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12439514480305402469112955 18659271720458103703669433)
          ·
            refine ⟨13994453790343577777752075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18659271720458103703669433 13994453790343577777752075)
            ·
              refine ⟨20991680685515366666628113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13994453790343577777752075 20991680685515366666628113)
              ·
                refine ⟨15743760514136524999971085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20991680685515366666628113 15743760514136524999971085)
                ·
                  refine ⟨5903910192801196874989157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15743760514136524999971085 5903910192801196874989157)
                  ·
                    refine ⟨1106983161150224414060467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5903910192801196874989157 1106983161150224414060467)
                    ·
                      rfl

theorem cell22_3233763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 4].length) (baseStart_3233763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233763 prefixEnd_3233763 := by exact prefixLift 3233763
  have htrace : WordTrace (prefixWord ++ tailWord_3233763) baseStart_3233763 baseEnd_3233763 := by
    simpa [prefixWord, tailWord_3233763, baseEnd_3233763] using wordTrace_append hprefix tailTrace_3233763
  have hstable : (prefixWord ++ tailWord_3233763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233763).length < 2 ^ (prefixWord ++ tailWord_3233763).sum := by decide
  have hdescent : baseEnd_3233763 < baseStart_3233763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233793 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3233793 : Nat := 118140960795 + 3233793 * 2 ^ 59
def prefixEnd_3233793 : Nat := 4983230072969 + 3 ^ 40 * 3233793 * 2
def baseEnd_3233793 : Nat := 1106993430763314335810375

theorem tailTrace_3233793 : CollatzResearch.WordTrace tailWord_3233793 prefixEnd_3233793 1106993430763314335810375 := by
  unfold tailWord_3233793
  simp only [CollatzResearch.WordTrace]
  refine ⟨117946120373527723719626033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78630746915685149146417355 117946120373527723719626033)
  ·
    refine ⟨88459590280145792789719525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117946120373527723719626033 88459590280145792789719525)
    ·
      refine ⟨16586173177527336148072411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88459590280145792789719525 16586173177527336148072411)
      ·
        refine ⟨24879259766291004222108617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16586173177527336148072411 24879259766291004222108617)
        ·
          refine ⟨18659444824718253166581463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24879259766291004222108617 18659444824718253166581463)
          ·
            refine ⟨27989167237077379749872195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18659444824718253166581463 27989167237077379749872195)
            ·
              refine ⟨41983750855616069624808293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27989167237077379749872195 41983750855616069624808293)
              ·
                refine ⟨7871953285428013054651555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41983750855616069624808293 7871953285428013054651555)
                ·
                  refine ⟨11807929928142019581977333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7871953285428013054651555 11807929928142019581977333)
                  ·
                    refine ⟨1106993430763314335810375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11807929928142019581977333 1106993430763314335810375)
                    ·
                      rfl

theorem cell22_3233793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3233793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233793 prefixEnd_3233793 := by exact prefixLift 3233793
  have htrace : WordTrace (prefixWord ++ tailWord_3233793) baseStart_3233793 baseEnd_3233793 := by
    simpa [prefixWord, tailWord_3233793, baseEnd_3233793] using wordTrace_append hprefix tailTrace_3233793
  have hstable : (prefixWord ++ tailWord_3233793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233793).length < 2 ^ (prefixWord ++ tailWord_3233793).sum := by decide
  have hdescent : baseEnd_3233793 < baseStart_3233793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233797 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 1, 4]
def baseStart_3233797 : Nat := 118140960795 + 3233797 * 2 ^ 59
def prefixEnd_3233797 : Nat := 4983230072969 + 3 ^ 40 * 3233797 * 2
def baseEnd_3233797 : Nat := 1106994800045059658710363

theorem tailTrace_3233797 : CollatzResearch.WordTrace tailWord_3233797 prefixEnd_3233797 1106994800045059658710363 := by
  unfold tailWord_3233797
  simp only [CollatzResearch.WordTrace]
  refine ⟨117946266265513232402771645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78630844177008821601847763 117946266265513232402771645)
  ·
    refine ⟨44229849849567462151039367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117946266265513232402771645 44229849849567462151039367)
    ·
      refine ⟨66344774774351193226559051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44229849849567462151039367 66344774774351193226559051)
      ·
        refine ⟨99517162161526789839838577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66344774774351193226559051 99517162161526789839838577)
        ·
          refine ⟨74637871621145092379878933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99517162161526789839838577 74637871621145092379878933)
          ·
            refine ⟨3498650232241176205306825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74637871621145092379878933 3498650232241176205306825)
            ·
              refine ⟨2623987674180882153980119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3498650232241176205306825 2623987674180882153980119)
              ·
                refine ⟨3935981511271323230970179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623987674180882153980119 3935981511271323230970179)
                ·
                  refine ⟨5903972266906984846455269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935981511271323230970179 5903972266906984846455269)
                  ·
                    refine ⟨1106994800045059658710363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5903972266906984846455269 1106994800045059658710363)
                    ·
                      rfl

theorem cell22_3233797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_3233797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233797 prefixEnd_3233797 := by exact prefixLift 3233797
  have htrace : WordTrace (prefixWord ++ tailWord_3233797) baseStart_3233797 baseEnd_3233797 := by
    simpa [prefixWord, tailWord_3233797, baseEnd_3233797] using wordTrace_append hprefix tailTrace_3233797
  have hstable : (prefixWord ++ tailWord_3233797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233797).length < 2 ^ (prefixWord ++ tailWord_3233797).sum := by decide
  have hdescent : baseEnd_3233797 < baseStart_3233797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233827 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 2, 3]
def baseStart_3233827 : Nat := 118140960795 + 3233827 * 2 ^ 59
def prefixEnd_3233827 : Nat := 4983230072969 + 3 ^ 40 * 3233827 * 2
def baseEnd_3233827 : Nat := 1107005069658149580460271

theorem tailTrace_3233827 : CollatzResearch.WordTrace tailWord_3233827 prefixEnd_3233827 1107005069658149580460271 := by
  unfold tailWord_3233827
  simp only [CollatzResearch.WordTrace]
  refine ⟨117947360455404547526363735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78631573636936365017575823 117947360455404547526363735)
  ·
    refine ⟨176921040683106821289545603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117947360455404547526363735 176921040683106821289545603)
    ·
      refine ⟨265381561024660231934318405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176921040683106821289545603 265381561024660231934318405)
      ·
        refine ⟨49759042692123793487684701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265381561024660231934318405 49759042692123793487684701)
        ·
          refine ⟨18659641009546422557881763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49759042692123793487684701 18659641009546422557881763)
          ·
            refine ⟨27989461514319633836822645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18659641009546422557881763 27989461514319633836822645)
            ·
              refine ⟨2624012016967465672202123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27989461514319633836822645 2624012016967465672202123)
              ·
                refine ⟨3936018025451198508303185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624012016967465672202123 3936018025451198508303185)
                ·
                  refine ⟨2952013519088398881227389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936018025451198508303185 2952013519088398881227389)
                  ·
                    refine ⟨1107005069658149580460271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952013519088398881227389 1107005069658149580460271)
                    ·
                      rfl

theorem cell22_3233827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 3].length) (baseStart_3233827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233827 prefixEnd_3233827 := by exact prefixLift 3233827
  have htrace : WordTrace (prefixWord ++ tailWord_3233827) baseStart_3233827 baseEnd_3233827 := by
    simpa [prefixWord, tailWord_3233827, baseEnd_3233827] using wordTrace_append hprefix tailTrace_3233827
  have hstable : (prefixWord ++ tailWord_3233827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233827).length < 2 ^ (prefixWord ++ tailWord_3233827).sum := by decide
  have hdescent : baseEnd_3233827 < baseStart_3233827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233840 : List Nat := [2, 1, 1, 1, 2, 7, 2, 6]
def baseStart_3233840 : Nat := 118140960795 + 3233840 * 2 ^ 59
def prefixEnd_3233840 : Nat := 4983230072969 + 3 ^ 40 * 3233840 * 2
def baseEnd_3233840 : Nat := 123001057758202431098359

theorem tailTrace_3233840 : CollatzResearch.WordTrace tailWord_3233840 prefixEnd_3233840 123001057758202431098359 := by
  unfold tailWord_3233840
  simp only [CollatzResearch.WordTrace]
  refine ⟨58973917302178725373293487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78631889736238300497724649 58973917302178725373293487)
  ·
    refine ⟨88460875953268088059940231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58973917302178725373293487 88460875953268088059940231)
    ·
      refine ⟨132691313929902132089910347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88460875953268088059940231 132691313929902132089910347)
      ·
        refine ⟨199036970894853198134865521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132691313929902132089910347 199036970894853198134865521)
        ·
          refine ⟨149277728171139898601149141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199036970894853198134865521 149277728171139898601149141)
          ·
            refine ⟨3498696754011091373464433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 149277728171139898601149141 3498696754011091373464433)
            ·
              refine ⟨2624022565508318530098325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3498696754011091373464433 2624022565508318530098325)
              ·
                refine ⟨123001057758202431098359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2624022565508318530098325 123001057758202431098359)
                ·
                  rfl

theorem cell22_3233840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 6].length) (baseStart_3233840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233840 prefixEnd_3233840 := by exact prefixLift 3233840
  have htrace : WordTrace (prefixWord ++ tailWord_3233840) baseStart_3233840 baseEnd_3233840 := by
    simpa [prefixWord, tailWord_3233840, baseEnd_3233840] using wordTrace_append hprefix tailTrace_3233840
  have hstable : (prefixWord ++ tailWord_3233840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233840).length < 2 ^ (prefixWord ++ tailWord_3233840).sum := by decide
  have hdescent : baseEnd_3233840 < baseStart_3233840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233868 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 7]
def baseStart_3233868 : Nat := 118140960795 + 3233868 * 2 ^ 59
def prefixEnd_3233868 : Nat := 4983230072969 + 3 ^ 40 * 3233868 * 2
def baseEnd_3233868 : Nat := 369006368265346380061715

theorem tailTrace_3233868 : CollatzResearch.WordTrace tailWord_3233868 prefixEnd_3233868 369006368265346380061715 := by
  unfold tailWord_3233868
  simp only [CollatzResearch.WordTrace]
  refine ⟨58974427924128005764303129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78632570565504007685737505 58974427924128005764303129)
  ·
    refine ⟨44230820943096004323227347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58974427924128005764303129 44230820943096004323227347)
    ·
      refine ⟨66346231414644006484841021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44230820943096004323227347 66346231414644006484841021)
      ·
        refine ⟨24879836780491502431815383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66346231414644006484841021 24879836780491502431815383)
        ·
          refine ⟨37319755170737253647723075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24879836780491502431815383 37319755170737253647723075)
          ·
            refine ⟨55979632756105880471584613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37319755170737253647723075 55979632756105880471584613)
            ·
              refine ⟨10496181141769852588422115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55979632756105880471584613 10496181141769852588422115)
              ·
                refine ⟨15744271712654778882633173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10496181141769852588422115 15744271712654778882633173)
                ·
                  refine ⟨369006368265346380061715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15744271712654778882633173 369006368265346380061715)
                  ·
                    rfl

theorem cell22_3233868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_3233868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233868 prefixEnd_3233868 := by exact prefixLift 3233868
  have htrace : WordTrace (prefixWord ++ tailWord_3233868) baseStart_3233868 baseEnd_3233868 := by
    simpa [prefixWord, tailWord_3233868, baseEnd_3233868] using wordTrace_append hprefix tailTrace_3233868
  have hstable : (prefixWord ++ tailWord_3233868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233868).length < 2 ^ (prefixWord ++ tailWord_3233868).sum := by decide
  have hdescent : baseEnd_3233868 < baseStart_3233868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233878 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3233878 : Nat := 118140960795 + 3233878 * 2 ^ 59
def prefixEnd_3233878 : Nat := 4983230072969 + 3 ^ 40 * 3233878 * 2
def baseEnd_3233878 : Nat := 1107022528000402447435115

theorem tailTrace_3233878 : CollatzResearch.WordTrace tailWord_3233878 prefixEnd_3233878 1107022528000402447435115 := by
  unfold tailWord_3233878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7371826286138736452279393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78632813718813188824313525 7371826286138736452279393)
  ·
    refine ⟨5528869714604052339209545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7371826286138736452279393 5528869714604052339209545)
    ·
      refine ⟨4146652285953039254407159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5528869714604052339209545 4146652285953039254407159)
      ·
        refine ⟨6219978428929558881610739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146652285953039254407159 6219978428929558881610739)
        ·
          refine ⟨9329967643394338322416109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6219978428929558881610739 9329967643394338322416109)
          ·
            refine ⟨3498737866272876870906041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9329967643394338322416109 3498737866272876870906041)
            ·
              refine ⟨2624053399704657653179531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3498737866272876870906041 2624053399704657653179531)
              ·
                refine ⟨3936080099556986479769297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624053399704657653179531 3936080099556986479769297)
                ·
                  refine ⟨2952060074667739859826973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936080099556986479769297 2952060074667739859826973)
                  ·
                    refine ⟨1107022528000402447435115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952060074667739859826973 1107022528000402447435115)
                    ·
                      rfl

theorem cell22_3233878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3233878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233878 prefixEnd_3233878 := by exact prefixLift 3233878
  have htrace : WordTrace (prefixWord ++ tailWord_3233878) baseStart_3233878 baseEnd_3233878 := by
    simpa [prefixWord, tailWord_3233878, baseEnd_3233878] using wordTrace_append hprefix tailTrace_3233878
  have hstable : (prefixWord ++ tailWord_3233878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233878).length < 2 ^ (prefixWord ++ tailWord_3233878).sum := by decide
  have hdescent : baseEnd_3233878 < baseStart_3233878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233966 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3233966 : Nat := 118140960795 + 3233966 * 2 ^ 59
def prefixEnd_3233966 : Nat := 4983230072969 + 3 ^ 40 * 3233966 * 2
def baseEnd_3233966 : Nat := 1107052652198799551234845

theorem tailTrace_3233966 : CollatzResearch.WordTrace tailWord_3233966 prefixEnd_3233966 1107052652198799551234845 := by
  unfold tailWord_3233966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14744053775237621783209219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78634953467933982843782501 14744053775237621783209219)
  ·
    refine ⟨22116080662856432674813829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14744053775237621783209219 22116080662856432674813829)
    ·
      refine ⟨4146765124285581126527593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22116080662856432674813829 4146765124285581126527593)
      ·
        refine ⟨3110073843214185844895695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4146765124285581126527593 3110073843214185844895695)
        ·
          refine ⟨4665110764821278767343543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110073843214185844895695 4665110764821278767343543)
          ·
            refine ⟨6997666147231918151015315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665110764821278767343543 6997666147231918151015315)
            ·
              refine ⟨10496499220847877226522973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997666147231918151015315 10496499220847877226522973)
              ·
                refine ⟨3936187207817953959946115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10496499220847877226522973 3936187207817953959946115)
                ·
                  refine ⟨5904280811726930939919173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936187207817953959946115 5904280811726930939919173)
                  ·
                    refine ⟨1107052652198799551234845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904280811726930939919173 1107052652198799551234845)
                    ·
                      rfl

theorem cell22_3233966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3233966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233966 prefixEnd_3233966 := by exact prefixLift 3233966
  have htrace : WordTrace (prefixWord ++ tailWord_3233966) baseStart_3233966 baseEnd_3233966 := by
    simpa [prefixWord, tailWord_3233966, baseEnd_3233966] using wordTrace_append hprefix tailTrace_3233966
  have hstable : (prefixWord ++ tailWord_3233966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233966).length < 2 ^ (prefixWord ++ tailWord_3233966).sum := by decide
  have hdescent : baseEnd_3233966 < baseStart_3233966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233996 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 1, 5]
def baseStart_3233996 : Nat := 118140960795 + 3233996 * 2 ^ 59
def prefixEnd_3233996 : Nat := 4983230072969 + 3 ^ 40 * 3233996 * 2
def baseEnd_3233996 : Nat := 1107062921811889472984753

theorem tailTrace_3233996 : CollatzResearch.WordTrace tailWord_3233996 prefixEnd_3233996 1107062921811889472984753 := by
  unfold tailWord_3233996
  simp only [CollatzResearch.WordTrace]
  refine ⟨58976762195896144694632921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78635682927861526259510561 58976762195896144694632921)
  ·
    refine ⟨44232571646922108520974691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58976762195896144694632921 44232571646922108520974691)
    ·
      refine ⟨66348857470383162781462037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44232571646922108520974691 66348857470383162781462037)
      ·
        refine ⟨3110102693924210755381033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66348857470383162781462037 3110102693924210755381033)
        ·
          refine ⟨2332577020443158066535775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3110102693924210755381033 2332577020443158066535775)
          ·
            refine ⟨3498865530664737099803663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332577020443158066535775 3498865530664737099803663)
            ·
              refine ⟨5248298295997105649705495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498865530664737099803663 5248298295997105649705495)
              ·
                refine ⟨7872447443995658474558243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248298295997105649705495 7872447443995658474558243)
                ·
                  refine ⟨11808671165993487711837365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872447443995658474558243 11808671165993487711837365)
                  ·
                    refine ⟨1107062921811889472984753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11808671165993487711837365 1107062921811889472984753)
                    ·
                      rfl

theorem cell22_3233996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_3233996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3233996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3233996 prefixEnd_3233996 := by exact prefixLift 3233996
  have htrace : WordTrace (prefixWord ++ tailWord_3233996) baseStart_3233996 baseEnd_3233996 := by
    simpa [prefixWord, tailWord_3233996, baseEnd_3233996] using wordTrace_append hprefix tailTrace_3233996
  have hstable : (prefixWord ++ tailWord_3233996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233996).length < 2 ^ (prefixWord ++ tailWord_3233996).sum := by decide
  have hdescent : baseEnd_3233996 < baseStart_3233996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234003 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 11]
def baseStart_3234003 : Nat := 118140960795 + 3234003 * 2 ^ 59
def prefixEnd_3234003 : Nat := 4983230072969 + 3 ^ 40 * 3234003 * 2
def baseEnd_3234003 : Nat := 369021772684981262686577

theorem tailTrace_3234003 : CollatzResearch.WordTrace tailWord_3234003 prefixEnd_3234003 369021772684981262686577 := by
  unfold tailWord_3234003
  simp only [CollatzResearch.WordTrace]
  refine ⟨117953779702766929584770663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78635853135177953056513775 117953779702766929584770663)
  ·
    refine ⟨176930669554150394377155995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117953779702766929584770663 176930669554150394377155995)
    ·
      refine ⟨265396004331225591565733993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176930669554150394377155995 265396004331225591565733993)
      ·
        refine ⟨199047003248419193674300495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265396004331225591565733993 199047003248419193674300495)
        ·
          refine ⟨298570504872628790511450743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199047003248419193674300495 298570504872628790511450743)
          ·
            refine ⟨447855757308943185767176115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298570504872628790511450743 447855757308943185767176115)
            ·
              refine ⟨671783635963414778650764173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447855757308943185767176115 671783635963414778650764173)
              ·
                refine ⟨251918863486280541994036565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 671783635963414778650764173 251918863486280541994036565)
                ·
                  refine ⟨369021772684981262686577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 251918863486280541994036565 369021772684981262686577)
                  ·
                    rfl

theorem cell22_3234003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 11].length) (baseStart_3234003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234003 prefixEnd_3234003 := by exact prefixLift 3234003
  have htrace : WordTrace (prefixWord ++ tailWord_3234003) baseStart_3234003 baseEnd_3234003 := by
    simpa [prefixWord, tailWord_3234003, baseEnd_3234003] using wordTrace_append hprefix tailTrace_3234003
  have hstable : (prefixWord ++ tailWord_3234003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234003).length < 2 ^ (prefixWord ++ tailWord_3234003).sum := by decide
  have hdescent : baseEnd_3234003 < baseStart_3234003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234129 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 2, 4]
def baseStart_3234129 : Nat := 118140960795 + 3234129 * 2 ^ 59
def prefixEnd_3234129 : Nat := 4983230072969 + 3 ^ 40 * 3234129 * 2
def baseEnd_3234129 : Nat := 1107108450429921459409345

theorem tailTrace_3234129 : CollatzResearch.WordTrace tailWord_3234129 prefixEnd_3234129 1107108450429921459409345 := by
  unfold tailWord_3234129
  simp only [CollatzResearch.WordTrace]
  refine ⟨117958375300310453103857441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78638916866873635402571627 117958375300310453103857441)
  ·
    refine ⟨88468781475232839827893081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117958375300310453103857441 88468781475232839827893081)
    ·
      refine ⟨66351586106424629870919811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88468781475232839827893081 66351586106424629870919811)
      ·
        refine ⟨99527379159636944806379717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66351586106424629870919811 99527379159636944806379717)
        ·
          refine ⟨18661383592431927151196197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99527379159636944806379717 18661383592431927151196197)
          ·
            refine ⟨3499009423580986340849287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18661383592431927151196197 3499009423580986340849287)
            ·
              refine ⟨5248514135371479511273931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499009423580986340849287 5248514135371479511273931)
              ·
                refine ⟨7872771203057219266910897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248514135371479511273931 7872771203057219266910897)
                ·
                  refine ⟨5904578402292914450183173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7872771203057219266910897 5904578402292914450183173)
                  ·
                    refine ⟨1107108450429921459409345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904578402292914450183173 1107108450429921459409345)
                    ·
                      rfl

theorem cell22_3234129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_3234129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234129 prefixEnd_3234129 := by exact prefixLift 3234129
  have htrace : WordTrace (prefixWord ++ tailWord_3234129) baseStart_3234129 baseEnd_3234129 := by
    simpa [prefixWord, tailWord_3234129, baseEnd_3234129] using wordTrace_append hprefix tailTrace_3234129
  have hstable : (prefixWord ++ tailWord_3234129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234129).length < 2 ^ (prefixWord ++ tailWord_3234129).sum := by decide
  have hdescent : baseEnd_3234129 < baseStart_3234129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234155 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 7]
def baseStart_3234155 : Nat := 118140960795 + 3234155 * 2 ^ 59
def prefixEnd_3234155 : Nat := 4983230072969 + 3 ^ 40 * 3234155 * 2
def baseEnd_3234155 : Nat := 369039116920422019419755

theorem tailTrace_3234155 : CollatzResearch.WordTrace tailWord_3234155 prefixEnd_3234155 369039116920422019419755 := by
  unfold tailWord_3234155
  simp only [CollatzResearch.WordTrace]
  refine ⟨117959323598216259544303919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78639549065477506362869279 117959323598216259544303919)
  ·
    refine ⟨176938985397324389316455879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117959323598216259544303919 176938985397324389316455879)
    ·
      refine ⟨265408478095986583974683819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176938985397324389316455879 265408478095986583974683819)
      ·
        refine ⟨398112717143979875962025729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265408478095986583974683819 398112717143979875962025729)
        ·
          refine ⟨298584537857984906971519297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398112717143979875962025729 298584537857984906971519297)
          ·
            refine ⟨223938403393488680228639473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298584537857984906971519297 223938403393488680228639473)
            ·
              refine ⟨167953802545116510171479605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223938403393488680228639473 167953802545116510171479605)
              ·
                refine ⟨15745668988604672828576213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167953802545116510171479605 15745668988604672828576213)
                ·
                  refine ⟨369039116920422019419755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15745668988604672828576213 369039116920422019419755)
                  ·
                    rfl

theorem cell22_3234155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 7].length) (baseStart_3234155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234155 prefixEnd_3234155 := by exact prefixLift 3234155
  have htrace : WordTrace (prefixWord ++ tailWord_3234155) baseStart_3234155 baseEnd_3234155 := by
    simpa [prefixWord, tailWord_3234155, baseEnd_3234155] using wordTrace_append hprefix tailTrace_3234155
  have hstable : (prefixWord ++ tailWord_3234155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234155).length < 2 ^ (prefixWord ++ tailWord_3234155).sum := by decide
  have hdescent : baseEnd_3234155 < baseStart_3234155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234178 : List Nat := [3, 4, 2, 1, 2, 2, 2, 6]
def baseStart_3234178 : Nat := 118140960795 + 3234178 * 2 ^ 59
def prefixEnd_3234178 : Nat := 4983230072969 + 3 ^ 40 * 3234178 * 2
def baseEnd_3234178 : Nat := 123013913792366851659355

theorem tailTrace_3234178 : CollatzResearch.WordTrace tailWord_3234178 prefixEnd_3234178 123013913792366851659355 := by
  unfold tailWord_3234178
  simp only [CollatzResearch.WordTrace]
  refine ⟨29490040619283233618097797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78640108318088622981594125 29490040619283233618097797)
  ·
    refine ⟨5529382616115606303393337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29490040619283233618097797 5529382616115606303393337)
    ·
      refine ⟨4147036962086704727545003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5529382616115606303393337 4147036962086704727545003)
      ·
        refine ⟨6220555443130057091317505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147036962086704727545003 6220555443130057091317505)
        ·
          refine ⟨4665416582347542818488129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6220555443130057091317505 4665416582347542818488129)
          ·
            refine ⟨3499062436760657113866097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4665416582347542818488129 3499062436760657113866097)
            ·
              refine ⟨2624296827570492835399573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3499062436760657113866097 2624296827570492835399573)
              ·
                refine ⟨123013913792366851659355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2624296827570492835399573 123013913792366851659355)
                ·
                  rfl

theorem cell22_3234178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_3234178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234178 prefixEnd_3234178 := by exact prefixLift 3234178
  have htrace : WordTrace (prefixWord ++ tailWord_3234178) baseStart_3234178 baseEnd_3234178 := by
    simpa [prefixWord, tailWord_3234178, baseEnd_3234178] using wordTrace_append hprefix tailTrace_3234178
  have hstable : (prefixWord ++ tailWord_3234178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234178).length < 2 ^ (prefixWord ++ tailWord_3234178).sum := by decide
  have hdescent : baseEnd_3234178 < baseStart_3234178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234232 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_3234232 : Nat := 118140960795 + 3234232 * 2 ^ 59
def prefixEnd_3234232 : Nat := 4983230072969 + 3 ^ 40 * 3234232 * 2
def baseEnd_3234232 : Nat := 1107143709434863524084029

theorem tailTrace_3234232 : CollatzResearch.WordTrace tailWord_3234232 prefixEnd_3234232 1107143709434863524084029 := by
  unfold tailWord_3234232
  simp only [CollatzResearch.WordTrace]
  refine ⟨58981066009468650847428475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78641421345958201129904633 58981066009468650847428475)
  ·
    refine ⟨88471599014202976271142713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58981066009468650847428475 88471599014202976271142713)
    ·
      refine ⟨66353699260652232203357035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88471599014202976271142713 66353699260652232203357035)
      ·
        refine ⟨99530548890978348305035553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66353699260652232203357035 99530548890978348305035553)
        ·
          refine ⟨74647911668233761228776665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99530548890978348305035553 74647911668233761228776665)
          ·
            refine ⟨55985933751175320921582499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74647911668233761228776665 55985933751175320921582499)
            ·
              refine ⟨83978900626762981382373749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55985933751175320921582499 83978900626762981382373749)
              ·
                refine ⟨7873021933759029504597539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83978900626762981382373749 7873021933759029504597539)
                ·
                  refine ⟨11809532900638544256896309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873021933759029504597539 11809532900638544256896309)
                  ·
                    refine ⟨1107143709434863524084029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11809532900638544256896309 1107143709434863524084029)
                    ·
                      rfl

theorem cell22_3234232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_3234232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234232 prefixEnd_3234232 := by exact prefixLift 3234232
  have htrace : WordTrace (prefixWord ++ tailWord_3234232) baseStart_3234232 baseEnd_3234232 := by
    simpa [prefixWord, tailWord_3234232, baseEnd_3234232] using wordTrace_append hprefix tailTrace_3234232
  have hstable : (prefixWord ++ tailWord_3234232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234232).length < 2 ^ (prefixWord ++ tailWord_3234232).sum := by decide
  have hdescent : baseEnd_3234232 < baseStart_3234232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234236 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_3234236 : Nat := 118140960795 + 3234236 * 2 ^ 59
def prefixEnd_3234236 : Nat := 4983230072969 + 3 ^ 40 * 3234236 * 2
def baseEnd_3234236 : Nat := 1107145078716608846984017

theorem tailTrace_3234236 : CollatzResearch.WordTrace tailWord_3234236 prefixEnd_3234236 1107145078716608846984017 := by
  unfold tailWord_3234236
  simp only [CollatzResearch.WordTrace]
  refine ⟨58981138955461405189001281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78641518607281873585335041 58981138955461405189001281)
  ·
    refine ⟨44235854216596053891750961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58981138955461405189001281 44235854216596053891750961)
    ·
      refine ⟨33176890662447040418813221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44235854216596053891750961 33176890662447040418813221)
      ·
        refine ⟨6220666999208820078527479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33176890662447040418813221 6220666999208820078527479)
        ·
          refine ⟨9331000498813230117791219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220666999208820078527479 9331000498813230117791219)
          ·
            refine ⟨13996500748219845176686829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331000498813230117791219 13996500748219845176686829)
            ·
              refine ⟨5248687780582441941257561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13996500748219845176686829 5248687780582441941257561)
              ·
                refine ⟨3936515835436831455943171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248687780582441941257561 3936515835436831455943171)
                ·
                  refine ⟨5904773753155247183914757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936515835436831455943171 5904773753155247183914757)
                  ·
                    refine ⟨1107145078716608846984017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904773753155247183914757 1107145078716608846984017)
                    ·
                      rfl

theorem cell22_3234236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_3234236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234236 prefixEnd_3234236 := by exact prefixLift 3234236
  have htrace : WordTrace (prefixWord ++ tailWord_3234236) baseStart_3234236 baseEnd_3234236 := by
    simpa [prefixWord, tailWord_3234236, baseEnd_3234236] using wordTrace_append hprefix tailTrace_3234236
  have hstable : (prefixWord ++ tailWord_3234236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234236).length < 2 ^ (prefixWord ++ tailWord_3234236).sum := by decide
  have hdescent : baseEnd_3234236 < baseStart_3234236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234266 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_3234266 : Nat := 118140960795 + 3234266 * 2 ^ 59
def prefixEnd_3234266 : Nat := 4983230072969 + 3 ^ 40 * 3234266 * 2
def baseEnd_3234266 : Nat := 1107155348329698768733925

theorem tailTrace_3234266 : CollatzResearch.WordTrace tailWord_3234266 prefixEnd_3234266 1107155348329698768733925 := by
  unfold tailWord_3234266
  simp only [CollatzResearch.WordTrace]
  refine ⟨29490843025203531375398663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78642248067209417001063101 29490843025203531375398663)
  ·
    refine ⟨44236264537805297063097995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29490843025203531375398663 44236264537805297063097995)
    ·
      refine ⟨66354396806707945594646993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44236264537805297063097995 66354396806707945594646993)
      ·
        refine ⟨49765797605030959195985245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66354396806707945594646993 49765797605030959195985245)
        ·
          refine ⟨18662174101886609698494467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49765797605030959195985245 18662174101886609698494467)
          ·
            refine ⟨27993261152829914547741701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18662174101886609698494467 27993261152829914547741701)
            ·
              refine ⟨5248736466155608977701569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27993261152829914547741701 5248736466155608977701569)
              ·
                refine ⟨3936552349616706733276177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248736466155608977701569 3936552349616706733276177)
                ·
                  refine ⟨2952414262212530049957133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936552349616706733276177 2952414262212530049957133)
                  ·
                    refine ⟨1107155348329698768733925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952414262212530049957133 1107155348329698768733925)
                    ·
                      rfl

theorem cell22_3234266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_3234266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234266 prefixEnd_3234266 := by exact prefixLift 3234266
  have htrace : WordTrace (prefixWord ++ tailWord_3234266) baseStart_3234266 baseEnd_3234266 := by
    simpa [prefixWord, tailWord_3234266, baseEnd_3234266] using wordTrace_append hprefix tailTrace_3234266
  have hstable : (prefixWord ++ tailWord_3234266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234266).length < 2 ^ (prefixWord ++ tailWord_3234266).sum := by decide
  have hdescent : baseEnd_3234266 < baseStart_3234266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234307 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 7]
def baseStart_3234307 : Nat := 118140960795 + 3234307 * 2 ^ 59
def prefixEnd_3234307 : Nat := 4983230072969 + 3 ^ 40 * 3234307 * 2
def baseEnd_3234307 : Nat := 369056461155862776152933

theorem tailTrace_3234307 : CollatzResearch.WordTrace tailWord_3234307 prefixEnd_3234307 369056461155862776152933 := by
  unfold tailWord_3234307
  simp only [CollatzResearch.WordTrace]
  refine ⟨117964867493665589503837175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78643244995777059669224783 117964867493665589503837175)
  ·
    refine ⟨176947301240498384255755763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117964867493665589503837175 176947301240498384255755763)
    ·
      refine ⟨265420951860747576383633645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176947301240498384255755763 265420951860747576383633645)
      ·
        refine ⟨99532856947780341143862617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265420951860747576383633645 99532856947780341143862617)
        ·
          refine ⟨74649642710835255857896963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99532856947780341143862617 74649642710835255857896963)
          ·
            refine ⟨111974464066252883786845445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74649642710835255857896963 111974464066252883786845445)
            ·
              refine ⟨20995212012422415710033521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111974464066252883786845445 20995212012422415710033521)
              ·
                refine ⟨15746409009316811782525141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20995212012422415710033521 15746409009316811782525141)
                ·
                  refine ⟨369056461155862776152933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15746409009316811782525141 369056461155862776152933)
                  ·
                    rfl

theorem cell22_3234307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 7].length) (baseStart_3234307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234307 prefixEnd_3234307 := by exact prefixLift 3234307
  have htrace : WordTrace (prefixWord ++ tailWord_3234307) baseStart_3234307 baseEnd_3234307 := by
    simpa [prefixWord, tailWord_3234307, baseEnd_3234307] using wordTrace_append hprefix tailTrace_3234307
  have hstable : (prefixWord ++ tailWord_3234307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234307).length < 2 ^ (prefixWord ++ tailWord_3234307).sum := by decide
  have hdescent : baseEnd_3234307 < baseStart_3234307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234317 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3234317 : Nat := 118140960795 + 3234317 * 2 ^ 59
def prefixEnd_3234317 : Nat := 4983230072969 + 3 ^ 40 * 3234317 * 2
def baseEnd_3234317 : Nat := 1107172806671951635708769

theorem tailTrace_3234317 : CollatzResearch.WordTrace tailWord_3234317 prefixEnd_3234317 1107172806671951635708769 := by
  unfold tailWord_3234317
  simp only [CollatzResearch.WordTrace]
  refine ⟨117965232223629361211701205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78643488149086240807800803 117965232223629361211701205)
  ·
    refine ⟨2764810130241313153399247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 117965232223629361211701205 2764810130241313153399247)
    ·
      refine ⟨4147215195361969730098871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2764810130241313153399247 4147215195361969730098871)
      ·
        refine ⟨6220822793042954595148307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147215195361969730098871 6220822793042954595148307)
        ·
          refine ⟨9331234189564431892722461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220822793042954595148307 9331234189564431892722461)
          ·
            refine ⟨3499212821086661959770923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9331234189564431892722461 3499212821086661959770923)
            ·
              refine ⟨5248819231629992939656385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499212821086661959770923 5248819231629992939656385)
              ·
                refine ⟨3936614423722494704742289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248819231629992939656385 3936614423722494704742289)
                ·
                  refine ⟨2952460817791871028556717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936614423722494704742289 2952460817791871028556717)
                  ·
                    refine ⟨1107172806671951635708769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952460817791871028556717 1107172806671951635708769)
                    ·
                      rfl

theorem cell22_3234317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3234317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234317 prefixEnd_3234317 := by exact prefixLift 3234317
  have htrace : WordTrace (prefixWord ++ tailWord_3234317) baseStart_3234317 baseEnd_3234317 := by
    simpa [prefixWord, tailWord_3234317, baseEnd_3234317] using wordTrace_append hprefix tailTrace_3234317
  have hstable : (prefixWord ++ tailWord_3234317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234317).length < 2 ^ (prefixWord ++ tailWord_3234317).sum := by decide
  have hdescent : baseEnd_3234317 < baseStart_3234317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234328 : List Nat := [2, 1, 2, 3, 3, 1, 2, 4, 1, 3]
def baseStart_3234328 : Nat := 118140960795 + 3234328 * 2 ^ 59
def prefixEnd_3234328 : Nat := 4983230072969 + 3 ^ 40 * 3234328 * 2
def baseEnd_3234328 : Nat := 1107176572196751273683735

theorem tailTrace_3234328 : CollatzResearch.WordTrace tailWord_3234328 prefixEnd_3234328 1107176572196751273683735 := by
  unfold tailWord_3234328
  simp only [CollatzResearch.WordTrace]
  refine ⟨58982816713294755045175819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78643755617726340060234425 58982816713294755045175819)
  ·
    refine ⟨88474225069942132567763729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58982816713294755045175819 88474225069942132567763729)
    ·
      refine ⟨66355668802456599425822797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88474225069942132567763729 66355668802456599425822797)
      ·
        refine ⟨24883375800921224784683549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66355668802456599425822797 24883375800921224784683549)
        ·
          refine ⟨9331265925345459294256331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24883375800921224784683549 9331265925345459294256331)
          ·
            refine ⟨13996898888018188941384497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331265925345459294256331 13996898888018188941384497)
            ·
              refine ⟨10497674166013641706038373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13996898888018188941384497 10497674166013641706038373)
              ·
                refine ⟨1968313906127557819882195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10497674166013641706038373 1968313906127557819882195)
                ·
                  refine ⟨2952470859191336729823293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968313906127557819882195 2952470859191336729823293)
                  ·
                    refine ⟨1107176572196751273683735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952470859191336729823293 1107176572196751273683735)
                    ·
                      rfl

theorem cell22_3234328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_3234328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234328 prefixEnd_3234328 := by exact prefixLift 3234328
  have htrace : WordTrace (prefixWord ++ tailWord_3234328) baseStart_3234328 baseEnd_3234328 := by
    simpa [prefixWord, tailWord_3234328, baseEnd_3234328] using wordTrace_append hprefix tailTrace_3234328
  have hstable : (prefixWord ++ tailWord_3234328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234328).length < 2 ^ (prefixWord ++ tailWord_3234328).sum := by decide
  have hdescent : baseEnd_3234328 < baseStart_3234328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234339 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 2, 5]
def baseStart_3234339 : Nat := 118140960795 + 3234339 * 2 ^ 59
def prefixEnd_3234339 : Nat := 4983230072969 + 3 ^ 40 * 3234339 * 2
def baseEnd_3234339 : Nat := 1107180337721550911658701

theorem tailTrace_3234339 : CollatzResearch.WordTrace tailWord_3234339 prefixEnd_3234339 1107180337721550911658701 := by
  unfold tailWord_3234339
  simp only [CollatzResearch.WordTrace]
  refine ⟨117966034629549658969002071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78644023086366439312668047 117966034629549658969002071)
  ·
    refine ⟨176949051944324488453503107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117966034629549658969002071 176949051944324488453503107)
    ·
      refine ⟨265423577916486732680254661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176949051944324488453503107 265423577916486732680254661)
      ·
        refine ⟨49766920859341262377547749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265423577916486732680254661 49766920859341262377547749)
        ·
          refine ⟨9331297661126486695790203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49766920859341262377547749 9331297661126486695790203)
          ·
            refine ⟨13996946491689730043685305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331297661126486695790203 13996946491689730043685305)
            ·
              refine ⟨10497709868767297532763979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13996946491689730043685305 10497709868767297532763979)
              ·
                refine ⟨15746564803150946299145969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10497709868767297532763979 15746564803150946299145969)
                ·
                  refine ⟨11809923602363209724359477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15746564803150946299145969 11809923602363209724359477)
                  ·
                    refine ⟨1107180337721550911658701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11809923602363209724359477 1107180337721550911658701)
                    ·
                      rfl

theorem cell22_3234339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_3234339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234339 prefixEnd_3234339 := by exact prefixLift 3234339
  have htrace : WordTrace (prefixWord ++ tailWord_3234339) baseStart_3234339 baseEnd_3234339 := by
    simpa [prefixWord, tailWord_3234339, baseEnd_3234339] using wordTrace_append hprefix tailTrace_3234339
  have hstable : (prefixWord ++ tailWord_3234339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234339).length < 2 ^ (prefixWord ++ tailWord_3234339).sum := by decide
  have hdescent : baseEnd_3234339 < baseStart_3234339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234354 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_3234354 : Nat := 118140960795 + 3234354 * 2 ^ 59
def prefixEnd_3234354 : Nat := 4983230072969 + 3 ^ 40 * 3234354 * 2
def baseEnd_3234354 : Nat := 1107185472528095872533655

theorem tailTrace_3234354 : CollatzResearch.WordTrace tailWord_3234354 prefixEnd_3234354 1107185472528095872533655 := by
  unfold tailWord_3234354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29491645431123829132699529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78644387816330211020532077 29491645431123829132699529)
  ·
    refine ⟨22118734073342871849524647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29491645431123829132699529 22118734073342871849524647)
    ·
      refine ⟨33178101110014307774286971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22118734073342871849524647 33178101110014307774286971)
      ·
        refine ⟨49767151665021461661430457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33178101110014307774286971 49767151665021461661430457)
        ·
          refine ⟨37325363748766096246072843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49767151665021461661430457 37325363748766096246072843)
          ·
            refine ⟨55988045623149144369109265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37325363748766096246072843 55988045623149144369109265)
            ·
              refine ⟨41991034217361858276831949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55988045623149144369109265 41991034217361858276831949)
              ·
                refine ⟨15746637831510696853811981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41991034217361858276831949 15746637831510696853811981)
                ·
                  refine ⟨5904989186816511320179493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15746637831510696853811981 5904989186816511320179493)
                  ·
                    refine ⟨1107185472528095872533655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904989186816511320179493 1107185472528095872533655)
                    ·
                      rfl

theorem cell22_3234354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_3234354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234354 prefixEnd_3234354 := by exact prefixLift 3234354
  have htrace : WordTrace (prefixWord ++ tailWord_3234354) baseStart_3234354 baseEnd_3234354 := by
    simpa [prefixWord, tailWord_3234354, baseEnd_3234354] using wordTrace_append hprefix tailTrace_3234354
  have hstable : (prefixWord ++ tailWord_3234354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234354).length < 2 ^ (prefixWord ++ tailWord_3234354).sum := by decide
  have hdescent : baseEnd_3234354 < baseStart_3234354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234405 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 1, 4]
def baseStart_3234405 : Nat := 118140960795 + 3234405 * 2 ^ 59
def prefixEnd_3234405 : Nat := 4983230072969 + 3 ^ 40 * 3234405 * 2
def baseEnd_3234405 : Nat := 1107202930870348739508499

theorem tailTrace_3234405 : CollatzResearch.WordTrace tailWord_3234405 prefixEnd_3234405 1107202930870348739508499 := by
  unfold tailWord_3234405
  simp only [CollatzResearch.WordTrace]
  refine ⟨117968441847310552240904669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78645627898207034827269779 117968441847310552240904669)
  ·
    refine ⟨44238165692741457090339251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117968441847310552240904669 44238165692741457090339251)
    ·
      refine ⟨66357248539112185635508877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44238165692741457090339251 66357248539112185635508877)
      ·
        refine ⟨24883968202167069613315829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66357248539112185635508877 24883968202167069613315829)
        ·
          refine ⟨2332872018953162776248359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24883968202167069613315829 2332872018953162776248359)
          ·
            refine ⟨3499308028429744164372539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332872018953162776248359 3499308028429744164372539)
            ·
              refine ⟨5248962042644616246558809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499308028429744164372539 5248962042644616246558809)
              ·
                refine ⟨3936721531983462184919107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248962042644616246558809 3936721531983462184919107)
                ·
                  refine ⟨5905082297975193277378661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936721531983462184919107 5905082297975193277378661)
                  ·
                    refine ⟨1107202930870348739508499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5905082297975193277378661 1107202930870348739508499)
                    ·
                      rfl

theorem cell22_3234405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_3234405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234405 prefixEnd_3234405 := by exact prefixLift 3234405
  have htrace : WordTrace (prefixWord ++ tailWord_3234405) baseStart_3234405 baseEnd_3234405 := by
    simpa [prefixWord, tailWord_3234405, baseEnd_3234405] using wordTrace_append hprefix tailTrace_3234405
  have hstable : (prefixWord ++ tailWord_3234405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234405).length < 2 ^ (prefixWord ++ tailWord_3234405).sum := by decide
  have hdescent : baseEnd_3234405 < baseStart_3234405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234493 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 5]
def baseStart_3234493 : Nat := 118140960795 + 3234493 * 2 ^ 59
def prefixEnd_3234493 : Nat := 4983230072969 + 3 ^ 40 * 3234493 * 2
def baseEnd_3234493 : Nat := 369077685022915281102743

theorem tailTrace_3234493 : CollatzResearch.WordTrace tailWord_3234493 prefixEnd_3234493 369077685022915281102743 := by
  unfold tailWord_3234493
  simp only [CollatzResearch.WordTrace]
  refine ⟨117971651470991743270108133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78647767647327828846738755 117971651470991743270108133)
  ·
    refine ⟨22119684650810951863145275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117971651470991743270108133 22119684650810951863145275)
    ·
      refine ⟨33179526976216427794717913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22119684650810951863145275 33179526976216427794717913)
      ·
        refine ⟨24884645232162320846038435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33179526976216427794717913 24884645232162320846038435)
        ·
          refine ⟨37326967848243481269057653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24884645232162320846038435 37326967848243481269057653)
          ·
            refine ⟨3499403235772826368974155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37326967848243481269057653 3499403235772826368974155)
            ·
              refine ⟨5249104853659239553461233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499403235772826368974155 5249104853659239553461233)
              ·
                refine ⟨3936828640244429665095925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5249104853659239553461233 3936828640244429665095925)
                ·
                  refine ⟨369077685022915281102743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3936828640244429665095925 369077685022915281102743)
                  ·
                    rfl

theorem cell22_3234493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_3234493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234493 prefixEnd_3234493 := by exact prefixLift 3234493
  have htrace : WordTrace (prefixWord ++ tailWord_3234493) baseStart_3234493 baseEnd_3234493 := by
    simpa [prefixWord, tailWord_3234493, baseEnd_3234493] using wordTrace_append hprefix tailTrace_3234493
  have hstable : (prefixWord ++ tailWord_3234493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234493).length < 2 ^ (prefixWord ++ tailWord_3234493).sum := by decide
  have hdescent : baseEnd_3234493 < baseStart_3234493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234497 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3234497 : Nat := 118140960795 + 3234497 * 2 ^ 59
def prefixEnd_3234497 : Nat := 4983230072969 + 3 ^ 40 * 3234497 * 2
def baseEnd_3234497 : Nat := 1107234424350491166208217

theorem tailTrace_3234497 : CollatzResearch.WordTrace tailWord_3234497 prefixEnd_3234497 1107234424350491166208217 := by
  unfold tailWord_3234497
  simp only [CollatzResearch.WordTrace]
  refine ⟨117971797362977251953253745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78647864908651501302169163 117971797362977251953253745)
  ·
    refine ⟨88478848022232938964940309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117971797362977251953253745 88478848022232938964940309)
    ·
      refine ⟨4147446001042169013981577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88478848022232938964940309 4147446001042169013981577)
      ·
        refine ⟨3110584500781626760486183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4147446001042169013981577 3110584500781626760486183)
        ·
          refine ⟨4665876751172440140729275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110584500781626760486183 4665876751172440140729275)
          ·
            refine ⟨6998815126758660211093913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665876751172440140729275 6998815126758660211093913)
            ·
              refine ⟨5249111345068995158320435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6998815126758660211093913 5249111345068995158320435)
              ·
                refine ⟨7873667017603492737480653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5249111345068995158320435 7873667017603492737480653)
                ·
                  refine ⟨2952625131601309776555245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7873667017603492737480653 2952625131601309776555245)
                  ·
                    refine ⟨1107234424350491166208217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952625131601309776555245 1107234424350491166208217)
                    ·
                      rfl

theorem cell22_3234497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3234497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234497 prefixEnd_3234497 := by exact prefixLift 3234497
  have htrace : WordTrace (prefixWord ++ tailWord_3234497) baseStart_3234497 baseEnd_3234497 := by
    simpa [prefixWord, tailWord_3234497, baseEnd_3234497] using wordTrace_append hprefix tailTrace_3234497
  have hstable : (prefixWord ++ tailWord_3234497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234497).length < 2 ^ (prefixWord ++ tailWord_3234497).sum := by decide
  have hdescent : baseEnd_3234497 < baseStart_3234497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234615 : List Nat := [1, 1, 3, 1, 2, 1, 5, 4, 1, 3]
def baseStart_3234615 : Nat := 118140960795 + 3234615 * 2 ^ 59
def prefixEnd_3234615 : Nat := 4983230072969 + 3 ^ 40 * 3234615 * 2
def baseEnd_3234615 : Nat := 1107274818161978191757855

theorem tailTrace_3234615 : CollatzResearch.WordTrace tailWord_3234615 prefixEnd_3234615 1107274818161978191757855 := by
  unfold tailWord_3234615
  simp only [CollatzResearch.WordTrace]
  refine ⟨117976101176549758106049299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78650734117699838737366199 117976101176549758106049299)
  ·
    refine ⟨176964151764824637159073949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117976101176549758106049299 176964151764824637159073949)
    ·
      refine ⟨66361556911809238934652731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176964151764824637159073949 66361556911809238934652731)
      ·
        refine ⟨99542335367713858401979097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66361556911809238934652731 99542335367713858401979097)
        ·
          refine ⟨74656751525785393801484323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99542335367713858401979097 74656751525785393801484323)
          ·
            refine ⟨111985127288678090702226485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74656751525785393801484323 111985127288678090702226485)
            ·
              refine ⟨10498605683313571003333733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111985127288678090702226485 10498605683313571003333733)
              ·
                refine ⟨1968488565621294563125075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10498605683313571003333733 1968488565621294563125075)
                ·
                  refine ⟨2952732848431941844687613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968488565621294563125075 2952732848431941844687613)
                  ·
                    refine ⟨1107274818161978191757855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952732848431941844687613 1107274818161978191757855)
                    ·
                      rfl

theorem cell22_3234615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_3234615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234615 prefixEnd_3234615 := by exact prefixLift 3234615
  have htrace : WordTrace (prefixWord ++ tailWord_3234615) baseStart_3234615 baseEnd_3234615 := by
    simpa [prefixWord, tailWord_3234615, baseEnd_3234615] using wordTrace_append hprefix tailTrace_3234615
  have hstable : (prefixWord ++ tailWord_3234615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234615).length < 2 ^ (prefixWord ++ tailWord_3234615).sum := by decide
  have hdescent : baseEnd_3234615 < baseStart_3234615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234656 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 8]
def baseStart_3234656 : Nat := 118140960795 + 3234656 * 2 ^ 59
def prefixEnd_3234656 : Nat := 4983230072969 + 3 ^ 40 * 3234656 * 2
def baseEnd_3234656 : Nat := 369096284433289250494243

theorem tailTrace_3234656 : CollatzResearch.WordTrace tailWord_3234656 prefixEnd_3234656 369096284433289250494243 := by
  unfold tailWord_3234656
  simp only [CollatzResearch.WordTrace]
  refine ⟨58988798284700611054145911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78651731046267481405527881 58988798284700611054145911)
  ·
    refine ⟨88483197427050916581218867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58988798284700611054145911 88483197427050916581218867)
    ·
      refine ⟨132724796140576374871828301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88483197427050916581218867 132724796140576374871828301)
      ·
        refine ⟨49771798552716140576935613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132724796140576374871828301 49771798552716140576935613)
        ·
          refine ⟨18664424457268552716350855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49771798552716140576935613 18664424457268552716350855)
          ·
            refine ⟨27996636685902829074526283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18664424457268552716350855 27996636685902829074526283)
            ·
              refine ⟨41994955028854243611789425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27996636685902829074526283 41994955028854243611789425)
              ·
                refine ⟨31496216271640682708842069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41994955028854243611789425 31496216271640682708842069)
                ·
                  refine ⟨369096284433289250494243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31496216271640682708842069 369096284433289250494243)
                  ·
                    rfl

theorem cell22_3234656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_3234656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234656 prefixEnd_3234656 := by exact prefixLift 3234656
  have htrace : WordTrace (prefixWord ++ tailWord_3234656) baseStart_3234656 baseEnd_3234656 := by
    simpa [prefixWord, tailWord_3234656, baseEnd_3234656] using wordTrace_append hprefix tailTrace_3234656
  have hstable : (prefixWord ++ tailWord_3234656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234656).length < 2 ^ (prefixWord ++ tailWord_3234656).sum := by decide
  have hdescent : baseEnd_3234656 < baseStart_3234656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234671 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 3, 5]
def baseStart_3234671 : Nat := 118140960795 + 3234671 * 2 ^ 59
def prefixEnd_3234671 : Nat := 4983230072969 + 3 ^ 40 * 3234671 * 2
def baseEnd_3234671 : Nat := 1107293988106412712357683

theorem tailTrace_3234671 : CollatzResearch.WordTrace tailWord_3234671 prefixEnd_3234671 1107293988106412712357683 := by
  unfold tailWord_3234671
  simp only [CollatzResearch.WordTrace]
  refine ⟨117978143664346879670087867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78652095776231253113391911 117978143664346879670087867)
  ·
    refine ⟨176967215496520319505131801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117978143664346879670087867 176967215496520319505131801)
    ·
      refine ⟨132725411622390239628848851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176967215496520319505131801 132725411622390239628848851)
      ·
        refine ⟨199088117433585359443273277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132725411622390239628848851 199088117433585359443273277)
        ·
          refine ⟨74658044037594509791227479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199088117433585359443273277 74658044037594509791227479)
          ·
            refine ⟨111987066056391764686841219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74658044037594509791227479 111987066056391764686841219)
            ·
              refine ⟨167980599084587647030261829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111987066056391764686841219 167980599084587647030261829)
              ·
                refine ⟨31496362328360183818174093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167980599084587647030261829 31496362328360183818174093)
                ·
                  refine ⟨11811135873135068931815285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31496362328360183818174093 11811135873135068931815285)
                  ·
                    refine ⟨1107293988106412712357683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11811135873135068931815285 1107293988106412712357683)
                    ·
                      rfl

theorem cell22_3234671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_3234671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234671 prefixEnd_3234671 := by exact prefixLift 3234671
  have htrace : WordTrace (prefixWord ++ tailWord_3234671) baseStart_3234671 baseEnd_3234671 := by
    simpa [prefixWord, tailWord_3234671, baseEnd_3234671] using wordTrace_append hprefix tailTrace_3234671
  have hstable : (prefixWord ++ tailWord_3234671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234671).length < 2 ^ (prefixWord ++ tailWord_3234671).sum := by decide
  have hdescent : baseEnd_3234671 < baseStart_3234671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234673 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 6]
def baseStart_3234673 : Nat := 118140960795 + 3234673 * 2 ^ 59
def prefixEnd_3234673 : Nat := 4983230072969 + 3 ^ 40 * 3234673 * 2
def baseEnd_3234673 : Nat := 369098224249095124602559

theorem tailTrace_3234673 : CollatzResearch.WordTrace tailWord_3234673 prefixEnd_3234673 369098224249095124602559 := by
  unfold tailWord_3234673
  simp only [CollatzResearch.WordTrace]
  refine ⟨117978216610339634011660673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78652144406893089341107115 117978216610339634011660673)
  ·
    refine ⟨88483662457754725508745505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117978216610339634011660673 88483662457754725508745505)
    ·
      refine ⟨66362746843316044131559129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88483662457754725508745505 66362746843316044131559129)
      ·
        refine ⟨49772060132487033098669347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66362746843316044131559129 49772060132487033098669347)
        ·
          refine ⟨74658090198730549648004021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49772060132487033098669347 74658090198730549648004021)
          ·
            refine ⟨6999195956130989029500377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74658090198730549648004021 6999195956130989029500377)
            ·
              refine ⟨5249396967098241772125283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6999195956130989029500377 5249396967098241772125283)
              ·
                refine ⟨7874095450647362658187925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5249396967098241772125283 7874095450647362658187925)
                ·
                  refine ⟨369098224249095124602559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7874095450647362658187925 369098224249095124602559)
                  ·
                    rfl

theorem cell22_3234673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_3234673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234673 prefixEnd_3234673 := by exact prefixLift 3234673
  have htrace : WordTrace (prefixWord ++ tailWord_3234673) baseStart_3234673 baseEnd_3234673 := by
    simpa [prefixWord, tailWord_3234673, baseEnd_3234673] using wordTrace_append hprefix tailTrace_3234673
  have hstable : (prefixWord ++ tailWord_3234673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234673).length < 2 ^ (prefixWord ++ tailWord_3234673).sum := by decide
  have hdescent : baseEnd_3234673 < baseStart_3234673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234731 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 1, 8]
def baseStart_3234731 : Nat := 118140960795 + 3234731 * 2 ^ 59
def prefixEnd_3234731 : Nat := 4983230072969 + 3 ^ 40 * 3234731 * 2
def baseEnd_3234731 : Nat := 1107314527332592555857499

theorem tailTrace_3234731 : CollatzResearch.WordTrace tailWord_3234731 prefixEnd_3234731 1107314527332592555857499 := by
  unfold tailWord_3234731
  simp only [CollatzResearch.WordTrace]
  refine ⟨117980332044129509917272047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78653554696086339944848031 117980332044129509917272047)
  ·
    refine ⟨176970498066194264875908071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117980332044129509917272047 176970498066194264875908071)
    ·
      refine ⟨265455747099291397313862107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176970498066194264875908071 265455747099291397313862107)
      ·
        refine ⟨398183620648937095970793161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265455747099291397313862107 398183620648937095970793161)
        ·
          refine ⟨298637715486702821978094871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398183620648937095970793161 298637715486702821978094871)
          ·
            refine ⟨447956573230054232967142307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298637715486702821978094871 447956573230054232967142307)
            ·
              refine ⟨671934859845081349450713461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447956573230054232967142307 671934859845081349450713461)
              ·
                refine ⟨62993893110476376511004387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 671934859845081349450713461 62993893110476376511004387)
                ·
                  refine ⟨94490839665714564766506581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62993893110476376511004387 94490839665714564766506581)
                  ·
                    refine ⟨1107314527332592555857499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94490839665714564766506581 1107314527332592555857499)
                    ·
                      rfl

theorem cell22_3234731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_3234731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234731 prefixEnd_3234731 := by exact prefixLift 3234731
  have htrace : WordTrace (prefixWord ++ tailWord_3234731) baseStart_3234731 baseEnd_3234731 := by
    simpa [prefixWord, tailWord_3234731, baseEnd_3234731] using wordTrace_append hprefix tailTrace_3234731
  have hstable : (prefixWord ++ tailWord_3234731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234731).length < 2 ^ (prefixWord ++ tailWord_3234731).sum := by decide
  have hdescent : baseEnd_3234731 < baseStart_3234731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234750 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_3234750 : Nat := 118140960795 + 3234750 * 2 ^ 59
def prefixEnd_3234750 : Nat := 4983230072969 + 3 ^ 40 * 3234750 * 2
def baseEnd_3234750 : Nat := 1107321031420882839632441

theorem tailTrace_3234750 : CollatzResearch.WordTrace tailWord_3234750 prefixEnd_3234750 1107321031420882839632441 := by
  unfold tailWord_3234750
  simp only [CollatzResearch.WordTrace]
  refine ⟨14747628128882584520276713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78654016687373784108142469 14747628128882584520276713)
  ·
    refine ⟨11060721096661938390207535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14747628128882584520276713 11060721096661938390207535)
    ·
      refine ⟨16591081644992907585311303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11060721096661938390207535 16591081644992907585311303)
      ·
        refine ⟨24886622467489361377966955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16591081644992907585311303 24886622467489361377966955)
        ·
          refine ⟨37329933701234042066950433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24886622467489361377966955 37329933701234042066950433)
          ·
            refine ⟨27997450275925531550212825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37329933701234042066950433 27997450275925531550212825)
            ·
              refine ⟨20998087706944148662659619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27997450275925531550212825 20998087706944148662659619)
              ·
                refine ⟨31497131560416222993989429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20998087706944148662659619 31497131560416222993989429)
                ·
                  refine ⟨2952856083789020905686509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31497131560416222993989429 2952856083789020905686509)
                  ·
                    refine ⟨1107321031420882839632441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952856083789020905686509 1107321031420882839632441)
                    ·
                      rfl

theorem cell22_3234750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_3234750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234750 prefixEnd_3234750 := by exact prefixLift 3234750
  have htrace : WordTrace (prefixWord ++ tailWord_3234750) baseStart_3234750 baseEnd_3234750 := by
    simpa [prefixWord, tailWord_3234750, baseEnd_3234750] using wordTrace_append hprefix tailTrace_3234750
  have hstable : (prefixWord ++ tailWord_3234750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234750).length < 2 ^ (prefixWord ++ tailWord_3234750).sum := by decide
  have hdescent : baseEnd_3234750 < baseStart_3234750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234818 : List Nat := [3, 4, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3234818 : Nat := 118140960795 + 3234818 * 2 ^ 59
def prefixEnd_3234818 : Nat := 4983230072969 + 3 ^ 40 * 3234818 * 2
def baseEnd_3234818 : Nat := 1107344309210553328932233

theorem tailTrace_3234818 : CollatzResearch.WordTrace tailWord_3234818 prefixEnd_3234818 1107344309210553328932233 := by
  unfold tailWord_3234818
  simp only [CollatzResearch.WordTrace]
  refine ⟨29495876298703580943922277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78655670129876215850459405 29495876298703580943922277)
  ·
    refine ⟨5530476806006921426985427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29495876298703580943922277 5530476806006921426985427)
    ·
      refine ⟨8295715209010382140478141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5530476806006921426985427 8295715209010382140478141)
      ·
        refine ⟨3110893203378893302679303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8295715209010382140478141 3110893203378893302679303)
        ·
          refine ⟨4666339805068339954018955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110893203378893302679303 4666339805068339954018955)
          ·
            refine ⟨6999509707602509931028433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666339805068339954018955 6999509707602509931028433)
            ·
              refine ⟨5249632280701882448271325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6999509707602509931028433 5249632280701882448271325)
              ·
                refine ⟨1968612105263205918101747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5249632280701882448271325 1968612105263205918101747)
                ·
                  refine ⟨2952918157894808877152621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968612105263205918101747 2952918157894808877152621)
                  ·
                    refine ⟨1107344309210553328932233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952918157894808877152621 1107344309210553328932233)
                    ·
                      rfl

theorem cell22_3234818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3234818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234818 prefixEnd_3234818 := by exact prefixLift 3234818
  have htrace : WordTrace (prefixWord ++ tailWord_3234818) baseStart_3234818 baseEnd_3234818 := by
    simpa [prefixWord, tailWord_3234818, baseEnd_3234818] using wordTrace_append hprefix tailTrace_3234818
  have hstable : (prefixWord ++ tailWord_3234818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234818).length < 2 ^ (prefixWord ++ tailWord_3234818).sum := by decide
  have hdescent : baseEnd_3234818 < baseStart_3234818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234827 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 1, 4]
def baseStart_3234827 : Nat := 118140960795 + 3234827 * 2 ^ 59
def prefixEnd_3234827 : Nat := 4983230072969 + 3 ^ 40 * 3234827 * 2
def baseEnd_3234827 : Nat := 1107347390094480305457205

theorem tailTrace_3234827 : CollatzResearch.WordTrace tailWord_3234827 prefixEnd_3234827 1107347390094480305457205 := by
  unfold tailWord_3234827
  simp only [CollatzResearch.WordTrace]
  refine ⟨117983833451781718312766735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78655888967854478875177823 117983833451781718312766735)
  ·
    refine ⟨176975750177672577469150103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117983833451781718312766735 176975750177672577469150103)
    ·
      refine ⟨265463625266508866203725155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176975750177672577469150103 265463625266508866203725155)
      ·
        refine ⟨398195437899763299305587733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265463625266508866203725155 398195437899763299305587733)
        ·
          refine ⟨18665411151551404654949425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 398195437899763299305587733 18665411151551404654949425)
          ·
            refine ⟨13999058363663553491212069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18665411151551404654949425 13999058363663553491212069)
            ·
              refine ⟨2624823443186916279602263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13999058363663553491212069 2624823443186916279602263)
              ·
                refine ⟨3937235164780374419403395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624823443186916279602263 3937235164780374419403395)
                ·
                  refine ⟨5905852747170561629105093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3937235164780374419403395 5905852747170561629105093)
                  ·
                    refine ⟨1107347390094480305457205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5905852747170561629105093 1107347390094480305457205)
                    ·
                      rfl

theorem cell22_3234827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 4].length) (baseStart_3234827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234827 prefixEnd_3234827 := by exact prefixLift 3234827
  have htrace : WordTrace (prefixWord ++ tailWord_3234827) baseStart_3234827 baseEnd_3234827 := by
    simpa [prefixWord, tailWord_3234827, baseEnd_3234827] using wordTrace_append hprefix tailTrace_3234827
  have hstable : (prefixWord ++ tailWord_3234827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234827).length < 2 ^ (prefixWord ++ tailWord_3234827).sum := by decide
  have hdescent : baseEnd_3234827 < baseStart_3234827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234853 : List Nat := [1, 3, 1, 2, 2, 2, 2, 9]
def baseStart_3234853 : Nat := 118140960795 + 3234853 * 2 ^ 59
def prefixEnd_3234853 : Nat := 4983230072969 + 3 ^ 40 * 3234853 * 2
def baseEnd_3234853 : Nat := 123039587825091656034125

theorem tailTrace_3234853 : CollatzResearch.WordTrace tailWord_3234853 prefixEnd_3234853 123039587825091656034125 := by
  unfold tailWord_3234853
  simp only [CollatzResearch.WordTrace]
  refine ⟨117984781749687524753213213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78656521166458349835475475 117984781749687524753213213)
  ·
    refine ⟨44244293156132821782454955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117984781749687524753213213 44244293156132821782454955)
    ·
      refine ⟨66366439734199232673682433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44244293156132821782454955 66366439734199232673682433)
      ·
        refine ⟨49774829800649424505261825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66366439734199232673682433 49774829800649424505261825)
        ·
          refine ⟨37331122350487068378946369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49774829800649424505261825 37331122350487068378946369)
          ·
            refine ⟨27998341762865301284209777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37331122350487068378946369 27998341762865301284209777)
            ·
              refine ⟨20998756322148975963157333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27998341762865301284209777 20998756322148975963157333)
              ·
                refine ⟨123039587825091656034125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20998756322148975963157333 123039587825091656034125)
                ·
                  rfl

theorem cell22_3234853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 9].length) (baseStart_3234853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234853 prefixEnd_3234853 := by exact prefixLift 3234853
  have htrace : WordTrace (prefixWord ++ tailWord_3234853) baseStart_3234853 baseEnd_3234853 := by
    simpa [prefixWord, tailWord_3234853, baseEnd_3234853] using wordTrace_append hprefix tailTrace_3234853
  have hstable : (prefixWord ++ tailWord_3234853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234853).length < 2 ^ (prefixWord ++ tailWord_3234853).sum := by decide
  have hdescent : baseEnd_3234853 < baseStart_3234853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234885 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_3234885 : Nat := 118140960795 + 3234885 * 2 ^ 59
def prefixEnd_3234885 : Nat := 4983230072969 + 3 ^ 40 * 3234885 * 2
def baseEnd_3234885 : Nat := 1107367244679787487507027

theorem tailTrace_3234885 : CollatzResearch.WordTrace tailWord_3234885 prefixEnd_3234885 1107367244679787487507027 := by
  unfold tailWord_3234885
  simp only [CollatzResearch.WordTrace]
  refine ⟨117985948885571594218378109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78657299257047729478918739 117985948885571594218378109)
  ·
    refine ⟨44244730832089347831891791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117985948885571594218378109 44244730832089347831891791)
    ·
      refine ⟨66367096248134021747837687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44244730832089347831891791 66367096248134021747837687)
      ·
        refine ⟨99550644372201032621756531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66367096248134021747837687 99550644372201032621756531)
        ·
          refine ⟨149325966558301548932634797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99550644372201032621756531 149325966558301548932634797)
          ·
            refine ⟨55997237459363080849738049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149325966558301548932634797 55997237459363080849738049)
            ·
              refine ⟨41997928094522310637303537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55997237459363080849738049 41997928094522310637303537)
              ·
                refine ⟨31498446070891732977977653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41997928094522310637303537 31498446070891732977977653)
                ·
                  refine ⟨2952979319146099966685405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31498446070891732977977653 2952979319146099966685405)
                  ·
                    refine ⟨1107367244679787487507027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2952979319146099966685405 1107367244679787487507027)
                    ·
                      rfl

theorem cell22_3234885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_3234885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234885 prefixEnd_3234885 := by exact prefixLift 3234885
  have htrace : WordTrace (prefixWord ++ tailWord_3234885) baseStart_3234885 baseEnd_3234885 := by
    simpa [prefixWord, tailWord_3234885, baseEnd_3234885] using wordTrace_append hprefix tailTrace_3234885
  have hstable : (prefixWord ++ tailWord_3234885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234885).length < 2 ^ (prefixWord ++ tailWord_3234885).sum := by decide
  have hdescent : baseEnd_3234885 < baseStart_3234885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234962 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3234962 : Nat := 118140960795 + 3234962 * 2 ^ 59
def prefixEnd_3234962 : Nat := 4983230072969 + 3 ^ 40 * 3234962 * 2
def baseEnd_3234962 : Nat := 1107393603353384953331791

theorem tailTrace_3234962 : CollatzResearch.WordTrace tailWord_3234962 prefixEnd_3234962 1107393603353384953331791 := by
  unfold tailWord_3234962
  simp only [CollatzResearch.WordTrace]
  refine ⟨29497189326573159092232785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78659171537528424245954093 29497189326573159092232785)
  ·
    refine ⟨22122891994929869319174589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29497189326573159092232785 22122891994929869319174589)
    ·
      refine ⟨8296084498098700994690471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22122891994929869319174589 8296084498098700994690471)
      ·
        refine ⟨12444126747148051492035707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8296084498098700994690471 12444126747148051492035707)
        ·
          refine ⟨18666190120722077238053561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12444126747148051492035707 18666190120722077238053561)
          ·
            refine ⟨13999642590541557928540171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18666190120722077238053561 13999642590541557928540171)
            ·
              refine ⟨20999463885812336892810257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13999642590541557928540171 20999463885812336892810257)
              ·
                refine ⟨15749597914359252669607693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20999463885812336892810257 15749597914359252669607693)
                ·
                  refine ⟨5906099217884719751102885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15749597914359252669607693 5906099217884719751102885)
                  ·
                    refine ⟨1107393603353384953331791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5906099217884719751102885 1107393603353384953331791)
                    ·
                      rfl

theorem cell22_3234962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3234962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234962 prefixEnd_3234962 := by exact prefixLift 3234962
  have htrace : WordTrace (prefixWord ++ tailWord_3234962) baseStart_3234962 baseEnd_3234962 := by
    simpa [prefixWord, tailWord_3234962, baseEnd_3234962] using wordTrace_append hprefix tailTrace_3234962
  have hstable : (prefixWord ++ tailWord_3234962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234962).length < 2 ^ (prefixWord ++ tailWord_3234962).sum := by decide
  have hdescent : baseEnd_3234962 < baseStart_3234962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234994 : List Nat := [3, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_3234994 : Nat := 118140960795 + 3234994 * 2 ^ 59
def prefixEnd_3234994 : Nat := 4983230072969 + 3 ^ 40 * 3234994 * 2
def baseEnd_3234994 : Nat := 369134852535782512177231

theorem tailTrace_3234994 : CollatzResearch.WordTrace tailWord_3234994 prefixEnd_3234994 369134852535782512177231 := by
  unfold tailWord_3234994
  simp only [CollatzResearch.WordTrace]
  refine ⟨29497481110544176458524009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78659949628117803889397357 29497481110544176458524009)
  ·
    refine ⟨22123110832908132343893007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29497481110544176458524009 22123110832908132343893007)
    ·
      refine ⟨33184666249362198515839511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22123110832908132343893007 33184666249362198515839511)
      ·
        refine ⟨49776999374043297773759267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33184666249362198515839511 49776999374043297773759267)
        ·
          refine ⟨74665499061064946660638901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49776999374043297773759267 74665499061064946660638901)
          ·
            refine ⟨6999890536974838749434897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74665499061064946660638901 6999890536974838749434897)
            ·
              refine ⟨5249917902731129062076173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6999890536974838749434897 5249917902731129062076173)
              ·
                refine ⟨1968719213524173398278565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5249917902731129062076173 1968719213524173398278565)
                ·
                  refine ⟨369134852535782512177231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1968719213524173398278565 369134852535782512177231)
                  ·
                    rfl

theorem cell22_3234994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_3234994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3234994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3234994 prefixEnd_3234994 := by exact prefixLift 3234994
  have htrace : WordTrace (prefixWord ++ tailWord_3234994) baseStart_3234994 baseEnd_3234994 := by
    simpa [prefixWord, tailWord_3234994, baseEnd_3234994] using wordTrace_append hprefix tailTrace_3234994
  have hstable : (prefixWord ++ tailWord_3234994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234994).length < 2 ^ (prefixWord ++ tailWord_3234994).sum := by decide
  have hdescent : baseEnd_3234994 < baseStart_3234994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235026 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_3235026 : Nat := 118140960795 + 3235026 * 2 ^ 59
def prefixEnd_3235026 : Nat := 4983230072969 + 3 ^ 40 * 3235026 * 2
def baseEnd_3235026 : Nat := 1107415511861310119731595

theorem tailTrace_3235026 : CollatzResearch.WordTrace tailWord_3235026 prefixEnd_3235026 1107415511861310119731595 := by
  unfold tailWord_3235026
  simp only [CollatzResearch.WordTrace]
  refine ⟨29497772894515193824815233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78660727718707183532840621 29497772894515193824815233)
  ·
    refine ⟨22123329670886395368611425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29497772894515193824815233 22123329670886395368611425)
    ·
      refine ⟨16592497253164796526458569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22123329670886395368611425 16592497253164796526458569)
      ·
        refine ⟨12444372939873597394843927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16592497253164796526458569 12444372939873597394843927)
        ·
          refine ⟨18666559409810396092265891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12444372939873597394843927 18666559409810396092265891)
          ·
            refine ⟨27999839114715594138398837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18666559409810396092265891 27999839114715594138398837)
            ·
              refine ⟨2624984917004586950474891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27999839114715594138398837 2624984917004586950474891)
              ·
                refine ⟨3937477375506880425712337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624984917004586950474891 3937477375506880425712337)
                ·
                  refine ⟨2953108031630160319284253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3937477375506880425712337 2953108031630160319284253)
                  ·
                    refine ⟨1107415511861310119731595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2953108031630160319284253 1107415511861310119731595)
                    ·
                      rfl

theorem cell22_3235026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_3235026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235026 prefixEnd_3235026 := by exact prefixLift 3235026
  have htrace : WordTrace (prefixWord ++ tailWord_3235026) baseStart_3235026 baseEnd_3235026 := by
    simpa [prefixWord, tailWord_3235026, baseEnd_3235026] using wordTrace_append hprefix tailTrace_3235026
  have hstable : (prefixWord ++ tailWord_3235026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235026).length < 2 ^ (prefixWord ++ tailWord_3235026).sum := by decide
  have hdescent : baseEnd_3235026 < baseStart_3235026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235084 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 5]
def baseStart_3235084 : Nat := 118140960795 + 3235084 * 2 ^ 59
def prefixEnd_3235084 : Nat := 4983230072969 + 3 ^ 40 * 3235084 * 2
def baseEnd_3235084 : Nat := 369145122148872433927139

theorem tailTrace_3235084 : CollatzResearch.WordTrace tailWord_3235084 prefixEnd_3235084 369145122148872433927139 := by
  unfold tailWord_3235084
  simp only [CollatzResearch.WordTrace]
  refine ⟨58996603505925325602436153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78662138007900434136581537 58996603505925325602436153)
  ·
    refine ⟨44247452629443994201827115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58996603505925325602436153 44247452629443994201827115)
    ·
      refine ⟨66371178944165991302740673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44247452629443994201827115 66371178944165991302740673)
      ·
        refine ⟨49778384208124493477055505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66371178944165991302740673 49778384208124493477055505)
        ·
          refine ⟨37333788156093370107791629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49778384208124493477055505 37333788156093370107791629)
          ·
            refine ⟨14000170558535013790421861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37333788156093370107791629 14000170558535013790421861)
            ·
              refine ⟨2625031979725315085704099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14000170558535013790421861 2625031979725315085704099)
              ·
                refine ⟨3937547969587972628556149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625031979725315085704099 3937547969587972628556149)
                ·
                  refine ⟨369145122148872433927139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3937547969587972628556149 369145122148872433927139)
                  ·
                    rfl

theorem cell22_3235084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_3235084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235084 prefixEnd_3235084 := by exact prefixLift 3235084
  have htrace : WordTrace (prefixWord ++ tailWord_3235084) baseStart_3235084 baseEnd_3235084 := by
    simpa [prefixWord, tailWord_3235084, baseEnd_3235084] using wordTrace_append hprefix tailTrace_3235084
  have hstable : (prefixWord ++ tailWord_3235084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235084).length < 2 ^ (prefixWord ++ tailWord_3235084).sum := by decide
  have hdescent : baseEnd_3235084 < baseStart_3235084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235159 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 2, 4]
def baseStart_3235159 : Nat := 118140960795 + 3235159 * 2 ^ 59
def prefixEnd_3235159 : Nat := 4983230072969 + 3 ^ 40 * 3235159 * 2
def baseEnd_3235159 : Nat := 1107461040479342106156187

theorem tailTrace_3235159 : CollatzResearch.WordTrace tailWord_3235159 prefixEnd_3235159 1107461040479342106156187 := by
  unfold tailWord_3235159
  simp only [CollatzResearch.WordTrace]
  refine ⟨117995942486578939013852531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78663961657719292675901687 117995942486578939013852531)
  ·
    refine ⟨176993913729868408520778797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117995942486578939013852531 176993913729868408520778797)
    ·
      refine ⟨66372717648700653195292049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176993913729868408520778797 66372717648700653195292049)
      ·
        refine ⟨49779538236525489896469037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66372717648700653195292049 49779538236525489896469037)
        ·
          refine ⟨18667326838697058711175889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49779538236525489896469037 18667326838697058711175889)
          ·
            refine ⟨14000495129022794033381917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18667326838697058711175889 14000495129022794033381917)
            ·
              refine ⟨5250185673383547762518219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14000495129022794033381917 5250185673383547762518219)
              ·
                refine ⟨7875278510075321643777329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250185673383547762518219 7875278510075321643777329)
                ·
                  refine ⟨5906458882556491232832997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7875278510075321643777329 5906458882556491232832997)
                  ·
                    refine ⟨1107461040479342106156187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5906458882556491232832997 1107461040479342106156187)
                    ·
                      rfl

theorem cell22_3235159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_3235159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235159 prefixEnd_3235159 := by exact prefixLift 3235159
  have htrace : WordTrace (prefixWord ++ tailWord_3235159) baseStart_3235159 baseEnd_3235159 := by
    simpa [prefixWord, tailWord_3235159, baseEnd_3235159] using wordTrace_append hprefix tailTrace_3235159
  have hstable : (prefixWord ++ tailWord_3235159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235159).length < 2 ^ (prefixWord ++ tailWord_3235159).sum := by decide
  have hdescent : baseEnd_3235159 < baseStart_3235159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235165 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3235165 : Nat := 118140960795 + 3235165 * 2 ^ 59
def prefixEnd_3235165 : Nat := 4983230072969 + 3 ^ 40 * 3235165 * 2
def baseEnd_3235165 : Nat := 1107463094401960090506169

theorem tailTrace_3235165 : CollatzResearch.WordTrace tailWord_3235165 prefixEnd_3235165 1107463094401960090506169 := by
  unfold tailWord_3235165
  simp only [CollatzResearch.WordTrace]
  refine ⟨117996161324557202038570949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78664107549704801359047299 117996161324557202038570949)
  ·
    refine ⟨22124280248354475382232053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117996161324557202038570949 22124280248354475382232053)
    ·
      refine ⟨2074151273283232067084255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22124280248354475382232053 2074151273283232067084255)
      ·
        refine ⟨3111226909924848100626383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074151273283232067084255 3111226909924848100626383)
        ·
          refine ⟨4666840364887272150939575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3111226909924848100626383 4666840364887272150939575)
          ·
            refine ⟨7000260547330908226409363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666840364887272150939575 7000260547330908226409363)
            ·
              refine ⟨10500390820996362339614045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7000260547330908226409363 10500390820996362339614045)
              ·
                refine ⟨3937646557873635877355267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10500390820996362339614045 3937646557873635877355267)
                ·
                  refine ⟨5906469836810453816032901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3937646557873635877355267 5906469836810453816032901)
                  ·
                    refine ⟨1107463094401960090506169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5906469836810453816032901 1107463094401960090506169)
                    ·
                      rfl

theorem cell22_3235165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3235165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235165 prefixEnd_3235165 := by exact prefixLift 3235165
  have htrace : WordTrace (prefixWord ++ tailWord_3235165) baseStart_3235165 baseEnd_3235165 := by
    simpa [prefixWord, tailWord_3235165, baseEnd_3235165] using wordTrace_append hprefix tailTrace_3235165
  have hstable : (prefixWord ++ tailWord_3235165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235165).length < 2 ^ (prefixWord ++ tailWord_3235165).sum := by decide
  have hdescent : baseEnd_3235165 < baseStart_3235165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235240 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3235240 : Nat := 118140960795 + 3235240 * 2 ^ 59
def prefixEnd_3235240 : Nat := 4983230072969 + 3 ^ 40 * 3235240 * 2
def baseEnd_3235240 : Nat := 1107488768434684894880939

theorem tailTrace_3235240 : CollatzResearch.WordTrace tailWord_3235240 prefixEnd_3235240 1107488768434684894880939 := by
  unfold tailWord_3235240
  simp only [CollatzResearch.WordTrace]
  refine ⟨58999448399642744923775587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78665931199523659898367449 58999448399642744923775587)
  ·
    refine ⟨88499172599464117385663381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58999448399642744923775587 88499172599464117385663381)
    ·
      refine ⟨4148398715599880502452971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88499172599464117385663381 4148398715599880502452971)
      ·
        refine ⟨6222598073399820753679457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4148398715599880502452971 6222598073399820753679457)
        ·
          refine ⟨4666948555049865565259593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6222598073399820753679457 4666948555049865565259593)
          ·
            refine ⟨3500211416287399173944695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4666948555049865565259593 3500211416287399173944695)
            ·
              refine ⟨5250317124431098760917043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500211416287399173944695 5250317124431098760917043)
              ·
                refine ⟨7875475686646648141375565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250317124431098760917043 7875475686646648141375565)
                ·
                  refine ⟨2953303382492493053015837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7875475686646648141375565 2953303382492493053015837)
                  ·
                    refine ⟨1107488768434684894880939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2953303382492493053015837 1107488768434684894880939)
                    ·
                      rfl

theorem cell22_3235240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3235240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235240 prefixEnd_3235240 := by exact prefixLift 3235240
  have htrace : WordTrace (prefixWord ++ tailWord_3235240) baseStart_3235240 baseEnd_3235240 := by
    simpa [prefixWord, tailWord_3235240, baseEnd_3235240] using wordTrace_append hprefix tailTrace_3235240
  have hstable : (prefixWord ++ tailWord_3235240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235240).length < 2 ^ (prefixWord ++ tailWord_3235240).sum := by decide
  have hdescent : baseEnd_3235240 < baseStart_3235240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235249 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_3235249 : Nat := 118140960795 + 3235249 * 2 ^ 59
def prefixEnd_3235249 : Nat := 4983230072969 + 3 ^ 40 * 3235249 * 2
def baseEnd_3235249 : Nat := 1107491849318611871405911

theorem tailTrace_3235249 : CollatzResearch.WordTrace tailWord_3235249 prefixEnd_3235249 1107491849318611871405911 := by
  unfold tailWord_3235249
  simp only [CollatzResearch.WordTrace]
  refine ⟨117999225056252884384628801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78666150037501922923085867 117999225056252884384628801)
  ·
    refine ⟨88499418792189663288471601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117999225056252884384628801 88499418792189663288471601)
    ·
      refine ⟨66374564094142247466353701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88499418792189663288471601 66374564094142247466353701)
      ·
        refine ⟨12445230767651671399941319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66374564094142247466353701 12445230767651671399941319)
        ·
          refine ⟨18667846151477507099911979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12445230767651671399941319 18667846151477507099911979)
          ·
            refine ⟨28001769227216260649867969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18667846151477507099911979 28001769227216260649867969)
            ·
              refine ⟨21001326920412195487400977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28001769227216260649867969 21001326920412195487400977)
              ·
                refine ⟨15750995190309146615550733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21001326920412195487400977 15750995190309146615550733)
                ·
                  refine ⟨5906623196365929980831525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15750995190309146615550733 5906623196365929980831525)
                  ·
                    refine ⟨1107491849318611871405911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5906623196365929980831525 1107491849318611871405911)
                    ·
                      rfl

theorem cell22_3235249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_3235249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235249 prefixEnd_3235249 := by exact prefixLift 3235249
  have htrace : WordTrace (prefixWord ++ tailWord_3235249) baseStart_3235249 baseEnd_3235249 := by
    simpa [prefixWord, tailWord_3235249, baseEnd_3235249] using wordTrace_append hprefix tailTrace_3235249
  have hstable : (prefixWord ++ tailWord_3235249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235249).length < 2 ^ (prefixWord ++ tailWord_3235249).sum := by decide
  have hdescent : baseEnd_3235249 < baseStart_3235249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235253 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 5]
def baseStart_3235253 : Nat := 118140960795 + 3235253 * 2 ^ 59
def prefixEnd_3235253 : Nat := 4983230072969 + 3 ^ 40 * 3235253 * 2
def baseEnd_3235253 : Nat := 369164406200119064768633

theorem tailTrace_3235253 : CollatzResearch.WordTrace tailWord_3235253 prefixEnd_3235253 369164406200119064768633 := by
  unfold tailWord_3235253
  simp only [CollatzResearch.WordTrace]
  refine ⟨117999370948238393067774413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78666247298825595378516275 117999370948238393067774413)
  ·
    refine ⟨44249764105589397400415405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117999370948238393067774413 44249764105589397400415405)
    ·
      refine ⟨16593661539596024025155777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44249764105589397400415405 16593661539596024025155777)
      ·
        refine ⟨12445246154697018018866833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16593661539596024025155777 12445246154697018018866833)
        ·
          refine ⟨9333934616022763514150125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12445246154697018018866833 9333934616022763514150125)
          ·
            refine ⟨3500225481008536317806297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9333934616022763514150125 3500225481008536317806297)
            ·
              refine ⟨2625169110756402238354723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500225481008536317806297 2625169110756402238354723)
              ·
                refine ⟨3937753666134603357532085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625169110756402238354723 3937753666134603357532085)
                ·
                  refine ⟨369164406200119064768633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3937753666134603357532085 369164406200119064768633)
                  ·
                    rfl

theorem cell22_3235253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_3235253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235253 prefixEnd_3235253 := by exact prefixLift 3235253
  have htrace : WordTrace (prefixWord ++ tailWord_3235253) baseStart_3235253 baseEnd_3235253 := by
    simpa [prefixWord, tailWord_3235253, baseEnd_3235253] using wordTrace_append hprefix tailTrace_3235253
  have hstable : (prefixWord ++ tailWord_3235253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235253).length < 2 ^ (prefixWord ++ tailWord_3235253).sum := by decide
  have hdescent : baseEnd_3235253 < baseStart_3235253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235279 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 6, 3]
def baseStart_3235279 : Nat := 118140960795 + 3235279 * 2 ^ 59
def prefixEnd_3235279 : Nat := 4983230072969 + 3 ^ 40 * 3235279 * 2
def baseEnd_3235279 : Nat := 1107502118931701793155819

theorem tailTrace_3235279 : CollatzResearch.WordTrace tailWord_3235279 prefixEnd_3235279 1107502118931701793155819 := by
  unfold tailWord_3235279
  simp only [CollatzResearch.WordTrace]
  refine ⟨118000319246144199508220891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78666879497429466338813927 118000319246144199508220891)
  ·
    refine ⟨177000478869216299262331337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118000319246144199508220891 177000478869216299262331337)
    ·
      refine ⟨132750359151912224446748503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177000478869216299262331337 132750359151912224446748503)
      ·
        refine ⟨199125538727868336670122755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132750359151912224446748503 199125538727868336670122755)
        ·
          refine ⟨298688308091802505005184133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199125538727868336670122755 298688308091802505005184133)
          ·
            refine ⟨56004057767212969688472025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298688308091802505005184133 56004057767212969688472025)
            ·
              refine ⟨42003043325409727266354019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56004057767212969688472025 42003043325409727266354019)
              ·
                refine ⟨63004564988114590899531029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42003043325409727266354019 63004564988114590899531029)
                ·
                  refine ⟨2953338983817871448415517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63004564988114590899531029 2953338983817871448415517)
                  ·
                    refine ⟨1107502118931701793155819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2953338983817871448415517 1107502118931701793155819)
                    ·
                      rfl

theorem cell22_3235279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_3235279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235279 prefixEnd_3235279 := by exact prefixLift 3235279
  have htrace : WordTrace (prefixWord ++ tailWord_3235279) baseStart_3235279 baseEnd_3235279 := by
    simpa [prefixWord, tailWord_3235279, baseEnd_3235279] using wordTrace_append hprefix tailTrace_3235279
  have hstable : (prefixWord ++ tailWord_3235279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235279).length < 2 ^ (prefixWord ++ tailWord_3235279).sum := by decide
  have hdescent : baseEnd_3235279 < baseStart_3235279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235292 : List Nat := [2, 2, 18]
def baseStart_3235292 : Nat := 118140960795 + 3235292 * 2 ^ 59
def prefixEnd_3235292 : Nat := 4983230072969 + 3 ^ 40 * 3235292 * 2
def baseEnd_3235292 : Nat := 506404466894089662817

theorem tailTrace_3235292 : CollatzResearch.WordTrace tailWord_3235292 prefixEnd_3235292 506404466894089662817 := by
  unfold tailWord_3235292
  simp only [CollatzResearch.WordTrace]
  refine ⟨59000396697548551364222065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78667195596731401818962753 59000396697548551364222065)
  ·
    refine ⟨44250297523161413523166549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59000396697548551364222065 44250297523161413523166549)
    ·
      refine ⟨506404466894089662817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 18 44250297523161413523166549 506404466894089662817)
      ·
        rfl

theorem cell22_3235292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 18].length) (baseStart_3235292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235292 prefixEnd_3235292 := by exact prefixLift 3235292
  have htrace : WordTrace (prefixWord ++ tailWord_3235292) baseStart_3235292 baseEnd_3235292 := by
    simpa [prefixWord, tailWord_3235292, baseEnd_3235292] using wordTrace_append hprefix tailTrace_3235292
  have hstable : (prefixWord ++ tailWord_3235292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235292).length < 2 ^ (prefixWord ++ tailWord_3235292).sum := by decide
  have hdescent : baseEnd_3235292 < baseStart_3235292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235536 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_3235536 : Nat := 118140960795 + 3235536 * 2 ^ 59
def prefixEnd_3235536 : Nat := 4983230072969 + 3 ^ 40 * 3235536 * 2
def baseEnd_3235536 : Nat := 1107590095283838789480031

theorem tailTrace_3235536 : CollatzResearch.WordTrace tailWord_3235536 prefixEnd_3235536 1107590095283838789480031 := by
  unfold tailWord_3235536
  simp only [CollatzResearch.WordTrace]
  refine ⟨59004846403106566200163231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78673128537475421600217641 59004846403106566200163231)
  ·
    refine ⟨88507269604659849300244847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59004846403106566200163231 88507269604659849300244847)
    ·
      refine ⟨132760904406989773950367271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88507269604659849300244847 132760904406989773950367271)
      ·
        refine ⟨199141356610484660925550907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132760904406989773950367271 199141356610484660925550907)
        ·
          refine ⟨298712034915726991388326361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199141356610484660925550907 298712034915726991388326361)
          ·
            refine ⟨224034026186795243541244771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298712034915726991388326361 224034026186795243541244771)
            ·
              refine ⟨336051039280192865311867157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224034026186795243541244771 336051039280192865311867157)
              ·
                refine ⟨15752392466259040561493773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 336051039280192865311867157 15752392466259040561493773)
                ·
                  refine ⟨5907147174847140210560165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15752392466259040561493773 5907147174847140210560165)
                  ·
                    refine ⟨1107590095283838789480031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5907147174847140210560165 1107590095283838789480031)
                    ·
                      rfl

theorem cell22_3235536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_3235536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235536 prefixEnd_3235536 := by exact prefixLift 3235536
  have htrace : WordTrace (prefixWord ++ tailWord_3235536) baseStart_3235536 baseEnd_3235536 := by
    simpa [prefixWord, tailWord_3235536, baseEnd_3235536] using wordTrace_append hprefix tailTrace_3235536
  have hstable : (prefixWord ++ tailWord_3235536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235536).length < 2 ^ (prefixWord ++ tailWord_3235536).sum := by decide
  have hdescent : baseEnd_3235536 < baseStart_3235536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235538 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_3235538 : Nat := 118140960795 + 3235538 * 2 ^ 59
def prefixEnd_3235538 : Nat := 4983230072969 + 3 ^ 40 * 3235538 * 2
def baseEnd_3235538 : Nat := 1107590779924711450930025

theorem tailTrace_3235538 : CollatzResearch.WordTrace tailWord_3235538 prefixEnd_3235538 1107590779924711450930025 := by
  unfold tailWord_3235538
  simp only [CollatzResearch.WordTrace]
  refine ⟨29502441438051471685474817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78673177168137257827932845 29502441438051471685474817)
  ·
    refine ⟨22126831078538603764106113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29502441438051471685474817 22126831078538603764106113)
    ·
      refine ⟨16595123308903952823079585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22126831078538603764106113 16595123308903952823079585)
      ·
        refine ⟨12446342481677964617309689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16595123308903952823079585 12446342481677964617309689)
        ·
          refine ⟨9334756861258473462982267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12446342481677964617309689 9334756861258473462982267)
          ·
            refine ⟨14002135291887710194473401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9334756861258473462982267 14002135291887710194473401)
            ·
              refine ⟨10501601468915782645855051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14002135291887710194473401 10501601468915782645855051)
              ·
                refine ⟨15752402203373673968782577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10501601468915782645855051 15752402203373673968782577)
                ·
                  refine ⟨11814301652530255476586933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15752402203373673968782577 11814301652530255476586933)
                  ·
                    refine ⟨1107590779924711450930025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11814301652530255476586933 1107590779924711450930025)
                    ·
                      rfl

theorem cell22_3235538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_3235538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235538 prefixEnd_3235538 := by exact prefixLift 3235538
  have htrace : WordTrace (prefixWord ++ tailWord_3235538) baseStart_3235538 baseEnd_3235538 := by
    simpa [prefixWord, tailWord_3235538, baseEnd_3235538] using wordTrace_append hprefix tailTrace_3235538
  have hstable : (prefixWord ++ tailWord_3235538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235538).length < 2 ^ (prefixWord ++ tailWord_3235538).sum := by decide
  have hdescent : baseEnd_3235538 < baseStart_3235538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235551 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 6]
def baseStart_3235551 : Nat := 118140960795 + 3235551 * 2 ^ 59
def prefixEnd_3235551 : Nat := 4983230072969 + 3 ^ 40 * 3235551 * 2
def baseEnd_3235551 : Nat := 369198410030127916784995

theorem tailTrace_3235551 : CollatzResearch.WordTrace tailWord_3235551 prefixEnd_3235551 369198410030127916784995 := by
  unfold tailWord_3235551
  simp only [CollatzResearch.WordTrace]
  refine ⟨118010239901158789962122507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78673493267439193308081671 118010239901158789962122507)
  ·
    refine ⟨177015359851738184943183761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118010239901158789962122507 177015359851738184943183761)
    ·
      refine ⟨132761519888803638707387821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177015359851738184943183761 132761519888803638707387821)
      ·
        refine ⟨49785569958301364515270433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132761519888803638707387821 49785569958301364515270433)
        ·
          refine ⟨37339177468726023386452825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49785569958301364515270433 37339177468726023386452825)
          ·
            refine ⟨28004383101544517539839619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37339177468726023386452825 28004383101544517539839619)
            ·
              refine ⟨42006574652316776309759429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28004383101544517539839619 42006574652316776309759429)
              ·
                refine ⟨7876232747309395558079893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42006574652316776309759429 7876232747309395558079893)
                ·
                  refine ⟨369198410030127916784995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7876232747309395558079893 369198410030127916784995)
                  ·
                    rfl

theorem cell22_3235551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 6].length) (baseStart_3235551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235551 prefixEnd_3235551 := by exact prefixLift 3235551
  have htrace : WordTrace (prefixWord ++ tailWord_3235551) baseStart_3235551 baseEnd_3235551 := by
    simpa [prefixWord, tailWord_3235551, baseEnd_3235551] using wordTrace_append hprefix tailTrace_3235551
  have hstable : (prefixWord ++ tailWord_3235551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235551).length < 2 ^ (prefixWord ++ tailWord_3235551).sum := by decide
  have hdescent : baseEnd_3235551 < baseStart_3235551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235568 : List Nat := [2, 1, 1, 1, 3, 1, 2, 7, 4]
def baseStart_3235568 : Nat := 118140960795 + 3235568 * 2 ^ 59
def prefixEnd_3235568 : Nat := 4983230072969 + 3 ^ 40 * 3235568 * 2
def baseEnd_3235568 : Nat := 369200349845933790893311

theorem tailTrace_3235568 : CollatzResearch.WordTrace tailWord_3235568 prefixEnd_3235568 369200349845933790893311 := by
  unfold tailWord_3235568
  simp only [CollatzResearch.WordTrace]
  refine ⟨59005429971048600932745679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78673906628064801243660905 59005429971048600932745679)
  ·
    refine ⟨88508144956572901399118519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59005429971048600932745679 88508144956572901399118519)
    ·
      refine ⟨132762217434859352098677779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88508144956572901399118519 132762217434859352098677779)
      ·
        refine ⟨199143326152289028148016669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132762217434859352098677779 199143326152289028148016669)
        ·
          refine ⟨74678747307108385555506251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199143326152289028148016669 74678747307108385555506251)
          ·
            refine ⟨112018120960662578333259377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74678747307108385555506251 112018120960662578333259377)
            ·
              refine ⟨84013590720496933749944533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112018120960662578333259377 84013590720496933749944533)
              ·
                refine ⟨1969068532511646884764325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84013590720496933749944533 1969068532511646884764325)
                ·
                  refine ⟨369200349845933790893311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1969068532511646884764325 369200349845933790893311)
                  ·
                    rfl

theorem cell22_3235568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 4].length) (baseStart_3235568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235568 prefixEnd_3235568 := by exact prefixLift 3235568
  have htrace : WordTrace (prefixWord ++ tailWord_3235568) baseStart_3235568 baseEnd_3235568 := by
    simpa [prefixWord, tailWord_3235568, baseEnd_3235568] using wordTrace_append hprefix tailTrace_3235568
  have hstable : (prefixWord ++ tailWord_3235568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235568).length < 2 ^ (prefixWord ++ tailWord_3235568).sum := by decide
  have hdescent : baseEnd_3235568 < baseStart_3235568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235581 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_3235581 : Nat := 118140960795 + 3235581 * 2 ^ 59
def prefixEnd_3235581 : Nat := 4983230072969 + 3 ^ 40 * 3235581 * 2
def baseEnd_3235581 : Nat := 1107605499703473672104893

theorem tailTrace_3235581 : CollatzResearch.WordTrace tailWord_3235581 prefixEnd_3235581 1107605499703473672104893 := by
  unfold tailWord_3235581
  simp only [CollatzResearch.WordTrace]
  refine ⟨118011334091050105085714597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78674222727366736723809731 118011334091050105085714597)
  ·
    refine ⟨22127125142071894703571487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118011334091050105085714597 22127125142071894703571487)
    ·
      refine ⟨33190687713107842055357231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22127125142071894703571487 33190687713107842055357231)
      ·
        refine ⟨49786031569661763083035847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33190687713107842055357231 49786031569661763083035847)
        ·
          refine ⟨74679047354492644624553771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49786031569661763083035847 74679047354492644624553771)
          ·
            refine ⟨112018571031738966936830657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74679047354492644624553771 112018571031738966936830657)
            ·
              refine ⟨84013928273804225202622993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112018571031738966936830657 84013928273804225202622993)
              ·
                refine ⟨63010446205353168901967245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84013928273804225202622993 63010446205353168901967245)
                ·
                  refine ⟨23628917327007438338237717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63010446205353168901967245 23628917327007438338237717)
                  ·
                    refine ⟨1107605499703473672104893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23628917327007438338237717 1107605499703473672104893)
                    ·
                      rfl

theorem cell22_3235581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_3235581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235581 prefixEnd_3235581 := by exact prefixLift 3235581
  have htrace : WordTrace (prefixWord ++ tailWord_3235581) baseStart_3235581 baseEnd_3235581 := by
    simpa [prefixWord, tailWord_3235581, baseEnd_3235581] using wordTrace_append hprefix tailTrace_3235581
  have hstable : (prefixWord ++ tailWord_3235581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235581).length < 2 ^ (prefixWord ++ tailWord_3235581).sum := by decide
  have hdescent : baseEnd_3235581 < baseStart_3235581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235583 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 4, 3]
def baseStart_3235583 : Nat := 118140960795 + 3235583 * 2 ^ 59
def prefixEnd_3235583 : Nat := 4983230072969 + 3 ^ 40 * 3235583 * 2
def baseEnd_3235583 : Nat := 1107606184344346333554887

theorem tailTrace_3235583 : CollatzResearch.WordTrace tailWord_3235583 prefixEnd_3235583 1107606184344346333554887 := by
  unfold tailWord_3235583
  simp only [CollatzResearch.WordTrace]
  refine ⟨118011407037042859427287403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78674271358028572951524935 118011407037042859427287403)
  ·
    refine ⟨177017110555564289140931105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118011407037042859427287403 177017110555564289140931105)
    ·
      refine ⟨132762832916673216855698329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177017110555564289140931105 132762832916673216855698329)
      ·
        refine ⟨99572124687504912641773747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132762832916673216855698329 99572124687504912641773747)
        ·
          refine ⟨149358187031257368962660621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99572124687504912641773747 149358187031257368962660621)
          ·
            refine ⟨56009320136721513360997733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149358187031257368962660621 56009320136721513360997733)
            ·
              refine ⟨10501747525635283755187075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56009320136721513360997733 10501747525635283755187075)
              ·
                refine ⟨15752621288452925632780613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10501747525635283755187075 15752621288452925632780613)
                ·
                  refine ⟨2953616491584923556146365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15752621288452925632780613 2953616491584923556146365)
                  ·
                    refine ⟨1107606184344346333554887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2953616491584923556146365 1107606184344346333554887)
                    ·
                      rfl

theorem cell22_3235583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_3235583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235583 prefixEnd_3235583 := by exact prefixLift 3235583
  have htrace : WordTrace (prefixWord ++ tailWord_3235583) baseStart_3235583 baseEnd_3235583 := by
    simpa [prefixWord, tailWord_3235583, baseEnd_3235583] using wordTrace_append hprefix tailTrace_3235583
  have hstable : (prefixWord ++ tailWord_3235583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235583).length < 2 ^ (prefixWord ++ tailWord_3235583).sum := by decide
  have hdescent : baseEnd_3235583 < baseStart_3235583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235596 : List Nat := [2, 2, 1, 2, 2, 1, 3, 9]
def baseStart_3235596 : Nat := 118140960795 + 3235596 * 2 ^ 59
def prefixEnd_3235596 : Nat := 4983230072969 + 3 ^ 40 * 3235596 * 2
def baseEnd_3235596 : Nat := 123067848278890959219983

theorem tailTrace_3235596 : CollatzResearch.WordTrace tailWord_3235596 prefixEnd_3235596 123067848278890959219983 := by
  unfold tailWord_3235596
  simp only [CollatzResearch.WordTrace]
  refine ⟨59005940592997881323755321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78674587457330508431673761 59005940592997881323755321)
  ·
    refine ⟨44254455444748410992816491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59005940592997881323755321 44254455444748410992816491)
    ·
      refine ⟨66381683167122616489224737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44254455444748410992816491 66381683167122616489224737)
      ·
        refine ⟨49786262375341962366918553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66381683167122616489224737 49786262375341962366918553)
        ·
          refine ⟨37339696781506471775188915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49786262375341962366918553 37339696781506471775188915)
          ·
            refine ⟨56009545172259707662783373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37339696781506471775188915 56009545172259707662783373)
            ·
              refine ⟨21003579439597390373543765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56009545172259707662783373 21003579439597390373543765)
              ·
                refine ⟨123067848278890959219983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21003579439597390373543765 123067848278890959219983)
                ·
                  rfl

theorem cell22_3235596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 9].length) (baseStart_3235596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235596 prefixEnd_3235596 := by exact prefixLift 3235596
  have htrace : WordTrace (prefixWord ++ tailWord_3235596) baseStart_3235596 baseEnd_3235596 := by
    simpa [prefixWord, tailWord_3235596, baseEnd_3235596] using wordTrace_append hprefix tailTrace_3235596
  have hstable : (prefixWord ++ tailWord_3235596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235596).length < 2 ^ (prefixWord ++ tailWord_3235596).sum := by decide
  have hdescent : baseEnd_3235596 < baseStart_3235596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235604 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3235604 : Nat := 118140960795 + 3235604 * 2 ^ 59
def prefixEnd_3235604 : Nat := 4983230072969 + 3 ^ 40 * 3235604 * 2
def baseEnd_3235604 : Nat := 1107613373073509278779823

theorem tailTrace_3235604 : CollatzResearch.WordTrace tailWord_3235604 prefixEnd_3235604 1107613373073509278779823 := by
  unfold tailWord_3235604
  simp only [CollatzResearch.WordTrace]
  refine ⟨59006086484983390006900933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78674781979977853342534577 59006086484983390006900933)
  ·
    refine ⟨11063641215934385626293925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59006086484983390006900933 11063641215934385626293925)
    ·
      refine ⟨2074432727987697304930111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11063641215934385626293925 2074432727987697304930111)
      ·
        refine ⟨3111649091981545957395167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074432727987697304930111 3111649091981545957395167)
        ·
          refine ⟨4667473637972318936092751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3111649091981545957395167 4667473637972318936092751)
          ·
            refine ⟨7001210456958478404139127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4667473637972318936092751 7001210456958478404139127)
            ·
              refine ⟨10501815685437717606208691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7001210456958478404139127 10501815685437717606208691)
              ·
                refine ⟨15752723528156576409313037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10501815685437717606208691 15752723528156576409313037)
                ·
                  refine ⟨5907271323058716153492389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15752723528156576409313037 5907271323058716153492389)
                  ·
                    refine ⟨1107613373073509278779823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5907271323058716153492389 1107613373073509278779823)
                    ·
                      rfl

theorem cell22_3235604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3235604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235604 prefixEnd_3235604 := by exact prefixLift 3235604
  have htrace : WordTrace (prefixWord ++ tailWord_3235604) baseStart_3235604 baseEnd_3235604 := by
    simpa [prefixWord, tailWord_3235604, baseEnd_3235604] using wordTrace_append hprefix tailTrace_3235604
  have hstable : (prefixWord ++ tailWord_3235604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235604).length < 2 ^ (prefixWord ++ tailWord_3235604).sum := by decide
  have hdescent : baseEnd_3235604 < baseStart_3235604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235630 : List Nat := [4, 1, 3, 2, 3, 9]
def baseStart_3235630 : Nat := 118140960795 + 3235630 * 2 ^ 59
def prefixEnd_3235630 : Nat := 4983230072969 + 3 ^ 40 * 3235630 * 2
def baseEnd_3235630 : Nat := 13674349054380912069503

theorem tailTrace_3235630 : CollatzResearch.WordTrace tailWord_3235630 prefixEnd_3235630 13674349054380912069503 := by
  unfold tailWord_3235630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14751640158484073306781043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78675414178581724302832229 14751640158484073306781043)
  ·
    refine ⟨22127460237726109960171565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14751640158484073306781043 22127460237726109960171565)
    ·
      refine ⟨8297797589147291235064337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22127460237726109960171565 8297797589147291235064337)
      ·
        refine ⟨6223348191860468426298253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8297797589147291235064337 6223348191860468426298253)
        ·
          refine ⟨2333755571947675659861845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6223348191860468426298253 2333755571947675659861845)
          ·
            refine ⟨13674349054380912069503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2333755571947675659861845 13674349054380912069503)
            ·
              rfl

theorem cell22_3235630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 9].length) (baseStart_3235630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235630 prefixEnd_3235630 := by exact prefixLift 3235630
  have htrace : WordTrace (prefixWord ++ tailWord_3235630) baseStart_3235630 baseEnd_3235630 := by
    simpa [prefixWord, tailWord_3235630, baseEnd_3235630] using wordTrace_append hprefix tailTrace_3235630
  have hstable : (prefixWord ++ tailWord_3235630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235630).length < 2 ^ (prefixWord ++ tailWord_3235630).sum := by decide
  have hdescent : baseEnd_3235630 < baseStart_3235630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235658 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_3235658 : Nat := 118140960795 + 3235658 * 2 ^ 59
def prefixEnd_3235658 : Nat := 4983230072969 + 3 ^ 40 * 3235658 * 2
def baseEnd_3235658 : Nat := 369210619459023712643219

theorem tailTrace_3235658 : CollatzResearch.WordTrace tailWord_3235658 prefixEnd_3235658 369210619459023712643219 := by
  unfold tailWord_3235658
  simp only [CollatzResearch.WordTrace]
  refine ⟨29503535627942786809066907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78676095007847431490845085 29503535627942786809066907)
  ·
    refine ⟨44255303441914180213600361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29503535627942786809066907 44255303441914180213600361)
    ·
      refine ⟨33191477581435635160200271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44255303441914180213600361 33191477581435635160200271)
      ·
        refine ⟨49787216372153452740300407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33191477581435635160200271 49787216372153452740300407)
        ·
          refine ⟨74680824558230179110450611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49787216372153452740300407 74680824558230179110450611)
          ·
            refine ⟨112021236837345268665675917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74680824558230179110450611 112021236837345268665675917)
            ·
              refine ⟨42007963814004475749628469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112021236837345268665675917 42007963814004475749628469)
              ·
                refine ⟨3938246607562919601527669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42007963814004475749628469 3938246607562919601527669)
                ·
                  refine ⟨369210619459023712643219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3938246607562919601527669 369210619459023712643219)
                  ·
                    rfl

theorem cell22_3235658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_3235658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235658 prefixEnd_3235658 := by exact prefixLift 3235658
  have htrace : WordTrace (prefixWord ++ tailWord_3235658) baseStart_3235658 baseEnd_3235658 := by
    simpa [prefixWord, tailWord_3235658, baseEnd_3235658] using wordTrace_append hprefix tailTrace_3235658
  have hstable : (prefixWord ++ tailWord_3235658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235658).length < 2 ^ (prefixWord ++ tailWord_3235658).sum := by decide
  have hdescent : baseEnd_3235658 < baseStart_3235658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235733 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3235733 : Nat := 118140960795 + 3235733 * 2 ^ 59
def prefixEnd_3235733 : Nat := 4983230072969 + 3 ^ 40 * 3235733 * 2
def baseEnd_3235733 : Nat := 1107657532409795942304427

theorem tailTrace_3235733 : CollatzResearch.WordTrace tailWord_3235733 prefixEnd_3235733 1107657532409795942304427 := by
  unfold tailWord_3235733
  simp only [CollatzResearch.WordTrace]
  refine ⟨118016877986499435045247853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78677918657666290030165235 118016877986499435045247853)
  ·
    refine ⟨44256329244937288141967945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118016877986499435045247853 44256329244937288141967945)
    ·
      refine ⟨33192246933702966106475959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44256329244937288141967945 33192246933702966106475959)
      ·
        refine ⟨49788370400554449159713939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33192246933702966106475959 49788370400554449159713939)
        ·
          refine ⟨74682555600831673739570909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49788370400554449159713939 74682555600831673739570909)
          ·
            refine ⟨28005958350311877652339091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74682555600831673739570909 28005958350311877652339091)
            ·
              refine ⟨42008937525467816478508637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28005958350311877652339091 42008937525467816478508637)
              ·
                refine ⟨15753351572050431179440739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42008937525467816478508637 15753351572050431179440739)
                ·
                  refine ⟨23630027358075646769161109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15753351572050431179440739 23630027358075646769161109)
                  ·
                    refine ⟨1107657532409795942304427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23630027358075646769161109 1107657532409795942304427)
                    ·
                      rfl

theorem cell22_3235733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3235733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235733 prefixEnd_3235733 := by exact prefixLift 3235733
  have htrace : WordTrace (prefixWord ++ tailWord_3235733) baseStart_3235733 baseEnd_3235733 := by
    simpa [prefixWord, tailWord_3235733, baseEnd_3235733] using wordTrace_append hprefix tailTrace_3235733
  have hstable : (prefixWord ++ tailWord_3235733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235733).length < 2 ^ (prefixWord ++ tailWord_3235733).sum := by decide
  have hdescent : baseEnd_3235733 < baseStart_3235733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235735 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 4, 3]
def baseStart_3235735 : Nat := 118140960795 + 3235735 * 2 ^ 59
def prefixEnd_3235735 : Nat := 4983230072969 + 3 ^ 40 * 3235735 * 2
def baseEnd_3235735 : Nat := 1107658217050668603754421

theorem tailTrace_3235735 : CollatzResearch.WordTrace tailWord_3235735 prefixEnd_3235735 1107658217050668603754421 := by
  unfold tailWord_3235735
  simp only [CollatzResearch.WordTrace]
  refine ⟨118016950932492189386820659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78677967288328126257880439 118016950932492189386820659)
  ·
    refine ⟨177025426398738284080230989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118016950932492189386820659 177025426398738284080230989)
    ·
      refine ⟨66384534899526856530086621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177025426398738284080230989 66384534899526856530086621)
      ·
        refine ⟨24894200587322571198782483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66384534899526856530086621 24894200587322571198782483)
        ·
          refine ⟨37341300880983856798173725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24894200587322571198782483 37341300880983856798173725)
          ·
            refine ⟨14002987830368946299315147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37341300880983856798173725 14002987830368946299315147)
            ·
              refine ⟨21004481745553419448972721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14002987830368946299315147 21004481745553419448972721)
              ·
                refine ⟨15753361309165064586729541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21004481745553419448972721 15753361309165064586729541)
                ·
                  refine ⟨2953755245468449610011789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15753361309165064586729541 2953755245468449610011789)
                  ·
                    refine ⟨1107658217050668603754421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2953755245468449610011789 1107658217050668603754421)
                    ·
                      rfl

theorem cell22_3235735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_3235735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235735 prefixEnd_3235735 := by exact prefixLift 3235735
  have htrace : WordTrace (prefixWord ++ tailWord_3235735) baseStart_3235735 baseEnd_3235735 := by
    simpa [prefixWord, tailWord_3235735, baseEnd_3235735] using wordTrace_append hprefix tailTrace_3235735
  have hstable : (prefixWord ++ tailWord_3235735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235735).length < 2 ^ (prefixWord ++ tailWord_3235735).sum := by decide
  have hdescent : baseEnd_3235735 < baseStart_3235735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235748 : List Nat := [2, 3, 1, 2, 1, 3, 10]
def baseStart_3235748 : Nat := 118140960795 + 3235748 * 2 ^ 59
def prefixEnd_3235748 : Nat := 4983230072969 + 3 ^ 40 * 3235748 * 2
def baseEnd_3235748 : Nat := 41024543230234848265903

theorem tailTrace_3235748 : CollatzResearch.WordTrace tailWord_3235748 prefixEnd_3235748 41024543230234848265903 := by
  unfold tailWord_3235748
  simp only [CollatzResearch.WordTrace]
  refine ⟨59008712540722546303521949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78678283387630061738029265 59008712540722546303521949)
  ·
    refine ⟨22128267202770954863820731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59008712540722546303521949 22128267202770954863820731)
    ·
      refine ⟨33192400804156432295731097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22128267202770954863820731 33192400804156432295731097)
      ·
        refine ⟨24894300603117324221798323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33192400804156432295731097 24894300603117324221798323)
        ·
          refine ⟨37341450904675986332697485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24894300603117324221798323 37341450904675986332697485)
          ·
            refine ⟨14003044089253494874761557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37341450904675986332697485 14003044089253494874761557)
            ·
              refine ⟨41024543230234848265903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14003044089253494874761557 41024543230234848265903)
              ·
                rfl

theorem cell22_3235748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 10].length) (baseStart_3235748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235748 prefixEnd_3235748 := by exact prefixLift 3235748
  have htrace : WordTrace (prefixWord ++ tailWord_3235748) baseStart_3235748 baseEnd_3235748 := by
    simpa [prefixWord, tailWord_3235748, baseEnd_3235748] using wordTrace_append hprefix tailTrace_3235748
  have hstable : (prefixWord ++ tailWord_3235748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235748).length < 2 ^ (prefixWord ++ tailWord_3235748).sum := by decide
  have hdescent : baseEnd_3235748 < baseStart_3235748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235765 : List Nat := [1, 3, 3, 2, 1, 3, 2, 7]
def baseStart_3235765 : Nat := 118140960795 + 3235765 * 2 ^ 59
def prefixEnd_3235765 : Nat := 4983230072969 + 3 ^ 40 * 3235765 * 2
def baseEnd_3235765 : Nat := 123074276295973169500481

theorem tailTrace_3235765 : CollatzResearch.WordTrace tailWord_3235765 prefixEnd_3235765 123074276295973169500481 := by
  unfold tailWord_3235765
  simp only [CollatzResearch.WordTrace]
  refine ⟨118018045122383504510412749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78678696748255669673608499 118018045122383504510412749)
  ·
    refine ⟨44256766920893814191404781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118018045122383504510412749 44256766920893814191404781)
    ·
      refine ⟨16596287595335180321776793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44256766920893814191404781 16596287595335180321776793)
      ·
        refine ⟨12447215696501385241332595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16596287595335180321776793 12447215696501385241332595)
        ·
          refine ⟨18670823544752077861998893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12447215696501385241332595 18670823544752077861998893)
          ·
            refine ⟨7001558829282029198249585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18670823544752077861998893 7001558829282029198249585)
            ·
              refine ⟨5251169121961521898687189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7001558829282029198249585 5251169121961521898687189)
              ·
                refine ⟨123074276295973169500481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5251169121961521898687189 123074276295973169500481)
                ·
                  rfl

theorem cell22_3235765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 7].length) (baseStart_3235765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235765 prefixEnd_3235765 := by exact prefixLift 3235765
  have htrace : WordTrace (prefixWord ++ tailWord_3235765) baseStart_3235765 baseEnd_3235765 := by
    simpa [prefixWord, tailWord_3235765, baseEnd_3235765] using wordTrace_append hprefix tailTrace_3235765
  have hstable : (prefixWord ++ tailWord_3235765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235765).length < 2 ^ (prefixWord ++ tailWord_3235765).sum := by decide
  have hdescent : baseEnd_3235765 < baseStart_3235765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235793 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 7]
def baseStart_3235793 : Nat := 118140960795 + 3235793 * 2 ^ 59
def prefixEnd_3235793 : Nat := 4983230072969 + 3 ^ 40 * 3235793 * 2
def baseEnd_3235793 : Nat := 369226023878658595268081

theorem tailTrace_3235793 : CollatzResearch.WordTrace tailWord_3235793 prefixEnd_3235793 369226023878658595268081 := by
  unfold tailWord_3235793
  simp only [CollatzResearch.WordTrace]
  refine ⟨118019066366282065292432033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78679377577521376861621355 118019066366282065292432033)
  ·
    refine ⟨88514299774711548969324025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118019066366282065292432033 88514299774711548969324025)
    ·
      refine ⟨66385724831033661726993019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88514299774711548969324025 66385724831033661726993019)
      ·
        refine ⟨99578587246550492590489529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66385724831033661726993019 99578587246550492590489529)
        ·
          refine ⟨74683940434912869442867147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99578587246550492590489529 74683940434912869442867147)
          ·
            refine ⟨112025910652369304164300721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74683940434912869442867147 112025910652369304164300721)
            ·
              refine ⟨84019432989276978123225541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112025910652369304164300721 84019432989276978123225541)
              ·
                refine ⟨15753643685489433398104789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84019432989276978123225541 15753643685489433398104789)
                ·
                  refine ⟨369226023878658595268081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15753643685489433398104789 369226023878658595268081)
                  ·
                    rfl

theorem cell22_3235793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_3235793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235793 prefixEnd_3235793 := by exact prefixLift 3235793
  have htrace : WordTrace (prefixWord ++ tailWord_3235793) baseStart_3235793 baseEnd_3235793 := by
    simpa [prefixWord, tailWord_3235793, baseEnd_3235793] using wordTrace_append hprefix tailTrace_3235793
  have hstable : (prefixWord ++ tailWord_3235793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235793).length < 2 ^ (prefixWord ++ tailWord_3235793).sum := by decide
  have hdescent : baseEnd_3235793 < baseStart_3235793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235808 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_3235808 : Nat := 118140960795 + 3235808 * 2 ^ 59
def prefixEnd_3235808 : Nat := 4983230072969 + 3 ^ 40 * 3235808 * 2
def baseEnd_3235808 : Nat := 1107683206442520746679197

theorem tailTrace_3235808 : CollatzResearch.WordTrace tailWord_3235808 prefixEnd_3235808 1107683206442520746679197 := by
  unfold tailWord_3235808
  simp only [CollatzResearch.WordTrace]
  refine ⟨59009806730613861427114039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78679742307485148569485385 59009806730613861427114039)
  ·
    refine ⟨88514710095920792140671059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59009806730613861427114039 88514710095920792140671059)
    ·
      refine ⟨132772065143881188211006589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88514710095920792140671059 132772065143881188211006589)
      ·
        refine ⟨49789524428955445579127471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132772065143881188211006589 49789524428955445579127471)
        ·
          refine ⟨74684286643433168368691207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49789524428955445579127471 74684286643433168368691207)
          ·
            refine ⟨112026429965149752553036811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74684286643433168368691207 112026429965149752553036811)
            ·
              refine ⟨168039644947724628829555217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112026429965149752553036811 168039644947724628829555217)
              ·
                refine ⟨126029733710793471622166413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168039644947724628829555217 126029733710793471622166413)
                ·
                  refine ⟨47261150141547551858312405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126029733710793471622166413 47261150141547551858312405)
                  ·
                    refine ⟨1107683206442520746679197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47261150141547551858312405 1107683206442520746679197)
                    ·
                      rfl

theorem cell22_3235808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_3235808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235808 prefixEnd_3235808 := by exact prefixLift 3235808
  have htrace : WordTrace (prefixWord ++ tailWord_3235808) baseStart_3235808 baseEnd_3235808 := by
    simpa [prefixWord, tailWord_3235808, baseEnd_3235808] using wordTrace_append hprefix tailTrace_3235808
  have hstable : (prefixWord ++ tailWord_3235808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235808).length < 2 ^ (prefixWord ++ tailWord_3235808).sum := by decide
  have hdescent : baseEnd_3235808 < baseStart_3235808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235900 : List Nat := [2, 2, 2, 2, 2, 1, 3, 8]
def baseStart_3235900 : Nat := 118140960795 + 3235900 * 2 ^ 59
def prefixEnd_3235900 : Nat := 4983230072969 + 3 ^ 40 * 3235900 * 2
def baseEnd_3235900 : Nat := 123079411102518130375435

theorem tailTrace_3235900 : CollatzResearch.WordTrace tailWord_3235900 prefixEnd_3235900 123079411102518130375435 := by
  unfold tailWord_3235900
  simp only [CollatzResearch.WordTrace]
  refine ⟨59011484488447211283288577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78681979317929615044384769 59011484488447211283288577)
  ·
    refine ⟨44258613366335408462466433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59011484488447211283288577 44258613366335408462466433)
    ·
      refine ⟨33193960024751556346849825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44258613366335408462466433 33193960024751556346849825)
      ·
        refine ⟨24895470018563667260137369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33193960024751556346849825 24895470018563667260137369)
        ·
          refine ⟨18671602513922750445103027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24895470018563667260137369 18671602513922750445103027)
          ·
            refine ⟨28007403770884125667654541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18671602513922750445103027 28007403770884125667654541)
            ·
              refine ⟨10502776414081547125370453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28007403770884125667654541 10502776414081547125370453)
              ·
                refine ⟨123079411102518130375435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10502776414081547125370453 123079411102518130375435)
                ·
                  rfl

theorem cell22_3235900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 8].length) (baseStart_3235900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235900 prefixEnd_3235900 := by exact prefixLift 3235900
  have htrace : WordTrace (prefixWord ++ tailWord_3235900) baseStart_3235900 baseEnd_3235900 := by
    simpa [prefixWord, tailWord_3235900, baseEnd_3235900] using wordTrace_append hprefix tailTrace_3235900
  have hstable : (prefixWord ++ tailWord_3235900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235900).length < 2 ^ (prefixWord ++ tailWord_3235900).sum := by decide
  have hdescent : baseEnd_3235900 < baseStart_3235900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235930 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_3235930 : Nat := 118140960795 + 3235930 * 2 ^ 59
def prefixEnd_3235930 : Nat := 4983230072969 + 3 ^ 40 * 3235930 * 2
def baseEnd_3235930 : Nat := 1107724969535753095128823

theorem tailTrace_3235930 : CollatzResearch.WordTrace tailWord_3235930 prefixEnd_3235930 1107724969535753095128823 := by
  unfold tailWord_3235930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29506015791696434422542311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78682708777857158460112829 29506015791696434422542311)
  ·
    refine ⟨44259023687544651633813467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29506015791696434422542311 44259023687544651633813467)
    ·
      refine ⟨66388535531316977450720201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44259023687544651633813467 66388535531316977450720201)
      ·
        refine ⟨49791401648487733088040151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66388535531316977450720201 49791401648487733088040151)
        ·
          refine ⟨74687102472731599632060227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49791401648487733088040151 74687102472731599632060227)
          ·
            refine ⟨112030653709097399448090341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74687102472731599632060227 112030653709097399448090341)
            ·
              refine ⟨21005747570455762396516939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112030653709097399448090341 21005747570455762396516939)
              ·
                refine ⟨31508621355683643594775409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21005747570455762396516939 31508621355683643594775409)
                ·
                  refine ⟨23631466016762732696081557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31508621355683643594775409 23631466016762732696081557)
                  ·
                    refine ⟨1107724969535753095128823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23631466016762732696081557 1107724969535753095128823)
                    ·
                      rfl

theorem cell22_3235930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_3235930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235930 prefixEnd_3235930 := by exact prefixLift 3235930
  have htrace : WordTrace (prefixWord ++ tailWord_3235930) baseStart_3235930 baseEnd_3235930 := by
    simpa [prefixWord, tailWord_3235930, baseEnd_3235930] using wordTrace_append hprefix tailTrace_3235930
  have hstable : (prefixWord ++ tailWord_3235930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235930).length < 2 ^ (prefixWord ++ tailWord_3235930).sum := by decide
  have hdescent : baseEnd_3235930 < baseStart_3235930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235960 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_3235960 : Nat := 118140960795 + 3235960 * 2 ^ 59
def prefixEnd_3235960 : Nat := 4983230072969 + 3 ^ 40 * 3235960 * 2
def baseEnd_3235960 : Nat := 1107735239148843016878731

theorem tailTrace_3235960 : CollatzResearch.WordTrace tailWord_3235960 prefixEnd_3235960 1107735239148843016878731 := by
  unfold tailWord_3235960
  simp only [CollatzResearch.WordTrace]
  refine ⟨59012578678338526406880667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78683438237784701875840889 59012578678338526406880667)
  ·
    refine ⟨88518868017507789610321001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59012578678338526406880667 88518868017507789610321001)
    ·
      refine ⟨66389151013130842207740751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88518868017507789610321001 66389151013130842207740751)
      ·
        refine ⟨99583726519696263311611127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66389151013130842207740751 99583726519696263311611127)
        ·
          refine ⟨149375589779544394967416691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99583726519696263311611127 149375589779544394967416691)
          ·
            refine ⟨224063384669316592451125037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149375589779544394967416691 224063384669316592451125037)
            ·
              refine ⟨84023769250993722169171889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224063384669316592451125037 84023769250993722169171889)
              ·
                refine ⟨63017826938245291626878917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84023769250993722169171889 63017826938245291626878917)
                ·
                  refine ⟨11815842550920992180039797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63017826938245291626878917 11815842550920992180039797)
                  ·
                    refine ⟨1107735239148843016878731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11815842550920992180039797 1107735239148843016878731)
                    ·
                      rfl

theorem cell22_3235960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_3235960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235960 prefixEnd_3235960 := by exact prefixLift 3235960
  have htrace : WordTrace (prefixWord ++ tailWord_3235960) baseStart_3235960 baseEnd_3235960 := by
    simpa [prefixWord, tailWord_3235960, baseEnd_3235960] using wordTrace_append hprefix tailTrace_3235960
  have hstable : (prefixWord ++ tailWord_3235960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235960).length < 2 ^ (prefixWord ++ tailWord_3235960).sum := by decide
  have hdescent : baseEnd_3235960 < baseStart_3235960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235994 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_3235994 : Nat := 118140960795 + 3235994 * 2 ^ 59
def prefixEnd_3235994 : Nat := 4983230072969 + 3 ^ 40 * 3235994 * 2
def baseEnd_3235994 : Nat := 1107746878043678261528627

theorem tailTrace_3235994 : CollatzResearch.WordTrace tailWord_3235994 prefixEnd_3235994 1107746878043678261528627 := by
  unfold tailWord_3235994
  simp only [CollatzResearch.WordTrace]
  refine ⟨29506599359638469155124759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78684264959035917746999357 29506599359638469155124759)
  ·
    refine ⟨44259899039457703732687139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29506599359638469155124759 44259899039457703732687139)
    ·
      refine ⟨66389848559186555599030709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44259899039457703732687139 66389848559186555599030709)
      ·
        refine ⟨6224048302423739587409129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66389848559186555599030709 6224048302423739587409129)
        ·
          refine ⟨4668036226817804690556847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6224048302423739587409129 4668036226817804690556847)
          ·
            refine ⟨7002054340226707035835271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668036226817804690556847 7002054340226707035835271)
            ·
              refine ⟨10503081510340060553752907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002054340226707035835271 10503081510340060553752907)
              ·
                refine ⟨15754622265510090830629361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10503081510340060553752907 15754622265510090830629361)
                ·
                  refine ⟨11815966699132568122972021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15754622265510090830629361 11815966699132568122972021)
                  ·
                    refine ⟨1107746878043678261528627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11815966699132568122972021 1107746878043678261528627)
                    ·
                      rfl

theorem cell22_3235994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_3235994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3235994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3235994 prefixEnd_3235994 := by exact prefixLift 3235994
  have htrace : WordTrace (prefixWord ++ tailWord_3235994) baseStart_3235994 baseEnd_3235994 := by
    simpa [prefixWord, tailWord_3235994, baseEnd_3235994] using wordTrace_append hprefix tailTrace_3235994
  have hstable : (prefixWord ++ tailWord_3235994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235994).length < 2 ^ (prefixWord ++ tailWord_3235994).sum := by decide
  have hdescent : baseEnd_3235994 < baseStart_3235994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236024 : List Nat := [2, 1, 2, 1, 2, 1, 6, 3, 4]
def baseStart_3236024 : Nat := 118140960795 + 3236024 * 2 ^ 59
def prefixEnd_3236024 : Nat := 4983230072969 + 3 ^ 40 * 3236024 * 2
def baseEnd_3236024 : Nat := 369252382552256061092845

theorem tailTrace_3236024 : CollatzResearch.WordTrace tailWord_3236024 prefixEnd_3236024 369252382552256061092845 := by
  unfold tailWord_3236024
  simp only [CollatzResearch.WordTrace]
  refine ⟨59013745814222595872045563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78684994418963461162727417 59013745814222595872045563)
  ·
    refine ⟨88520618721333893808068345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59013745814222595872045563 88520618721333893808068345)
    ·
      refine ⟨66390464041000420356051259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88520618721333893808068345 66390464041000420356051259)
      ·
        refine ⟨99585696061500630534076889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66390464041000420356051259 99585696061500630534076889)
        ·
          refine ⟨74689272046125472900557667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99585696061500630534076889 74689272046125472900557667)
          ·
            refine ⟨112033908069188209350836501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74689272046125472900557667 112033908069188209350836501)
            ·
              refine ⟨5251589440743197313320461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112033908069188209350836501 5251589440743197313320461)
              ·
                refine ⟨1969346040278698992495173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5251589440743197313320461 1969346040278698992495173)
                ·
                  refine ⟨369252382552256061092845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1969346040278698992495173 369252382552256061092845)
                  ·
                    rfl

theorem cell22_3236024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 4].length) (baseStart_3236024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236024 prefixEnd_3236024 := by exact prefixLift 3236024
  have htrace : WordTrace (prefixWord ++ tailWord_3236024) baseStart_3236024 baseEnd_3236024 := by
    simpa [prefixWord, tailWord_3236024, baseEnd_3236024] using wordTrace_append hprefix tailTrace_3236024
  have hstable : (prefixWord ++ tailWord_3236024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236024).length < 2 ^ (prefixWord ++ tailWord_3236024).sum := by decide
  have hdescent : baseEnd_3236024 < baseStart_3236024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236037 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_3236037 : Nat := 118140960795 + 3236037 * 2 ^ 59
def prefixEnd_3236037 : Nat := 4983230072969 + 3 ^ 40 * 3236037 * 2
def baseEnd_3236037 : Nat := 1107761597822440482703495

theorem tailTrace_3236037 : CollatzResearch.WordTrace tailWord_3236037 prefixEnd_3236037 1107761597822440482703495 := by
  unfold tailWord_3236037
  simp only [CollatzResearch.WordTrace]
  refine ⟨118027965777398094964314365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78685310518265396642876243 118027965777398094964314365)
  ·
    refine ⟨44260487166524285611617887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118027965777398094964314365 44260487166524285611617887)
    ·
      refine ⟨66390730749786428417426831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44260487166524285611617887 66390730749786428417426831)
      ·
        refine ⟨99586096124679642626140247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66390730749786428417426831 99586096124679642626140247)
        ·
          refine ⟨149379144187019463939210371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99586096124679642626140247 149379144187019463939210371)
          ·
            refine ⟨224068716280529195908815557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149379144187019463939210371 224068716280529195908815557)
            ·
              refine ⟨42012884302599224232902917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224068716280529195908815557 42012884302599224232902917)
              ·
                refine ⟨7877415806737354543669297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42012884302599224232902917 7877415806737354543669297)
                ·
                  refine ⟨5908061855053015907751973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7877415806737354543669297 5908061855053015907751973)
                  ·
                    refine ⟨1107761597822440482703495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5908061855053015907751973 1107761597822440482703495)
                    ·
                      rfl

theorem cell22_3236037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_3236037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236037 prefixEnd_3236037 := by exact prefixLift 3236037
  have htrace : WordTrace (prefixWord ++ tailWord_3236037) baseStart_3236037 baseEnd_3236037 := by
    simpa [prefixWord, tailWord_3236037, baseEnd_3236037] using wordTrace_append hprefix tailTrace_3236037
  have hstable : (prefixWord ++ tailWord_3236037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236037).length < 2 ^ (prefixWord ++ tailWord_3236037).sum := by decide
  have hdescent : baseEnd_3236037 < baseStart_3236037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236069 : List Nat := [1, 3, 1, 4, 2, 1, 4, 6]
def baseStart_3236069 : Nat := 118140960795 + 3236069 * 2 ^ 59
def prefixEnd_3236069 : Nat := 4983230072969 + 3 ^ 40 * 3236069 * 2
def baseEnd_3236069 : Nat := 123085839119600340655933

theorem tailTrace_3236069 : CollatzResearch.WordTrace tailWord_3236069 prefixEnd_3236069 123085839119600340655933 := by
  unfold tailWord_3236069
  simp only [CollatzResearch.WordTrace]
  refine ⟨118029132913282164429479261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78686088608854776286319507 118029132913282164429479261)
  ·
    refine ⟨44260924842480811661054723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118029132913282164429479261 44260924842480811661054723)
    ·
      refine ⟨66391387263721217491582085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44260924842480811661054723 66391387263721217491582085)
      ·
        refine ⟨12448385111947728279671641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66391387263721217491582085 12448385111947728279671641)
        ·
          refine ⟨9336288833960796209753731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12448385111947728279671641 9336288833960796209753731)
          ·
            refine ⟨14004433250941194314630597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336288833960796209753731 14004433250941194314630597)
            ·
              refine ⟨2625831234551473933993237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14004433250941194314630597 2625831234551473933993237)
              ·
                refine ⟨123085839119600340655933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2625831234551473933993237 123085839119600340655933)
                ·
                  rfl

theorem cell22_3236069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 6].length) (baseStart_3236069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236069 prefixEnd_3236069 := by exact prefixLift 3236069
  have htrace : WordTrace (prefixWord ++ tailWord_3236069) baseStart_3236069 baseEnd_3236069 := by
    simpa [prefixWord, tailWord_3236069, baseEnd_3236069] using wordTrace_append hprefix tailTrace_3236069
  have hstable : (prefixWord ++ tailWord_3236069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236069).length < 2 ^ (prefixWord ++ tailWord_3236069).sum := by decide
  have hdescent : baseEnd_3236069 < baseStart_3236069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236097 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 7]
def baseStart_3236097 : Nat := 118140960795 + 3236097 * 2 ^ 59
def prefixEnd_3236097 : Nat := 4983230072969 + 3 ^ 40 * 3236097 * 2
def baseEnd_3236097 : Nat := 369260712349540108734437

theorem tailTrace_3236097 : CollatzResearch.WordTrace tailWord_3236097 prefixEnd_3236097 369260712349540108734437 := by
  unfold tailWord_3236097
  simp only [CollatzResearch.WordTrace]
  refine ⟨118030154157180725211498545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78686769438120483474332363 118030154157180725211498545)
  ·
    refine ⟨88522615617885543908623909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118030154157180725211498545 88522615617885543908623909)
    ·
      refine ⟨16597990428353539482866983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88522615617885543908623909 16597990428353539482866983)
      ·
        refine ⟨24896985642530309224300475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16597990428353539482866983 24896985642530309224300475)
        ·
          refine ⟨37345478463795463836450713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24896985642530309224300475 37345478463795463836450713)
          ·
            refine ⟨28009108847846597877338035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37345478463795463836450713 28009108847846597877338035)
            ·
              refine ⟨42013663271769896816007053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28009108847846597877338035 42013663271769896816007053)
              ·
                refine ⟨15755123726913711306002645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42013663271769896816007053 15755123726913711306002645)
                ·
                  refine ⟨369260712349540108734437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15755123726913711306002645 369260712349540108734437)
                  ·
                    rfl

theorem cell22_3236097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_3236097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236097 prefixEnd_3236097 := by exact prefixLift 3236097
  have htrace : WordTrace (prefixWord ++ tailWord_3236097) baseStart_3236097 baseEnd_3236097 := by
    simpa [prefixWord, tailWord_3236097, baseEnd_3236097] using wordTrace_append hprefix tailTrace_3236097
  have hstable : (prefixWord ++ tailWord_3236097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236097).length < 2 ^ (prefixWord ++ tailWord_3236097).sum := by decide
  have hdescent : baseEnd_3236097 < baseStart_3236097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236204 : List Nat := [2, 2, 1, 1, 6, 1, 9]
def baseStart_3236204 : Nat := 118140960795 + 3236204 * 2 ^ 59
def prefixEnd_3236204 : Nat := 4983230072969 + 3 ^ 40 * 3236204 * 2
def baseEnd_3236204 : Nat := 41030324642048433843629

theorem tailTrace_3236204 : CollatzResearch.WordTrace tailWord_3236204 prefixEnd_3236204 41030324642048433843629 := by
  unfold tailWord_3236204
  simp only [CollatzResearch.WordTrace]
  refine ⟨59017028383896541242821833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78689371178528721657095777 59017028383896541242821833)
  ·
    refine ⟨44262771287922405932116375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59017028383896541242821833 44262771287922405932116375)
    ·
      refine ⟨66394156931883608898174563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44262771287922405932116375 66394156931883608898174563)
      ·
        refine ⟨99591235397825413347261845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66394156931883608898174563 99591235397825413347261845)
        ·
          refine ⟨4668339159273066250652899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99591235397825413347261845 4668339159273066250652899)
          ·
            refine ⟨7002508738909599375979349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668339159273066250652899 7002508738909599375979349)
            ·
              refine ⟨41030324642048433843629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7002508738909599375979349 41030324642048433843629)
              ·
                rfl

theorem cell22_3236204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 9].length) (baseStart_3236204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236204 prefixEnd_3236204 := by exact prefixLift 3236204
  have htrace : WordTrace (prefixWord ++ tailWord_3236204) baseStart_3236204 baseEnd_3236204 := by
    simpa [prefixWord, tailWord_3236204, baseEnd_3236204] using wordTrace_append hprefix tailTrace_3236204
  have hstable : (prefixWord ++ tailWord_3236204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236204).length < 2 ^ (prefixWord ++ tailWord_3236204).sum := by decide
  have hdescent : baseEnd_3236204 < baseStart_3236204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236208 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 2, 3]
def baseStart_3236208 : Nat := 118140960795 + 3236208 * 2 ^ 59
def prefixEnd_3236208 : Nat := 4983230072969 + 3 ^ 40 * 3236208 * 2
def baseEnd_3236208 : Nat := 1107820134617053036677971

theorem tailTrace_3236208 : CollatzResearch.WordTrace tailWord_3236208 prefixEnd_3236208 1107820134617053036677971 := by
  unfold tailWord_3236208
  simp only [CollatzResearch.WordTrace]
  refine ⟨59017101329889295584394639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78689468439852394112526185 59017101329889295584394639)
  ·
    refine ⟨88525651994833943376591959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59017101329889295584394639 88525651994833943376591959)
    ·
      refine ⟨132788477992250915064887939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88525651994833943376591959 132788477992250915064887939)
      ·
        refine ⟨199182716988376372597331909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132788477992250915064887939 199182716988376372597331909)
        ·
          refine ⟨37346759435320569861999733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199182716988376372597331909 37346759435320569861999733)
          ·
            refine ⟨3501258697061303424562475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37346759435320569861999733 3501258697061303424562475)
            ·
              refine ⟨5251888045591955136843713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501258697061303424562475 5251888045591955136843713)
              ·
                refine ⟨3938916034193966352632785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5251888045591955136843713 3938916034193966352632785)
                ·
                  refine ⟨2954187025645474764474589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3938916034193966352632785 2954187025645474764474589)
                  ·
                    refine ⟨1107820134617053036677971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954187025645474764474589 1107820134617053036677971)
                    ·
                      rfl

theorem cell22_3236208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_3236208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236208 prefixEnd_3236208 := by exact prefixLift 3236208
  have htrace : WordTrace (prefixWord ++ tailWord_3236208) baseStart_3236208 baseEnd_3236208 := by
    simpa [prefixWord, tailWord_3236208, baseEnd_3236208] using wordTrace_append hprefix tailTrace_3236208
  have hstable : (prefixWord ++ tailWord_3236208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236208).length < 2 ^ (prefixWord ++ tailWord_3236208).sum := by decide
  have hdescent : baseEnd_3236208 < baseStart_3236208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236225 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 2, 3]
def baseStart_3236225 : Nat := 118140960795 + 3236225 * 2 ^ 59
def prefixEnd_3236225 : Nat := 4983230072969 + 3 ^ 40 * 3236225 * 2
def baseEnd_3236225 : Nat := 1107825954064470659002919

theorem tailTrace_3236225 : CollatzResearch.WordTrace tailWord_3236225 prefixEnd_3236225 1107825954064470659002919 := by
  unfold tailWord_3236225
  simp only [CollatzResearch.WordTrace]
  refine ⟨118034822700717003072158129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78689881800478002048105419 118034822700717003072158129)
  ·
    refine ⟨88526117025537752304118597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118034822700717003072158129 88526117025537752304118597)
    ·
      refine ⟨16598646942288328557022237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88526117025537752304118597 16598646942288328557022237)
      ·
        refine ⟨6224492603358123208883339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16598646942288328557022237 6224492603358123208883339)
        ·
          refine ⟨9336738905037184813325009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224492603358123208883339 9336738905037184813325009)
          ·
            refine ⟨7002554178777888609993757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9336738905037184813325009 7002554178777888609993757)
            ·
              refine ⟨2625957817041708228747659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7002554178777888609993757 2625957817041708228747659)
              ·
                refine ⟨3938936725562562343121489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625957817041708228747659 3938936725562562343121489)
                ·
                  refine ⟨2954202544171921757341117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3938936725562562343121489 2954202544171921757341117)
                  ·
                    refine ⟨1107825954064470659002919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954202544171921757341117 1107825954064470659002919)
                    ·
                      rfl

theorem cell22_3236225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_3236225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236225 prefixEnd_3236225 := by exact prefixLift 3236225
  have htrace : WordTrace (prefixWord ++ tailWord_3236225) baseStart_3236225 baseEnd_3236225 := by
    simpa [prefixWord, tailWord_3236225, baseEnd_3236225] using wordTrace_append hprefix tailTrace_3236225
  have hstable : (prefixWord ++ tailWord_3236225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236225).length < 2 ^ (prefixWord ++ tailWord_3236225).sum := by decide
  have hdescent : baseEnd_3236225 < baseStart_3236225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236236 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_3236236 : Nat := 118140960795 + 3236236 * 2 ^ 59
def prefixEnd_3236236 : Nat := 4983230072969 + 3 ^ 40 * 3236236 * 2
def baseEnd_3236236 : Nat := 1107829719589270296977885

theorem tailTrace_3236236 : CollatzResearch.WordTrace tailWord_3236236 prefixEnd_3236236 1107829719589270296977885 := by
  unfold tailWord_3236236
  simp only [CollatzResearch.WordTrace]
  refine ⟨59017611951838575975404281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78690149269118101300539041 59017611951838575975404281)
  ·
    refine ⟨44263208963878931981553211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59017611951838575975404281 44263208963878931981553211)
    ·
      refine ⟨66394813445818397972329817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44263208963878931981553211 66394813445818397972329817)
      ·
        refine ⟨49796110084363798479247363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66394813445818397972329817 49796110084363798479247363)
        ·
          refine ⟨74694165126545697718871045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49796110084363798479247363 74694165126545697718871045)
          ·
            refine ⟨14005155961227318322288321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74694165126545697718871045 14005155961227318322288321)
            ·
              refine ⟨10503866970920488741716241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14005155961227318322288321 10503866970920488741716241)
              ·
                refine ⟨7877900228190366556287181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10503866970920488741716241 7877900228190366556287181)
                ·
                  refine ⟨2954212585571387458607693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7877900228190366556287181 2954212585571387458607693)
                  ·
                    refine ⟨1107829719589270296977885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954212585571387458607693 1107829719589270296977885)
                    ·
                      rfl

theorem cell22_3236236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_3236236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236236 prefixEnd_3236236 := by exact prefixLift 3236236
  have htrace : WordTrace (prefixWord ++ tailWord_3236236) baseStart_3236236 baseEnd_3236236 := by
    simpa [prefixWord, tailWord_3236236, baseEnd_3236236] using wordTrace_append hprefix tailTrace_3236236
  have hstable : (prefixWord ++ tailWord_3236236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236236).length < 2 ^ (prefixWord ++ tailWord_3236236).sum := by decide
  have hdescent : baseEnd_3236236 < baseStart_3236236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236238 : List Nat := [4, 1, 1, 4, 1, 3, 2, 6]
def baseStart_3236238 : Nat := 118140960795 + 3236238 * 2 ^ 59
def prefixEnd_3236238 : Nat := 4983230072969 + 3 ^ 40 * 3236238 * 2
def baseEnd_3236238 : Nat := 123092267136682550936431

theorem tailTrace_3236238 : CollatzResearch.WordTrace tailWord_3236238 prefixEnd_3236238 123092267136682550936431 := by
  unfold tailWord_3236238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754412106208738286547671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78690197899779937528254245 14754412106208738286547671)
  ·
    refine ⟨22131618159313107429821507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14754412106208738286547671 22131618159313107429821507)
    ·
      refine ⟨33197427238969661144732261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22131618159313107429821507 33197427238969661144732261)
      ·
        refine ⟨6224517607306811464637299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33197427238969661144732261 6224517607306811464637299)
        ·
          refine ⟨9336776410960217196955949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224517607306811464637299 9336776410960217196955949)
          ·
            refine ⟨3501291154110081448858481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9336776410960217196955949 3501291154110081448858481)
            ·
              refine ⟨2625968365582561086643861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3501291154110081448858481 2625968365582561086643861)
              ·
                refine ⟨123092267136682550936431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2625968365582561086643861 123092267136682550936431)
                ·
                  rfl

theorem cell22_3236238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_3236238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236238 prefixEnd_3236238 := by exact prefixLift 3236238
  have htrace : WordTrace (prefixWord ++ tailWord_3236238) baseStart_3236238 baseEnd_3236238 := by
    simpa [prefixWord, tailWord_3236238, baseEnd_3236238] using wordTrace_append hprefix tailTrace_3236238
  have hstable : (prefixWord ++ tailWord_3236238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236238).length < 2 ^ (prefixWord ++ tailWord_3236238).sum := by decide
  have hdescent : baseEnd_3236238 < baseStart_3236238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236276 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3236276 : Nat := 118140960795 + 3236276 * 2 ^ 59
def prefixEnd_3236276 : Nat := 4983230072969 + 3 ^ 40 * 3236276 * 2
def baseEnd_3236276 : Nat := 1107843412406723525977763

theorem tailTrace_3236276 : CollatzResearch.WordTrace tailWord_3236276 prefixEnd_3236276 1107843412406723525977763 := by
  unfold tailWord_3236276
  simp only [CollatzResearch.WordTrace]
  refine ⟨59018341411766119391132341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78691121882354825854843121 59018341411766119391132341)
  ·
    refine ⟨5532969507353073692918657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59018341411766119391132341 5532969507353073692918657)
    ·
      refine ⟨4149727130514805269688993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5532969507353073692918657 4149727130514805269688993)
      ·
        refine ⟨3112295347886103952266745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4149727130514805269688993 3112295347886103952266745)
        ·
          refine ⟨2334221510914577964200059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3112295347886103952266745 2334221510914577964200059)
          ·
            refine ⟨3501332266371866946300089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334221510914577964200059 3501332266371866946300089)
            ·
              refine ⟨2625999199778900209725067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3501332266371866946300089 2625999199778900209725067)
              ·
                refine ⟨3938998799668350314587601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625999199778900209725067 3938998799668350314587601)
                ·
                  refine ⟨2954249099751262735940701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3938998799668350314587601 2954249099751262735940701)
                  ·
                    refine ⟨1107843412406723525977763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954249099751262735940701 1107843412406723525977763)
                    ·
                      rfl

theorem cell22_3236276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3236276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236276 prefixEnd_3236276 := by exact prefixLift 3236276
  have htrace : WordTrace (prefixWord ++ tailWord_3236276) baseStart_3236276 baseEnd_3236276 := by
    simpa [prefixWord, tailWord_3236276, baseEnd_3236276] using wordTrace_append hprefix tailTrace_3236276
  have hstable : (prefixWord ++ tailWord_3236276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236276).length < 2 ^ (prefixWord ++ tailWord_3236276).sum := by decide
  have hdescent : baseEnd_3236276 < baseStart_3236276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236296 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_3236296 : Nat := 118140960795 + 3236296 * 2 ^ 59
def prefixEnd_3236296 : Nat := 4983230072969 + 3 ^ 40 * 3236296 * 2
def baseEnd_3236296 : Nat := 1107850258815450140477701

theorem tailTrace_3236296 : CollatzResearch.WordTrace tailWord_3236296 prefixEnd_3236296 1107850258815450140477701 := by
  unfold tailWord_3236296
  simp only [CollatzResearch.WordTrace]
  refine ⟨59018706141729891098996371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78691608188973188131995161 59018706141729891098996371)
  ·
    refine ⟨88528059212594836648494557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59018706141729891098996371 88528059212594836648494557)
    ·
      refine ⟨33198022204723063743185459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88528059212594836648494557 33198022204723063743185459)
      ·
        refine ⟨49797033307084595614778189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33198022204723063743185459 49797033307084595614778189)
        ·
          refine ⟨18673887490156723355541821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49797033307084595614778189 18673887490156723355541821)
          ·
            refine ⟨7002707808808771258328183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18673887490156723355541821 7002707808808771258328183)
            ·
              refine ⟨10504061713213156887492275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002707808808771258328183 10504061713213156887492275)
              ·
                refine ⟨15756092569819735331238413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10504061713213156887492275 15756092569819735331238413)
                ·
                  refine ⟨5908534713682400749214405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15756092569819735331238413 5908534713682400749214405)
                  ·
                    refine ⟨1107850258815450140477701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5908534713682400749214405 1107850258815450140477701)
                    ·
                      rfl

theorem cell22_3236296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_3236296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236296 prefixEnd_3236296 := by exact prefixLift 3236296
  have htrace : WordTrace (prefixWord ++ tailWord_3236296) baseStart_3236296 baseEnd_3236296 := by
    simpa [prefixWord, tailWord_3236296, baseEnd_3236296] using wordTrace_append hprefix tailTrace_3236296
  have hstable : (prefixWord ++ tailWord_3236296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236296).length < 2 ^ (prefixWord ++ tailWord_3236296).sum := by decide
  have hdescent : baseEnd_3236296 < baseStart_3236296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236313 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 1, 4]
def baseStart_3236313 : Nat := 118140960795 + 3236313 * 2 ^ 59
def prefixEnd_3236313 : Nat := 4983230072969 + 3 ^ 40 * 3236313 * 2
def baseEnd_3236313 : Nat := 1107856078262867762802649

theorem tailTrace_3236313 : CollatzResearch.WordTrace tailWord_3236313 prefixEnd_3236313 1107856078262867762802649 := by
  unfold tailWord_3236313
  simp only [CollatzResearch.WordTrace]
  refine ⟨118038032324398194101361593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78692021549598796067574395 118038032324398194101361593)
  ·
    refine ⟨88528524243298645576021195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118038032324398194101361593 88528524243298645576021195)
    ·
      refine ⟨132792786364947968364031793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88528524243298645576021195 132792786364947968364031793)
      ·
        refine ⟨99594589773710976273023845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132792786364947968364031793 99594589773710976273023845)
        ·
          refine ⟨18673985582570808051191971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99594589773710976273023845 18673985582570808051191971)
          ·
            refine ⟨28010978373856212076787957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18673985582570808051191971 28010978373856212076787957)
            ·
              refine ⟨2626029222549019882198871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28010978373856212076787957 2626029222549019882198871)
              ·
                refine ⟨3939043833823529823298307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626029222549019882198871 3939043833823529823298307)
                ·
                  refine ⟨5908565750735294734947461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939043833823529823298307 5908565750735294734947461)
                  ·
                    refine ⟨1107856078262867762802649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5908565750735294734947461 1107856078262867762802649)
                    ·
                      rfl

theorem cell22_3236313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 4].length) (baseStart_3236313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236313 prefixEnd_3236313 := by exact prefixLift 3236313
  have htrace : WordTrace (prefixWord ++ tailWord_3236313) baseStart_3236313 baseEnd_3236313 := by
    simpa [prefixWord, tailWord_3236313, baseEnd_3236313] using wordTrace_append hprefix tailTrace_3236313
  have hstable : (prefixWord ++ tailWord_3236313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236313).length < 2 ^ (prefixWord ++ tailWord_3236313).sum := by decide
  have hdescent : baseEnd_3236313 < baseStart_3236313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236324 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_3236324 : Nat := 118140960795 + 3236324 * 2 ^ 59
def prefixEnd_3236324 : Nat := 4983230072969 + 3 ^ 40 * 3236324 * 2
def baseEnd_3236324 : Nat := 1107859843787667400777615

theorem tailTrace_3236324 : CollatzResearch.WordTrace tailWord_3236324 prefixEnd_3236324 1107859843787667400777615 := by
  unfold tailWord_3236324
  simp only [CollatzResearch.WordTrace]
  refine ⟨59019216763679171490006013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78692289018238895320008017 59019216763679171490006013)
  ·
    refine ⟨22132206286379689308752255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59019216763679171490006013 22132206286379689308752255)
    ·
      refine ⟨33198309429569533963128383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22132206286379689308752255 33198309429569533963128383)
      ·
        refine ⟨49797464144354300944692575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33198309429569533963128383 49797464144354300944692575)
        ·
          refine ⟨74696196216531451417038863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49797464144354300944692575 74696196216531451417038863)
          ·
            refine ⟨112044294324797177125558295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74696196216531451417038863 112044294324797177125558295)
            ·
              refine ⟨168066441487195765688337443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112044294324797177125558295 168066441487195765688337443)
              ·
                refine ⟨252099662230793648532506165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168066441487195765688337443 252099662230793648532506165)
                ·
                  refine ⟨23634343334136904549922453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252099662230793648532506165 23634343334136904549922453)
                  ·
                    refine ⟨1107859843787667400777615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23634343334136904549922453 1107859843787667400777615)
                    ·
                      rfl

theorem cell22_3236324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_3236324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236324 prefixEnd_3236324 := by exact prefixLift 3236324
  have htrace : WordTrace (prefixWord ++ tailWord_3236324) baseStart_3236324 baseEnd_3236324 := by
    simpa [prefixWord, tailWord_3236324, baseEnd_3236324] using wordTrace_append hprefix tailTrace_3236324
  have hstable : (prefixWord ++ tailWord_3236324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236324).length < 2 ^ (prefixWord ++ tailWord_3236324).sum := by decide
  have hdescent : baseEnd_3236324 < baseStart_3236324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236328 : List Nat := [2, 1, 4, 1, 1, 4, 1, 4, 4]
def baseStart_3236328 : Nat := 118140960795 + 3236328 * 2 ^ 59
def prefixEnd_3236328 : Nat := 4983230072969 + 3 ^ 40 * 3236328 * 2
def baseEnd_3236328 : Nat := 369287071023137574559201

theorem tailTrace_3236328 : CollatzResearch.WordTrace tailWord_3236328 prefixEnd_3236328 369287071023137574559201 := by
  unfold tailWord_3236328
  simp only [CollatzResearch.WordTrace]
  refine ⟨59019289709671925831578819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78692386279562567775438425 59019289709671925831578819)
  ·
    refine ⟨88528934564507888747368229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59019289709671925831578819 88528934564507888747368229)
    ·
      refine ⟨16599175230845229140131543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88528934564507888747368229 16599175230845229140131543)
      ·
        refine ⟨24898762846267843710197315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16599175230845229140131543 24898762846267843710197315)
        ·
          refine ⟨37348144269401765565295973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24898762846267843710197315 37348144269401765565295973)
          ·
            refine ⟨7002777050512831043492995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37348144269401765565295973 7002777050512831043492995)
            ·
              refine ⟨10504165575769246565239493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002777050512831043492995 10504165575769246565239493)
              ·
                refine ⟨1969531045456733730982405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10504165575769246565239493 1969531045456733730982405)
                ·
                  refine ⟨369287071023137574559201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1969531045456733730982405 369287071023137574559201)
                  ·
                    rfl

theorem cell22_3236328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 4].length) (baseStart_3236328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236328 prefixEnd_3236328 := by exact prefixLift 3236328
  have htrace : WordTrace (prefixWord ++ tailWord_3236328) baseStart_3236328 baseEnd_3236328 := by
    simpa [prefixWord, tailWord_3236328, baseEnd_3236328] using wordTrace_append hprefix tailTrace_3236328
  have hstable : (prefixWord ++ tailWord_3236328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236328).length < 2 ^ (prefixWord ++ tailWord_3236328).sum := by decide
  have hdescent : baseEnd_3236328 < baseStart_3236328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236369 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3236369 : Nat := 118140960795 + 3236369 * 2 ^ 59
def prefixEnd_3236369 : Nat := 4983230072969 + 3 ^ 40 * 3236369 * 2
def baseEnd_3236369 : Nat := 1107875248207302283402477

theorem tailTrace_3236369 : CollatzResearch.WordTrace tailWord_3236369 prefixEnd_3236369 1107875248207302283402477 := by
  unfold tailWord_3236369
  simp only [CollatzResearch.WordTrace]
  refine ⟨118040074812195315665400161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78693383208130210443600107 118040074812195315665400161)
  ·
    refine ⟨88530056109146486749050121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118040074812195315665400161 88530056109146486749050121)
    ·
      refine ⟨66397542081859865061787591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88530056109146486749050121 66397542081859865061787591)
      ·
        refine ⟨99596313122789797592681387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66397542081859865061787591 99596313122789797592681387)
        ·
          refine ⟨149394469684184696389022081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99596313122789797592681387 149394469684184696389022081)
          ·
            refine ⟨112045852263138522291766561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149394469684184696389022081 112045852263138522291766561)
            ·
              refine ⟨84034389197353891718824921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112045852263138522291766561 84034389197353891718824921)
              ·
                refine ⟨63025791898015418789118691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84034389197353891718824921 63025791898015418789118691)
                ·
                  refine ⟨94538687847023128183678037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63025791898015418789118691 94538687847023128183678037)
                  ·
                    refine ⟨1107875248207302283402477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94538687847023128183678037 1107875248207302283402477)
                    ·
                      rfl

theorem cell22_3236369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3236369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236369 prefixEnd_3236369 := by exact prefixLift 3236369
  have htrace : WordTrace (prefixWord ++ tailWord_3236369) baseStart_3236369 baseEnd_3236369 := by
    simpa [prefixWord, tailWord_3236369, baseEnd_3236369] using wordTrace_append hprefix tailTrace_3236369
  have hstable : (prefixWord ++ tailWord_3236369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236369).length < 2 ^ (prefixWord ++ tailWord_3236369).sum := by decide
  have hdescent : baseEnd_3236369 < baseStart_3236369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236371 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 5, 3]
def baseStart_3236371 : Nat := 118140960795 + 3236371 * 2 ^ 59
def prefixEnd_3236371 : Nat := 4983230072969 + 3 ^ 40 * 3236371 * 2
def baseEnd_3236371 : Nat := 1107875932848174944852471

theorem tailTrace_3236371 : CollatzResearch.WordTrace tailWord_3236371 prefixEnd_3236371 1107875932848174944852471 := by
  unfold tailWord_3236371
  simp only [CollatzResearch.WordTrace]
  refine ⟨118040147758188070006972967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78693431838792046671315311 118040147758188070006972967)
  ·
    refine ⟨177060221637282105010459451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118040147758188070006972967 177060221637282105010459451)
    ·
      refine ⟨265590332455923157515689177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177060221637282105010459451 265590332455923157515689177)
      ·
        refine ⟨199192749341942368136766883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265590332455923157515689177 199192749341942368136766883)
        ·
          refine ⟨298789124012913552205150325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199192749341942368136766883 298789124012913552205150325)
          ·
            refine ⟨28011480376210645519232843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298789124012913552205150325 28011480376210645519232843)
            ·
              refine ⟨42017220564315968278849265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28011480376210645519232843 42017220564315968278849265)
              ·
                refine ⟨31512915423236976209136949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42017220564315968278849265 31512915423236976209136949)
                ·
                  refine ⟨2954335820928466519606589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31512915423236976209136949 2954335820928466519606589)
                  ·
                    refine ⟨1107875932848174944852471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954335820928466519606589 1107875932848174944852471)
                    ·
                      rfl

theorem cell22_3236371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 3].length) (baseStart_3236371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236371 prefixEnd_3236371 := by exact prefixLift 3236371
  have htrace : WordTrace (prefixWord ++ tailWord_3236371) baseStart_3236371 baseEnd_3236371 := by
    simpa [prefixWord, tailWord_3236371, baseEnd_3236371] using wordTrace_append hprefix tailTrace_3236371
  have hstable : (prefixWord ++ tailWord_3236371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236371).length < 2 ^ (prefixWord ++ tailWord_3236371).sum := by decide
  have hdescent : baseEnd_3236371 < baseStart_3236371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236401 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 5]
def baseStart_3236401 : Nat := 118140960795 + 3236401 * 2 ^ 59
def prefixEnd_3236401 : Nat := 4983230072969 + 3 ^ 40 * 3236401 * 2
def baseEnd_3236401 : Nat := 369295400820421622200793

theorem tailTrace_3236401 : CollatzResearch.WordTrace tailWord_3236401 prefixEnd_3236401 369295400820421622200793 := by
  unfold tailWord_3236401
  simp only [CollatzResearch.WordTrace]
  refine ⟨118041241948079385130565057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78694161298719590087043371 118041241948079385130565057)
  ·
    refine ⟨88530931461059538847923793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118041241948079385130565057 88530931461059538847923793)
    ·
      refine ⟨66398198595794654135942845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88530931461059538847923793 66398198595794654135942845)
      ·
        refine ⟨24899324473422995300978567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66398198595794654135942845 24899324473422995300978567)
        ·
          refine ⟨37348986710134492951467851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24899324473422995300978567 37348986710134492951467851)
          ·
            refine ⟨56023480065201739427201777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37348986710134492951467851 56023480065201739427201777)
            ·
              refine ⟨42017610048901304570401333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56023480065201739427201777 42017610048901304570401333)
              ·
                refine ⟨3939150942084497303475125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42017610048901304570401333 3939150942084497303475125)
                ·
                  refine ⟨369295400820421622200793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3939150942084497303475125 369295400820421622200793)
                  ·
                    rfl

theorem cell22_3236401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_3236401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236401 prefixEnd_3236401 := by exact prefixLift 3236401
  have htrace : WordTrace (prefixWord ++ tailWord_3236401) baseStart_3236401 baseEnd_3236401 := by
    simpa [prefixWord, tailWord_3236401, baseEnd_3236401] using wordTrace_append hprefix tailTrace_3236401
  have hstable : (prefixWord ++ tailWord_3236401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236401).length < 2 ^ (prefixWord ++ tailWord_3236401).sum := by decide
  have hdescent : baseEnd_3236401 < baseStart_3236401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236476 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_3236476 : Nat := 118140960795 + 3236476 * 2 ^ 59
def prefixEnd_3236476 : Nat := 4983230072969 + 3 ^ 40 * 3236476 * 2
def baseEnd_3236476 : Nat := 1107911876493989670977149

theorem tailTrace_3236476 : CollatzResearch.WordTrace tailWord_3236476 prefixEnd_3236476 1107911876493989670977149 := by
  unfold tailWord_3236476
  simp only [CollatzResearch.WordTrace]
  refine ⟨59021988711403836469772641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78695984948538448626363521 59021988711403836469772641)
  ·
    refine ⟨44266491533552877352329481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59021988711403836469772641 44266491533552877352329481)
    ·
      refine ⟨33199868650164658014247111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44266491533552877352329481 33199868650164658014247111)
      ·
        refine ⟨49799802975246987021370667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33199868650164658014247111 49799802975246987021370667)
        ·
          refine ⟨74699704462870480532056001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49799802975246987021370667 74699704462870480532056001)
          ·
            refine ⟨56024778347152860399042001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74699704462870480532056001 56024778347152860399042001)
            ·
              refine ⟨42018583760364645299281501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56024778347152860399042001 42018583760364645299281501)
              ·
                refine ⟨15756968910136741987230563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42018583760364645299281501 15756968910136741987230563)
                ·
                  refine ⟨23635453365205112980845845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15756968910136741987230563 23635453365205112980845845)
                  ·
                    refine ⟨1107911876493989670977149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23635453365205112980845845 1107911876493989670977149)
                    ·
                      rfl

theorem cell22_3236476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_3236476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236476 prefixEnd_3236476 := by exact prefixLift 3236476
  have htrace : WordTrace (prefixWord ++ tailWord_3236476) baseStart_3236476 baseEnd_3236476 := by
    simpa [prefixWord, tailWord_3236476, baseEnd_3236476] using wordTrace_append hprefix tailTrace_3236476
  have hstable : (prefixWord ++ tailWord_3236476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236476).length < 2 ^ (prefixWord ++ tailWord_3236476).sum := by decide
  have hdescent : baseEnd_3236476 < baseStart_3236476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236508 : List Nat := [2, 2, 3, 2, 2, 1, 3, 7]
def baseStart_3236508 : Nat := 118140960795 + 3236508 * 2 ^ 59
def prefixEnd_3236508 : Nat := 4983230072969 + 3 ^ 40 * 3236508 * 2
def baseEnd_3236508 : Nat := 123102536749772472686339

theorem tailTrace_3236508 : CollatzResearch.WordTrace tailWord_3236508 prefixEnd_3236508 123102536749772472686339 := by
  unfold tailWord_3236508
  simp only [CollatzResearch.WordTrace]
  refine ⟨59022572279345871202355089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78696763039127828269806785 59022572279345871202355089)
  ·
    refine ⟨44266929209509403401766317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59022572279345871202355089 44266929209509403401766317)
    ·
      refine ⟨16600098453566026275662369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44266929209509403401766317 16600098453566026275662369)
      ·
        refine ⟨12450073840174519706746777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16600098453566026275662369 12450073840174519706746777)
        ·
          refine ⟨9337555380130889780060083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12450073840174519706746777 9337555380130889780060083)
          ·
            refine ⟨14006333070196334670090125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9337555380130889780060083 14006333070196334670090125)
            ·
              refine ⟨5252374901323625501283797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14006333070196334670090125 5252374901323625501283797)
              ·
                refine ⟨123102536749772472686339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5252374901323625501283797 123102536749772472686339)
                ·
                  rfl

theorem cell22_3236508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 7].length) (baseStart_3236508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236508 prefixEnd_3236508 := by exact prefixLift 3236508
  have htrace : WordTrace (prefixWord ++ tailWord_3236508) baseStart_3236508 baseEnd_3236508 := by
    simpa [prefixWord, tailWord_3236508, baseEnd_3236508] using wordTrace_append hprefix tailTrace_3236508
  have hstable : (prefixWord ++ tailWord_3236508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236508).length < 2 ^ (prefixWord ++ tailWord_3236508).sum := by decide
  have hdescent : baseEnd_3236508 < baseStart_3236508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236525 : List Nat := [1, 5, 2, 1, 1, 3, 3, 6]
def baseStart_3236525 : Nat := 118140960795 + 3236525 * 2 ^ 59
def prefixEnd_3236525 : Nat := 4983230072969 + 3 ^ 40 * 3236525 * 2
def baseEnd_3236525 : Nat := 123103183355041097389111

theorem tailTrace_3236525 : CollatzResearch.WordTrace tailWord_3236525 prefixEnd_3236525 123103183355041097389111 := by
  unfold tailWord_3236525
  simp only [CollatzResearch.WordTrace]
  refine ⟨118045764599630154308079029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78697176399753436205386019 118045764599630154308079029)
  ·
    refine ⟨11066790431215326966382409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118045764599630154308079029 11066790431215326966382409)
    ·
      refine ⟨8300092823411495224786807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11066790431215326966382409 8300092823411495224786807)
      ·
        refine ⟨12450139235117242837180211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8300092823411495224786807 12450139235117242837180211)
        ·
          refine ⟨18675208852675864255770317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12450139235117242837180211 18675208852675864255770317)
          ·
            refine ⟨7003203319753449095913869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18675208852675864255770317 7003203319753449095913869)
            ·
              refine ⟨2626201244907543410967701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7003203319753449095913869 2626201244907543410967701)
              ·
                refine ⟨123103183355041097389111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2626201244907543410967701 123103183355041097389111)
                ·
                  rfl

theorem cell22_3236525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 6].length) (baseStart_3236525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236525 prefixEnd_3236525 := by exact prefixLift 3236525
  have htrace : WordTrace (prefixWord ++ tailWord_3236525) baseStart_3236525 baseEnd_3236525 := by
    simpa [prefixWord, tailWord_3236525, baseEnd_3236525] using wordTrace_append hprefix tailTrace_3236525
  have hstable : (prefixWord ++ tailWord_3236525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236525).length < 2 ^ (prefixWord ++ tailWord_3236525).sum := by decide
  have hdescent : baseEnd_3236525 < baseStart_3236525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236568 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_3236568 : Nat := 118140960795 + 3236568 * 2 ^ 59
def prefixEnd_3236568 : Nat := 4983230072969 + 3 ^ 40 * 3236568 * 2
def baseEnd_3236568 : Nat := 1107943369974132097676867

theorem tailTrace_3236568 : CollatzResearch.WordTrace tailWord_3236568 prefixEnd_3236568 1107943369974132097676867 := by
  unfold tailWord_3236568
  simp only [CollatzResearch.WordTrace]
  refine ⟨59023666469237186325947179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78698221958982915101262905 59023666469237186325947179)
  ·
    refine ⟨88535499703855779488920769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59023666469237186325947179 88535499703855779488920769)
    ·
      refine ⟨66401624777891834616690577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88535499703855779488920769 66401624777891834616690577)
      ·
        refine ⟨49801218583418875962517933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66401624777891834616690577 49801218583418875962517933)
        ·
          refine ⟨18675456968782078485944225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49801218583418875962517933 18675456968782078485944225)
          ·
            refine ⟨14006592726586558864458169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18675456968782078485944225 14006592726586558864458169)
            ·
              refine ⟨10504944544939919148343627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14006592726586558864458169 10504944544939919148343627)
              ·
                refine ⟨15757416817409878722515441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10504944544939919148343627 15757416817409878722515441)
                ·
                  refine ⟨11818062613057409041886581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15757416817409878722515441 11818062613057409041886581)
                  ·
                    refine ⟨1107943369974132097676867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11818062613057409041886581 1107943369974132097676867)
                    ·
                      rfl

theorem cell22_3236568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_3236568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236568 prefixEnd_3236568 := by exact prefixLift 3236568
  have htrace : WordTrace (prefixWord ++ tailWord_3236568) baseStart_3236568 baseEnd_3236568 := by
    simpa [prefixWord, tailWord_3236568, baseEnd_3236568] using wordTrace_append hprefix tailTrace_3236568
  have hstable : (prefixWord ++ tailWord_3236568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236568).length < 2 ^ (prefixWord ++ tailWord_3236568).sum := by decide
  have hdescent : baseEnd_3236568 < baseStart_3236568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236570 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_3236570 : Nat := 118140960795 + 3236570 * 2 ^ 59
def prefixEnd_3236570 : Nat := 4983230072969 + 3 ^ 40 * 3236570 * 2
def baseEnd_3236570 : Nat := 369314684871668253042287

theorem tailTrace_3236570 : CollatzResearch.WordTrace tailWord_3236570 prefixEnd_3236570 369314684871668253042287 := by
  unfold tailWord_3236570
  simp only [CollatzResearch.WordTrace]
  refine ⟨29511851471116781748366791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78698270589644751328978109 29511851471116781748366791)
  ·
    refine ⟨44267777206675172622550187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29511851471116781748366791 44267777206675172622550187)
    ·
      refine ⟨66401665810012758933825281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44267777206675172622550187 66401665810012758933825281)
      ·
        refine ⟨49801249357509569200368961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66401665810012758933825281 49801249357509569200368961)
        ·
          refine ⟨37350937018132176900276721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49801249357509569200368961 37350937018132176900276721)
          ·
            refine ⟨28013202763599132675207541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37350937018132176900276721 28013202763599132675207541)
            ·
              refine ⟨2626237759087418688300707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28013202763599132675207541 2626237759087418688300707)
              ·
                refine ⟨3939356638631128032451061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626237759087418688300707 3939356638631128032451061)
                ·
                  refine ⟨369314684871668253042287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3939356638631128032451061 369314684871668253042287)
                  ·
                    rfl

theorem cell22_3236570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_3236570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236570 prefixEnd_3236570 := by exact prefixLift 3236570
  have htrace : WordTrace (prefixWord ++ tailWord_3236570) baseStart_3236570 baseEnd_3236570 := by
    simpa [prefixWord, tailWord_3236570, baseEnd_3236570] using wordTrace_append hprefix tailTrace_3236570
  have hstable : (prefixWord ++ tailWord_3236570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236570).length < 2 ^ (prefixWord ++ tailWord_3236570).sum := by decide
  have hdescent : baseEnd_3236570 < baseStart_3236570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236615 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 6]
def baseStart_3236615 : Nat := 118140960795 + 3236615 * 2 ^ 59
def prefixEnd_3236615 : Nat := 4983230072969 + 3 ^ 40 * 3236615 * 2
def baseEnd_3236615 : Nat := 369319819678213213917241

theorem tailTrace_3236615 : CollatzResearch.WordTrace tailWord_3236615 prefixEnd_3236615 369319819678213213917241 := by
  unfold tailWord_3236615
  simp only [CollatzResearch.WordTrace]
  refine ⟨118049047169304099678855299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78699364779536066452570199 118049047169304099678855299)
  ·
    refine ⟨177073570753956149518282949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118049047169304099678855299 177073570753956149518282949)
    ·
      refine ⟨33201294516366778034678053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177073570753956149518282949 33201294516366778034678053)
      ·
        refine ⟨6225242721818770881502135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33201294516366778034678053 6225242721818770881502135)
        ·
          refine ⟨9337864082728156322253203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6225242721818770881502135 9337864082728156322253203)
          ·
            refine ⟨14006796124092234483379805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9337864082728156322253203 14006796124092234483379805)
            ·
              refine ⟨5252548546534587931267427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14006796124092234483379805 5252548546534587931267427)
              ·
                refine ⟨7878822819801881896901141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252548546534587931267427 7878822819801881896901141)
                ·
                  refine ⟨369319819678213213917241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7878822819801881896901141 369319819678213213917241)
                  ·
                    rfl

theorem cell22_3236615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 6].length) (baseStart_3236615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236615 prefixEnd_3236615 := by exact prefixLift 3236615
  have htrace : WordTrace (prefixWord ++ tailWord_3236615) baseStart_3236615 baseEnd_3236615 := by
    simpa [prefixWord, tailWord_3236615, baseEnd_3236615] using wordTrace_append hprefix tailTrace_3236615
  have hstable : (prefixWord ++ tailWord_3236615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236615).length < 2 ^ (prefixWord ++ tailWord_3236615).sum := by decide
  have hdescent : baseEnd_3236615 < baseStart_3236615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236645 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_3236645 : Nat := 118140960795 + 3236645 * 2 ^ 59
def prefixEnd_3236645 : Nat := 4983230072969 + 3 ^ 40 * 3236645 * 2
def baseEnd_3236645 : Nat := 1107969728647729563501631

theorem tailTrace_3236645 : CollatzResearch.WordTrace tailWord_3236645 prefixEnd_3236645 1107969728647729563501631 := by
  unfold tailWord_3236645
  simp only [CollatzResearch.WordTrace]
  refine ⟨118050141359195414802447389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78700094239463609868298259 118050141359195414802447389)
  ·
    refine ⟨44268803009698280550917771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118050141359195414802447389 44268803009698280550917771)
    ·
      refine ⟨66403204514547420826376657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44268803009698280550917771 66403204514547420826376657)
      ·
        refine ⟨49802403385910565619782493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66403204514547420826376657 49802403385910565619782493)
        ·
          refine ⟨18675901269716462107418435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49802403385910565619782493 18675901269716462107418435)
          ·
            refine ⟨28013851904574693161127653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18675901269716462107418435 28013851904574693161127653)
            ·
              refine ⟨5252597232107754967711435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28013851904574693161127653 5252597232107754967711435)
              ·
                refine ⟨7878895848161632451567153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252597232107754967711435 7878895848161632451567153)
                ·
                  refine ⟨5909171886121224338675365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7878895848161632451567153 5909171886121224338675365)
                  ·
                    refine ⟨1107969728647729563501631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5909171886121224338675365 1107969728647729563501631)
                    ·
                      rfl

theorem cell22_3236645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_3236645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236645 prefixEnd_3236645 := by exact prefixLift 3236645
  have htrace : WordTrace (prefixWord ++ tailWord_3236645) baseStart_3236645 baseEnd_3236645 := by
    simpa [prefixWord, tailWord_3236645, baseEnd_3236645] using wordTrace_append hprefix tailTrace_3236645
  have hstable : (prefixWord ++ tailWord_3236645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236645).length < 2 ^ (prefixWord ++ tailWord_3236645).sum := by decide
  have hdescent : baseEnd_3236645 < baseStart_3236645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236660 : List Nat := [2, 5, 1, 1, 3, 10]
def baseStart_3236660 : Nat := 118140960795 + 3236660 * 2 ^ 59
def prefixEnd_3236660 : Nat := 4983230072969 + 3 ^ 40 * 3236660 * 2
def baseEnd_3236660 : Nat := 13678702017954006473785

theorem tailTrace_3236660 : CollatzResearch.WordTrace tailWord_3236660 prefixEnd_3236660 13678702017954006473785 := by
  unfold tailWord_3236660
  simp only [CollatzResearch.WordTrace]
  refine ⟨59025344227070536182121717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78700458969427381576162289 59025344227070536182121717)
  ·
    refine ⟨5533626021287862767073911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59025344227070536182121717 5533626021287862767073911)
    ·
      refine ⟨8300439031931794150610867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5533626021287862767073911 8300439031931794150610867)
      ·
        refine ⟨12450658547897691225916301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8300439031931794150610867 12450658547897691225916301)
        ·
          refine ⟨4668996955461634209718613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12450658547897691225916301 4668996955461634209718613)
          ·
            refine ⟨13678702017954006473785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4668996955461634209718613 13678702017954006473785)
            ·
              rfl

theorem cell22_3236660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 10].length) (baseStart_3236660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236660 prefixEnd_3236660 := by exact prefixLift 3236660
  have htrace : WordTrace (prefixWord ++ tailWord_3236660) baseStart_3236660 baseEnd_3236660 := by
    simpa [prefixWord, tailWord_3236660, baseEnd_3236660] using wordTrace_append hprefix tailTrace_3236660
  have hstable : (prefixWord ++ tailWord_3236660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236660).length < 2 ^ (prefixWord ++ tailWord_3236660).sum := by decide
  have hdescent : baseEnd_3236660 < baseStart_3236660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236666 : List Nat := [3, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_3236666 : Nat := 118140960795 + 3236666 * 2 ^ 59
def prefixEnd_3236666 : Nat := 4983230072969 + 3 ^ 40 * 3236666 * 2
def baseEnd_3236666 : Nat := 369325639125630836242189

theorem tailTrace_3236666 : CollatzResearch.WordTrace tailWord_3236666 prefixEnd_3236666 369325639125630836242189 := by
  unfold tailWord_3236666
  simp only [CollatzResearch.WordTrace]
  refine ⟨29512726823029833847240463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78700604861412890259307901 29512726823029833847240463)
  ·
    refine ⟨44269090234544750770860695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29512726823029833847240463 44269090234544750770860695)
    ·
      refine ⟨66403635351817126156291043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44269090234544750770860695 66403635351817126156291043)
      ·
        refine ⟨99605453027725689234436565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66403635351817126156291043 99605453027725689234436565)
        ·
          refine ⟨2334502805337320841432107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 99605453027725689234436565 2334502805337320841432107)
          ·
            refine ⟨3501754208005981262148161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334502805337320841432107 3501754208005981262148161)
            ·
              refine ⟨2626315656004485946611121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3501754208005981262148161 2626315656004485946611121)
              ·
                refine ⟨1969736742003364459958341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2626315656004485946611121 1969736742003364459958341)
                ·
                  refine ⟨369325639125630836242189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1969736742003364459958341 369325639125630836242189)
                  ·
                    rfl

theorem cell22_3236666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_3236666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236666 prefixEnd_3236666 := by exact prefixLift 3236666
  have htrace : WordTrace (prefixWord ++ tailWord_3236666) baseStart_3236666 baseEnd_3236666 := by
    simpa [prefixWord, tailWord_3236666, baseEnd_3236666] using wordTrace_append hprefix tailTrace_3236666
  have hstable : (prefixWord ++ tailWord_3236666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236666).length < 2 ^ (prefixWord ++ tailWord_3236666).sum := by decide
  have hdescent : baseEnd_3236666 < baseStart_3236666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236675 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 3, 3]
def baseStart_3236675 : Nat := 118140960795 + 3236675 * 2 ^ 59
def prefixEnd_3236675 : Nat := 4983230072969 + 3 ^ 40 * 3236675 * 2
def baseEnd_3236675 : Nat := 1107979998260819485251539

theorem tailTrace_3236675 : CollatzResearch.WordTrace tailWord_3236675 prefixEnd_3236675 1107979998260819485251539 := by
  unfold tailWord_3236675
  simp only [CollatzResearch.WordTrace]
  refine ⟨118051235549086729926039479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78700823699391153284026319 118051235549086729926039479)
  ·
    refine ⟨177076853323630094889059219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118051235549086729926039479 177076853323630094889059219)
    ·
      refine ⟨265615279985445142333588829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177076853323630094889059219 265615279985445142333588829)
      ·
        refine ⟨99605729994541928375095811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265615279985445142333588829 99605729994541928375095811)
        ·
          refine ⟨149408594991812892562643717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99605729994541928375095811 149408594991812892562643717)
          ·
            refine ⟨28014111560964917355495697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149408594991812892562643717 28014111560964917355495697)
            ·
              refine ⟨21010583670723688016621773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28014111560964917355495697 21010583670723688016621773)
              ·
                refine ⟨7878968876521383006233165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21010583670723688016621773 7878968876521383006233165)
                ·
                  refine ⟨2954613328695518627337437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7878968876521383006233165 2954613328695518627337437)
                  ·
                    refine ⟨1107979998260819485251539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954613328695518627337437 1107979998260819485251539)
                    ·
                      rfl

theorem cell22_3236675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 3].length) (baseStart_3236675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236675 prefixEnd_3236675 := by exact prefixLift 3236675
  have htrace : WordTrace (prefixWord ++ tailWord_3236675) baseStart_3236675 baseEnd_3236675 := by
    simpa [prefixWord, tailWord_3236675, baseEnd_3236675] using wordTrace_append hprefix tailTrace_3236675
  have hstable : (prefixWord ++ tailWord_3236675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236675).length < 2 ^ (prefixWord ++ tailWord_3236675).sum := by decide
  have hdescent : baseEnd_3236675 < baseStart_3236675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236703 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 1, 7]
def baseStart_3236703 : Nat := 118140960795 + 3236703 * 2 ^ 59
def prefixEnd_3236703 : Nat := 4983230072969 + 3 ^ 40 * 3236703 * 2
def baseEnd_3236703 : Nat := 1107989583233036745551453

theorem tailTrace_3236703 : CollatzResearch.WordTrace tailWord_3236703 prefixEnd_3236703 1107989583233036745551453 := by
  unfold tailWord_3236703
  simp only [CollatzResearch.WordTrace]
  refine ⟨118052256792985290708058763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78701504528656860472039175 118052256792985290708058763)
  ·
    refine ⟨177078385189477936062088145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118052256792985290708058763 177078385189477936062088145)
    ·
      refine ⟨132808788892108452046566109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177078385189477936062088145 132808788892108452046566109)
      ·
        refine ⟨49803295834540669517462291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132808788892108452046566109 49803295834540669517462291)
        ·
          refine ⟨74704943751811004276193437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49803295834540669517462291 74704943751811004276193437)
          ·
            refine ⟨28014353906929126603572539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74704943751811004276193437 28014353906929126603572539)
            ·
              refine ⟨42021530860393689905358809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28014353906929126603572539 42021530860393689905358809)
              ·
                refine ⟨31516148145295267429019107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42021530860393689905358809 31516148145295267429019107)
                ·
                  refine ⟨47274222217942901143528661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31516148145295267429019107 47274222217942901143528661)
                  ·
                    refine ⟨1107989583233036745551453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47274222217942901143528661 1107989583233036745551453)
                    ·
                      rfl

theorem cell22_3236703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_3236703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236703 prefixEnd_3236703 := by exact prefixLift 3236703
  have htrace : WordTrace (prefixWord ++ tailWord_3236703) baseStart_3236703 baseEnd_3236703 := by
    simpa [prefixWord, tailWord_3236703, baseEnd_3236703] using wordTrace_append hprefix tailTrace_3236703
  have hstable : (prefixWord ++ tailWord_3236703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236703).length < 2 ^ (prefixWord ++ tailWord_3236703).sum := by decide
  have hdescent : baseEnd_3236703 < baseStart_3236703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236726 : List Nat := [5, 1, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_3236726 : Nat := 118140960795 + 3236726 * 2 ^ 59
def prefixEnd_3236726 : Nat := 4983230072969 + 3 ^ 40 * 3236726 * 2
def baseEnd_3236726 : Nat := 1107997456603072352226383

theorem tailTrace_3236726 : CollatzResearch.WordTrace tailWord_3236726 prefixEnd_3236726 1107997456603072352226383 := by
  unfold tailWord_3236726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378318479493872852259127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78702063781267977090764021 7378318479493872852259127)
  ·
    refine ⟨11067477719240809278388691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7378318479493872852259127 11067477719240809278388691)
    ·
      refine ⟨16601216578861213917583037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11067477719240809278388691 16601216578861213917583037)
      ·
        refine ⟨6225456217072955219093639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16601216578861213917583037 6225456217072955219093639)
        ·
          refine ⟨9338184325609432828640459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6225456217072955219093639 9338184325609432828640459)
          ·
            refine ⟨14007276488414149242960689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9338184325609432828640459 14007276488414149242960689)
            ·
              refine ⟨10505457366310611932220517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14007276488414149242960689 10505457366310611932220517)
              ·
                refine ⟨1969773256183239737291347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10505457366310611932220517 1969773256183239737291347)
                ·
                  refine ⟨2954659884274859605937021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969773256183239737291347 2954659884274859605937021)
                  ·
                    refine ⟨1107997456603072352226383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954659884274859605937021 1107997456603072352226383)
                    ·
                      rfl

theorem cell22_3236726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_3236726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236726 prefixEnd_3236726 := by exact prefixLift 3236726
  have htrace : WordTrace (prefixWord ++ tailWord_3236726) baseStart_3236726 baseEnd_3236726 := by
    simpa [prefixWord, tailWord_3236726, baseEnd_3236726] using wordTrace_append hprefix tailTrace_3236726
  have hstable : (prefixWord ++ tailWord_3236726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236726).length < 2 ^ (prefixWord ++ tailWord_3236726).sum := by decide
  have hdescent : baseEnd_3236726 < baseStart_3236726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236765 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_3236765 : Nat := 118140960795 + 3236765 * 2 ^ 59
def prefixEnd_3236765 : Nat := 4983230072969 + 3 ^ 40 * 3236765 * 2
def baseEnd_3236765 : Nat := 1108010807100089250501263

theorem tailTrace_3236765 : CollatzResearch.WordTrace tailWord_3236765 prefixEnd_3236765 1108010807100089250501263 := by
  unfold tailWord_3236765
  simp only [CollatzResearch.WordTrace]
  refine ⟨118054518118760675296815749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78703012079173783531210499 118054518118760675296815749)
  ·
    refine ⟨22135222147267626618152953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118054518118760675296815749 22135222147267626618152953)
    ·
      refine ⟨16601416610450719963614715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22135222147267626618152953 16601416610450719963614715)
      ·
        refine ⟨24902124915676079945422073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16601416610450719963614715 24902124915676079945422073)
        ·
          refine ⟨18676593686757059959066555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24902124915676079945422073 18676593686757059959066555)
          ·
            refine ⟨28014890530135589938599833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18676593686757059959066555 28014890530135589938599833)
            ·
              refine ⟨21011167897601692453949875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28014890530135589938599833 21011167897601692453949875)
              ·
                refine ⟨31516751846402538680924813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21011167897601692453949875 31516751846402538680924813)
                ·
                  refine ⟨11818781942400952005346805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31516751846402538680924813 11818781942400952005346805)
                  ·
                    refine ⟨1108010807100089250501263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11818781942400952005346805 1108010807100089250501263)
                    ·
                      rfl

theorem cell22_3236765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_3236765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236765 prefixEnd_3236765 := by exact prefixLift 3236765
  have htrace : WordTrace (prefixWord ++ tailWord_3236765) baseStart_3236765 baseEnd_3236765 := by
    simpa [prefixWord, tailWord_3236765, baseEnd_3236765] using wordTrace_append hprefix tailTrace_3236765
  have hstable : (prefixWord ++ tailWord_3236765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236765).length < 2 ^ (prefixWord ++ tailWord_3236765).sum := by decide
  have hdescent : baseEnd_3236765 < baseStart_3236765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236780 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_3236780 : Nat := 118140960795 + 3236780 * 2 ^ 59
def prefixEnd_3236780 : Nat := 4983230072969 + 3 ^ 40 * 3236780 * 2
def baseEnd_3236780 : Nat := 1108015941906634211376217

theorem tailTrace_3236780 : CollatzResearch.WordTrace tailWord_3236780 prefixEnd_3236780 1108015941906634211376217 := by
  unfold tailWord_3236780
  simp only [CollatzResearch.WordTrace]
  refine ⟨59027532606853166429305897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78703376809137555239074529 59027532606853166429305897)
  ·
    refine ⟨44270649455139874821979423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59027532606853166429305897 44270649455139874821979423)
    ·
      refine ⟨66405974182709812232969135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44270649455139874821979423 66405974182709812232969135)
      ·
        refine ⟨99608961274064718349453703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66405974182709812232969135 99608961274064718349453703)
        ·
          refine ⟨149413441911097077524180555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99608961274064718349453703 149413441911097077524180555)
          ·
            refine ⟨224120162866645616286270833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149413441911097077524180555 224120162866645616286270833)
            ·
              refine ⟨168090122149984212214703125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224120162866645616286270833 168090122149984212214703125)
              ·
                refine ⟨7879224475780509947564209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168090122149984212214703125 7879224475780509947564209)
                ·
                  refine ⟨5909418356835382460673157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7879224475780509947564209 5909418356835382460673157)
                  ·
                    refine ⟨1108015941906634211376217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5909418356835382460673157 1108015941906634211376217)
                    ·
                      rfl

theorem cell22_3236780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_3236780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236780 prefixEnd_3236780 := by exact prefixLift 3236780
  have htrace : WordTrace (prefixWord ++ tailWord_3236780) baseStart_3236780 baseEnd_3236780 := by
    simpa [prefixWord, tailWord_3236780, baseEnd_3236780] using wordTrace_append hprefix tailTrace_3236780
  have hstable : (prefixWord ++ tailWord_3236780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236780).length < 2 ^ (prefixWord ++ tailWord_3236780).sum := by decide
  have hdescent : baseEnd_3236780 < baseStart_3236780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236790 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_3236790 : Nat := 118140960795 + 3236790 * 2 ^ 59
def prefixEnd_3236790 : Nat := 4983230072969 + 3 ^ 40 * 3236790 * 2
def baseEnd_3236790 : Nat := 369339788370332506208729

theorem tailTrace_3236790 : CollatzResearch.WordTrace tailWord_3236790 prefixEnd_3236790 369339788370332506208729 := by
  unfold tailWord_3236790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378464371479381535404739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78703619962446736377650549 7378464371479381535404739)
  ·
    refine ⟨11067696557219072303107109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7378464371479381535404739 11067696557219072303107109)
    ·
      refine ⟨2075193104478576056832583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11067696557219072303107109 2075193104478576056832583)
      ·
        refine ⟨3112789656717864085248875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2075193104478576056832583 3112789656717864085248875)
        ·
          refine ⟨4669184485076796127873313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112789656717864085248875 4669184485076796127873313)
          ·
            refine ⟨3501888363807597095904985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4669184485076796127873313 3501888363807597095904985)
            ·
              refine ⟨2626416272855697821928739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3501888363807597095904985 2626416272855697821928739)
              ·
                refine ⟨3939624409283546732893109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626416272855697821928739 3939624409283546732893109)
                ·
                  refine ⟨369339788370332506208729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3939624409283546732893109 369339788370332506208729)
                  ·
                    rfl

theorem cell22_3236790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_3236790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236790 prefixEnd_3236790 := by exact prefixLift 3236790
  have htrace : WordTrace (prefixWord ++ tailWord_3236790) baseStart_3236790 baseEnd_3236790 := by
    simpa [prefixWord, tailWord_3236790, baseEnd_3236790] using wordTrace_append hprefix tailTrace_3236790
  have hstable : (prefixWord ++ tailWord_3236790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236790).length < 2 ^ (prefixWord ++ tailWord_3236790).sum := by decide
  have hdescent : baseEnd_3236790 < baseStart_3236790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236840 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 7]
def baseStart_3236840 : Nat := 118140960795 + 3236840 * 2 ^ 59
def prefixEnd_3236840 : Nat := 4983230072969 + 3 ^ 40 * 3236840 * 2
def baseEnd_3236840 : Nat := 369345493710938018292011

theorem tailTrace_3236840 : CollatzResearch.WordTrace tailWord_3236840 prefixEnd_3236840 369345493710938018292011 := by
  unfold tailWord_3236840
  simp only [CollatzResearch.WordTrace]
  refine ⟨59028626796744481552897987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78704835728992642070530649 59028626796744481552897987)
  ·
    refine ⟨88542940195116722329346981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59028626796744481552897987 88542940195116722329346981)
    ·
      refine ⟨16601801286584385436752559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88542940195116722329346981 16601801286584385436752559)
      ·
        refine ⟨24902701929876578155128839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16601801286584385436752559 24902701929876578155128839)
        ·
          refine ⟨37354052894814867232693259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24902701929876578155128839 37354052894814867232693259)
          ·
            refine ⟨56031079342222300849039889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37354052894814867232693259 56031079342222300849039889)
            ·
              refine ⟨42023309506666725636779917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56031079342222300849039889 42023309506666725636779917)
              ·
                refine ⟨15758741065000022113792469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42023309506666725636779917 15758741065000022113792469)
                ·
                  refine ⟨369345493710938018292011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15758741065000022113792469 369345493710938018292011)
                  ·
                    rfl

theorem cell22_3236840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_3236840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236840 prefixEnd_3236840 := by exact prefixLift 3236840
  have htrace : WordTrace (prefixWord ++ tailWord_3236840) baseStart_3236840 baseEnd_3236840 := by
    simpa [prefixWord, tailWord_3236840, baseEnd_3236840] using wordTrace_append hprefix tailTrace_3236840
  have hstable : (prefixWord ++ tailWord_3236840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236840).length < 2 ^ (prefixWord ++ tailWord_3236840).sum := by decide
  have hdescent : baseEnd_3236840 < baseStart_3236840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236968 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 2, 3]
def baseStart_3236968 : Nat := 118140960795 + 3236968 * 2 ^ 59
def prefixEnd_3236968 : Nat := 4983230072969 + 3 ^ 40 * 3236968 * 2
def baseEnd_3236968 : Nat := 1108080298148664387675641

theorem tailTrace_3236968 : CollatzResearch.WordTrace tailWord_3236968 prefixEnd_3236968 1108080298148664387675641 := by
  unfold tailWord_3236968
  simp only [CollatzResearch.WordTrace]
  refine ⟨59030961068512620483227779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78707948091350160644303705 59030961068512620483227779)
  ·
    refine ⟨88546441602768930724841669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59030961068512620483227779 88546441602768930724841669)
    ·
      refine ⟨16602457800519174510907813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88546441602768930724841669 16602457800519174510907813)
      ·
        refine ⟨3112960837597345220795215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16602457800519174510907813 3112960837597345220795215)
        ·
          refine ⟨4669441256396017831192823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112960837597345220795215 4669441256396017831192823)
          ·
            refine ⟨7004161884594026746789235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669441256396017831192823 7004161884594026746789235)
            ·
              refine ⟨10506242826891040120183853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7004161884594026746789235 10506242826891040120183853)
              ·
                refine ⟨3939841060084140045068945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10506242826891040120183853 3939841060084140045068945)
                ·
                  refine ⟨2954880795063105033801709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3939841060084140045068945 2954880795063105033801709)
                  ·
                    refine ⟨1108080298148664387675641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2954880795063105033801709 1108080298148664387675641)
                    ·
                      rfl

theorem cell22_3236968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_3236968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3236968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3236968 prefixEnd_3236968 := by exact prefixLift 3236968
  have htrace : WordTrace (prefixWord ++ tailWord_3236968) baseStart_3236968 baseEnd_3236968 := by
    simpa [prefixWord, tailWord_3236968, baseEnd_3236968] using wordTrace_append hprefix tailTrace_3236968
  have hstable : (prefixWord ++ tailWord_3236968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236968).length < 2 ^ (prefixWord ++ tailWord_3236968).sum := by decide
  have hdescent : baseEnd_3236968 < baseStart_3236968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237056 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_3237056 : Nat := 118140960795 + 3237056 * 2 ^ 59
def prefixEnd_3237056 : Nat := 4983230072969 + 3 ^ 40 * 3237056 * 2
def baseEnd_3237056 : Nat := 1108110422347061491475371

theorem tailTrace_3237056 : CollatzResearch.WordTrace tailWord_3237056 prefixEnd_3237056 1108110422347061491475371 := by
  unfold tailWord_3237056
  simp only [CollatzResearch.WordTrace]
  refine ⟨59032565880353215997829511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78710087840470954663772681 59032565880353215997829511)
  ·
    refine ⟨88548848820529823996744267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59032565880353215997829511 88548848820529823996744267)
    ·
      refine ⟨132823273230794735995116401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88548848820529823996744267 132823273230794735995116401)
      ·
        refine ⟨99617454923096051996337301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132823273230794735995116401 99617454923096051996337301)
        ·
          refine ⟨4669568199520127437328311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99617454923096051996337301 4669568199520127437328311)
          ·
            refine ⟨7004352299280191155992467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669568199520127437328311 7004352299280191155992467)
            ·
              refine ⟨10506528448920286733988701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7004352299280191155992467 10506528448920286733988701)
              ·
                refine ⟨3939948168345107525245763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10506528448920286733988701 3939948168345107525245763)
                ·
                  refine ⟨5909922252517661287868645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939948168345107525245763 5909922252517661287868645)
                  ·
                    refine ⟨1108110422347061491475371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5909922252517661287868645 1108110422347061491475371)
                    ·
                      rfl

theorem cell22_3237056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_3237056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237056 prefixEnd_3237056 := by exact prefixLift 3237056
  have htrace : WordTrace (prefixWord ++ tailWord_3237056) baseStart_3237056 baseEnd_3237056 := by
    simpa [prefixWord, tailWord_3237056, baseEnd_3237056] using wordTrace_append hprefix tailTrace_3237056
  have hstable : (prefixWord ++ tailWord_3237056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237056).length < 2 ^ (prefixWord ++ tailWord_3237056).sum := by decide
  have hdescent : baseEnd_3237056 < baseStart_3237056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237082 : List Nat := [3, 1, 1, 2, 2, 1, 1, 11]
def baseStart_3237082 : Nat := 118140960795 + 3237082 * 2 ^ 59
def prefixEnd_3237082 : Nat := 4983230072969 + 3 ^ 40 * 3237082 * 2
def baseEnd_3237082 : Nat := 123124369186489565591699

theorem tailTrace_3237082 : CollatzResearch.WordTrace tailWord_3237082 prefixEnd_3237082 123124369186489565591699 := by
  unfold tailWord_3237082
  simp only [CollatzResearch.WordTrace]
  refine ⟨29516520014653059609026375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78710720039074825624070333 29516520014653059609026375)
  ·
    refine ⟨44274780021979589413539563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29516520014653059609026375 44274780021979589413539563)
    ·
      refine ⟨66412170032969384120309345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44274780021979589413539563 66412170032969384120309345)
      ·
        refine ⟨49809127524727038090232009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66412170032969384120309345 49809127524727038090232009)
        ·
          refine ⟨37356845643545278567674007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49809127524727038090232009 37356845643545278567674007)
          ·
            refine ⟨56035268465317917851511011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37356845643545278567674007 56035268465317917851511011)
            ·
              refine ⟨84052902697976876777266517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56035268465317917851511011 84052902697976876777266517)
              ·
                refine ⟨123124369186489565591699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 84052902697976876777266517 123124369186489565591699)
                ·
                  rfl

theorem cell22_3237082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_3237082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237082 prefixEnd_3237082 := by exact prefixLift 3237082
  have htrace : WordTrace (prefixWord ++ tailWord_3237082) baseStart_3237082 baseEnd_3237082 := by
    simpa [prefixWord, tailWord_3237082, baseEnd_3237082] using wordTrace_append hprefix tailTrace_3237082
  have hstable : (prefixWord ++ tailWord_3237082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237082).length < 2 ^ (prefixWord ++ tailWord_3237082).sum := by decide
  have hdescent : baseEnd_3237082 < baseStart_3237082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237099 : List Nat := [1, 1, 1, 1, 2, 6, 4, 6]
def baseStart_3237099 : Nat := 118140960795 + 3237099 * 2 ^ 59
def prefixEnd_3237099 : Nat := 4983230072969 + 3 ^ 40 * 3237099 * 2
def baseEnd_3237099 : Nat := 123125015791758190294471

theorem tailTrace_3237099 : CollatzResearch.WordTrace tailWord_3237099 prefixEnd_3237099 123125015791758190294471 := by
  unfold tailWord_3237099
  simp only [CollatzResearch.WordTrace]
  refine ⟨118066700099550650339474351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78711133399700433559649567 118066700099550650339474351)
  ·
    refine ⟨177100050149325975509211527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118066700099550650339474351 177100050149325975509211527)
    ·
      refine ⟨265650075223988963263817291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177100050149325975509211527 265650075223988963263817291)
      ·
        refine ⟨398475112835983444895725937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265650075223988963263817291 398475112835983444895725937)
        ·
          refine ⟨298856334626987583671794453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398475112835983444895725937 298856334626987583671794453)
          ·
            refine ⟨14008890685640042984615365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 298856334626987583671794453 14008890685640042984615365)
            ·
              refine ⟨2626667003557508059615381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14008890685640042984615365 2626667003557508059615381)
              ·
                refine ⟨123125015791758190294471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2626667003557508059615381 123125015791758190294471)
                ·
                  rfl

theorem cell22_3237099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 6].length) (baseStart_3237099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237099 prefixEnd_3237099 := by exact prefixLift 3237099
  have htrace : WordTrace (prefixWord ++ tailWord_3237099) baseStart_3237099 baseEnd_3237099 := by
    simpa [prefixWord, tailWord_3237099, baseEnd_3237099] using wordTrace_append hprefix tailTrace_3237099
  have hstable : (prefixWord ++ tailWord_3237099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237099).length < 2 ^ (prefixWord ++ tailWord_3237099).sum := by decide
  have hdescent : baseEnd_3237099 < baseStart_3237099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237112 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_3237112 : Nat := 118140960795 + 3237112 * 2 ^ 59
def prefixEnd_3237112 : Nat := 4983230072969 + 3 ^ 40 * 3237112 * 2
def baseEnd_3237112 : Nat := 1108129592291496012075199

theorem tailTrace_3237112 : CollatzResearch.WordTrace tailWord_3237112 prefixEnd_3237112 1108129592291496012075199 := by
  unfold tailWord_3237112
  simp only [CollatzResearch.WordTrace]
  refine ⟨59033587124251776779848795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78711449499002369039798393 59033587124251776779848795)
  ·
    refine ⟨88550380686377665169773193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59033587124251776779848795 88550380686377665169773193)
    ·
      refine ⟨66412785514783248877329895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88550380686377665169773193 66412785514783248877329895)
      ·
        refine ⟨99619178272174873315994843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66412785514783248877329895 99619178272174873315994843)
        ·
          refine ⟨149428767408262309973992265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99619178272174873315994843 149428767408262309973992265)
          ·
            refine ⟨112071575556196732480494199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149428767408262309973992265 112071575556196732480494199)
            ·
              refine ⟨168107363334295098720741299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112071575556196732480494199 168107363334295098720741299)
              ·
                refine ⟨252161045001442648081111949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168107363334295098720741299 252161045001442648081111949)
                ·
                  refine ⟨94560391875540993030416981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252161045001442648081111949 94560391875540993030416981)
                  ·
                    refine ⟨1108129592291496012075199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94560391875540993030416981 1108129592291496012075199)
                    ·
                      rfl

theorem cell22_3237112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_3237112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237112 prefixEnd_3237112 := by exact prefixLift 3237112
  have htrace : WordTrace (prefixWord ++ tailWord_3237112) baseStart_3237112 baseEnd_3237112 := by
    simpa [prefixWord, tailWord_3237112, baseEnd_3237112] using wordTrace_append hprefix tailTrace_3237112
  have hstable : (prefixWord ++ tailWord_3237112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237112).length < 2 ^ (prefixWord ++ tailWord_3237112).sum := by decide
  have hdescent : baseEnd_3237112 < baseStart_3237112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237116 : List Nat := [2, 2, 2, 1, 6, 1, 8]
def baseStart_3237116 : Nat := 118140960795 + 3237116 * 2 ^ 59
def prefixEnd_3237116 : Nat := 4983230072969 + 3 ^ 40 * 3237116 * 2
def baseEnd_3237116 : Nat := 41041887465675604999081

theorem tailTrace_3237116 : CollatzResearch.WordTrace tailWord_3237116 prefixEnd_3237116 41041887465675604999081 := by
  unfold tailWord_3237116
  simp only [CollatzResearch.WordTrace]
  refine ⟨59033660070244531121421601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78711546760326041495228801 59033660070244531121421601)
  ·
    refine ⟨44275245052683398341066201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59033660070244531121421601 44275245052683398341066201)
    ·
      refine ⟨33206433789512548755799651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44275245052683398341066201 33206433789512548755799651)
      ·
        refine ⟨49809650684268823133699477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33206433789512548755799651 49809650684268823133699477)
        ·
          refine ⟨2334827375825101084392163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49809650684268823133699477 2334827375825101084392163)
          ·
            refine ⟨3502241063737651626588245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334827375825101084392163 3502241063737651626588245)
            ·
              refine ⟨41041887465675604999081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3502241063737651626588245 41041887465675604999081)
              ·
                rfl

theorem cell22_3237116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 8].length) (baseStart_3237116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237116 prefixEnd_3237116 := by exact prefixLift 3237116
  have htrace : WordTrace (prefixWord ++ tailWord_3237116) baseStart_3237116 baseEnd_3237116 := by
    simpa [prefixWord, tailWord_3237116, baseEnd_3237116] using wordTrace_append hprefix tailTrace_3237116
  have hstable : (prefixWord ++ tailWord_3237116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237116).length < 2 ^ (prefixWord ++ tailWord_3237116).sum := by decide
  have hdescent : baseEnd_3237116 < baseStart_3237116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237131 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 3, 3]
def baseStart_3237131 : Nat := 118140960795 + 3237131 * 2 ^ 59
def prefixEnd_3237131 : Nat := 4983230072969 + 3 ^ 40 * 3237131 * 2
def baseEnd_3237131 : Nat := 1108136096379786295850141

theorem tailTrace_3237131 : CollatzResearch.WordTrace tailWord_3237131 prefixEnd_3237131 1108136096379786295850141 := by
  unfold tailWord_3237131
  simp only [CollatzResearch.WordTrace]
  refine ⟨118067867235434719804639247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78711911490289813203092831 118067867235434719804639247)
  ·
    refine ⟨177101800853152079706958871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118067867235434719804639247 177101800853152079706958871)
    ·
      refine ⟨265652701279728119560438307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177101800853152079706958871 265652701279728119560438307)
      ·
        refine ⟨398479051919592179340657461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265652701279728119560438307 398479051919592179340657461)
        ·
          refine ⟨37357411117461766813186637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 398479051919592179340657461 37357411117461766813186637)
          ·
            refine ⟨14009029169048162554944989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37357411117461766813186637 14009029169048162554944989)
            ·
              refine ⟨5253385938393060958104371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14009029169048162554944989 5253385938393060958104371)
              ·
                refine ⟨7880078907589591437156557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5253385938393060958104371 7880078907589591437156557)
                ·
                  refine ⟨2955029590346096788933709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7880078907589591437156557 2955029590346096788933709)
                  ·
                    refine ⟨1108136096379786295850141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2955029590346096788933709 1108136096379786295850141)
                    ·
                      rfl

theorem cell22_3237131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 3].length) (baseStart_3237131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237131 prefixEnd_3237131 := by exact prefixLift 3237131
  have htrace : WordTrace (prefixWord ++ tailWord_3237131) baseStart_3237131 baseEnd_3237131 := by
    simpa [prefixWord, tailWord_3237131, baseEnd_3237131] using wordTrace_append hprefix tailTrace_3237131
  have hstable : (prefixWord ++ tailWord_3237131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237131).length < 2 ^ (prefixWord ++ tailWord_3237131).sum := by decide
  have hdescent : baseEnd_3237131 < baseStart_3237131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
