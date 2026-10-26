import V185TrunkScan23Chunk1391

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8245044 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_8245044 : Nat := 118140960795 + 8245044 * 2 ^ 59
def prefixEnd_8245044 : Nat := 4983230072969 + 3 ^ 40 * 8245044 * 2
def baseEnd_8245044 : Nat := 4233670589469144461131739

theorem tailTrace_8245044 : CollatzResearch.WordTrace tailWord_8245044 prefixEnd_8245044 4233670589469144461131739 := by
  unfold tailWord_8245044
  simp only [CollatzResearch.WordTrace]
  refine ⟨150360729970810602126223093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200480973294414136168297457 150360729970810602126223093)
  ·
    refine ⟨14096318434763493949333415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150360729970810602126223093 14096318434763493949333415)
    ·
      refine ⟨21144477652145240924000123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14096318434763493949333415 21144477652145240924000123)
      ·
        refine ⟨31716716478217861386000185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21144477652145240924000123 31716716478217861386000185)
        ·
          refine ⟨23787537358663396039500139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31716716478217861386000185 23787537358663396039500139)
          ·
            refine ⟨35681306037995094059250209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23787537358663396039500139 35681306037995094059250209)
            ·
              refine ⟨26760979528496320544437657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35681306037995094059250209 26760979528496320544437657)
              ·
                refine ⟨20070734646372240408328243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26760979528496320544437657 20070734646372240408328243)
                ·
                  refine ⟨30106101969558360612492365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20070734646372240408328243 30106101969558360612492365)
                  ·
                    refine ⟨11289788238584385229684637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30106101969558360612492365 11289788238584385229684637)
                    ·
                      refine ⟨4233670589469144461131739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11289788238584385229684637 4233670589469144461131739)
                      ·
                        rfl

theorem cell23_8245044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_8245044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245044 prefixEnd_8245044 := by exact prefixLift 8245044
  have htrace : WordTrace (prefixWord ++ tailWord_8245044) baseStart_8245044 baseEnd_8245044 := by
    simpa [prefixWord, tailWord_8245044, baseEnd_8245044] using wordTrace_append hprefix tailTrace_8245044
  have hstable : (prefixWord ++ tailWord_8245044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245044).length < 2 ^ (prefixWord ++ tailWord_8245044).sum := by decide
  have hdescent : baseEnd_8245044 < baseStart_8245044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245070 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_8245070 : Nat := 118140960795 + 8245070 * 2 ^ 59
def prefixEnd_8245070 : Nat := 4983230072969 + 3 ^ 40 * 8245070 * 2
def baseEnd_8245070 : Nat := 4233683939966161359406619

theorem tailTrace_8245070 : CollatzResearch.WordTrace tailWord_8245070 prefixEnd_8245070 4233683939966161359406619 := by
  unfold tailWord_8245070
  simp only [CollatzResearch.WordTrace]
  refine ⟨37590301029940876336611583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200481605493018007128595109 37590301029940876336611583)
  ·
    refine ⟨56385451544911314504917375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37590301029940876336611583 56385451544911314504917375)
    ·
      refine ⟨84578177317366971757376063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56385451544911314504917375 84578177317366971757376063)
      ·
        refine ⟨126867265976050457636064095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84578177317366971757376063 126867265976050457636064095)
        ·
          refine ⟨190300898964075686454096143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126867265976050457636064095 190300898964075686454096143)
          ·
            refine ⟨285451348446113529681144215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190300898964075686454096143 285451348446113529681144215)
            ·
              refine ⟨428177022669170294521716323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285451348446113529681144215 428177022669170294521716323)
              ·
                refine ⟨642265534003755441782574485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428177022669170294521716323 642265534003755441782574485)
                ·
                  refine ⟨30106196906426036333558179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 642265534003755441782574485 30106196906426036333558179)
                  ·
                    refine ⟨45159295359639054500337269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30106196906426036333558179 45159295359639054500337269)
                    ·
                      refine ⟨4233683939966161359406619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45159295359639054500337269 4233683939966161359406619)
                      ·
                        rfl

theorem cell23_8245070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_8245070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245070 prefixEnd_8245070 := by exact prefixLift 8245070
  have htrace : WordTrace (prefixWord ++ tailWord_8245070) baseStart_8245070 baseEnd_8245070 := by
    simpa [prefixWord, tailWord_8245070, baseEnd_8245070] using wordTrace_append hprefix tailTrace_8245070
  have hstable : (prefixWord ++ tailWord_8245070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245070).length < 2 ^ (prefixWord ++ tailWord_8245070).sum := by decide
  have hdescent : baseEnd_8245070 < baseStart_8245070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245118 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_8245118 : Nat := 118140960795 + 8245118 * 2 ^ 59
def prefixEnd_8245118 : Nat := 4983230072969 + 3 ^ 40 * 8245118 * 2
def baseEnd_8245118 : Nat := 4233708587037577171606399

theorem tailTrace_8245118 : CollatzResearch.WordTrace tailWord_8245118 prefixEnd_8245118 4233708587037577171606399 := by
  unfold tailWord_8245118
  simp only [CollatzResearch.WordTrace]
  refine ⟨37590519867919139361330001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200482772628902076593760005 37590519867919139361330001)
  ·
    refine ⟨28192889900939354520997501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37590519867919139361330001 28192889900939354520997501)
    ·
      refine ⟨10572333712852257945374063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28192889900939354520997501 10572333712852257945374063)
      ·
        refine ⟨15858500569278386918061095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10572333712852257945374063 15858500569278386918061095)
        ·
          refine ⟨23787750853917580377091643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15858500569278386918061095 23787750853917580377091643)
          ·
            refine ⟨35681626280876370565637465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23787750853917580377091643 35681626280876370565637465)
            ·
              refine ⟨26761219710657277924228099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35681626280876370565637465 26761219710657277924228099)
              ·
                refine ⟨40141829565985916886342149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26761219710657277924228099 40141829565985916886342149)
                ·
                  refine ⟨7526593043622359416189153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40141829565985916886342149 7526593043622359416189153)
                  ·
                    refine ⟨5644944782716769562141865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7526593043622359416189153 5644944782716769562141865)
                    ·
                      refine ⟨4233708587037577171606399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5644944782716769562141865 4233708587037577171606399)
                      ·
                        rfl

theorem cell23_8245118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_8245118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245118 prefixEnd_8245118 := by exact prefixLift 8245118
  have htrace : WordTrace (prefixWord ++ tailWord_8245118) baseStart_8245118 baseEnd_8245118 := by
    simpa [prefixWord, tailWord_8245118, baseEnd_8245118] using wordTrace_append hprefix tailTrace_8245118
  have hstable : (prefixWord ++ tailWord_8245118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245118).length < 2 ^ (prefixWord ++ tailWord_8245118).sum := by decide
  have hdescent : baseEnd_8245118 < baseStart_8245118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245224 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_8245224 : Nat := 118140960795 + 8245224 * 2 ^ 59
def prefixEnd_8245224 : Nat := 4983230072969 + 3 ^ 40 * 8245224 * 2
def baseEnd_8245224 : Nat := 4233763015986953756880911

theorem tailTrace_8245224 : CollatzResearch.WordTrace tailWord_8245224 prefixEnd_8245224 4233763015986953756880911 := by
  unfold tailWord_8245224
  simp only [CollatzResearch.WordTrace]
  refine ⟨150364012540484547496999363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200485350053979396662665817 150364012540484547496999363)
  ·
    refine ⟨225546018810726821245499045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150364012540484547496999363 225546018810726821245499045)
    ·
      refine ⟨42289878527011278983531071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225546018810726821245499045 42289878527011278983531071)
      ·
        refine ⟨63434817790516918475296607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42289878527011278983531071 63434817790516918475296607)
        ·
          refine ⟨95152226685775377712944911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63434817790516918475296607 95152226685775377712944911)
          ·
            refine ⟨142728340028663066569417367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95152226685775377712944911 142728340028663066569417367)
            ·
              refine ⟨214092510042994599854126051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142728340028663066569417367 214092510042994599854126051)
              ·
                refine ⟨321138765064491899781189077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214092510042994599854126051 321138765064491899781189077)
                ·
                  refine ⟨7526689806199028901121619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 321138765064491899781189077 7526689806199028901121619)
                  ·
                    refine ⟨11290034709298543351682429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7526689806199028901121619 11290034709298543351682429)
                    ·
                      refine ⟨4233763015986953756880911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11290034709298543351682429 4233763015986953756880911)
                      ·
                        rfl

theorem cell23_8245224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_8245224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245224 prefixEnd_8245224 := by exact prefixLift 8245224
  have htrace : WordTrace (prefixWord ++ tailWord_8245224) baseStart_8245224 baseEnd_8245224 := by
    simpa [prefixWord, tailWord_8245224, baseEnd_8245224] using wordTrace_append hprefix tailTrace_8245224
  have hstable : (prefixWord ++ tailWord_8245224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245224).length < 2 ^ (prefixWord ++ tailWord_8245224).sum := by decide
  have hdescent : baseEnd_8245224 < baseStart_8245224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245241 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 3]
def baseStart_8245241 : Nat := 118140960795 + 8245241 * 2 ^ 59
def prefixEnd_8245241 : Nat := 4983230072969 + 3 ^ 40 * 8245241 * 2
def baseEnd_8245241 : Nat := 4233771745158080190368333

theorem tailTrace_8245241 : CollatzResearch.WordTrace tailWord_8245241 prefixEnd_8245241 4233771745158080190368333 := by
  unfold tailWord_8245241
  simp only [CollatzResearch.WordTrace]
  refine ⟨300728645121907506897367577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200485763414605004598245051 300728645121907506897367577)
  ·
    refine ⟨225546483841430630173025683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300728645121907506897367577 225546483841430630173025683)
    ·
      refine ⟨338319725762145945259538525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225546483841430630173025683 338319725762145945259538525)
      ·
        refine ⟨126869897160804729472326947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338319725762145945259538525 126869897160804729472326947)
        ·
          refine ⟨190304845741207094208490421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126869897160804729472326947 190304845741207094208490421)
          ·
            refine ⟨17841079288238165082045977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190304845741207094208490421 17841079288238165082045977)
            ·
              refine ⟨13380809466178623811534483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17841079288238165082045977 13380809466178623811534483)
              ·
                refine ⟨20071214199267935717301725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13380809466178623811534483 20071214199267935717301725)
                ·
                  refine ⟨7526705324725475893988147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20071214199267935717301725 7526705324725475893988147)
                  ·
                    refine ⟨11290057987088213840982221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7526705324725475893988147 11290057987088213840982221)
                    ·
                      refine ⟨4233771745158080190368333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11290057987088213840982221 4233771745158080190368333)
                      ·
                        rfl

theorem cell23_8245241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_8245241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245241 prefixEnd_8245241 := by exact prefixLift 8245241
  have htrace : WordTrace (prefixWord ++ tailWord_8245241) baseStart_8245241 baseEnd_8245241 := by
    simpa [prefixWord, tailWord_8245241, baseEnd_8245241] using wordTrace_append hprefix tailTrace_8245241
  have hstable : (prefixWord ++ tailWord_8245241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245241).length < 2 ^ (prefixWord ++ tailWord_8245241).sum := by decide
  have hdescent : baseEnd_8245241 < baseStart_8245241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245247 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_8245247 : Nat := 118140960795 + 8245247 * 2 ^ 59
def prefixEnd_8245247 : Nat := 4983230072969 + 3 ^ 40 * 8245247 * 2
def baseEnd_8245247 : Nat := 4233774826042007166893305

theorem tailTrace_8245247 : CollatzResearch.WordTrace tailWord_8245247 prefixEnd_8245247 4233774826042007166893305 := by
  unfold tailWord_8245247
  simp only [CollatzResearch.WordTrace]
  refine ⟨300728863959885769922085995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200485909306590513281390663 300728863959885769922085995)
  ·
    refine ⟨451093295939828654883128993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300728863959885769922085995 451093295939828654883128993)
    ·
      refine ⟨338319971954871491162346745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451093295939828654883128993 338319971954871491162346745)
      ·
        refine ⟨253739978966153618371760059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338319971954871491162346745 253739978966153618371760059)
        ·
          refine ⟨380609968449230427557640089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253739978966153618371760059 380609968449230427557640089)
          ·
            refine ⟨285457476336922820668230067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380609968449230427557640089 285457476336922820668230067)
            ·
              refine ⟨428186214505384231002345101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285457476336922820668230067 428186214505384231002345101)
              ·
                refine ⟨160569830439519086625879413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428186214505384231002345101 160569830439519086625879413)
                ·
                  refine ⟨15053421603704914371176195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160569830439519086625879413 15053421603704914371176195)
                  ·
                    refine ⟨22580132405557371556764293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15053421603704914371176195 22580132405557371556764293)
                    ·
                      refine ⟨4233774826042007166893305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22580132405557371556764293 4233774826042007166893305)
                      ·
                        rfl

theorem cell23_8245247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_8245247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245247 prefixEnd_8245247 := by exact prefixLift 8245247
  have htrace : WordTrace (prefixWord ++ tailWord_8245247) baseStart_8245247 baseEnd_8245247 := by
    simpa [prefixWord, tailWord_8245247, baseEnd_8245247] using wordTrace_append hprefix tailTrace_8245247
  have hstable : (prefixWord ++ tailWord_8245247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245247).length < 2 ^ (prefixWord ++ tailWord_8245247).sum := by decide
  have hdescent : baseEnd_8245247 < baseStart_8245247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245274 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_8245274 : Nat := 118140960795 + 8245274 * 2 ^ 59
def prefixEnd_8245274 : Nat := 4983230072969 + 3 ^ 40 * 8245274 * 2
def baseEnd_8245274 : Nat := 1411262896673226187085227

theorem tailTrace_8245274 : CollatzResearch.WordTrace tailWord_8245274 prefixEnd_8245274 1411262896673226187085227 := by
  unfold tailWord_8245274
  simp only [CollatzResearch.WordTrace]
  refine ⟨75182462182696988383329719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200486565820525302355545917 75182462182696988383329719)
  ·
    refine ⟨112773693274045482574994579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75182462182696988383329719 112773693274045482574994579)
    ·
      refine ⟨169160539911068223862491869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112773693274045482574994579 169160539911068223862491869)
      ·
        refine ⟨63435202466650583948434451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169160539911068223862491869 63435202466650583948434451)
        ·
          refine ⟨95152803699975875922651677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63435202466650583948434451 95152803699975875922651677)
          ·
            refine ⟨35682301387490953470994379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95152803699975875922651677 35682301387490953470994379)
            ·
              refine ⟨53523452081236430206491569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35682301387490953470994379 53523452081236430206491569)
              ·
                refine ⟨40142589060927322654868677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53523452081236430206491569 40142589060927322654868677)
                ·
                  refine ⟨7526735448923872997787877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40142589060927322654868677 7526735448923872997787877)
                  ·
                    refine ⟨1411262896673226187085227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7526735448923872997787877 1411262896673226187085227)
                    ·
                      rfl

theorem cell23_8245274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_8245274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245274 prefixEnd_8245274 := by exact prefixLift 8245274
  have htrace : WordTrace (prefixWord ++ tailWord_8245274) baseStart_8245274 baseEnd_8245274 := by
    simpa [prefixWord, tailWord_8245274, baseEnd_8245274] using wordTrace_append hprefix tailTrace_8245274
  have hstable : (prefixWord ++ tailWord_8245274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245274).length < 2 ^ (prefixWord ++ tailWord_8245274).sum := by decide
  have hdescent : baseEnd_8245274 < baseStart_8245274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245294 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_8245294 : Nat := 118140960795 + 8245294 * 2 ^ 59
def prefixEnd_8245294 : Nat := 4983230072969 + 3 ^ 40 * 8245294 * 2
def baseEnd_8245294 : Nat := 4233798959632768483005589

theorem tailTrace_8245294 : CollatzResearch.WordTrace tailWord_8245294 prefixEnd_8245294 4233798959632768483005589 := by
  unfold tailWord_8245294
  simp only [CollatzResearch.WordTrace]
  refine ⟨37591322273839437118630867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200487052127143664632697957 37591322273839437118630867)
  ·
    refine ⟨56386983410759155677946301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37591322273839437118630867 56386983410759155677946301)
    ·
      refine ⟨21145118779034683379229863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56386983410759155677946301 21145118779034683379229863)
      ·
        refine ⟨31717678168552025068844795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21145118779034683379229863 31717678168552025068844795)
        ·
          refine ⟨47576517252828037603267193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31717678168552025068844795 47576517252828037603267193)
          ·
            refine ⟨35682387939621028202450395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47576517252828037603267193 35682387939621028202450395)
            ·
              refine ⟨53523581909431542303675593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35682387939621028202450395 53523581909431542303675593)
              ·
                refine ⟨40142686432073656727756695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53523581909431542303675593 40142686432073656727756695)
                ·
                  refine ⟨60214029648110485091635043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40142686432073656727756695 60214029648110485091635043)
                  ·
                    refine ⟨90321044472165727637452565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60214029648110485091635043 90321044472165727637452565)
                    ·
                      refine ⟨4233798959632768483005589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90321044472165727637452565 4233798959632768483005589)
                      ·
                        rfl

theorem cell23_8245294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_8245294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245294 prefixEnd_8245294 := by exact prefixLift 8245294
  have htrace : WordTrace (prefixWord ++ tailWord_8245294) baseStart_8245294 baseEnd_8245294 := by
    simpa [prefixWord, tailWord_8245294, baseEnd_8245294] using wordTrace_append hprefix tailTrace_8245294
  have hstable : (prefixWord ++ tailWord_8245294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245294).length < 2 ^ (prefixWord ++ tailWord_8245294).sum := by decide
  have hdescent : baseEnd_8245294 < baseStart_8245294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245298 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_8245298 : Nat := 118140960795 + 8245298 * 2 ^ 59
def prefixEnd_8245298 : Nat := 4983230072969 + 3 ^ 40 * 8245298 * 2
def baseEnd_8245298 : Nat := 4233801013555386467355571

theorem tailTrace_8245298 : CollatzResearch.WordTrace tailWord_8245298 prefixEnd_8245298 4233801013555386467355571 := by
  unfold tailWord_8245298
  simp only [CollatzResearch.WordTrace]
  refine ⟨75182681020675251408048137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200487149388467337088128365 75182681020675251408048137)
  ·
    refine ⟨56387010765506438556036103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75182681020675251408048137 56387010765506438556036103)
    ·
      refine ⟨84580516148259657834054155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56387010765506438556036103 84580516148259657834054155)
      ·
        refine ⟨126870774222389486751081233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84580516148259657834054155 126870774222389486751081233)
        ·
          refine ⟨95153080666792115063310925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126870774222389486751081233 95153080666792115063310925)
          ·
            refine ⟨35682405250047043148741597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95153080666792115063310925 35682405250047043148741597)
            ·
              refine ⟨13380901968767641180778099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35682405250047043148741597 13380901968767641180778099)
              ·
                refine ⟨20071352953151461771167149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13380901968767641180778099 20071352953151461771167149)
                ·
                  refine ⟨7526757357431798164187681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20071352953151461771167149 7526757357431798164187681)
                  ·
                    refine ⟨5645068018073848623140761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7526757357431798164187681 5645068018073848623140761)
                    ·
                      refine ⟨4233801013555386467355571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645068018073848623140761 4233801013555386467355571)
                      ·
                        rfl

theorem cell23_8245298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_8245298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245298 prefixEnd_8245298 := by exact prefixLift 8245298
  have htrace : WordTrace (prefixWord ++ tailWord_8245298) baseStart_8245298 baseEnd_8245298 := by
    simpa [prefixWord, tailWord_8245298, baseEnd_8245298] using wordTrace_append hprefix tailTrace_8245298
  have hstable : (prefixWord ++ tailWord_8245298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245298).length < 2 ^ (prefixWord ++ tailWord_8245298).sum := by decide
  have hdescent : baseEnd_8245298 < baseStart_8245298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245304 : List Nat := [2, 1, 2, 1, 6, 1, 2, 8]
def baseStart_8245304 : Nat := 118140960795 + 8245304 * 2 ^ 59
def prefixEnd_8245304 : Nat := 4983230072969 + 3 ^ 40 * 8245304 * 2
def baseEnd_8245304 : Nat := 156807559053307905328909

theorem tailTrace_8245304 : CollatzResearch.WordTrace tailWord_8245304 prefixEnd_8245304 156807559053307905328909 := by
  unfold tailWord_8245304
  simp only [CollatzResearch.WordTrace]
  refine ⟨150365471460339634328455483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200487295280452845771273977 150365471460339634328455483)
  ·
    refine ⟨225548207190509451492683225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150365471460339634328455483 225548207190509451492683225)
    ·
      refine ⟨169161155392882088619512419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225548207190509451492683225 169161155392882088619512419)
      ·
        refine ⟨253741733089323132929268629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169161155392882088619512419 253741733089323132929268629)
        ·
          refine ⟨11894143738562021856059467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253741733089323132929268629 11894143738562021856059467)
          ·
            refine ⟨17841215607843032784089201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11894143738562021856059467 17841215607843032784089201)
            ·
              refine ⟨13380911705882274588066901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17841215607843032784089201 13380911705882274588066901)
              ·
                refine ⟨156807559053307905328909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13380911705882274588066901 156807559053307905328909)
                ·
                  rfl

theorem cell23_8245304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 8].length) (baseStart_8245304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245304 prefixEnd_8245304 := by exact prefixLift 8245304
  have htrace : WordTrace (prefixWord ++ tailWord_8245304) baseStart_8245304 baseEnd_8245304 := by
    simpa [prefixWord, tailWord_8245304, baseEnd_8245304] using wordTrace_append hprefix tailTrace_8245304
  have hstable : (prefixWord ++ tailWord_8245304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245304).length < 2 ^ (prefixWord ++ tailWord_8245304).sum := by decide
  have hdescent : baseEnd_8245304 < baseStart_8245304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245318 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_8245318 : Nat := 118140960795 + 8245318 * 2 ^ 59
def prefixEnd_8245318 : Nat := 4983230072969 + 3 ^ 40 * 8245318 * 2
def baseEnd_8245318 : Nat := 4233811283168476389105479

theorem tailTrace_8245318 : CollatzResearch.WordTrace tailWord_8245318 prefixEnd_8245318 4233811283168476389105479 := by
  unfold tailWord_8245318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9397857923207142157747519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200487635695085699365280405 9397857923207142157747519)
  ·
    refine ⟨14096786884810713236621279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9397857923207142157747519 14096786884810713236621279)
    ·
      refine ⟨21145180327216069854931919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14096786884810713236621279 21145180327216069854931919)
      ·
        refine ⟨31717770490824104782397879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21145180327216069854931919 31717770490824104782397879)
        ·
          refine ⟨47576655736236157173596819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31717770490824104782397879 47576655736236157173596819)
          ·
            refine ⟨71364983604354235760395229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47576655736236157173596819 71364983604354235760395229)
            ·
              refine ⟨26761868851632838410148211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71364983604354235760395229 26761868851632838410148211)
              ·
                refine ⟨40142803277449257615222317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26761868851632838410148211 40142803277449257615222317)
                ·
                  refine ⟨15053551229043471605708369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40142803277449257615222317 15053551229043471605708369)
                  ·
                    refine ⟨11290163421782603704281277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15053551229043471605708369 11290163421782603704281277)
                    ·
                      refine ⟨4233811283168476389105479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11290163421782603704281277 4233811283168476389105479)
                      ·
                        rfl

theorem cell23_8245318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_8245318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245318 prefixEnd_8245318 := by exact prefixLift 8245318
  have htrace : WordTrace (prefixWord ++ tailWord_8245318) baseStart_8245318 baseEnd_8245318 := by
    simpa [prefixWord, tailWord_8245318, baseEnd_8245318] using wordTrace_append hprefix tailTrace_8245318
  have hstable : (prefixWord ++ tailWord_8245318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245318).length < 2 ^ (prefixWord ++ tailWord_8245318).sum := by decide
  have hdescent : baseEnd_8245318 < baseStart_8245318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245342 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_8245342 : Nat := 118140960795 + 8245342 * 2 ^ 59
def prefixEnd_8245342 : Nat := 4983230072969 + 3 ^ 40 * 8245342 * 2
def baseEnd_8245342 : Nat := 1411274535568061431735123

theorem tailTrace_8245342 : CollatzResearch.WordTrace tailWord_8245342 prefixEnd_8245342 1411274535568061431735123 := by
  unfold tailWord_8245342
  simp only [CollatzResearch.WordTrace]
  refine ⟨37591541111817700143349285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200488219263027734097862853 37591541111817700143349285)
  ·
    refine ⟨7048413958465818776877991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37591541111817700143349285 7048413958465818776877991)
    ·
      refine ⟨10572620937698728165316987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7048413958465818776877991 10572620937698728165316987)
      ·
        refine ⟨15858931406548092247975481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10572620937698728165316987 15858931406548092247975481)
        ·
          refine ⟨11894198554911069185981611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15858931406548092247975481 11894198554911069185981611)
          ·
            refine ⟨17841297832366603778972417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11894198554911069185981611 17841297832366603778972417)
            ·
              refine ⟨13380973374274952834229313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17841297832366603778972417 13380973374274952834229313)
              ·
                refine ⟨10035730030706214625671985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13380973374274952834229313 10035730030706214625671985)
                ·
                  refine ⟨7526797523029660969253989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10035730030706214625671985 7526797523029660969253989)
                  ·
                    refine ⟨1411274535568061431735123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7526797523029660969253989 1411274535568061431735123)
                    ·
                      rfl

theorem cell23_8245342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_8245342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245342 prefixEnd_8245342 := by exact prefixLift 8245342
  have htrace : WordTrace (prefixWord ++ tailWord_8245342) baseStart_8245342 baseEnd_8245342 := by
    simpa [prefixWord, tailWord_8245342, baseEnd_8245342] using wordTrace_append hprefix tailTrace_8245342
  have hstable : (prefixWord ++ tailWord_8245342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245342).length < 2 ^ (prefixWord ++ tailWord_8245342).sum := by decide
  have hdescent : baseEnd_8245342 < baseStart_8245342 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245371 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 8, 2, 2]
def baseStart_8245371 : Nat := 118140960795 + 8245371 * 2 ^ 59
def prefixEnd_8245371 : Nat := 4983230072969 + 3 ^ 40 * 8245371 * 2
def baseEnd_8245371 : Nat := 4233838497643164681742735

theorem tailTrace_8245371 : CollatzResearch.WordTrace tailWord_8245371 prefixEnd_8245371 4233838497643164681742735 := by
  unfold tailWord_8245371
  simp only [CollatzResearch.WordTrace]
  refine ⟨300733386611436539099599967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200488924407624359399733311 300733386611436539099599967)
  ·
    refine ⟨451100079917154808649399951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300733386611436539099599967 451100079917154808649399951)
    ·
      refine ⟨676650119875732212974099927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451100079917154808649399951 676650119875732212974099927)
      ·
        refine ⟨1014975179813598319461149891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676650119875732212974099927 1014975179813598319461149891)
        ·
          refine ⟨1522462769720397479191724837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014975179813598319461149891 1522462769720397479191724837)
          ·
            refine ⟨285461769322574527348448407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1522462769720397479191724837 285461769322574527348448407)
            ·
              refine ⟨428192653983861791022672611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285461769322574527348448407 428192653983861791022672611)
              ·
                refine ⟨642288980975792686534008917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428192653983861791022672611 642288980975792686534008917)
                ·
                  refine ⟨7526823995810070545320417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 642288980975792686534008917 7526823995810070545320417)
                  ·
                    refine ⟨5645117996857552908990313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7526823995810070545320417 5645117996857552908990313)
                    ·
                      refine ⟨4233838497643164681742735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645117996857552908990313 4233838497643164681742735)
                      ·
                        rfl

theorem cell23_8245371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 2, 2].length) (baseStart_8245371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245371 prefixEnd_8245371 := by exact prefixLift 8245371
  have htrace : WordTrace (prefixWord ++ tailWord_8245371) baseStart_8245371 baseEnd_8245371 := by
    simpa [prefixWord, tailWord_8245371, baseEnd_8245371] using wordTrace_append hprefix tailTrace_8245371
  have hstable : (prefixWord ++ tailWord_8245371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245371).length < 2 ^ (prefixWord ++ tailWord_8245371).sum := by decide
  have hdescent : baseEnd_8245371 < baseStart_8245371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245387 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 7]
def baseStart_8245387 : Nat := 118140960795 + 8245387 * 2 ^ 59
def prefixEnd_8245387 : Nat := 4983230072969 + 3 ^ 40 * 8245387 * 2
def baseEnd_8245387 : Nat := 4233846713333636619142661

theorem tailTrace_8245387 : CollatzResearch.WordTrace tailWord_8245387 prefixEnd_8245387 4233846713333636619142661 := by
  unfold tailWord_8245387
  simp only [CollatzResearch.WordTrace]
  refine ⟨300733970179378573832182415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200489313452919049221454943 300733970179378573832182415)
  ·
    refine ⟨451100955269067860748273623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300733970179378573832182415 451100955269067860748273623)
    ·
      refine ⟨676651432903601791122410435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451100955269067860748273623 676651432903601791122410435)
      ·
        refine ⟨1014977149355402686683615653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676651432903601791122410435 1014977149355402686683615653)
        ·
          refine ⟨190308215504138003753177935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1014977149355402686683615653 190308215504138003753177935)
          ·
            refine ⟨285462323256207005629766903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190308215504138003753177935 285462323256207005629766903)
            ·
              refine ⟨428193484884310508444650355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285462323256207005629766903 428193484884310508444650355)
              ·
                refine ⟨642290227326465762666975533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428193484884310508444650355 642290227326465762666975533)
                ·
                  refine ⟨240858835247424661000115825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642290227326465762666975533 240858835247424661000115825)
                  ·
                    refine ⟨180644126435568495750086869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240858835247424661000115825 180644126435568495750086869)
                    ·
                      refine ⟨4233846713333636619142661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180644126435568495750086869 4233846713333636619142661)
                      ·
                        rfl

theorem cell23_8245387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_8245387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245387 prefixEnd_8245387 := by exact prefixLift 8245387
  have htrace : WordTrace (prefixWord ++ tailWord_8245387) baseStart_8245387 baseEnd_8245387 := by
    simpa [prefixWord, tailWord_8245387, baseEnd_8245387] using wordTrace_append hprefix tailTrace_8245387
  have hstable : (prefixWord ++ tailWord_8245387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245387).length < 2 ^ (prefixWord ++ tailWord_8245387).sum := by decide
  have hdescent : baseEnd_8245387 < baseStart_8245387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245394 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 9]
def baseStart_8245394 : Nat := 118140960795 + 8245394 * 2 ^ 59
def prefixEnd_8245394 : Nat := 4983230072969 + 3 ^ 40 * 8245394 * 2
def baseEnd_8245394 : Nat := 470427811966468676861681

theorem tailTrace_8245394 : CollatzResearch.WordTrace tailWord_8245394 prefixEnd_8245394 470427811966468676861681 := by
  unfold tailWord_8245394
  simp only [CollatzResearch.WordTrace]
  refine ⟨75183556372588303506921809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200489483660235476018458157 75183556372588303506921809)
  ·
    refine ⟨56387667279441227630191357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75183556372588303506921809 56387667279441227630191357)
    ·
      refine ⟨21145375229790460361321759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56387667279441227630191357 21145375229790460361321759)
      ·
        refine ⟨31718062844685690541982639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21145375229790460361321759 31718062844685690541982639)
        ·
          refine ⟨47577094267028535812973959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31718062844685690541982639 47577094267028535812973959)
          ·
            refine ⟨71365641400542803719460939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47577094267028535812973959 71365641400542803719460939)
            ·
              refine ⟨107048462100814205579191409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71365641400542803719460939 107048462100814205579191409)
              ·
                refine ⟨80286346575610654184393557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107048462100814205579191409 80286346575610654184393557)
                ·
                  refine ⟨470427811966468676861681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80286346575610654184393557 470427811966468676861681)
                  ·
                    rfl

theorem cell23_8245394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_8245394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245394 prefixEnd_8245394 := by exact prefixLift 8245394
  have htrace : WordTrace (prefixWord ++ tailWord_8245394) baseStart_8245394 baseEnd_8245394 := by
    simpa [prefixWord, tailWord_8245394, baseEnd_8245394] using wordTrace_append hprefix tailTrace_8245394
  have hstable : (prefixWord ++ tailWord_8245394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245394).length < 2 ^ (prefixWord ++ tailWord_8245394).sum := by decide
  have hdescent : baseEnd_8245394 < baseStart_8245394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245405 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_8245405 : Nat := 118140960795 + 8245405 * 2 ^ 59
def prefixEnd_8245405 : Nat := 4983230072969 + 3 ^ 40 * 8245405 * 2
def baseEnd_8245405 : Nat := 4233855955985417548717579

theorem tailTrace_8245405 : CollatzResearch.WordTrace tailWord_8245405 prefixEnd_8245405 4233855955985417548717579 := by
  unfold tailWord_8245405
  simp only [CollatzResearch.WordTrace]
  refine ⟨300734626693313362906337669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200489751128875575270891779 300734626693313362906337669)
  ·
    refine ⟨56387742504996255544938313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300734626693313362906337669 56387742504996255544938313)
    ·
      refine ⟨42290806878747191658703735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56387742504996255544938313 42290806878747191658703735)
      ·
        refine ⟨63436210318120787488055603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42290806878747191658703735 63436210318120787488055603)
        ·
          refine ⟨95154315477181181232083405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63436210318120787488055603 95154315477181181232083405)
          ·
            refine ⟨35682868303942942962031277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95154315477181181232083405 35682868303942942962031277)
            ·
              refine ⟨13381075613978603610761729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35682868303942942962031277 13381075613978603610761729)
              ·
                refine ⟨10035806710483952708071297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13381075613978603610761729 10035806710483952708071297)
                ·
                  refine ⟨7526855032862964531053473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10035806710483952708071297 7526855032862964531053473)
                  ·
                    refine ⟨5645141274647223398290105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7526855032862964531053473 5645141274647223398290105)
                    ·
                      refine ⟨4233855955985417548717579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645141274647223398290105 4233855955985417548717579)
                      ·
                        rfl

theorem cell23_8245405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_8245405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245405 prefixEnd_8245405 := by exact prefixLift 8245405
  have htrace : WordTrace (prefixWord ++ tailWord_8245405) baseStart_8245405 baseEnd_8245405 := by
    simpa [prefixWord, tailWord_8245405, baseEnd_8245405] using wordTrace_append hprefix tailTrace_8245405
  have hstable : (prefixWord ++ tailWord_8245405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245405).length < 2 ^ (prefixWord ++ tailWord_8245405).sum := by decide
  have hdescent : baseEnd_8245405 < baseStart_8245405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245462 : List Nat := [5, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_8245462 : Nat := 118140960795 + 8245462 * 2 ^ 59
def prefixEnd_8245462 : Nat := 4983230072969 + 3 ^ 40 * 8245462 * 2
def baseEnd_8245462 : Nat := 470431691598080425078313

theorem tailTrace_8245462 : CollatzResearch.WordTrace tailWord_8245462 prefixEnd_8245462 470431691598080425078313 := by
  unfold tailWord_8245462
  simp only [CollatzResearch.WordTrace]
  refine ⟨18796044103381678852572665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200491137102737907760775093 18796044103381678852572665)
  ·
    refine ⟨14097033077536259139429499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18796044103381678852572665 14097033077536259139429499)
    ·
      refine ⟨21145549616304388709144249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14097033077536259139429499 21145549616304388709144249)
      ·
        refine ⟨15859162212228291531858187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21145549616304388709144249 15859162212228291531858187)
        ·
          refine ⟨23788743318342437297787281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15859162212228291531858187 23788743318342437297787281)
          ·
            refine ⟨17841557488756827973340461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23788743318342437297787281 17841557488756827973340461)
            ·
              refine ⟨6690584058283810490002673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17841557488756827973340461 6690584058283810490002673)
              ·
                refine ⟨5017938043712857867502005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6690584058283810490002673 5017938043712857867502005)
                ·
                  refine ⟨470431691598080425078313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5017938043712857867502005 470431691598080425078313)
                  ·
                    rfl

theorem cell23_8245462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_8245462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245462 prefixEnd_8245462 := by exact prefixLift 8245462
  have htrace : WordTrace (prefixWord ++ tailWord_8245462) baseStart_8245462 baseEnd_8245462 := by
    simpa [prefixWord, tailWord_8245462, baseEnd_8245462] using wordTrace_append hprefix tailTrace_8245462
  have hstable : (prefixWord ++ tailWord_8245462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245462).length < 2 ^ (prefixWord ++ tailWord_8245462).sum := by decide
  have hdescent : baseEnd_8245462 < baseStart_8245462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245498 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_8245498 : Nat := 118140960795 + 8245498 * 2 ^ 59
def prefixEnd_8245498 : Nat := 4983230072969 + 3 ^ 40 * 8245498 * 2
def baseEnd_8245498 : Nat := 4233903709686285684854651

theorem tailTrace_8245498 : CollatzResearch.WordTrace tailWord_8245498 prefixEnd_8245498 4233903709686285684854651 := by
  unfold tailWord_8245498
  simp only [CollatzResearch.WordTrace]
  refine ⟨75184504670494109947368287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200492012454650959859648765 75184504670494109947368287)
  ·
    refine ⟨112776757005741164921052431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75184504670494109947368287 112776757005741164921052431)
    ·
      refine ⟨169165135508611747381578647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112776757005741164921052431 169165135508611747381578647)
      ·
        refine ⟨253747703262917621072367971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169165135508611747381578647 253747703262917621072367971)
        ·
          refine ⟨380621554894376431608551957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253747703262917621072367971 380621554894376431608551957)
          ·
            refine ⟨17841635385673895231650873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 380621554894376431608551957 17841635385673895231650873)
            ·
              refine ⟨13381226539255421423738155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17841635385673895231650873 13381226539255421423738155)
              ·
                refine ⟨20071839808883132135607233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13381226539255421423738155 20071839808883132135607233)
                ·
                  refine ⟨15053879856662349101705425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20071839808883132135607233 15053879856662349101705425)
                  ·
                    refine ⟨11290409892496761826279069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15053879856662349101705425 11290409892496761826279069)
                    ·
                      refine ⟨4233903709686285684854651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11290409892496761826279069 4233903709686285684854651)
                      ·
                        rfl

theorem cell23_8245498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_8245498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245498 prefixEnd_8245498 := by exact prefixLift 8245498
  have htrace : WordTrace (prefixWord ++ tailWord_8245498) baseStart_8245498 baseEnd_8245498 := by
    simpa [prefixWord, tailWord_8245498, baseEnd_8245498] using wordTrace_append hprefix tailTrace_8245498
  have hstable : (prefixWord ++ tailWord_8245498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245498).length < 2 ^ (prefixWord ++ tailWord_8245498).sum := by decide
  have hdescent : baseEnd_8245498 < baseStart_8245498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245528 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 3, 1, 3]
def baseStart_8245528 : Nat := 118140960795 + 8245528 * 2 ^ 59
def prefixEnd_8245528 : Nat := 4983230072969 + 3 ^ 40 * 8245528 * 2
def baseEnd_8245528 : Nat := 4233919114105920567479513

theorem tailTrace_8245528 : CollatzResearch.WordTrace tailWord_8245528 prefixEnd_8245528 4233919114105920567479513 := by
  unfold tailWord_8245528
  simp only [CollatzResearch.WordTrace]
  refine ⟨150369556435933877456532619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200492741914578503275376825 150369556435933877456532619)
  ·
    refine ⟨225554334653900816184798929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150369556435933877456532619 225554334653900816184798929)
    ·
      refine ⟨169165750990425612138599197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225554334653900816184798929 169165750990425612138599197)
      ·
        refine ⟨63437156621409604551974699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169165750990425612138599197 63437156621409604551974699)
        ·
          refine ⟨95155734932114406827962049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63437156621409604551974699 95155734932114406827962049)
          ·
            refine ⟨71366801199085805120971537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95155734932114406827962049 71366801199085805120971537)
            ·
              refine ⟨53525100899314353840728653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71366801199085805120971537 53525100899314353840728653)
              ·
                refine ⟨20071912837242882690273245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53525100899314353840728653 20071912837242882690273245)
                ·
                  refine ⟨7526967313966081008852467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20071912837242882690273245 7526967313966081008852467)
                  ·
                    refine ⟨11290450970949121513278701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7526967313966081008852467 11290450970949121513278701)
                    ·
                      refine ⟨4233919114105920567479513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11290450970949121513278701 4233919114105920567479513)
                      ·
                        rfl

theorem cell23_8245528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_8245528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245528 prefixEnd_8245528 := by exact prefixLift 8245528
  have htrace : WordTrace (prefixWord ++ tailWord_8245528) baseStart_8245528 baseEnd_8245528 := by
    simpa [prefixWord, tailWord_8245528, baseEnd_8245528] using wordTrace_append hprefix tailTrace_8245528
  have hstable : (prefixWord ++ tailWord_8245528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245528).length < 2 ^ (prefixWord ++ tailWord_8245528).sum := by decide
  have hdescent : baseEnd_8245528 < baseStart_8245528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245549 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_8245549 : Nat := 118140960795 + 8245549 * 2 ^ 59
def prefixEnd_8245549 : Nat := 4983230072969 + 3 ^ 40 * 8245549 * 2
def baseEnd_8245549 : Nat := 4233929897199664985316917

theorem tailTrace_8245549 : CollatzResearch.WordTrace tailWord_8245549 prefixEnd_8245549 4233929897199664985316917 := by
  unfold tailWord_8245549
  simp only [CollatzResearch.WordTrace]
  refine ⟨300739878804791675499579701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200493252536527783666386467 300739878804791675499579701)
  ·
    refine ⟨28194363637949219578085597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300739878804791675499579701 28194363637949219578085597)
    ·
      refine ⟨10572886364230957341782099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28194363637949219578085597 10572886364230957341782099)
      ·
        refine ⟨15859329546346436012673149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10572886364230957341782099 15859329546346436012673149)
        ·
          refine ⟨5947248579879913504752431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15859329546346436012673149 5947248579879913504752431)
          ·
            refine ⟨8920872869819870257128647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947248579879913504752431 8920872869819870257128647)
            ·
              refine ⟨13381309304729805385692971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8920872869819870257128647 13381309304729805385692971)
              ·
                refine ⟨20071963957094708078539457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13381309304729805385692971 20071963957094708078539457)
                ·
                  refine ⟨15053972967821031058904593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20071963957094708078539457 15053972967821031058904593)
                  ·
                    refine ⟨11290479725865773294178445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15053972967821031058904593 11290479725865773294178445)
                    ·
                      refine ⟨4233929897199664985316917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11290479725865773294178445 4233929897199664985316917)
                      ·
                        rfl

theorem cell23_8245549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_8245549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245549 prefixEnd_8245549 := by exact prefixLift 8245549
  have htrace : WordTrace (prefixWord ++ tailWord_8245549) baseStart_8245549 baseEnd_8245549 := by
    simpa [prefixWord, tailWord_8245549, baseEnd_8245549] using wordTrace_append hprefix tailTrace_8245549
  have hstable : (prefixWord ++ tailWord_8245549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245549).length < 2 ^ (prefixWord ++ tailWord_8245549).sum := by decide
  have hdescent : baseEnd_8245549 < baseStart_8245549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245551 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_8245551 : Nat := 118140960795 + 8245551 * 2 ^ 59
def prefixEnd_8245551 : Nat := 4983230072969 + 3 ^ 40 * 8245551 * 2
def baseEnd_8245551 : Nat := 4233930924160973977491907

theorem tailTrace_8245551 : CollatzResearch.WordTrace tailWord_8245551 prefixEnd_8245551 4233930924160973977491907 := by
  unfold tailWord_8245551
  simp only [CollatzResearch.WordTrace]
  refine ⟨300739951750784429841152507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200493301167189619894101671 300739951750784429841152507)
  ·
    refine ⟨451109927626176644761728761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300739951750784429841152507 451109927626176644761728761)
    ·
      refine ⟨338332445719632483571296571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451109927626176644761728761 338332445719632483571296571)
      ·
        refine ⟨507498668579448725356944857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338332445719632483571296571 507498668579448725356944857)
        ·
          refine ⟨380624001434586544017708643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507498668579448725356944857 380624001434586544017708643)
          ·
            refine ⟨570936002151879816026562965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380624001434586544017708643 570936002151879816026562965)
            ·
              refine ⟨26762625100869366376245139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 570936002151879816026562965 26762625100869366376245139)
              ·
                refine ⟨40143937651304049564367709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26762625100869366376245139 40143937651304049564367709)
                ·
                  refine ⟨15053976619239018586637891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40143937651304049564367709 15053976619239018586637891)
                  ·
                    refine ⟨22580964928858527879956837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15053976619239018586637891 22580964928858527879956837)
                    ·
                      refine ⟨4233930924160973977491907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22580964928858527879956837 4233930924160973977491907)
                      ·
                        rfl

theorem cell23_8245551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_8245551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245551 prefixEnd_8245551 := by exact prefixLift 8245551
  have htrace : WordTrace (prefixWord ++ tailWord_8245551) baseStart_8245551 baseEnd_8245551 := by
    simpa [prefixWord, tailWord_8245551, baseEnd_8245551] using wordTrace_append hprefix tailTrace_8245551
  have hstable : (prefixWord ++ tailWord_8245551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245551).length < 2 ^ (prefixWord ++ tailWord_8245551).sum := by decide
  have hdescent : baseEnd_8245551 < baseStart_8245551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245562 : List Nat := [3, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3]
def baseStart_8245562 : Nat := 118140960795 + 8245562 * 2 ^ 59
def prefixEnd_8245562 : Nat := 4983230072969 + 3 ^ 40 * 8245562 * 2
def baseEnd_8245562 : Nat := 4233936572448173434454357

theorem tailTrace_8245562 : CollatzResearch.WordTrace tailWord_8245562 prefixEnd_8245562 4233936572448173434454357 := by
  unfold tailWord_8245562
  simp only [CollatzResearch.WordTrace]
  refine ⟨75185088238436144679950735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200493568635829719146535293 75185088238436144679950735)
  ·
    refine ⟨112777632357654217019926103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75185088238436144679950735 112777632357654217019926103)
    ·
      refine ⟨169166448536481325529889155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112777632357654217019926103 169166448536481325529889155)
      ·
        refine ⟨253749672804721988294833733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169166448536481325529889155 253749672804721988294833733)
        ·
          refine ⟨47578063650885372805281325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253749672804721988294833733 47578063650885372805281325)
          ·
            refine ⟨17841773869082014801980497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47578063650885372805281325 17841773869082014801980497)
            ·
              refine ⟨13381330401811511101485373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17841773869082014801980497 13381330401811511101485373)
              ·
                refine ⟨5017998900679316663057015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13381330401811511101485373 5017998900679316663057015)
                ·
                  refine ⟨7526998351018974994585523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5017998900679316663057015 7526998351018974994585523)
                  ·
                    refine ⟨11290497526528462491878285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7526998351018974994585523 11290497526528462491878285)
                    ·
                      refine ⟨4233936572448173434454357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11290497526528462491878285 4233936572448173434454357)
                      ·
                        rfl

theorem cell23_8245562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3].length) (baseStart_8245562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245562 prefixEnd_8245562 := by exact prefixLift 8245562
  have htrace : WordTrace (prefixWord ++ tailWord_8245562) baseStart_8245562 baseEnd_8245562 := by
    simpa [prefixWord, tailWord_8245562, baseEnd_8245562] using wordTrace_append hprefix tailTrace_8245562
  have hstable : (prefixWord ++ tailWord_8245562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245562).length < 2 ^ (prefixWord ++ tailWord_8245562).sum := by decide
  have hdescent : baseEnd_8245562 < baseStart_8245562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245585 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 3, 2, 2]
def baseStart_8245585 : Nat := 118140960795 + 8245585 * 2 ^ 59
def prefixEnd_8245585 : Nat := 4983230072969 + 3 ^ 40 * 8245585 * 2
def baseEnd_8245585 : Nat := 4233948382503226844466751

theorem tailTrace_8245585 : CollatzResearch.WordTrace tailWord_8245585 prefixEnd_8245585 4233948382503226844466751 := by
  unfold tailWord_8245585
  simp only [CollatzResearch.WordTrace]
  refine ⟨300741191832661253647890209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200494127888440835765260139 300741191832661253647890209)
  ·
    refine ⟨225555893874495940235917657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300741191832661253647890209 225555893874495940235917657)
    ·
      refine ⟨169166920405871955176938243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225555893874495940235917657 169166920405871955176938243)
      ·
        refine ⟨253750380608807932765407365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169166920405871955176938243 253750380608807932765407365)
        ·
          refine ⟨47578196364151487393513881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253750380608807932765407365 47578196364151487393513881)
          ·
            refine ⟨35683647273113615545135411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47578196364151487393513881 35683647273113615545135411)
            ·
              refine ⟨53525470909670423317703117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35683647273113615545135411 53525470909670423317703117)
              ·
                refine ⟨20072051591126408744138669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53525470909670423317703117 20072051591126408744138669)
                ·
                  refine ⟨7527019346672403279052001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20072051591126408744138669 7527019346672403279052001)
                  ·
                    refine ⟨5645264510004302459289001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7527019346672403279052001 5645264510004302459289001)
                    ·
                      refine ⟨4233948382503226844466751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645264510004302459289001 4233948382503226844466751)
                      ·
                        rfl

theorem cell23_8245585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_8245585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245585 prefixEnd_8245585 := by exact prefixLift 8245585
  have htrace : WordTrace (prefixWord ++ tailWord_8245585) baseStart_8245585 baseEnd_8245585 := by
    simpa [prefixWord, tailWord_8245585, baseEnd_8245585] using wordTrace_append hprefix tailTrace_8245585
  have hstable : (prefixWord ++ tailWord_8245585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245585).length < 2 ^ (prefixWord ++ tailWord_8245585).sum := by decide
  have hdescent : baseEnd_8245585 < baseStart_8245585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245588 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_8245588 : Nat := 118140960795 + 8245588 * 2 ^ 59
def prefixEnd_8245588 : Nat := 4983230072969 + 3 ^ 40 * 8245588 * 2
def baseEnd_8245588 : Nat := 4233949922945190332729237

theorem tailTrace_8245588 : CollatzResearch.WordTrace tailWord_8245588 prefixEnd_8245588 4233949922945190332729237 := by
  unfold tailWord_8245588
  simp only [CollatzResearch.WordTrace]
  refine ⟨150370650625825192580124709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200494200834433590106832945 150370650625825192580124709)
  ·
    refine ⟨28194496992342223608773383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150370650625825192580124709 28194496992342223608773383)
    ·
      refine ⟨42291745488513335413160075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28194496992342223608773383 42291745488513335413160075)
      ·
        refine ⟨63437618232770003119740113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42291745488513335413160075 63437618232770003119740113)
        ·
          refine ⟨47578213674577502339805085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63437618232770003119740113 47578213674577502339805085)
          ·
            refine ⟨17841830127966563377426907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47578213674577502339805085 17841830127966563377426907)
            ·
              refine ⟨26762745191949845066140361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17841830127966563377426907 26762745191949845066140361)
              ·
                refine ⟨20072058893962383799605271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26762745191949845066140361 20072058893962383799605271)
                ·
                  refine ⟨30108088340943575699407907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20072058893962383799605271 30108088340943575699407907)
                  ·
                    refine ⟨45162132511415363549111861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30108088340943575699407907 45162132511415363549111861)
                    ·
                      refine ⟨4233949922945190332729237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45162132511415363549111861 4233949922945190332729237)
                      ·
                        rfl

theorem cell23_8245588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_8245588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245588 prefixEnd_8245588 := by exact prefixLift 8245588
  have htrace : WordTrace (prefixWord ++ tailWord_8245588) baseStart_8245588 baseEnd_8245588 := by
    simpa [prefixWord, tailWord_8245588, baseEnd_8245588] using wordTrace_append hprefix tailTrace_8245588
  have hstable : (prefixWord ++ tailWord_8245588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245588).length < 2 ^ (prefixWord ++ tailWord_8245588).sum := by decide
  have hdescent : baseEnd_8245588 < baseStart_8245588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245602 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_8245602 : Nat := 118140960795 + 8245602 * 2 ^ 59
def prefixEnd_8245602 : Nat := 4983230072969 + 3 ^ 40 * 8245602 * 2
def baseEnd_8245602 : Nat := 4233957111674353277954173

theorem tailTrace_8245602 : CollatzResearch.WordTrace tailWord_8245602 prefixEnd_8245602 4233957111674353277954173 := by
  unfold tailWord_8245602
  simp only [CollatzResearch.WordTrace]
  refine ⟨75185452968399916387814765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200494541249066443700839373 75185452968399916387814765)
  ·
    refine ⟨28194544863149968645430537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75185452968399916387814765 28194544863149968645430537)
    ·
      refine ⟨21145908647362476484072903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28194544863149968645430537 21145908647362476484072903)
      ·
        refine ⟨31718862971043714726109355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21145908647362476484072903 31718862971043714726109355)
        ·
          refine ⟨47578294456565572089164033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31718862971043714726109355 47578294456565572089164033)
          ·
            refine ⟨35683720842424179066873025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47578294456565572089164033 35683720842424179066873025)
            ·
              refine ⟨26762790631818134300154769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35683720842424179066873025 26762790631818134300154769)
              ·
                refine ⟨20072092973863600725116077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26762790631818134300154769 20072092973863600725116077)
                ·
                  refine ⟨7527034865198850271918529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20072092973863600725116077 7527034865198850271918529)
                  ·
                    refine ⟨5645276148899137703938897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7527034865198850271918529 5645276148899137703938897)
                    ·
                      refine ⟨4233957111674353277954173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645276148899137703938897 4233957111674353277954173)
                      ·
                        rfl

theorem cell23_8245602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_8245602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245602 prefixEnd_8245602 := by exact prefixLift 8245602
  have htrace : WordTrace (prefixWord ++ tailWord_8245602) baseStart_8245602 baseEnd_8245602 := by
    simpa [prefixWord, tailWord_8245602, baseEnd_8245602] using wordTrace_append hprefix tailTrace_8245602
  have hstable : (prefixWord ++ tailWord_8245602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245602).length < 2 ^ (prefixWord ++ tailWord_8245602).sum := by decide
  have hdescent : baseEnd_8245602 < baseStart_8245602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245605 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 3]
def baseStart_8245605 : Nat := 118140960795 + 8245605 * 2 ^ 59
def prefixEnd_8245605 : Nat := 4983230072969 + 3 ^ 40 * 8245605 * 2
def baseEnd_8245605 : Nat := 4233958652116316766216659

theorem tailTrace_8245605 : CollatzResearch.WordTrace tailWord_8245605 prefixEnd_8245605 4233958652116316766216659 := by
  unfold tailWord_8245605
  simp only [CollatzResearch.WordTrace]
  refine ⟨300741921292588797063618269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200494614195059198042412179 300741921292588797063618269)
  ·
    refine ⟨112778220484720798898856851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300741921292588797063618269 112778220484720798898856851)
    ·
      refine ⟨169167330727081198348285277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112778220484720798898856851 169167330727081198348285277)
      ·
        refine ⟨63437749022655449380606979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169167330727081198348285277 63437749022655449380606979)
        ·
          refine ⟨95156623533983174070910469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63437749022655449380606979 95156623533983174070910469)
          ·
            refine ⟨17841866912621845138295713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95156623533983174070910469 17841866912621845138295713)
            ·
              refine ⟨13381400184466383853721785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17841866912621845138295713 13381400184466383853721785)
              ·
                refine ⟨10036050138349787890291339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13381400184466383853721785 10036050138349787890291339)
                ·
                  refine ⟨15054075207524681835437009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036050138349787890291339 15054075207524681835437009)
                  ·
                    refine ⟨11290556405643511376577757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15054075207524681835437009 11290556405643511376577757)
                    ·
                      refine ⟨4233958652116316766216659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11290556405643511376577757 4233958652116316766216659)
                      ·
                        rfl

theorem cell23_8245605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_8245605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245605 prefixEnd_8245605 := by exact prefixLift 8245605
  have htrace : WordTrace (prefixWord ++ tailWord_8245605) baseStart_8245605 baseEnd_8245605 := by
    simpa [prefixWord, tailWord_8245605, baseEnd_8245605] using wordTrace_append hprefix tailTrace_8245605
  have hstable : (prefixWord ++ tailWord_8245605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245605).length < 2 ^ (prefixWord ++ tailWord_8245605).sum := by decide
  have hdescent : baseEnd_8245605 < baseStart_8245605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245608 : List Nat := [2, 1, 4, 2, 2, 1, 4, 7]
def baseStart_8245608 : Nat := 118140960795 + 8245608 * 2 ^ 59
def prefixEnd_8245608 : Nat := 4983230072969 + 3 ^ 40 * 8245608 * 2
def baseEnd_8245608 : Nat := 156813340465121490906635

theorem tailTrace_8245608 : CollatzResearch.WordTrace tailWord_8245608 prefixEnd_8245608 156813340465121490906635 := by
  unfold tailWord_8245608
  simp only [CollatzResearch.WordTrace]
  refine ⟨150371015355788964287988739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200494687141051952383984985 150371015355788964287988739)
  ·
    refine ⟨225556523033683446431983109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150371015355788964287988739 225556523033683446431983109)
    ·
      refine ⟨42291848068815646205996833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225556523033683446431983109 42291848068815646205996833)
      ·
        refine ⟨31718886051611734654497625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42291848068815646205996833 31718886051611734654497625)
        ·
          refine ⟨23789164538708800990873219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31718886051611734654497625 23789164538708800990873219)
          ·
            refine ⟨35683746808063201486309829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23789164538708800990873219 35683746808063201486309829)
            ·
              refine ⟨6690702526511850278683093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35683746808063201486309829 6690702526511850278683093)
              ·
                refine ⟨156813340465121490906635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6690702526511850278683093 156813340465121490906635)
                ·
                  rfl

theorem cell23_8245608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 7].length) (baseStart_8245608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245608 prefixEnd_8245608 := by exact prefixLift 8245608
  have htrace : WordTrace (prefixWord ++ tailWord_8245608) baseStart_8245608 baseEnd_8245608 := by
    simpa [prefixWord, tailWord_8245608, baseEnd_8245608] using wordTrace_append hprefix tailTrace_8245608
  have hstable : (prefixWord ++ tailWord_8245608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245608).length < 2 ^ (prefixWord ++ tailWord_8245608).sum := by decide
  have hdescent : baseEnd_8245608 < baseStart_8245608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245622 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_8245622 : Nat := 118140960795 + 8245622 * 2 ^ 59
def prefixEnd_8245622 : Nat := 4983230072969 + 3 ^ 40 * 8245622 * 2
def baseEnd_8245622 : Nat := 4233967381287443199704081

theorem tailTrace_8245622 : CollatzResearch.WordTrace tailWord_8245622 prefixEnd_8245622 4233967381287443199704081 := by
  unfold tailWord_8245622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18796408833345450560436695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200495027555684805977991413 18796408833345450560436695)
  ·
    refine ⟨28194613250018175840655043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18796408833345450560436695 28194613250018175840655043)
    ·
      refine ⟨42291919875027263760982565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28194613250018175840655043 42291919875027263760982565)
      ·
        refine ⟨7929734976567611955184231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42291919875027263760982565 7929734976567611955184231)
        ·
          refine ⟨11894602464851417932776347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7929734976567611955184231 11894602464851417932776347)
          ·
            refine ⟨17841903697277126899164521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11894602464851417932776347 17841903697277126899164521)
            ·
              refine ⟨13381427772957845174373391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17841903697277126899164521 13381427772957845174373391)
              ·
                refine ⟨20072141659436767761560087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13381427772957845174373391 20072141659436767761560087)
                ·
                  refine ⟨30108212489155151642340131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20072141659436767761560087 30108212489155151642340131)
                  ·
                    refine ⟨45162318733732727463510197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30108212489155151642340131 45162318733732727463510197)
                    ·
                      refine ⟨4233967381287443199704081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45162318733732727463510197 4233967381287443199704081)
                      ·
                        rfl

theorem cell23_8245622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_8245622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245622 prefixEnd_8245622 := by exact prefixLift 8245622
  have htrace : WordTrace (prefixWord ++ tailWord_8245622) baseStart_8245622 baseEnd_8245622 := by
    simpa [prefixWord, tailWord_8245622, baseEnd_8245622] using wordTrace_append hprefix tailTrace_8245622
  have hstable : (prefixWord ++ tailWord_8245622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245622).length < 2 ^ (prefixWord ++ tailWord_8245622).sum := by decide
  have hdescent : baseEnd_8245622 < baseStart_8245622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245711 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 1, 7]
def baseStart_8245711 : Nat := 118140960795 + 8245711 * 2 ^ 59
def prefixEnd_8245711 : Nat := 4983230072969 + 3 ^ 40 * 8245711 * 2
def baseEnd_8245711 : Nat := 1411337693688564450497057

theorem tailTrace_8245711 : CollatzResearch.WordTrace tailWord_8245711 prefixEnd_8245711 1411337693688564450497057 := by
  unfold tailWord_8245711
  simp only [CollatzResearch.WordTrace]
  refine ⟨300745787430204777166976987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200497191620136518111317991 300745787430204777166976987)
  ·
    refine ⟨451118681145307165750465481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300745787430204777166976987 451118681145307165750465481)
    ·
      refine ⟨338339010858980374312849111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451118681145307165750465481 338339010858980374312849111)
      ·
        refine ⟨507508516288470561469273667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338339010858980374312849111 507508516288470561469273667)
        ·
          refine ⟨761262774432705842203910501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507508516288470561469273667 761262774432705842203910501)
          ·
            refine ⟨142736770206132345413233219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 761262774432705842203910501 142736770206132345413233219)
            ·
              refine ⟨214105155309198518119849829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142736770206132345413233219 214105155309198518119849829)
              ·
                refine ⟨40144716620474722147471843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214105155309198518119849829 40144716620474722147471843)
                ·
                  refine ⟨60217074930712083221207765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40144716620474722147471843 60217074930712083221207765)
                  ·
                    refine ⟨1411337693688564450497057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60217074930712083221207765 1411337693688564450497057)
                    ·
                      rfl

theorem cell23_8245711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_8245711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245711 prefixEnd_8245711 := by exact prefixLift 8245711
  have htrace : WordTrace (prefixWord ++ tailWord_8245711) baseStart_8245711 baseEnd_8245711 := by
    simpa [prefixWord, tailWord_8245711, baseEnd_8245711] using wordTrace_append hprefix tailTrace_8245711
  have hstable : (prefixWord ++ tailWord_8245711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245711).length < 2 ^ (prefixWord ++ tailWord_8245711).sum := by decide
  have hdescent : baseEnd_8245711 < baseStart_8245711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245730 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_8245730 : Nat := 118140960795 + 8245730 * 2 ^ 59
def prefixEnd_8245730 : Nat := 4983230072969 + 3 ^ 40 * 8245730 * 2
def baseEnd_8245730 : Nat := 4234022837198128777153585

theorem tailTrace_8245730 : CollatzResearch.WordTrace tailWord_8245730 prefixEnd_8245730 4234022837198128777153585 := by
  unfold tailWord_8245730
  simp only [CollatzResearch.WordTrace]
  refine ⟨75186620104283985852979661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200497653611423962274612429 75186620104283985852979661)
  ·
    refine ⟨28194982539106494694867373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75186620104283985852979661 28194982539106494694867373)
    ·
      refine ⟨10573118452164935510575265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28194982539106494694867373 10573118452164935510575265)
      ·
        refine ⟨7929838839123701632931449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10573118452164935510575265 7929838839123701632931449)
        ·
          refine ⟨5947379129342776224698587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7929838839123701632931449 5947379129342776224698587)
          ·
            refine ⟨8921068694014164337047881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947379129342776224698587 8921068694014164337047881)
            ·
              refine ⟨6690801520510623252785911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8921068694014164337047881 6690801520510623252785911)
              ·
                refine ⟨10036202280765934879178867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690801520510623252785911 10036202280765934879178867)
                ·
                  refine ⟨15054303421148902318768301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036202280765934879178867 15054303421148902318768301)
                  ·
                    refine ⟨5645363782930838369538113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15054303421148902318768301 5645363782930838369538113)
                    ·
                      refine ⟨4234022837198128777153585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645363782930838369538113 4234022837198128777153585)
                      ·
                        rfl

theorem cell23_8245730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_8245730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245730 prefixEnd_8245730 := by exact prefixLift 8245730
  have htrace : WordTrace (prefixWord ++ tailWord_8245730) baseStart_8245730 baseEnd_8245730 := by
    simpa [prefixWord, tailWord_8245730, baseEnd_8245730] using wordTrace_append hprefix tailTrace_8245730
  have hstable : (prefixWord ++ tailWord_8245730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245730).length < 2 ^ (prefixWord ++ tailWord_8245730).sum := by decide
  have hdescent : baseEnd_8245730 < baseStart_8245730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245765 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 2, 4, 2]
def baseStart_8245765 : Nat := 118140960795 + 8245765 * 2 ^ 59
def prefixEnd_8245765 : Nat := 4983230072969 + 3 ^ 40 * 8245765 * 2
def baseEnd_8245765 : Nat := 4234040809021036140215923

theorem tailTrace_8245765 : CollatzResearch.WordTrace tailWord_8245765 prefixEnd_8245765 4234040809021036140215923 := by
  unfold tailWord_8245765
  simp only [CollatzResearch.WordTrace]
  refine ⟨300747756972009144389442749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200498504648006096259628499 300747756972009144389442749)
  ·
    refine ⟨112780408864503429146041031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300747756972009144389442749 112780408864503429146041031)
    ·
      refine ⟨169170613296755143719061547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112780408864503429146041031 169170613296755143719061547)
      ·
        refine ⟨253755919945132715578592321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169170613296755143719061547 253755919945132715578592321)
        ·
          refine ⟨190316939958849536683944241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253755919945132715578592321 190316939958849536683944241)
          ·
            refine ⟨142737704969137152512958181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190316939958849536683944241 142737704969137152512958181)
            ·
              refine ⟨26763319681713216096179659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142737704969137152512958181 26763319681713216096179659)
              ·
                refine ⟨40144979522569824144269489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26763319681713216096179659 40144979522569824144269489)
                ·
                  refine ⟨30108734641927368108202117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40144979522569824144269489 30108734641927368108202117)
                  ·
                    refine ⟨5645387745361381520287897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30108734641927368108202117 5645387745361381520287897)
                    ·
                      refine ⟨4234040809021036140215923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645387745361381520287897 4234040809021036140215923)
                      ·
                        rfl

theorem cell23_8245765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_8245765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245765 prefixEnd_8245765 := by exact prefixLift 8245765
  have htrace : WordTrace (prefixWord ++ tailWord_8245765) baseStart_8245765 baseEnd_8245765 := by
    simpa [prefixWord, tailWord_8245765, baseEnd_8245765] using wordTrace_append hprefix tailTrace_8245765
  have hstable : (prefixWord ++ tailWord_8245765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245765).length < 2 ^ (prefixWord ++ tailWord_8245765).sum := by decide
  have hdescent : baseEnd_8245765 < baseStart_8245765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245788 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 8]
def baseStart_8245788 : Nat := 118140960795 + 8245788 * 2 ^ 59
def prefixEnd_8245788 : Nat := 4983230072969 + 3 ^ 40 * 8245788 * 2
def baseEnd_8245788 : Nat := 470450291008454394469813

theorem tailTrace_8245788 : CollatzResearch.WordTrace tailWord_8245788 prefixEnd_8245788 470450291008454394469813 := by
  unfold tailWord_8245788
  simp only [CollatzResearch.WordTrace]
  refine ⟨150374297925462909658765009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200499063900617212878353345 150374297925462909658765009)
  ·
    refine ⟨112780723444097182244073757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150374297925462909658765009 112780723444097182244073757)
    ·
      refine ⟨42292771291536443341527659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112780723444097182244073757 42292771291536443341527659)
      ·
        refine ⟨63439156937304665012291489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42292771291536443341527659 63439156937304665012291489)
        ·
          refine ⟨47579367702978498759218617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63439156937304665012291489 47579367702978498759218617)
          ·
            refine ⟨35684525777233874069413963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47579367702978498759218617 35684525777233874069413963)
            ·
              refine ⟨53526788665850811104120945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35684525777233874069413963 53526788665850811104120945)
              ·
                refine ⟨40145091499388108328090709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53526788665850811104120945 40145091499388108328090709)
                ·
                  refine ⟨470450291008454394469813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40145091499388108328090709 470450291008454394469813)
                  ·
                    rfl

theorem cell23_8245788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_8245788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245788 prefixEnd_8245788 := by exact prefixLift 8245788
  have htrace : WordTrace (prefixWord ++ tailWord_8245788) baseStart_8245788 baseEnd_8245788 := by
    simpa [prefixWord, tailWord_8245788, baseEnd_8245788] using wordTrace_append hprefix tailTrace_8245788
  have hstable : (prefixWord ++ tailWord_8245788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245788).length < 2 ^ (prefixWord ++ tailWord_8245788).sum := by decide
  have hdescent : baseEnd_8245788 < baseStart_8245788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245799 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_8245799 : Nat := 118140960795 + 8245799 * 2 ^ 59
def prefixEnd_8245799 : Nat := 4983230072969 + 3 ^ 40 * 8245799 * 2
def baseEnd_8245799 : Nat := 4234058267363289007190767

theorem tailTrace_8245799 : CollatzResearch.WordTrace tailWord_8245799 prefixEnd_8245799 4234058267363289007190767 := by
  unfold tailWord_8245799
  simp only [CollatzResearch.WordTrace]
  refine ⟨300748997053885968196180451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200499331369257312130786967 300748997053885968196180451)
  ·
    refine ⟨451123495580828952294270677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300748997053885968196180451 451123495580828952294270677)
    ·
      refine ⟨10573206927675678569396969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 451123495580828952294270677 10573206927675678569396969)
      ·
        refine ⟨7929905195756758927047727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10573206927675678569396969 7929905195756758927047727)
        ·
          refine ⟨11894857793635138390571591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7929905195756758927047727 11894857793635138390571591)
          ·
            refine ⟨17842286690452707585857387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11894857793635138390571591 17842286690452707585857387)
            ·
              refine ⟨26763430035679061378786081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17842286690452707585857387 26763430035679061378786081)
              ·
                refine ⟨20072572526759296034089561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26763430035679061378786081 20072572526759296034089561)
                ·
                  refine ⟨15054429395069472025567171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20072572526759296034089561 15054429395069472025567171)
                  ·
                    refine ⟨22581644092604208038350757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15054429395069472025567171 22581644092604208038350757)
                    ·
                      refine ⟨4234058267363289007190767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22581644092604208038350757 4234058267363289007190767)
                      ·
                        rfl

theorem cell23_8245799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_8245799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245799 prefixEnd_8245799 := by exact prefixLift 8245799
  have htrace : WordTrace (prefixWord ++ tailWord_8245799) baseStart_8245799 baseEnd_8245799 := by
    simpa [prefixWord, tailWord_8245799, baseEnd_8245799] using wordTrace_append hprefix tailTrace_8245799
  have hstable : (prefixWord ++ tailWord_8245799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245799).length < 2 ^ (prefixWord ++ tailWord_8245799).sum := by decide
  have hdescent : baseEnd_8245799 < baseStart_8245799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245802 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_8245802 : Nat := 118140960795 + 8245802 * 2 ^ 59
def prefixEnd_8245802 : Nat := 4983230072969 + 3 ^ 40 * 8245802 * 2
def baseEnd_8245802 : Nat := 4234059807805252495453253

theorem tailTrace_8245802 : CollatzResearch.WordTrace tailWord_8245802 prefixEnd_8245802 4234059807805252495453253 := by
  unfold tailWord_8245802
  simp only [CollatzResearch.WordTrace]
  refine ⟨75187276618218774927134915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200499404315250066472359773 75187276618218774927134915)
  ·
    refine ⟨112780914927328162390702373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75187276618218774927134915 112780914927328162390702373)
    ·
      refine ⟨21146421548874030448256695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112780914927328162390702373 21146421548874030448256695)
      ·
        refine ⟨31719632323311045672385043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21146421548874030448256695 31719632323311045672385043)
        ·
          refine ⟨47579448484966568508577565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31719632323311045672385043 47579448484966568508577565)
          ·
            refine ⟨17842293181862463190716587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47579448484966568508577565 17842293181862463190716587)
            ·
              refine ⟨26763439772793694786074881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17842293181862463190716587 26763439772793694786074881)
              ·
                refine ⟨20072579829595271089556161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26763439772793694786074881 20072579829595271089556161)
                ·
                  refine ⟨15054434872196453317167121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20072579829595271089556161 15054434872196453317167121)
                  ·
                    refine ⟨11290826154147339987875341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15054434872196453317167121 11290826154147339987875341)
                    ·
                      refine ⟨4234059807805252495453253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11290826154147339987875341 4234059807805252495453253)
                      ·
                        rfl

theorem cell23_8245802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_8245802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245802 prefixEnd_8245802 := by exact prefixLift 8245802
  have htrace : WordTrace (prefixWord ++ tailWord_8245802) baseStart_8245802 baseEnd_8245802 := by
    simpa [prefixWord, tailWord_8245802, baseEnd_8245802] using wordTrace_append hprefix tailTrace_8245802
  have hstable : (prefixWord ++ tailWord_8245802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245802).length < 2 ^ (prefixWord ++ tailWord_8245802).sum := by decide
  have hdescent : baseEnd_8245802 < baseStart_8245802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245835 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 1, 5]
def baseStart_8245835 : Nat := 118140960795 + 8245835 * 2 ^ 59
def prefixEnd_8245835 : Nat := 4983230072969 + 3 ^ 40 * 8245835 * 2
def baseEnd_8245835 : Nat := 1411358917555616955446867

theorem tailTrace_8245835 : CollatzResearch.WordTrace tailWord_8245835 prefixEnd_8245835 1411358917555616955446867 := by
  unfold tailWord_8245835
  simp only [CollatzResearch.WordTrace]
  refine ⟨300750310081755546344490959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200500206721170364229660639 300750310081755546344490959)
  ·
    refine ⟨451125465122633319516736439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300750310081755546344490959 451125465122633319516736439)
    ·
      refine ⟨676688197683949979275104659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451125465122633319516736439 676688197683949979275104659)
      ·
        refine ⟨1015032296525924968912656989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676688197683949979275104659 1015032296525924968912656989)
        ·
          refine ⟨380637111197221863342246371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1015032296525924968912656989 380637111197221863342246371)
          ·
            refine ⟨570955666795832795013369557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380637111197221863342246371 570955666795832795013369557)
            ·
              refine ⟨13381773440527331133125849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 570955666795832795013369557 13381773440527331133125849)
              ·
                refine ⟨10036330080395498349844387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13381773440527331133125849 10036330080395498349844387)
                ·
                  refine ⟨15054495120593247524766581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036330080395498349844387 15054495120593247524766581)
                  ·
                    refine ⟨1411358917555616955446867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15054495120593247524766581 1411358917555616955446867)
                    ·
                      rfl

theorem cell23_8245835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 5].length) (baseStart_8245835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245835 prefixEnd_8245835 := by exact prefixLift 8245835
  have htrace : WordTrace (prefixWord ++ tailWord_8245835) baseStart_8245835 baseEnd_8245835 := by
    simpa [prefixWord, tailWord_8245835, baseEnd_8245835] using wordTrace_append hprefix tailTrace_8245835
  have hstable : (prefixWord ++ tailWord_8245835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245835).length < 2 ^ (prefixWord ++ tailWord_8245835).sum := by decide
  have hdescent : baseEnd_8245835 < baseStart_8245835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245848 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 3, 6]
def baseStart_8245848 : Nat := 118140960795 + 8245848 * 2 ^ 59
def prefixEnd_8245848 : Nat := 4983230072969 + 3 ^ 40 * 8245848 * 2
def baseEnd_8245848 : Nat := 1411361142638453105159347

theorem tailTrace_8245848 : CollatzResearch.WordTrace tailWord_8245848 prefixEnd_8245848 1411361142638453105159347 := by
  unfold tailWord_8245848
  simp only [CollatzResearch.WordTrace]
  refine ⟨150375392115354224782357099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200500522820472299709809465 150375392115354224782357099)
  ·
    refine ⟨225563088173031337173535649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150375392115354224782357099 225563088173031337173535649)
    ·
      refine ⟨169172316129773502880151737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225563088173031337173535649 169172316129773502880151737)
      ·
        refine ⟨126879237097330127160113803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169172316129773502880151737 126879237097330127160113803)
        ·
          refine ⟨190318855645995190740170705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126879237097330127160113803 190318855645995190740170705)
          ·
            refine ⟨142739141734496393055128029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190318855645995190740170705 142739141734496393055128029)
            ·
              refine ⟨53527178150436147395673011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142739141734496393055128029 53527178150436147395673011)
              ·
                refine ⟨80290767225654221093509517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53527178150436147395673011 80290767225654221093509517)
                ·
                  refine ⟨30109037709620332910066069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80290767225654221093509517 30109037709620332910066069)
                  ·
                    refine ⟨1411361142638453105159347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30109037709620332910066069 1411361142638453105159347)
                    ·
                      rfl

theorem cell23_8245848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_8245848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245848 prefixEnd_8245848 := by exact prefixLift 8245848
  have htrace : WordTrace (prefixWord ++ tailWord_8245848) baseStart_8245848 baseEnd_8245848 := by
    simpa [prefixWord, tailWord_8245848, baseEnd_8245848] using wordTrace_append hprefix tailTrace_8245848
  have hstable : (prefixWord ++ tailWord_8245848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245848).length < 2 ^ (prefixWord ++ tailWord_8245848).sum := by decide
  have hdescent : baseEnd_8245848 < baseStart_8245848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245855 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 4]
def baseStart_8245855 : Nat := 118140960795 + 8245855 * 2 ^ 59
def prefixEnd_8245855 : Nat := 4983230072969 + 3 ^ 40 * 8245855 * 2
def baseEnd_8245855 : Nat := 4234087022279940788090509

theorem tailTrace_8245855 : CollatzResearch.WordTrace tailWord_8245855 prefixEnd_8245855 4234087022279940788090509 := by
  unfold tailWord_8245855
  simp only [CollatzResearch.WordTrace]
  refine ⟨300751039541683089760219019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200500693027788726506812679 300751039541683089760219019)
  ·
    refine ⟨451126559312524634640328529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300751039541683089760219019 451126559312524634640328529)
    ·
      refine ⟨338344919484393475980246397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451126559312524634640328529 338344919484393475980246397)
      ·
        refine ⟨126879344806647553492592399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338344919484393475980246397 126879344806647553492592399)
        ·
          refine ⟨190319017209971330238888599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126879344806647553492592399 190319017209971330238888599)
          ·
            refine ⟨285478525814956995358332899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190319017209971330238888599 285478525814956995358332899)
            ·
              refine ⟨428217788722435493037499349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285478525814956995358332899 428217788722435493037499349)
              ·
                refine ⟨10036354423182081868066391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 428217788722435493037499349 10036354423182081868066391)
                ·
                  refine ⟨15054531634773122802099587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036354423182081868066391 15054531634773122802099587)
                  ·
                    refine ⟨22581797452159684203149381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15054531634773122802099587 22581797452159684203149381)
                    ·
                      refine ⟨4234087022279940788090509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22581797452159684203149381 4234087022279940788090509)
                      ·
                        rfl

theorem cell23_8245855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_8245855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245855 prefixEnd_8245855 := by exact prefixLift 8245855
  have htrace : WordTrace (prefixWord ++ tailWord_8245855) baseStart_8245855 baseEnd_8245855 := by
    simpa [prefixWord, tailWord_8245855, baseEnd_8245855] using wordTrace_append hprefix tailTrace_8245855
  have hstable : (prefixWord ++ tailWord_8245855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245855).length < 2 ^ (prefixWord ++ tailWord_8245855).sum := by decide
  have hdescent : baseEnd_8245855 < baseStart_8245855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245868 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_8245868 : Nat := 118140960795 + 8245868 * 2 ^ 59
def prefixEnd_8245868 : Nat := 4983230072969 + 3 ^ 40 * 8245868 * 2
def baseEnd_8245868 : Nat := 4234093697528449237227949

theorem tailTrace_8245868 : CollatzResearch.WordTrace tailWord_8245868 prefixEnd_8245868 4234093697528449237227949 := by
  unfold tailWord_8245868
  simp only [CollatzResearch.WordTrace]
  refine ⟨150375756845317996490221129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200501009127090661986961505 150375756845317996490221129)
  ·
    refine ⟨112781817633988497367665847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150375756845317996490221129 112781817633988497367665847)
    ·
      refine ⟨169172726450982746051498771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112781817633988497367665847 169172726450982746051498771)
      ·
        refine ⟨253759089676474119077248157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169172726450982746051498771 253759089676474119077248157)
        ·
          refine ⟨95159658628677794653968059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253759089676474119077248157 95159658628677794653968059)
          ·
            refine ⟨142739487943016691980952089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95159658628677794653968059 142739487943016691980952089)
            ·
              refine ⟨107054615957262518985714067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142739487943016691980952089 107054615957262518985714067)
              ·
                refine ⟨160581923935893778478571101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107054615957262518985714067 160581923935893778478571101)
                ·
                  refine ⟨60218221475960166929464163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160581923935893778478571101 60218221475960166929464163)
                  ·
                    refine ⟨90327332213940250394196245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60218221475960166929464163 90327332213940250394196245)
                    ·
                      refine ⟨4234093697528449237227949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90327332213940250394196245 4234093697528449237227949)
                      ·
                        rfl

theorem cell23_8245868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_8245868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245868 prefixEnd_8245868 := by exact prefixLift 8245868
  have htrace : WordTrace (prefixWord ++ tailWord_8245868) baseStart_8245868 baseEnd_8245868 := by
    simpa [prefixWord, tailWord_8245868, baseEnd_8245868] using wordTrace_append hprefix tailTrace_8245868
  have hstable : (prefixWord ++ tailWord_8245868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245868).length < 2 ^ (prefixWord ++ tailWord_8245868).sum := by decide
  have hdescent : baseEnd_8245868 < baseStart_8245868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245889 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_8245889 : Nat := 118140960795 + 8245889 * 2 ^ 59
def prefixEnd_8245889 : Nat := 4983230072969 + 3 ^ 40 * 8245889 * 2
def baseEnd_8245889 : Nat := 4234104480622193655065353

theorem tailTrace_8245889 : CollatzResearch.WordTrace tailWord_8245889 prefixEnd_8245889 4234104480622193655065353 := by
  unfold tailWord_8245889
  simp only [CollatzResearch.WordTrace]
  refine ⟨300752279623559913566956721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200501519749039942377971147 300752279623559913566956721)
  ·
    refine ⟨225564209717669935175217541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300752279623559913566956721 225564209717669935175217541)
    ·
      refine ⟨42293289322063112845353289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225564209717669935175217541 42293289322063112845353289)
      ·
        refine ⟨31719966991547334634014967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42293289322063112845353289 31719966991547334634014967)
        ·
          refine ⟨47579950487321001951022451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31719966991547334634014967 47579950487321001951022451)
          ·
            refine ⟨71369925730981502926533677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47579950487321001951022451 71369925730981502926533677)
            ·
              refine ⟨26763722149118063597450129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71369925730981502926533677 26763722149118063597450129)
              ·
                refine ⟨20072791611838547698087597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26763722149118063597450129 20072791611838547698087597)
                ·
                  refine ⟨7527296854439455386782849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20072791611838547698087597 7527296854439455386782849)
                  ·
                    refine ⟨5645472640829591540087137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7527296854439455386782849 5645472640829591540087137)
                    ·
                      refine ⟨4234104480622193655065353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645472640829591540087137 4234104480622193655065353)
                      ·
                        rfl

theorem cell23_8245889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_8245889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245889 prefixEnd_8245889 := by exact prefixLift 8245889
  have htrace : WordTrace (prefixWord ++ tailWord_8245889) baseStart_8245889 baseEnd_8245889 := by
    simpa [prefixWord, tailWord_8245889, baseEnd_8245889] using wordTrace_append hprefix tailTrace_8245889
  have hstable : (prefixWord ++ tailWord_8245889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245889).length < 2 ^ (prefixWord ++ tailWord_8245889).sum := by decide
  have hdescent : baseEnd_8245889 < baseStart_8245889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245892 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_8245892 : Nat := 118140960795 + 8245892 * 2 ^ 59
def prefixEnd_8245892 : Nat := 4983230072969 + 3 ^ 40 * 8245892 * 2
def baseEnd_8245892 : Nat := 4234106021064157143327839

theorem tailTrace_8245892 : CollatzResearch.WordTrace tailWord_8245892 prefixEnd_8245892 4234106021064157143327839 := by
  unfold tailWord_8245892
  simp only [CollatzResearch.WordTrace]
  refine ⟨150376194521274522539657965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200501592695032696719543953 150376194521274522539657965)
  ·
    refine ⟨56391072945477945952371737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150376194521274522539657965 56391072945477945952371737)
    ·
      refine ⟨42293304709108459464278803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56391072945477945952371737 42293304709108459464278803)
      ·
        refine ⟨63439957063662689196418205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42293304709108459464278803 63439957063662689196418205)
        ·
          refine ⟨23789983898873508448656827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63439957063662689196418205 23789983898873508448656827)
          ·
            refine ⟨35684975848310262672985241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23789983898873508448656827 35684975848310262672985241)
            ·
              refine ⟨26763731886232697004738931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35684975848310262672985241 26763731886232697004738931)
              ·
                refine ⟨40145597829349045507108397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26763731886232697004738931 40145597829349045507108397)
                ·
                  refine ⟨15054599186005892065165649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40145597829349045507108397 15054599186005892065165649)
                  ·
                    refine ⟨11290949389504419048874237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15054599186005892065165649 11290949389504419048874237)
                    ·
                      refine ⟨4234106021064157143327839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11290949389504419048874237 4234106021064157143327839)
                      ·
                        rfl

theorem cell23_8245892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_8245892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245892 prefixEnd_8245892 := by exact prefixLift 8245892
  have htrace : WordTrace (prefixWord ++ tailWord_8245892) baseStart_8245892 baseEnd_8245892 := by
    simpa [prefixWord, tailWord_8245892, baseEnd_8245892] using wordTrace_append hprefix tailTrace_8245892
  have hstable : (prefixWord ++ tailWord_8245892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245892).length < 2 ^ (prefixWord ++ tailWord_8245892).sum := by decide
  have hdescent : baseEnd_8245892 < baseStart_8245892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245895 : List Nat := [1, 1, 4, 2, 1, 2, 5, 7]
def baseStart_8245895 : Nat := 118140960795 + 8245895 * 2 ^ 59
def prefixEnd_8245895 : Nat := 4983230072969 + 3 ^ 40 * 8245895 * 2
def baseEnd_8245895 : Nat := 156818798574300764132975

theorem tailTrace_8245895 : CollatzResearch.WordTrace tailWord_8245895 prefixEnd_8245895 156818798574300764132975 := by
  unfold tailWord_8245895
  simp only [CollatzResearch.WordTrace]
  refine ⟨300752498461538176591675139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200501665641025451061116759 300752498461538176591675139)
  ·
    refine ⟨451128747692307264887512709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300752498461538176591675139 451128747692307264887512709)
    ·
      refine ⟨84586640192307612166408633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451128747692307264887512709 84586640192307612166408633)
      ·
        refine ⟨63439980144230709124806475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84586640192307612166408633 63439980144230709124806475)
        ·
          refine ⟨95159970216346063687209713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63439980144230709124806475 95159970216346063687209713)
          ·
            refine ⟨71369977662259547765407285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95159970216346063687209713 71369977662259547765407285)
            ·
              refine ⟨6690935405836832603006933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71369977662259547765407285 6690935405836832603006933)
              ·
                refine ⟨156818798574300764132975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6690935405836832603006933 156818798574300764132975)
                ·
                  rfl

theorem cell23_8245895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 7].length) (baseStart_8245895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245895 prefixEnd_8245895 := by exact prefixLift 8245895
  have htrace : WordTrace (prefixWord ++ tailWord_8245895) baseStart_8245895 baseEnd_8245895 := by
    simpa [prefixWord, tailWord_8245895, baseEnd_8245895] using wordTrace_append hprefix tailTrace_8245895
  have hstable : (prefixWord ++ tailWord_8245895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245895).length < 2 ^ (prefixWord ++ tailWord_8245895).sum := by decide
  have hdescent : baseEnd_8245895 < baseStart_8245895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245906 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_8245906 : Nat := 118140960795 + 8245906 * 2 ^ 59
def prefixEnd_8245906 : Nat := 4983230072969 + 3 ^ 40 * 8245906 * 2
def baseEnd_8245906 : Nat := 4234113209793320088552775

theorem tailTrace_8245906 : CollatzResearch.WordTrace tailWord_8245906 prefixEnd_8245906 4234113209793320088552775 := by
  unfold tailWord_8245906
  simp only [CollatzResearch.WordTrace]
  refine ⟨75188224916124581367581393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200501933109665550313550381 75188224916124581367581393)
  ·
    refine ⟨56391168687093436025686045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75188224916124581367581393 56391168687093436025686045)
    ·
      refine ⟨21146688257660038509632267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56391168687093436025686045 21146688257660038509632267)
      ·
        refine ⟨31720032386490057764448401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21146688257660038509632267 31720032386490057764448401)
        ·
          refine ⟨23790024289867543323336301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31720032386490057764448401 23790024289867543323336301)
          ·
            refine ⟨8921259108700328746251113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23790024289867543323336301 8921259108700328746251113)
            ·
              refine ⟨6690944331525246559688335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8921259108700328746251113 6690944331525246559688335)
              ·
                refine ⟨10036416497287869839532503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690944331525246559688335 10036416497287869839532503)
                ·
                  refine ⟨15054624745931804759298755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036416497287869839532503 15054624745931804759298755)
                  ·
                    refine ⟨22581937118897707138948133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15054624745931804759298755 22581937118897707138948133)
                    ·
                      refine ⟨4234113209793320088552775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22581937118897707138948133 4234113209793320088552775)
                      ·
                        rfl

theorem cell23_8245906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_8245906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245906 prefixEnd_8245906 := by exact prefixLift 8245906
  have htrace : WordTrace (prefixWord ++ tailWord_8245906) baseStart_8245906 baseEnd_8245906 := by
    simpa [prefixWord, tailWord_8245906, baseEnd_8245906] using wordTrace_append hprefix tailTrace_8245906
  have hstable : (prefixWord ++ tailWord_8245906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245906).length < 2 ^ (prefixWord ++ tailWord_8245906).sum := by decide
  have hdescent : baseEnd_8245906 < baseStart_8245906 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245915 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 4, 7, 2]
def baseStart_8245915 : Nat := 118140960795 + 8245915 * 2 ^ 59
def prefixEnd_8245915 : Nat := 4983230072969 + 3 ^ 40 * 8245915 * 2
def baseEnd_8245915 : Nat := 4234117831119210553340233

theorem tailTrace_8245915 : CollatzResearch.WordTrace tailWord_8245915 prefixEnd_8245915 4234117831119210553340233 := by
  unfold tailWord_8245915
  simp only [CollatzResearch.WordTrace]
  refine ⟨300753227921465720007403199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200502151947643813338268799 300753227921465720007403199)
  ·
    refine ⟨451129841882198580011104799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300753227921465720007403199 451129841882198580011104799)
    ·
      refine ⟨676694762823297870016657199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451129841882198580011104799 676694762823297870016657199)
      ·
        refine ⟨1015042144234946805024985799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676694762823297870016657199 1015042144234946805024985799)
        ·
          refine ⟨1522563216352420207537478699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015042144234946805024985799 1522563216352420207537478699)
          ·
            refine ⟨2283844824528630311306218049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522563216352420207537478699 2283844824528630311306218049)
            ·
              refine ⟨1712883618396472733479663537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2283844824528630311306218049 1712883618396472733479663537)
              ·
                refine ⟨1284662713797354550109747653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1712883618396472733479663537 1284662713797354550109747653)
                ·
                  refine ⟨240874258837003978145577685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1284662713797354550109747653 240874258837003978145577685)
                  ·
                    refine ⟨5645490441492280737786977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 240874258837003978145577685 5645490441492280737786977)
                    ·
                      refine ⟨4234117831119210553340233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645490441492280737786977 4234117831119210553340233)
                      ·
                        rfl

theorem cell23_8245915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 7, 2].length) (baseStart_8245915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245915 prefixEnd_8245915 := by exact prefixLift 8245915
  have htrace : WordTrace (prefixWord ++ tailWord_8245915) baseStart_8245915 baseEnd_8245915 := by
    simpa [prefixWord, tailWord_8245915, baseEnd_8245915] using wordTrace_append hprefix tailTrace_8245915
  have hstable : (prefixWord ++ tailWord_8245915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245915).length < 2 ^ (prefixWord ++ tailWord_8245915).sum := by decide
  have hdescent : baseEnd_8245915 < baseStart_8245915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245949 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_8245949 : Nat := 118140960795 + 8245949 * 2 ^ 59
def prefixEnd_8245949 : Nat := 4983230072969 + 3 ^ 40 * 8245949 * 2
def baseEnd_8245949 : Nat := 4234135289461463420315077

theorem tailTrace_8245949 : CollatzResearch.WordTrace tailWord_8245949 prefixEnd_8245949 4234135289461463420315077 := by
  unfold tailWord_8245949
  simp only [CollatzResearch.WordTrace]
  refine ⟨300754468003342543814140901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200502978668895029209427267 300754468003342543814140901)
  ·
    refine ⟨56391462750626726965151419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300754468003342543814140901 56391462750626726965151419)
    ·
      refine ⟨84587194125940090447727129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56391462750626726965151419 84587194125940090447727129)
      ·
        refine ⟨63440395594455067835795347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84587194125940090447727129 63440395594455067835795347)
        ·
          refine ⟨95160593391682601753693021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63440395594455067835795347 95160593391682601753693021)
          ·
            refine ⟨35685222521880975657634883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95160593391682601753693021 35685222521880975657634883)
            ·
              refine ⟨53527833782821463486452325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35685222521880975657634883 53527833782821463486452325)
              ·
                refine ⟨10036468834279024403709811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53527833782821463486452325 10036468834279024403709811)
                ·
                  refine ⟨15054703251418536605564717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036468834279024403709811 15054703251418536605564717)
                  ·
                    refine ⟨5645513719281951227086769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15054703251418536605564717 5645513719281951227086769)
                    ·
                      refine ⟨4234135289461463420315077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645513719281951227086769 4234135289461463420315077)
                      ·
                        rfl

theorem cell23_8245949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_8245949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245949 prefixEnd_8245949 := by exact prefixLift 8245949
  have htrace : WordTrace (prefixWord ++ tailWord_8245949) baseStart_8245949 baseEnd_8245949 := by
    simpa [prefixWord, tailWord_8245949, baseEnd_8245949] using wordTrace_append hprefix tailTrace_8245949
  have hstable : (prefixWord ++ tailWord_8245949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245949).length < 2 ^ (prefixWord ++ tailWord_8245949).sum := by decide
  have hdescent : baseEnd_8245949 < baseStart_8245949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8245995 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 3]
def baseStart_8245995 : Nat := 118140960795 + 8245995 * 2 ^ 59
def prefixEnd_8245995 : Nat := 4983230072969 + 3 ^ 40 * 8245995 * 2
def baseEnd_8245995 : Nat := 4234158909571570240339865

theorem tailTrace_8245995 : CollatzResearch.WordTrace tailWord_8245995 prefixEnd_8245995 4234158909571570240339865 := by
  unfold tailWord_8245995
  simp only [CollatzResearch.WordTrace]
  refine ⟨300756145761175893670315439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200504097174117262446876959 300756145761175893670315439)
  ·
    refine ⟨451134218641763840505473159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300756145761175893670315439 451134218641763840505473159)
    ·
      refine ⟨676701327962645760758209739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451134218641763840505473159 676701327962645760758209739)
      ·
        refine ⟨1015051991943968641137314609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676701327962645760758209739 1015051991943968641137314609)
        ·
          refine ⟨761288993957976480852985957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015051991943968641137314609 761288993957976480852985957)
          ·
            refine ⟨142741686367120590159934867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 761288993957976480852985957 142741686367120590159934867)
            ·
              refine ⟨214112529550680885239902301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142741686367120590159934867 214112529550680885239902301)
              ·
                refine ⟨80292198581505331964963363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214112529550680885239902301 80292198581505331964963363)
                ·
                  refine ⟨120438297872257997947445045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80292198581505331964963363 120438297872257997947445045)
                  ·
                    refine ⟨11291090425524187307572973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120438297872257997947445045 11291090425524187307572973)
                    ·
                      refine ⟨4234158909571570240339865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11291090425524187307572973 4234158909571570240339865)
                      ·
                        rfl

theorem cell23_8245995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 3].length) (baseStart_8245995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8245995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8245995 prefixEnd_8245995 := by exact prefixLift 8245995
  have htrace : WordTrace (prefixWord ++ tailWord_8245995) baseStart_8245995 baseEnd_8245995 := by
    simpa [prefixWord, tailWord_8245995, baseEnd_8245995] using wordTrace_append hprefix tailTrace_8245995
  have hstable : (prefixWord ++ tailWord_8245995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8245995).length < 2 ^ (prefixWord ++ tailWord_8245995).sum := by decide
  have hdescent : baseEnd_8245995 < baseStart_8245995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8245995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246025 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_8246025 : Nat := 118140960795 + 8246025 * 2 ^ 59
def prefixEnd_8246025 : Nat := 4983230072969 + 3 ^ 40 * 8246025 * 2
def baseEnd_8246025 : Nat := 4234174313991205122964727

theorem tailTrace_8246025 : CollatzResearch.WordTrace tailWord_8246025 prefixEnd_8246025 4234174313991205122964727 := by
  unfold tailWord_8246025
  simp only [CollatzResearch.WordTrace]
  refine ⟨300757239951067208793907529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200504826634044805862605019 300757239951067208793907529)
  ·
    refine ⟨225567929963300406595430647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300757239951067208793907529 225567929963300406595430647)
    ·
      refine ⟨338351894944950609893145971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225567929963300406595430647 338351894944950609893145971)
      ·
        refine ⟨507527842417425914839718957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338351894944950609893145971 507527842417425914839718957)
        ·
          refine ⟨190322940906534718064894609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507527842417425914839718957 190322940906534718064894609)
          ·
            refine ⟨142742205679901038548670957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190322940906534718064894609 142742205679901038548670957)
            ·
              refine ⟨53528327129962889455751609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142742205679901038548670957 53528327129962889455751609)
              ·
                refine ⟨40146245347472167091813707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53528327129962889455751609 40146245347472167091813707)
                ·
                  refine ⟨60219368021208250637720561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40146245347472167091813707 60219368021208250637720561)
                  ·
                    refine ⟨45164526015906187978290421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60219368021208250637720561 45164526015906187978290421)
                    ·
                      refine ⟨4234174313991205122964727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45164526015906187978290421 4234174313991205122964727)
                      ·
                        rfl

theorem cell23_8246025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_8246025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246025 prefixEnd_8246025 := by exact prefixLift 8246025
  have htrace : WordTrace (prefixWord ++ tailWord_8246025) baseStart_8246025 baseEnd_8246025 := by
    simpa [prefixWord, tailWord_8246025, baseEnd_8246025] using wordTrace_append hprefix tailTrace_8246025
  have hstable : (prefixWord ++ tailWord_8246025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246025).length < 2 ^ (prefixWord ++ tailWord_8246025).sum := by decide
  have hdescent : baseEnd_8246025 < baseStart_8246025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246069 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_8246069 : Nat := 118140960795 + 8246069 * 2 ^ 59
def prefixEnd_8246069 : Nat := 4983230072969 + 3 ^ 40 * 8246069 * 2
def baseEnd_8246069 : Nat := 4234196907140002950814525

theorem tailTrace_8246069 : CollatzResearch.WordTrace tailWord_8246069 prefixEnd_8246069 4234196907140002950814525 := by
  unfold tailWord_8246069
  simp only [CollatzResearch.WordTrace]
  refine ⟨300758844762907804308509261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200505896508605202872339507 300758844762907804308509261)
  ·
    refine ⟨112784566786090426615690973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300758844762907804308509261 112784566786090426615690973)
    ·
      refine ⟨42294212544783909980884115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112784566786090426615690973 42294212544783909980884115)
      ·
        refine ⟨63441318817175864971326173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42294212544783909980884115 63441318817175864971326173)
        ·
          refine ⟨23790494556440949364247315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63441318817175864971326173 23790494556440949364247315)
          ·
            refine ⟨35685741834661424046370973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23790494556440949364247315 35685741834661424046370973)
            ·
              refine ⟨13382153187998034017389115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35685741834661424046370973 13382153187998034017389115)
              ·
                refine ⟨20073229781997051026083673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13382153187998034017389115 20073229781997051026083673)
                ·
                  refine ⟨15054922336497788269562755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20073229781997051026083673 15054922336497788269562755)
                  ·
                    refine ⟨22582383504746682404344133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15054922336497788269562755 22582383504746682404344133)
                    ·
                      refine ⟨4234196907140002950814525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22582383504746682404344133 4234196907140002950814525)
                      ·
                        rfl

theorem cell23_8246069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_8246069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246069 prefixEnd_8246069 := by exact prefixLift 8246069
  have htrace : WordTrace (prefixWord ++ tailWord_8246069) baseStart_8246069 baseEnd_8246069 := by
    simpa [prefixWord, tailWord_8246069, baseEnd_8246069] using wordTrace_append hprefix tailTrace_8246069
  have hstable : (prefixWord ++ tailWord_8246069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246069).length < 2 ^ (prefixWord ++ tailWord_8246069).sum := by decide
  have hdescent : baseEnd_8246069 < baseStart_8246069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246072 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_8246072 : Nat := 118140960795 + 8246072 * 2 ^ 59
def prefixEnd_8246072 : Nat := 4983230072969 + 3 ^ 40 * 8246072 * 2
def baseEnd_8246072 : Nat := 4234198447581966439077011

theorem tailTrace_8246072 : CollatzResearch.WordTrace tailWord_8246072 prefixEnd_8246072 4234198447581966439077011 := by
  unfold tailWord_8246072
  simp only [CollatzResearch.WordTrace]
  refine ⟨150379477090948467910434235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200505969454597957213912313 150379477090948467910434235)
  ·
    refine ⟨225569215636422701865651353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150379477090948467910434235 225569215636422701865651353)
    ·
      refine ⟨169176911727317026399238515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225569215636422701865651353 169176911727317026399238515)
      ·
        refine ⟨253765367590975539598857773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169176911727317026399238515 253765367590975539598857773)
        ·
          refine ⟨95162012846615827349571665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253765367590975539598857773 95162012846615827349571665)
          ·
            refine ⟨71371509634961870512178749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95162012846615827349571665 71371509634961870512178749)
            ·
              refine ⟨26764316113110701442067031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71371509634961870512178749 26764316113110701442067031)
              ·
                refine ⟨40146474169666052163100547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26764316113110701442067031 40146474169666052163100547)
                ·
                  refine ⟨60219711254499078244650821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40146474169666052163100547 60219711254499078244650821)
                  ·
                    refine ⟨11291195860218577170872029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60219711254499078244650821 11291195860218577170872029)
                    ·
                      refine ⟨4234198447581966439077011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11291195860218577170872029 4234198447581966439077011)
                      ·
                        rfl

theorem cell23_8246072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_8246072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246072 prefixEnd_8246072 := by exact prefixLift 8246072
  have htrace : WordTrace (prefixWord ++ tailWord_8246072) baseStart_8246072 baseEnd_8246072 := by
    simpa [prefixWord, tailWord_8246072, baseEnd_8246072] using wordTrace_append hprefix tailTrace_8246072
  have hstable : (prefixWord ++ tailWord_8246072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246072).length < 2 ^ (prefixWord ++ tailWord_8246072).sum := by decide
  have hdescent : baseEnd_8246072 < baseStart_8246072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246092 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 8]
def baseStart_8246092 : Nat := 118140960795 + 8246092 * 2 ^ 59
def prefixEnd_8246092 : Nat := 4983230072969 + 3 ^ 40 * 8246092 * 2
def baseEnd_8246092 : Nat := 470467635243895151202991

theorem tailTrace_8246092 : CollatzResearch.WordTrace tailWord_8246092 prefixEnd_8246092 470467635243895151202991 := by
  unfold tailWord_8246092
  simp only [CollatzResearch.WordTrace]
  refine ⟨150379841820912239618298265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200506455761216319491064353 150379841820912239618298265)
  ·
    refine ⟨112784881365684179713723699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150379841820912239618298265 112784881365684179713723699)
    ·
      refine ⟨169177322048526269570585549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112784881365684179713723699 169177322048526269570585549)
      ·
        refine ⟨63441495768197351088969581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169177322048526269570585549 63441495768197351088969581)
        ·
          refine ⟨23790560913074006658363593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63441495768197351088969581 23790560913074006658363593)
          ·
            refine ⟨17842920684805504993772695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23790560913074006658363593 17842920684805504993772695)
            ·
              refine ⟨26764381027208257490659043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17842920684805504993772695 26764381027208257490659043)
              ·
                refine ⟨40146571540812386235988565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26764381027208257490659043 40146571540812386235988565)
                ·
                  refine ⟨470467635243895151202991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40146571540812386235988565 470467635243895151202991)
                  ·
                    rfl

theorem cell23_8246092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_8246092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246092 prefixEnd_8246092 := by exact prefixLift 8246092
  have htrace : WordTrace (prefixWord ++ tailWord_8246092) baseStart_8246092 baseEnd_8246092 := by
    simpa [prefixWord, tailWord_8246092, baseEnd_8246092] using wordTrace_append hprefix tailTrace_8246092
  have hstable : (prefixWord ++ tailWord_8246092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246092).length < 2 ^ (prefixWord ++ tailWord_8246092).sum := by decide
  have hdescent : baseEnd_8246092 < baseStart_8246092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246129 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 1, 5, 2]
def baseStart_8246129 : Nat := 118140960795 + 8246129 * 2 ^ 59
def prefixEnd_8246129 : Nat := 4983230072969 + 3 ^ 40 * 8246129 * 2
def baseEnd_8246129 : Nat := 4234227715979272716064249

theorem tailTrace_8246129 : CollatzResearch.WordTrace tailWord_8246129 prefixEnd_8246129 4234227715979272716064249 := by
  unfold tailWord_8246129
  simp only [CollatzResearch.WordTrace]
  refine ⟨300761033142690434555693441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200507355428460289703795627 300761033142690434555693441)
  ·
    refine ⟨225570774857017825916770081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300761033142690434555693441 225570774857017825916770081)
    ·
      refine ⟨169178081142763369437577561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225570774857017825916770081 169178081142763369437577561)
      ·
        refine ⟨126883560857072527078183171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169178081142763369437577561 126883560857072527078183171)
        ·
          refine ⟨190325341285608790617274757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126883560857072527078183171 190325341285608790617274757)
          ·
            refine ⟨35686001491051648240739017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190325341285608790617274757 35686001491051648240739017)
            ·
              refine ⟨26764501118288736180554263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35686001491051648240739017 26764501118288736180554263)
              ·
                refine ⟨40146751677433104270831395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26764501118288736180554263 40146751677433104270831395)
                ·
                  refine ⟨60220127516149656406247093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40146751677433104270831395 60220127516149656406247093)
                  ·
                    refine ⟨5645636954639030288085665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60220127516149656406247093 5645636954639030288085665)
                    ·
                      refine ⟨4234227715979272716064249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645636954639030288085665 4234227715979272716064249)
                      ·
                        rfl

theorem cell23_8246129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_8246129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246129 prefixEnd_8246129 := by exact prefixLift 8246129
  have htrace : WordTrace (prefixWord ++ tailWord_8246129) baseStart_8246129 baseEnd_8246129 := by
    simpa [prefixWord, tailWord_8246129, baseEnd_8246129] using wordTrace_append hprefix tailTrace_8246129
  have hstable : (prefixWord ++ tailWord_8246129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246129).length < 2 ^ (prefixWord ++ tailWord_8246129).sum := by decide
  have hdescent : baseEnd_8246129 < baseStart_8246129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246136 : List Nat := [2, 1, 2, 1, 1, 1, 1, 9, 1, 1, 3]
def baseStart_8246136 : Nat := 118140960795 + 8246136 * 2 ^ 59
def prefixEnd_8246136 : Nat := 4983230072969 + 3 ^ 40 * 8246136 * 2
def baseEnd_8246136 : Nat := 4234231310343854188676717

theorem tailTrace_8246136 : CollatzResearch.WordTrace tailWord_8246136 prefixEnd_8246136 4234231310343854188676717 := by
  unfold tailWord_8246136
  simp only [CollatzResearch.WordTrace]
  refine ⟨150380644226832537375599131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200507525635776716500798841 150380644226832537375599131)
  ·
    refine ⟨225570966340248806063398697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150380644226832537375599131 225570966340248806063398697)
    ·
      refine ⟨169178224755186604547549023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225570966340248806063398697 169178224755186604547549023)
      ·
        refine ⟨253767337132779906821323535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169178224755186604547549023 253767337132779906821323535)
        ·
          refine ⟨380651005699169860231985303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253767337132779906821323535 380651005699169860231985303)
          ·
            refine ⟨570976508548754790347977955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380651005699169860231985303 570976508548754790347977955)
            ·
              refine ⟨856464762823132185521966933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570976508548754790347977955 856464762823132185521966933)
              ·
                refine ⟨5018348219666790149542775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 856464762823132185521966933 5018348219666790149542775)
                ·
                  refine ⟨7527522329500185224314163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5018348219666790149542775 7527522329500185224314163)
                  ·
                    refine ⟨11291283494250277836471245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7527522329500185224314163 11291283494250277836471245)
                    ·
                      refine ⟨4234231310343854188676717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11291283494250277836471245 4234231310343854188676717)
                      ·
                        rfl

theorem cell23_8246136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 1, 3].length) (baseStart_8246136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246136 prefixEnd_8246136 := by exact prefixLift 8246136
  have htrace : WordTrace (prefixWord ++ tailWord_8246136) baseStart_8246136 baseEnd_8246136 := by
    simpa [prefixWord, tailWord_8246136, baseEnd_8246136] using wordTrace_append hprefix tailTrace_8246136
  have hstable : (prefixWord ++ tailWord_8246136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246136).length < 2 ^ (prefixWord ++ tailWord_8246136).sum := by decide
  have hdescent : baseEnd_8246136 < baseStart_8246136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246176 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 3, 2, 2]
def baseStart_8246176 : Nat := 118140960795 + 8246176 * 2 ^ 59
def prefixEnd_8246176 : Nat := 4983230072969 + 3 ^ 40 * 8246176 * 2
def baseEnd_8246176 : Nat := 4234251849570034032176533

theorem tailTrace_8246176 : CollatzResearch.WordTrace tailWord_8246176 prefixEnd_8246176 4234251849570034032176533 := by
  unfold tailWord_8246176
  simp only [CollatzResearch.WordTrace]
  refine ⟨150381373686760080791327191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200508498249013441055102921 150381373686760080791327191)
  ·
    refine ⟨225572060530140121186990787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150381373686760080791327191 225572060530140121186990787)
    ·
      refine ⟨338358090795210181780486181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225572060530140121186990787 338358090795210181780486181)
      ·
        refine ⟨63442142024101909083841159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338358090795210181780486181 63442142024101909083841159)
        ·
          refine ⟨95163213036152863625761739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63442142024101909083841159 95163213036152863625761739)
          ·
            refine ⟨142744819554229295438642609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95163213036152863625761739 142744819554229295438642609)
            ·
              refine ⟨107058614665671971578981957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142744819554229295438642609 107058614665671971578981957)
              ·
                refine ⟨20073490249813494671059117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107058614665671971578981957 20073490249813494671059117)
                ·
                  refine ⟨7527558843680060501647169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20073490249813494671059117 7527558843680060501647169)
                  ·
                    refine ⟨5645669132760045376235377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7527558843680060501647169 5645669132760045376235377)
                    ·
                      refine ⟨4234251849570034032176533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645669132760045376235377 4234251849570034032176533)
                      ·
                        rfl

theorem cell23_8246176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_8246176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246176 prefixEnd_8246176 := by exact prefixLift 8246176
  have htrace : WordTrace (prefixWord ++ tailWord_8246176) baseStart_8246176 baseEnd_8246176 := by
    simpa [prefixWord, tailWord_8246176, baseEnd_8246176] using wordTrace_append hprefix tailTrace_8246176
  have hstable : (prefixWord ++ tailWord_8246176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246176).length < 2 ^ (prefixWord ++ tailWord_8246176).sum := by decide
  have hdescent : baseEnd_8246176 < baseStart_8246176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246193 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 1, 1, 4]
def baseStart_8246193 : Nat := 118140960795 + 8246193 * 2 ^ 59
def prefixEnd_8246193 : Nat := 4983230072969 + 3 ^ 40 * 8246193 * 2
def baseEnd_8246193 : Nat := 4234260578741160465663955

theorem tailTrace_8246193 : CollatzResearch.WordTrace tailWord_8246193 prefixEnd_8246193 4234260578741160465663955 := by
  unfold tailWord_8246193
  simp only [CollatzResearch.WordTrace]
  refine ⟨300763367414458573486023233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200508911609639048990682155 300763367414458573486023233)
  ·
    refine ⟨225572525560843930114517425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300763367414458573486023233 225572525560843930114517425)
    ·
      refine ⟨169179394170632947585888069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225572525560843930114517425 169179394170632947585888069)
      ·
        refine ⟨31721136406993677672354013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169179394170632947585888069 31721136406993677672354013)
        ·
          refine ⟨11895426152622629127132755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31721136406993677672354013 11895426152622629127132755)
          ·
            refine ⟨17843139228933943690699133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11895426152622629127132755 17843139228933943690699133)
            ·
              refine ⟨6691177210850228884012175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17843139228933943690699133 6691177210850228884012175)
              ·
                refine ⟨10036765816275343326018263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691177210850228884012175 10036765816275343326018263)
                ·
                  refine ⟨15055148724413014989027395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10036765816275343326018263 15055148724413014989027395)
                  ·
                    refine ⟨22582723086619522483541093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15055148724413014989027395 22582723086619522483541093)
                    ·
                      refine ⟨4234260578741160465663955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22582723086619522483541093 4234260578741160465663955)
                      ·
                        rfl

theorem cell23_8246193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_8246193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246193 prefixEnd_8246193 := by exact prefixLift 8246193
  have htrace : WordTrace (prefixWord ++ tailWord_8246193) baseStart_8246193 baseEnd_8246193 := by
    simpa [prefixWord, tailWord_8246193, baseEnd_8246193] using wordTrace_append hprefix tailTrace_8246193
  have hstable : (prefixWord ++ tailWord_8246193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246193).length < 2 ^ (prefixWord ++ tailWord_8246193).sum := by decide
  have hdescent : baseEnd_8246193 < baseStart_8246193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246216 : List Nat := [2, 1, 3, 1, 6, 1, 1, 8]
def baseStart_8246216 : Nat := 118140960795 + 8246216 * 2 ^ 59
def prefixEnd_8246216 : Nat := 4983230072969 + 3 ^ 40 * 8246216 * 2
def baseEnd_8246216 : Nat := 156824903288748662062087

theorem tailTrace_8246216 : CollatzResearch.WordTrace tailWord_8246216 prefixEnd_8246216 156824903288748662062087 := by
  unfold tailWord_8246216
  simp only [CollatzResearch.WordTrace]
  refine ⟨150382103146687624207055251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200509470862250165609407001 150382103146687624207055251)
  ·
    refine ⟨225573154720031436310582877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150382103146687624207055251 225573154720031436310582877)
    ·
      refine ⟨84589933020011788616468579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225573154720031436310582877 84589933020011788616468579)
      ·
        refine ⟨126884899530017682924702869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84589933020011788616468579 126884899530017682924702869)
        ·
          refine ⟨5947729665469578887095447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126884899530017682924702869 5947729665469578887095447)
          ·
            refine ⟨8921594498204368330643171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947729665469578887095447 8921594498204368330643171)
            ·
              refine ⟨13382391747306552495964757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921594498204368330643171 13382391747306552495964757)
              ·
                refine ⟨156824903288748662062087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13382391747306552495964757 156824903288748662062087)
                ·
                  rfl

theorem cell23_8246216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 8].length) (baseStart_8246216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246216 prefixEnd_8246216 := by exact prefixLift 8246216
  have htrace : WordTrace (prefixWord ++ tailWord_8246216) baseStart_8246216 baseEnd_8246216 := by
    simpa [prefixWord, tailWord_8246216, baseEnd_8246216] using wordTrace_append hprefix tailTrace_8246216
  have hstable : (prefixWord ++ tailWord_8246216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246216).length < 2 ^ (prefixWord ++ tailWord_8246216).sum := by decide
  have hdescent : baseEnd_8246216 < baseStart_8246216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246226 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_8246226 : Nat := 118140960795 + 8246226 * 2 ^ 59
def prefixEnd_8246226 : Nat := 4983230072969 + 3 ^ 40 * 8246226 * 2
def baseEnd_8246226 : Nat := 4234277523602758836551303

theorem tailTrace_8246226 : CollatzResearch.WordTrace tailWord_8246226 prefixEnd_8246226 4234277523602758836551303 := by
  unfold tailWord_8246226
  simp only [CollatzResearch.WordTrace]
  refine ⟨75191142755834755030493633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200509714015559346747983021 75191142755834755030493633)
  ·
    refine ⟨56393357066876066272870225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75191142755834755030493633 56393357066876066272870225)
    ·
      refine ⟨42295017800157049704652669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56393357066876066272870225 42295017800157049704652669)
      ·
        refine ⟨15860631675058893639244751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42295017800157049704652669 15860631675058893639244751)
        ·
          refine ⟨23790947512588340458867127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15860631675058893639244751 23790947512588340458867127)
          ·
            refine ⟨35686421268882510688300691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23790947512588340458867127 35686421268882510688300691)
            ·
              refine ⟨53529631903323766032451037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35686421268882510688300691 53529631903323766032451037)
              ·
                refine ⟨20073611963746412262169139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53529631903323766032451037 20073611963746412262169139)
                ·
                  refine ⟨30110417945619618393253709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20073611963746412262169139 30110417945619618393253709)
                  ·
                    refine ⟨11291406729607356897470141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30110417945619618393253709 11291406729607356897470141)
                    ·
                      refine ⟨4234277523602758836551303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11291406729607356897470141 4234277523602758836551303)
                      ·
                        rfl

theorem cell23_8246226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_8246226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246226 prefixEnd_8246226 := by exact prefixLift 8246226
  have htrace : WordTrace (prefixWord ++ tailWord_8246226) baseStart_8246226 baseEnd_8246226 := by
    simpa [prefixWord, tailWord_8246226, baseEnd_8246226] using wordTrace_append hprefix tailTrace_8246226
  have hstable : (prefixWord ++ tailWord_8246226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246226).length < 2 ^ (prefixWord ++ tailWord_8246226).sum := by decide
  have hdescent : baseEnd_8246226 < baseStart_8246226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246279 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_8246279 : Nat := 118140960795 + 8246279 * 2 ^ 59
def prefixEnd_8246279 : Nat := 4983230072969 + 3 ^ 40 * 8246279 * 2
def baseEnd_8246279 : Nat := 4234304738077447129188559

theorem tailTrace_8246279 : CollatzResearch.WordTrace tailWord_8246279 prefixEnd_8246279 4234304738077447129188559 := by
  unfold tailWord_8246279
  simp only [CollatzResearch.WordTrace]
  refine ⟨300766504092147010173653891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200511002728098006782435927 300766504092147010173653891)
  ·
    refine ⟨451149756138220515260480837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300766504092147010173653891 451149756138220515260480837)
    ·
      refine ⟨84590579275916346611340157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451149756138220515260480837 84590579275916346611340157)
      ·
        refine ⟨31721467228468629979252559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84590579275916346611340157 31721467228468629979252559)
        ·
          refine ⟨47582200842702944968878839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31721467228468629979252559 47582200842702944968878839)
          ·
            refine ⟨71373301264054417453318259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47582200842702944968878839 71373301264054417453318259)
            ·
              refine ⟨107059951896081626179977389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71373301264054417453318259 107059951896081626179977389)
              ·
                refine ⟨40147481961030609817491521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107059951896081626179977389 40147481961030609817491521)
                ·
                  refine ⟨30110611470772957363118641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40147481961030609817491521 30110611470772957363118641)
                  ·
                    refine ⟨22582958603079718022338981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30110611470772957363118641 22582958603079718022338981)
                    ·
                      refine ⟨4234304738077447129188559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22582958603079718022338981 4234304738077447129188559)
                      ·
                        rfl

theorem cell23_8246279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_8246279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246279 prefixEnd_8246279 := by exact prefixLift 8246279
  have htrace : WordTrace (prefixWord ++ tailWord_8246279) baseStart_8246279 baseEnd_8246279 := by
    simpa [prefixWord, tailWord_8246279, baseEnd_8246279] using wordTrace_append hprefix tailTrace_8246279
  have hstable : (prefixWord ++ tailWord_8246279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246279).length < 2 ^ (prefixWord ++ tailWord_8246279).sum := by decide
  have hdescent : baseEnd_8246279 < baseStart_8246279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246283 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 1, 4, 2]
def baseStart_8246283 : Nat := 118140960795 + 8246283 * 2 ^ 59
def prefixEnd_8246283 : Nat := 4983230072969 + 3 ^ 40 * 8246283 * 2
def baseEnd_8246283 : Nat := 4234306792000065113538541

theorem tailTrace_8246283 : CollatzResearch.WordTrace tailWord_8246283 prefixEnd_8246283 4234306792000065113538541 := by
  unfold tailWord_8246283
  simp only [CollatzResearch.WordTrace]
  refine ⟨300766649984132518856799503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200511099989421679237866335 300766649984132518856799503)
  ·
    refine ⟨451149974976198778285199255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300766649984132518856799503 451149974976198778285199255)
    ·
      refine ⟨676724962464298167427798883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451149974976198778285199255 676724962464298167427798883)
      ·
        refine ⟨1015087443696447251141698325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676724962464298167427798883 1015087443696447251141698325)
        ·
          refine ⟨47582223923270964897267109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1015087443696447251141698325 47582223923270964897267109)
          ·
            refine ⟨8921666985613305918237583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47582223923270964897267109 8921666985613305918237583)
            ·
              refine ⟨13382500478419958877356375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921666985613305918237583 13382500478419958877356375)
              ·
                refine ⟨20073750717629938316034563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13382500478419958877356375 20073750717629938316034563)
                ·
                  refine ⟨30110626076444907474051845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20073750717629938316034563 30110626076444907474051845)
                  ·
                    refine ⟨5645742389333420151384721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30110626076444907474051845 5645742389333420151384721)
                    ·
                      refine ⟨4234306792000065113538541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645742389333420151384721 4234306792000065113538541)
                      ·
                        rfl

theorem cell23_8246283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 4, 2].length) (baseStart_8246283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246283 prefixEnd_8246283 := by exact prefixLift 8246283
  have htrace : WordTrace (prefixWord ++ tailWord_8246283) baseStart_8246283 baseEnd_8246283 := by
    simpa [prefixWord, tailWord_8246283, baseEnd_8246283] using wordTrace_append hprefix tailTrace_8246283
  have hstable : (prefixWord ++ tailWord_8246283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246283).length < 2 ^ (prefixWord ++ tailWord_8246283).sum := by decide
  have hdescent : baseEnd_8246283 < baseStart_8246283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246329 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_8246329 : Nat := 118140960795 + 8246329 * 2 ^ 59
def prefixEnd_8246329 : Nat := 4983230072969 + 3 ^ 40 * 8246329 * 2
def baseEnd_8246329 : Nat := 4234330412110171933563329

theorem tailTrace_8246329 : CollatzResearch.WordTrace tailWord_8246329 prefixEnd_8246329 4234330412110171933563329 := by
  unfold tailWord_8246329
  simp only [CollatzResearch.WordTrace]
  refine ⟨300768327741965868712974041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200512218494643912475316027 300768327741965868712974041)
  ·
    refine ⟨225576245806474401534730531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300768327741965868712974041 225576245806474401534730531)
    ·
      refine ⟨338364368709711602302095797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225576245806474401534730531 338364368709711602302095797)
      ·
        refine ⟨31721659566535462715821481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338364368709711602302095797 31721659566535462715821481)
        ·
          refine ⟨23791244674901597036866111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31721659566535462715821481 23791244674901597036866111)
          ·
            refine ⟨35686867012352395555299167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23791244674901597036866111 35686867012352395555299167)
            ·
              refine ⟨53530300518528593332948751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35686867012352395555299167 53530300518528593332948751)
              ·
                refine ⟨80295450777792889999423127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53530300518528593332948751 80295450777792889999423127)
                ·
                  refine ⟨120443176166689334999134691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80295450777792889999423127 120443176166689334999134691)
                  ·
                    refine ⟨180664764250034002498702037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120443176166689334999134691 180664764250034002498702037)
                    ·
                      refine ⟨4234330412110171933563329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180664764250034002498702037 4234330412110171933563329)
                      ·
                        rfl

theorem cell23_8246329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_8246329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246329 prefixEnd_8246329 := by exact prefixLift 8246329
  have htrace : WordTrace (prefixWord ++ tailWord_8246329) baseStart_8246329 baseEnd_8246329 := by
    simpa [prefixWord, tailWord_8246329, baseEnd_8246329] using wordTrace_append hprefix tailTrace_8246329
  have hstable : (prefixWord ++ tailWord_8246329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246329).length < 2 ^ (prefixWord ++ tailWord_8246329).sum := by decide
  have hdescent : baseEnd_8246329 < baseStart_8246329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246334 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_8246334 : Nat := 118140960795 + 8246334 * 2 ^ 59
def prefixEnd_8246334 : Nat := 4983230072969 + 3 ^ 40 * 8246334 * 2
def baseEnd_8246334 : Nat := 4234332979513444414000807

theorem tailTrace_8246334 : CollatzResearch.WordTrace tailWord_8246334 prefixEnd_8246334 4234332979513444414000807 := by
  unfold tailWord_8246334
  simp only [CollatzResearch.WordTrace]
  refine ⟨37596063763368469320863257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200512340071298503044604037 37596063763368469320863257)
  ·
    refine ⟨28197047822526351990647443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37596063763368469320863257 28197047822526351990647443)
    ·
      refine ⟨42295571733789527985971165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28197047822526351990647443 42295571733789527985971165)
      ·
        refine ⟨15860839400171072994739187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42295571733789527985971165 15860839400171072994739187)
        ·
          refine ⟨23791259100256609492108781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15860839400171072994739187 23791259100256609492108781)
          ·
            refine ⟨8921722162596228559540793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23791259100256609492108781 8921722162596228559540793)
            ·
              refine ⟨6691291621947171419655595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8921722162596228559540793 6691291621947171419655595)
              ·
                refine ⟨10036937432920757129483393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691291621947171419655595 10036937432920757129483393)
                ·
                  refine ⟨7527703074690567847112545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10036937432920757129483393 7527703074690567847112545)
                  ·
                    refine ⟨5645777306017925885334409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7527703074690567847112545 5645777306017925885334409)
                    ·
                      refine ⟨4234332979513444414000807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645777306017925885334409 4234332979513444414000807)
                      ·
                        rfl

theorem cell23_8246334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_8246334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246334 prefixEnd_8246334 := by exact prefixLift 8246334
  have htrace : WordTrace (prefixWord ++ tailWord_8246334) baseStart_8246334 baseEnd_8246334 := by
    simpa [prefixWord, tailWord_8246334, baseEnd_8246334] using wordTrace_append hprefix tailTrace_8246334
  have hstable : (prefixWord ++ tailWord_8246334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246334).length < 2 ^ (prefixWord ++ tailWord_8246334).sum := by decide
  have hdescent : baseEnd_8246334 < baseStart_8246334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246339 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 4]
def baseStart_8246339 : Nat := 118140960795 + 8246339 * 2 ^ 59
def prefixEnd_8246339 : Nat := 4983230072969 + 3 ^ 40 * 8246339 * 2
def baseEnd_8246339 : Nat := 4234335546916716894438283

theorem tailTrace_8246339 : CollatzResearch.WordTrace tailWord_8246339 prefixEnd_8246339 4234335546916716894438283 := by
  unfold tailWord_8246339
  simp only [CollatzResearch.WordTrace]
  refine ⟨300768692471929640420838071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200512461647953093613892047 300768692471929640420838071)
  ·
    refine ⟨451153038707894460631257107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300768692471929640420838071 451153038707894460631257107)
    ·
      refine ⟨676729558061841690946885661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451153038707894460631257107 676729558061841690946885661)
      ·
        refine ⟨253773584273190634105082123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 676729558061841690946885661 253773584273190634105082123)
        ·
          refine ⟨380660376409785951157623185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253773584273190634105082123 380660376409785951157623185)
          ·
            refine ⟨285495282307339463368217389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380660376409785951157623185 285495282307339463368217389)
            ·
              refine ⟨107060730865252298763081521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285495282307339463368217389 107060730865252298763081521)
              ·
                refine ⟨80295548148939224072311141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107060730865252298763081521 80295548148939224072311141)
                ·
                  refine ⟨15055415277926104513558339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80295548148939224072311141 15055415277926104513558339)
                  ·
                    refine ⟨22583122916889156770337509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15055415277926104513558339 22583122916889156770337509)
                    ·
                      refine ⟨4234335546916716894438283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22583122916889156770337509 4234335546916716894438283)
                      ·
                        rfl

theorem cell23_8246339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_8246339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246339 prefixEnd_8246339 := by exact prefixLift 8246339
  have htrace : WordTrace (prefixWord ++ tailWord_8246339) baseStart_8246339 baseEnd_8246339 := by
    simpa [prefixWord, tailWord_8246339, baseEnd_8246339] using wordTrace_append hprefix tailTrace_8246339
  have hstable : (prefixWord ++ tailWord_8246339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246339).length < 2 ^ (prefixWord ++ tailWord_8246339).sum := by decide
  have hdescent : baseEnd_8246339 < baseStart_8246339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246356 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_8246356 : Nat := 118140960795 + 8246356 * 2 ^ 59
def prefixEnd_8246356 : Nat := 4983230072969 + 3 ^ 40 * 8246356 * 2
def baseEnd_8246356 : Nat := 4234344276087843327925705

theorem tailTrace_8246356 : CollatzResearch.WordTrace tailWord_8246356 prefixEnd_8246356 4234344276087843327925705 := by
  unfold tailWord_8246356
  simp only [CollatzResearch.WordTrace]
  refine ⟨150384656256434026162103461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200512875008578701549471281 150384656256434026162103461)
  ·
    refine ⟨28197123048081379905394399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150384656256434026162103461 28197123048081379905394399)
    ·
      refine ⟨42295684572122069858091599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28197123048081379905394399 42295684572122069858091599)
      ·
        refine ⟨63443526858183104787137399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42295684572122069858091599 63443526858183104787137399)
        ·
          refine ⟨95165290287274657180706099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63443526858183104787137399 95165290287274657180706099)
          ·
            refine ⟨142747935430911985771059149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95165290287274657180706099 142747935430911985771059149)
            ·
              refine ⟨53530475786591994664147181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142747935430911985771059149 53530475786591994664147181)
              ·
                refine ⟨20073928419971997999055193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53530475786591994664147181 20073928419971997999055193)
                ·
                  refine ⟨15055446314978998499291395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20073928419971997999055193 15055446314978998499291395)
                  ·
                    refine ⟨22583169472468497748937093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15055446314978998499291395 22583169472468497748937093)
                    ·
                      refine ⟨4234344276087843327925705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22583169472468497748937093 4234344276087843327925705)
                      ·
                        rfl

theorem cell23_8246356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_8246356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246356 prefixEnd_8246356 := by exact prefixLift 8246356
  have htrace : WordTrace (prefixWord ++ tailWord_8246356) baseStart_8246356 baseEnd_8246356 := by
    simpa [prefixWord, tailWord_8246356, baseEnd_8246356] using wordTrace_append hprefix tailTrace_8246356
  have hstable : (prefixWord ++ tailWord_8246356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246356).length < 2 ^ (prefixWord ++ tailWord_8246356).sum := by decide
  have hdescent : baseEnd_8246356 < baseStart_8246356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246383 : List Nat := [1, 1, 2, 1, 3, 3, 3, 4, 1, 4]
def baseStart_8246383 : Nat := 118140960795 + 8246383 * 2 ^ 59
def prefixEnd_8246383 : Nat := 4983230072969 + 3 ^ 40 * 8246383 * 2
def baseEnd_8246383 : Nat := 1411452713355171574096027

theorem tailTrace_8246383 : CollatzResearch.WordTrace tailWord_8246383 prefixEnd_8246383 1411452713355171574096027 := by
  unfold tailWord_8246383
  simp only [CollatzResearch.WordTrace]
  refine ⟨300770297283770235935439803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200513531522513490623626535 300770297283770235935439803)
  ·
    refine ⟨451155445925655353903159705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300770297283770235935439803 451155445925655353903159705)
    ·
      refine ⟨338366584444241515427369779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451155445925655353903159705 338366584444241515427369779)
      ·
        refine ⟨507549876666362273141054669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338366584444241515427369779 507549876666362273141054669)
        ·
          refine ⟨190331203749885852427895501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507549876666362273141054669 190331203749885852427895501)
          ·
            refine ⟨71374201406207194660460813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190331203749885852427895501 71374201406207194660460813)
            ·
              refine ⟨26765325527327697997672805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71374201406207194660460813 26765325527327697997672805)
              ·
                refine ⟨5018498536373943374563651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26765325527327697997672805 5018498536373943374563651)
                ·
                  refine ⟨7527747804560915061845477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5018498536373943374563651 7527747804560915061845477)
                  ·
                    refine ⟨1411452713355171574096027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7527747804560915061845477 1411452713355171574096027)
                    ·
                      rfl

theorem cell23_8246383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 4].length) (baseStart_8246383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246383 prefixEnd_8246383 := by exact prefixLift 8246383
  have htrace : WordTrace (prefixWord ++ tailWord_8246383) baseStart_8246383 baseEnd_8246383 := by
    simpa [prefixWord, tailWord_8246383, baseEnd_8246383] using wordTrace_append hprefix tailTrace_8246383
  have hstable : (prefixWord ++ tailWord_8246383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246383).length < 2 ^ (prefixWord ++ tailWord_8246383).sum := by decide
  have hdescent : baseEnd_8246383 < baseStart_8246383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246430 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_8246430 : Nat := 118140960795 + 8246430 * 2 ^ 59
def prefixEnd_8246430 : Nat := 4983230072969 + 3 ^ 40 * 8246430 * 2
def baseEnd_8246430 : Nat := 470486919295141782044485

theorem tailTrace_8246430 : CollatzResearch.WordTrace tailWord_8246430 prefixEnd_8246430 470486919295141782044485 := by
  unfold tailWord_8246430
  simp only [CollatzResearch.WordTrace]
  refine ⟨37596501439324995370300093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200514674343066641974933829 37596501439324995370300093)
  ·
    refine ⟨14098688039746873263862535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37596501439324995370300093 14098688039746873263862535)
    ·
      refine ⟨21148032059620309895793803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14098688039746873263862535 21148032059620309895793803)
      ·
        refine ⟨31722048089430464843690705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21148032059620309895793803 31722048089430464843690705)
        ·
          refine ⟨23791536067072848632768029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31722048089430464843690705 23791536067072848632768029)
          ·
            refine ⟨8921826025152318237288011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23791536067072848632768029 8921826025152318237288011)
            ·
              refine ⟨13382739037728477355932017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921826025152318237288011 13382739037728477355932017)
              ·
                refine ⟨10037054278296358016949013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13382739037728477355932017 10037054278296358016949013)
                ·
                  refine ⟨470486919295141782044485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10037054278296358016949013 470486919295141782044485)
                  ·
                    rfl

theorem cell23_8246430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_8246430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246430 prefixEnd_8246430 := by exact prefixLift 8246430
  have htrace : WordTrace (prefixWord ++ tailWord_8246430) baseStart_8246430 baseEnd_8246430 := by
    simpa [prefixWord, tailWord_8246430, baseEnd_8246430] using wordTrace_append hprefix tailTrace_8246430
  have hstable : (prefixWord ++ tailWord_8246430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246430).length < 2 ^ (prefixWord ++ tailWord_8246430).sum := by decide
  have hdescent : baseEnd_8246430 < baseStart_8246430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246433 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_8246433 : Nat := 118140960795 + 8246433 * 2 ^ 59
def prefixEnd_8246433 : Nat := 4983230072969 + 3 ^ 40 * 8246433 * 2
def baseEnd_8246433 : Nat := 4234383814098239526662851

theorem tailTrace_8246433 : CollatzResearch.WordTrace tailWord_8246433 prefixEnd_8246433 4234383814098239526662851 := by
  unfold tailWord_8246433
  simp only [CollatzResearch.WordTrace]
  refine ⟨300772120933589094474759953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200514747289059396316506635 300772120933589094474759953)
  ·
    refine ⟨225579090700191820856069965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300772120933589094474759953 225579090700191820856069965)
    ·
      refine ⟨84592159012571932821026237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225579090700191820856069965 84592159012571932821026237)
      ·
        refine ⟨31722059629714474807884839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84592159012571932821026237 31722059629714474807884839)
        ·
          refine ⟨47583089444571712211827259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31722059629714474807884839 47583089444571712211827259)
          ·
            refine ⟨71374634166857568317740889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47583089444571712211827259 71374634166857568317740889)
            ·
              refine ⟨53530975625143176238305667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71374634166857568317740889 53530975625143176238305667)
              ·
                refine ⟨80296463437714764357458501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53530975625143176238305667 80296463437714764357458501)
                ·
                  refine ⟨15055586894571518317023469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80296463437714764357458501 15055586894571518317023469)
                  ·
                    refine ⟨5645845085464319368883801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15055586894571518317023469 5645845085464319368883801)
                    ·
                      refine ⟨4234383814098239526662851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645845085464319368883801 4234383814098239526662851)
                      ·
                        rfl

theorem cell23_8246433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_8246433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246433 prefixEnd_8246433 := by exact prefixLift 8246433
  have htrace : WordTrace (prefixWord ++ tailWord_8246433) baseStart_8246433 baseEnd_8246433 := by
    simpa [prefixWord, tailWord_8246433, baseEnd_8246433] using wordTrace_append hprefix tailTrace_8246433
  have hstable : (prefixWord ++ tailWord_8246433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246433).length < 2 ^ (prefixWord ++ tailWord_8246433).sum := by decide
  have hdescent : baseEnd_8246433 < baseStart_8246433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246497 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_8246497 : Nat := 118140960795 + 8246497 * 2 ^ 59
def prefixEnd_8246497 : Nat := 4983230072969 + 3 ^ 40 * 8246497 * 2
def baseEnd_8246497 : Nat := 4234416676860127276262557

theorem tailTrace_8246497 : CollatzResearch.WordTrace tailWord_8246497 prefixEnd_8246497 4234416676860127276262557 := by
  unfold tailWord_8246497
  simp only [CollatzResearch.WordTrace]
  refine ⟨300774455205357233405089745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200516303470238155603393163 300774455205357233405089745)
  ·
    refine ⟨225580841404017925053817309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300774455205357233405089745 225580841404017925053817309)
    ·
      refine ⟨84592815526506721895181491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225580841404017925053817309 84592815526506721895181491)
      ·
        refine ⟨126889223289760082842772237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84592815526506721895181491 126889223289760082842772237)
        ·
          refine ⟨47583458733660031066039589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126889223289760082842772237 47583458733660031066039589)
          ·
            refine ⟨8921898512561255824882423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47583458733660031066039589 8921898512561255824882423)
            ·
              refine ⟨13382847768841883737323635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921898512561255824882423 13382847768841883737323635)
              ·
                refine ⟨20074271653262825605985453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13382847768841883737323635 20074271653262825605985453)
                ·
                  refine ⟨7527851869973559602244545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20074271653262825605985453 7527851869973559602244545)
                  ·
                    refine ⟨5645888902480169701683409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7527851869973559602244545 5645888902480169701683409)
                    ·
                      refine ⟨4234416676860127276262557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645888902480169701683409 4234416676860127276262557)
                      ·
                        rfl

theorem cell23_8246497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_8246497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246497 prefixEnd_8246497 := by exact prefixLift 8246497
  have htrace : WordTrace (prefixWord ++ tailWord_8246497) baseStart_8246497 baseEnd_8246497 := by
    simpa [prefixWord, tailWord_8246497, baseEnd_8246497] using wordTrace_append hprefix tailTrace_8246497
  have hstable : (prefixWord ++ tailWord_8246497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246497).length < 2 ^ (prefixWord ++ tailWord_8246497).sum := by decide
  have hdescent : baseEnd_8246497 < baseStart_8246497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246503 : List Nat := [1, 1, 5, 3, 2, 1, 2, 8]
def baseStart_8246503 : Nat := 118140960795 + 8246503 * 2 ^ 59
def prefixEnd_8246503 : Nat := 4983230072969 + 3 ^ 40 * 8246503 * 2
def baseEnd_8246503 : Nat := 156830361397927935288427

theorem tailTrace_8246503 : CollatzResearch.WordTrace tailWord_8246503 prefixEnd_8246503 156830361397927935288427 := by
  unfold tailWord_8246503
  simp only [CollatzResearch.WordTrace]
  refine ⟨300774674043335496429808163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200516449362223664286538775 300774674043335496429808163)
  ·
    refine ⟨451162011065003244644712245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300774674043335496429808163 451162011065003244644712245)
    ·
      refine ⟨42296438537344054185441773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 451162011065003244644712245 42296438537344054185441773)
      ·
        refine ⟨15861164451504020319540665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42296438537344054185441773 15861164451504020319540665)
        ·
          refine ⟨11895873338628015239655499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15861164451504020319540665 11895873338628015239655499)
          ·
            refine ⟨17843810007942022859483249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11895873338628015239655499 17843810007942022859483249)
            ·
              refine ⟨13382857505956517144612437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17843810007942022859483249 13382857505956517144612437)
              ·
                refine ⟨156830361397927935288427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13382857505956517144612437 156830361397927935288427)
                ·
                  rfl

theorem cell23_8246503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 8].length) (baseStart_8246503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246503 prefixEnd_8246503 := by exact prefixLift 8246503
  have htrace : WordTrace (prefixWord ++ tailWord_8246503) baseStart_8246503 baseEnd_8246503 := by
    simpa [prefixWord, tailWord_8246503, baseEnd_8246503] using wordTrace_append hprefix tailTrace_8246503
  have hstable : (prefixWord ++ tailWord_8246503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246503).length < 2 ^ (prefixWord ++ tailWord_8246503).sum := by decide
  have hdescent : baseEnd_8246503 < baseStart_8246503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246556 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_8246556 : Nat := 118140960795 + 8246556 * 2 ^ 59
def prefixEnd_8246556 : Nat := 4983230072969 + 3 ^ 40 * 8246556 * 2
def baseEnd_8246556 : Nat := 4234446972218742545424785

theorem tailTrace_8246556 : CollatzResearch.WordTrace tailWord_8246556 prefixEnd_8246556 4234446972218742545424785 := by
  unfold tailWord_8246556
  simp only [CollatzResearch.WordTrace]
  refine ⟨150388303556071743240743761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200517738074762324320991681 150388303556071743240743761)
  ·
    refine ⟨112791227667053807430557821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150388303556071743240743761 112791227667053807430557821)
    ·
      refine ⟨42296710375145177786459183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112791227667053807430557821 42296710375145177786459183)
      ·
        refine ⟨63445065562717766679688775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42296710375145177786459183 63445065562717766679688775)
        ·
          refine ⟨95167598344076650019533163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63445065562717766679688775 95167598344076650019533163)
          ·
            refine ⟨142751397516114975029299745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95167598344076650019533163 142751397516114975029299745)
            ·
              refine ⟨107063548137086231271974809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142751397516114975029299745 107063548137086231271974809)
              ·
                refine ⟨80297661102814673453981107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107063548137086231271974809 80297661102814673453981107)
                ·
                  refine ⟨120446491654222010180971661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80297661102814673453981107 120446491654222010180971661)
                  ·
                    refine ⟨45167434370333253817864373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120446491654222010180971661 45167434370333253817864373)
                    ·
                      refine ⟨4234446972218742545424785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45167434370333253817864373 4234446972218742545424785)
                      ·
                        rfl

theorem cell23_8246556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_8246556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246556 prefixEnd_8246556 := by exact prefixLift 8246556
  have htrace : WordTrace (prefixWord ++ tailWord_8246556) baseStart_8246556 baseEnd_8246556 := by
    simpa [prefixWord, tailWord_8246556, baseEnd_8246556] using wordTrace_append hprefix tailTrace_8246556
  have hstable : (prefixWord ++ tailWord_8246556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246556).length < 2 ^ (prefixWord ++ tailWord_8246556).sum := by decide
  have hdescent : baseEnd_8246556 < baseStart_8246556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246576 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 7]
def baseStart_8246576 : Nat := 118140960795 + 8246576 * 2 ^ 59
def prefixEnd_8246576 : Nat := 4983230072969 + 3 ^ 40 * 8246576 * 2
def baseEnd_8246576 : Nat := 470495249092425829686077

theorem tailTrace_8246576 : CollatzResearch.WordTrace tailWord_8246576 prefixEnd_8246576 470495249092425829686077 := by
  unfold tailWord_8246576
  simp only [CollatzResearch.WordTrace]
  refine ⟨150388668286035514948607791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200518224381380686598143721 150388668286035514948607791)
  ·
    refine ⟨225583002429053272422911687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150388668286035514948607791 225583002429053272422911687)
    ·
      refine ⟨338374503643579908634367531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225583002429053272422911687 338374503643579908634367531)
      ·
        refine ⟨507561755465369862951551297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338374503643579908634367531 507561755465369862951551297)
        ·
          refine ⟨380671316599027397213663473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507561755465369862951551297 380671316599027397213663473)
          ·
            refine ⟨285503487449270547910247605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380671316599027397213663473 285503487449270547910247605)
            ·
              refine ⟨26765951948369113866585713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285503487449270547910247605 26765951948369113866585713)
              ·
                refine ⟨20074463961276835399939285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26765951948369113866585713 20074463961276835399939285)
                ·
                  refine ⟨470495249092425829686077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20074463961276835399939285 470495249092425829686077)
                  ·
                    rfl

theorem cell23_8246576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 7].length) (baseStart_8246576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246576 prefixEnd_8246576 := by exact prefixLift 8246576
  have htrace : WordTrace (prefixWord ++ tailWord_8246576) baseStart_8246576 baseEnd_8246576 := by
    simpa [prefixWord, tailWord_8246576, baseEnd_8246576] using wordTrace_append hprefix tailTrace_8246576
  have hstable : (prefixWord ++ tailWord_8246576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246576).length < 2 ^ (prefixWord ++ tailWord_8246576).sum := by decide
  have hdescent : baseEnd_8246576 < baseStart_8246576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246598 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_8246598 : Nat := 118140960795 + 8246598 * 2 ^ 59
def prefixEnd_8246598 : Nat := 4983230072969 + 3 ^ 40 * 8246598 * 2
def baseEnd_8246598 : Nat := 4234468538406231381099593

theorem tailTrace_8246598 : CollatzResearch.WordTrace tailWord_8246598 prefixEnd_8246598 4234468538406231381099593 := by
  unfold tailWord_8246598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9399316843062228989203639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200518759318660885103010965 9399316843062228989203639)
  ·
    refine ⟨14098975264593343483805459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9399316843062228989203639 14098975264593343483805459)
    ·
      refine ⟨21148462896890015225708189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14098975264593343483805459 21148462896890015225708189)
      ·
        refine ⟨7930673586333755709640571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21148462896890015225708189 7930673586333755709640571)
        ·
          refine ⟨11896010379500633564460857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7930673586333755709640571 11896010379500633564460857)
          ·
            refine ⟨8922007784625475173345643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11896010379500633564460857 8922007784625475173345643)
            ·
              refine ⟨13383011676938212760018465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922007784625475173345643 13383011676938212760018465)
              ·
                refine ⟨10037258757703659570013849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13383011676938212760018465 10037258757703659570013849)
                ·
                  refine ⟨7527944068277744677510387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10037258757703659570013849 7527944068277744677510387)
                  ·
                    refine ⟨11291916102416617016265581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7527944068277744677510387 11291916102416617016265581)
                    ·
                      refine ⟨4234468538406231381099593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11291916102416617016265581 4234468538406231381099593)
                      ·
                        rfl

theorem cell23_8246598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_8246598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246598 prefixEnd_8246598 := by exact prefixLift 8246598
  have htrace : WordTrace (prefixWord ++ tailWord_8246598) baseStart_8246598 baseEnd_8246598 := by
    simpa [prefixWord, tailWord_8246598, baseEnd_8246598] using wordTrace_append hprefix tailTrace_8246598
  have hstable : (prefixWord ++ tailWord_8246598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246598).length < 2 ^ (prefixWord ++ tailWord_8246598).sum := by decide
  have hdescent : baseEnd_8246598 < baseStart_8246598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246604 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 2, 2, 2]
def baseStart_8246604 : Nat := 118140960795 + 8246604 * 2 ^ 59
def prefixEnd_8246604 : Nat := 4983230072969 + 3 ^ 40 * 8246604 * 2
def baseEnd_8246604 : Nat := 4234471619290158357624565

theorem tailTrace_8246604 : CollatzResearch.WordTrace tailWord_8246604 prefixEnd_8246604 4234471619290158357624565 := by
  unfold tailWord_8246604
  simp only [CollatzResearch.WordTrace]
  refine ⟨150389178907984795339617433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200518905210646393786156577 150389178907984795339617433)
  ·
    refine ⟨112791884180988596504713075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150389178907984795339617433 112791884180988596504713075)
    ·
      refine ⟨169187826271482894757069613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112791884180988596504713075 169187826271482894757069613)
      ·
        refine ⟨63445434851806085533901105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169187826271482894757069613 63445434851806085533901105)
        ·
          refine ⟨47584076138854564150425829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63445434851806085533901105 47584076138854564150425829)
          ·
            refine ⟨8922014276035230778204843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47584076138854564150425829 8922014276035230778204843)
            ·
              refine ⟨13383021414052846167307265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922014276035230778204843 13383021414052846167307265)
              ·
                refine ⟨10037266060539634625480449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13383021414052846167307265 10037266060539634625480449)
                ·
                  refine ⟨7527949545404725969110337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10037266060539634625480449 7527949545404725969110337)
                  ·
                    refine ⟨5645962159053544476832753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7527949545404725969110337 5645962159053544476832753)
                    ·
                      refine ⟨4234471619290158357624565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5645962159053544476832753 4234471619290158357624565)
                      ·
                        rfl

theorem cell23_8246604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_8246604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246604 prefixEnd_8246604 := by exact prefixLift 8246604
  have htrace : WordTrace (prefixWord ++ tailWord_8246604) baseStart_8246604 baseEnd_8246604 := by
    simpa [prefixWord, tailWord_8246604, baseEnd_8246604] using wordTrace_append hprefix tailTrace_8246604
  have hstable : (prefixWord ++ tailWord_8246604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246604).length < 2 ^ (prefixWord ++ tailWord_8246604).sum := by decide
  have hdescent : baseEnd_8246604 < baseStart_8246604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246616 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_8246616 : Nat := 118140960795 + 8246616 * 2 ^ 59
def prefixEnd_8246616 : Nat := 4983230072969 + 3 ^ 40 * 8246616 * 2
def baseEnd_8246616 : Nat := 4234477781058012310674509

theorem tailTrace_8246616 : CollatzResearch.WordTrace tailWord_8246616 prefixEnd_8246616 4234477781058012310674509 := by
  unfold tailWord_8246616
  simp only [CollatzResearch.WordTrace]
  refine ⟨150389397745963058364335851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200519196994617411152447801 150389397745963058364335851)
  ·
    refine ⟨225584096618944587546503777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150389397745963058364335851 225584096618944587546503777)
    ·
      refine ⟨169188072464208440659877833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225584096618944587546503777 169188072464208440659877833)
      ·
        refine ⟨126891054348156330494908375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169188072464208440659877833 126891054348156330494908375)
        ·
          refine ⟨190336581522234495742362563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126891054348156330494908375 190336581522234495742362563)
          ·
            refine ⟨285504872283351743613543845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190336581522234495742362563 285504872283351743613543845)
            ·
              refine ⟨53532163553128451927539471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285504872283351743613543845 53532163553128451927539471)
              ·
                refine ⟨80298245329692677891309207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53532163553128451927539471 80298245329692677891309207)
                ·
                  refine ⟨120447367994539016836963811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80298245329692677891309207 120447367994539016836963811)
                  ·
                    refine ⟨180671051991808525255445717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120447367994539016836963811 180671051991808525255445717)
                    ·
                      refine ⟨4234477781058012310674509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180671051991808525255445717 4234477781058012310674509)
                      ·
                        rfl

theorem cell23_8246616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_8246616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246616 prefixEnd_8246616 := by exact prefixLift 8246616
  have htrace : WordTrace (prefixWord ++ tailWord_8246616) baseStart_8246616 baseEnd_8246616 := by
    simpa [prefixWord, tailWord_8246616, baseEnd_8246616] using wordTrace_append hprefix tailTrace_8246616
  have hstable : (prefixWord ++ tailWord_8246616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246616).length < 2 ^ (prefixWord ++ tailWord_8246616).sum := by decide
  have hdescent : baseEnd_8246616 < baseStart_8246616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246656 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_8246656 : Nat := 118140960795 + 8246656 * 2 ^ 59
def prefixEnd_8246656 : Nat := 4983230072969 + 3 ^ 40 * 8246656 * 2
def baseEnd_8246656 : Nat := 4234498320284192154174325

theorem tailTrace_8246656 : CollatzResearch.WordTrace tailWord_8246656 prefixEnd_8246656 4234498320284192154174325 := by
  unfold tailWord_8246656
  simp only [CollatzResearch.WordTrace]
  refine ⟨150390127205890601780063911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200520169607854135706751881 150390127205890601780063911)
  ·
    refine ⟨225585190808835902670095867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150390127205890601780063911 225585190808835902670095867)
    ·
      refine ⟨338377786213253854005143801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225585190808835902670095867 338377786213253854005143801)
      ·
        refine ⟨253783339659940390503857851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338377786213253854005143801 253783339659940390503857851)
        ·
          refine ⟨380675009489910585755786777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253783339659940390503857851 380675009489910585755786777)
          ·
            refine ⟨285506257117432939316840083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380675009489910585755786777 285506257117432939316840083)
            ·
              refine ⟨428259385676149408975260125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285506257117432939316840083 428259385676149408975260125)
              ·
                refine ⟨160597269628556028365722547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428259385676149408975260125 160597269628556028365722547)
                ·
                  refine ⟨240895904442834042548583821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160597269628556028365722547 240895904442834042548583821)
                  ·
                    refine ⟨90335964166062765955718933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240895904442834042548583821 90335964166062765955718933)
                    ·
                      refine ⟨4234498320284192154174325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90335964166062765955718933 4234498320284192154174325)
                      ·
                        rfl

theorem cell23_8246656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_8246656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246656 prefixEnd_8246656 := by exact prefixLift 8246656
  have htrace : WordTrace (prefixWord ++ tailWord_8246656) baseStart_8246656 baseEnd_8246656 := by
    simpa [prefixWord, tailWord_8246656, baseEnd_8246656] using wordTrace_append hprefix tailTrace_8246656
  have hstable : (prefixWord ++ tailWord_8246656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246656).length < 2 ^ (prefixWord ++ tailWord_8246656).sum := by decide
  have hdescent : baseEnd_8246656 < baseStart_8246656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246660 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_8246660 : Nat := 118140960795 + 8246660 * 2 ^ 59
def prefixEnd_8246660 : Nat := 4983230072969 + 3 ^ 40 * 8246660 * 2
def baseEnd_8246660 : Nat := 4234500374206810138524307

theorem tailTrace_8246660 : CollatzResearch.WordTrace tailWord_8246660 prefixEnd_8246660 4234500374206810138524307 := by
  unfold tailWord_8246660
  simp only [CollatzResearch.WordTrace]
  refine ⟨150390200151883356121636717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200520266869177808162182289 150390200151883356121636717)
  ·
    refine ⟨56396325056956258545613769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150390200151883356121636717 56396325056956258545613769)
    ·
      refine ⟨42297243792717193909210327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56396325056956258545613769 42297243792717193909210327)
      ·
        refine ⟨63445865689075790863815491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42297243792717193909210327 63445865689075790863815491)
        ·
          refine ⟨95168798533613686295723237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63445865689075790863815491 95168798533613686295723237)
          ·
            refine ⟨17844149725052566180448107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95168798533613686295723237 17844149725052566180448107)
            ·
              refine ⟨26766224587578849270672161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17844149725052566180448107 26766224587578849270672161)
              ·
                refine ⟨20074668440684136953004121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26766224587578849270672161 20074668440684136953004121)
                ·
                  refine ⟨15056001330513102714753091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20074668440684136953004121 15056001330513102714753091)
                  ·
                    refine ⟨22584001995769654072129637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15056001330513102714753091 22584001995769654072129637)
                    ·
                      refine ⟨4234500374206810138524307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22584001995769654072129637 4234500374206810138524307)
                      ·
                        rfl

theorem cell23_8246660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_8246660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246660 prefixEnd_8246660 := by exact prefixLift 8246660
  have htrace : WordTrace (prefixWord ++ tailWord_8246660) baseStart_8246660 baseEnd_8246660 := by
    simpa [prefixWord, tailWord_8246660, baseEnd_8246660] using wordTrace_append hprefix tailTrace_8246660
  have hstable : (prefixWord ++ tailWord_8246660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246660).length < 2 ^ (prefixWord ++ tailWord_8246660).sum := by decide
  have hdescent : baseEnd_8246660 < baseStart_8246660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246760 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 4, 4]
def baseStart_8246760 : Nat := 118140960795 + 8246760 * 2 ^ 59
def prefixEnd_8246760 : Nat := 4983230072969 + 3 ^ 40 * 8246760 * 2
def baseEnd_8246760 : Nat := 1411517240757419915757949

theorem tailTrace_8246760 : CollatzResearch.WordTrace tailWord_8246760 prefixEnd_8246760 1411517240757419915757949 := by
  unfold tailWord_8246760
  simp only [CollatzResearch.WordTrace]
  refine ⟨150392023801702214660956867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200522698402269619547942489 150392023801702214660956867)
  ·
    refine ⟨225588035702553321991435301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150392023801702214660956867 225588035702553321991435301)
    ·
      refine ⟨42297756694228747873394119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225588035702553321991435301 42297756694228747873394119)
      ·
        refine ⟨63446635041343121810091179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42297756694228747873394119 63446635041343121810091179)
        ·
          refine ⟨95169952562014682715136769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63446635041343121810091179 95169952562014682715136769)
          ·
            refine ⟨71377464421511012036352577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95169952562014682715136769 71377464421511012036352577)
            ·
              refine ⟨53533098316133259027264433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71377464421511012036352577 53533098316133259027264433)
              ·
                refine ⟨40149823737099944270448325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53533098316133259027264433 40149823737099944270448325)
                ·
                  refine ⟨7528091950706239550709061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40149823737099944270448325 7528091950706239550709061)
                  ·
                    refine ⟨1411517240757419915757949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7528091950706239550709061 1411517240757419915757949)
                    ·
                      rfl

theorem cell23_8246760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_8246760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246760 prefixEnd_8246760 := by exact prefixLift 8246760
  have htrace : WordTrace (prefixWord ++ tailWord_8246760) baseStart_8246760 baseEnd_8246760 := by
    simpa [prefixWord, tailWord_8246760, baseEnd_8246760] using wordTrace_append hprefix tailTrace_8246760
  have hstable : (prefixWord ++ tailWord_8246760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246760).length < 2 ^ (prefixWord ++ tailWord_8246760).sum := by decide
  have hdescent : baseEnd_8246760 < baseStart_8246760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246763 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 4]
def baseStart_8246763 : Nat := 118140960795 + 8246763 * 2 ^ 59
def prefixEnd_8246763 : Nat := 4983230072969 + 3 ^ 40 * 8246763 * 2
def baseEnd_8246763 : Nat := 4234553262714223235536333

theorem tailTrace_8246763 : CollatzResearch.WordTrace tailWord_8246763 prefixEnd_8246763 4234553262714223235536333 := by
  unfold tailWord_8246763
  simp only [CollatzResearch.WordTrace]
  refine ⟨300784157022393560834272943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200522771348262373889515295 300784157022393560834272943)
  ·
    refine ⟨451176235533590341251409415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300784157022393560834272943 451176235533590341251409415)
    ·
      refine ⟨676764353300385511877114123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451176235533590341251409415 676764353300385511877114123)
      ·
        refine ⟨1015146529950578267815671185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676764353300385511877114123 1015146529950578267815671185)
        ·
          refine ⟨761359897462933700861753389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015146529950578267815671185 761359897462933700861753389)
          ·
            refine ⟨285509961548600137823157521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 761359897462933700861753389 285509961548600137823157521)
            ·
              refine ⟨214132471161450103367368141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285509961548600137823157521 214132471161450103367368141)
              ·
                refine ⟨80299676685543788762763053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214132471161450103367368141 80299676685543788762763053)
                ·
                  refine ⟨30112378757078920786036145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80299676685543788762763053 30112378757078920786036145)
                  ·
                    refine ⟨22584284067809190589527109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30112378757078920786036145 22584284067809190589527109)
                    ·
                      refine ⟨4234553262714223235536333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22584284067809190589527109 4234553262714223235536333)
                      ·
                        rfl

theorem cell23_8246763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 4].length) (baseStart_8246763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246763 prefixEnd_8246763 := by exact prefixLift 8246763
  have htrace : WordTrace (prefixWord ++ tailWord_8246763) baseStart_8246763 baseEnd_8246763 := by
    simpa [prefixWord, tailWord_8246763, baseEnd_8246763] using wordTrace_append hprefix tailTrace_8246763
  have hstable : (prefixWord ++ tailWord_8246763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246763).length < 2 ^ (prefixWord ++ tailWord_8246763).sum := by decide
  have hdescent : baseEnd_8246763 < baseStart_8246763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246767 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 1, 1, 4]
def baseStart_8246767 : Nat := 118140960795 + 8246767 * 2 ^ 59
def prefixEnd_8246767 : Nat := 4983230072969 + 3 ^ 40 * 8246767 * 2
def baseEnd_8246767 : Nat := 4234555316636841219886315

theorem tailTrace_8246767 : CollatzResearch.WordTrace tailWord_8246767 prefixEnd_8246767 4234555316636841219886315 := by
  unfold tailWord_8246767
  simp only [CollatzResearch.WordTrace]
  refine ⟨300784302914379069517418555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200522868609586046344945703 300784302914379069517418555)
  ·
    refine ⟨451176454371568604276127833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300784302914379069517418555 451176454371568604276127833)
    ·
      refine ⟨338382340778676453207095875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451176454371568604276127833 338382340778676453207095875)
      ·
        refine ⟨507573511168014679810643813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338382340778676453207095875 507573511168014679810643813)
        ·
          refine ⟨95170033344002752464495715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 507573511168014679810643813 95170033344002752464495715)
          ·
            refine ⟨142755050016004128696743573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95170033344002752464495715 142755050016004128696743573)
            ·
              refine ⟨6691642969500193532659855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142755050016004128696743573 6691642969500193532659855)
              ·
                refine ⟨10037464454250290298989783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691642969500193532659855 10037464454250290298989783)
                ·
                  refine ⟨15056196681375435448484675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10037464454250290298989783 15056196681375435448484675)
                  ·
                    refine ⟨22584295022063153172727013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15056196681375435448484675 22584295022063153172727013)
                    ·
                      refine ⟨4234555316636841219886315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22584295022063153172727013 4234555316636841219886315)
                      ·
                        rfl

theorem cell23_8246767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 1, 4].length) (baseStart_8246767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246767 prefixEnd_8246767 := by exact prefixLift 8246767
  have htrace : WordTrace (prefixWord ++ tailWord_8246767) baseStart_8246767 baseEnd_8246767 := by
    simpa [prefixWord, tailWord_8246767, baseEnd_8246767] using wordTrace_append hprefix tailTrace_8246767
  have hstable : (prefixWord ++ tailWord_8246767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246767).length < 2 ^ (prefixWord ++ tailWord_8246767).sum := by decide
  have hdescent : baseEnd_8246767 < baseStart_8246767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246794 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_8246794 : Nat := 118140960795 + 8246794 * 2 ^ 59
def prefixEnd_8246794 : Nat := 4983230072969 + 3 ^ 40 * 8246794 * 2
def baseEnd_8246794 : Nat := 1411523060204837538082897

theorem tailTrace_8246794 : CollatzResearch.WordTrace tailWord_8246794 prefixEnd_8246794 1411523060204837538082897 := by
  unfold tailWord_8246794
  simp only [CollatzResearch.WordTrace]
  refine ⟨75196321921320313282162859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200523525123520835419100957 75196321921320313282162859)
  ·
    refine ⟨112794482881980469923244289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75196321921320313282162859 112794482881980469923244289)
    ·
      refine ⟨84595862161485352442433217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112794482881980469923244289 84595862161485352442433217)
      ·
        refine ⟨63446896621114014331824913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84595862161485352442433217 63446896621114014331824913)
        ·
          refine ⟨47585172465835510748868685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63446896621114014331824913 47585172465835510748868685)
          ·
            refine ⟨17844439674688316530825757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47585172465835510748868685 17844439674688316530825757)
            ·
              refine ⟨6691664878008118699059659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17844439674688316530825757 6691664878008118699059659)
              ·
                refine ⟨10037497317012178048589489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691664878008118699059659 10037497317012178048589489)
                ·
                  refine ⟨7528122987759133536442117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10037497317012178048589489 7528122987759133536442117)
                  ·
                    refine ⟨1411523060204837538082897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7528122987759133536442117 1411523060204837538082897)
                    ·
                      rfl

theorem cell23_8246794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_8246794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246794 prefixEnd_8246794 := by exact prefixLift 8246794
  have htrace : WordTrace (prefixWord ++ tailWord_8246794) baseStart_8246794 baseEnd_8246794 := by
    simpa [prefixWord, tailWord_8246794, baseEnd_8246794] using wordTrace_append hprefix tailTrace_8246794
  have hstable : (prefixWord ++ tailWord_8246794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246794).length < 2 ^ (prefixWord ++ tailWord_8246794).sum := by decide
  have hdescent : baseEnd_8246794 < baseStart_8246794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246817 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_8246817 : Nat := 118140960795 + 8246817 * 2 ^ 59
def prefixEnd_8246817 : Nat := 4983230072969 + 3 ^ 40 * 8246817 * 2
def baseEnd_8246817 : Nat := 4234580990669566024261085

theorem tailTrace_8246817 : CollatzResearch.WordTrace tailWord_8246817 prefixEnd_8246817 4234580990669566024261085 := by
  unfold tailWord_8246817
  simp only [CollatzResearch.WordTrace]
  refine ⟨300786126564197928056738705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200524084376131952037825803 300786126564197928056738705)
  ·
    refine ⟨225589594923148446042554029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300786126564197928056738705 225589594923148446042554029)
    ·
      refine ⟨84596098096180667265957761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225589594923148446042554029 84596098096180667265957761)
      ·
        refine ⟨63447073572135500449468321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84596098096180667265957761 63447073572135500449468321)
        ·
          refine ⟨47585305179101625337101241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63447073572135500449468321 47585305179101625337101241)
          ·
            refine ⟨35688978884326219002825931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47585305179101625337101241 35688978884326219002825931)
            ·
              refine ⟨53533468326489328504238897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35688978884326219002825931 53533468326489328504238897)
              ·
                refine ⟨40150101244866996378179173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53533468326489328504238897 40150101244866996378179173)
                ·
                  refine ⟨7528143983412561820908595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40150101244866996378179173 7528143983412561820908595)
                  ·
                    refine ⟨11292215975118842731362893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7528143983412561820908595 11292215975118842731362893)
                    ·
                      refine ⟨4234580990669566024261085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11292215975118842731362893 4234580990669566024261085)
                      ·
                        rfl

theorem cell23_8246817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_8246817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246817 prefixEnd_8246817 := by exact prefixLift 8246817
  have htrace : WordTrace (prefixWord ++ tailWord_8246817) baseStart_8246817 baseEnd_8246817 := by
    simpa [prefixWord, tailWord_8246817, baseEnd_8246817] using wordTrace_append hprefix tailTrace_8246817
  have hstable : (prefixWord ++ tailWord_8246817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246817).length < 2 ^ (prefixWord ++ tailWord_8246817).sum := by decide
  have hdescent : baseEnd_8246817 < baseStart_8246817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246860 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_8246860 : Nat := 118140960795 + 8246860 * 2 ^ 59
def prefixEnd_8246860 : Nat := 4983230072969 + 3 ^ 40 * 8246860 * 2
def baseEnd_8246860 : Nat := 4234603070337709356023387

theorem tailTrace_8246860 : CollatzResearch.WordTrace tailWord_8246860 prefixEnd_8246860 4234603070337709356023387 := by
  unfold tailWord_8246860
  simp only [CollatzResearch.WordTrace]
  refine ⟨150393847451521073200277017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200525129935361430933702689 150393847451521073200277017)
  ·
    refine ⟨112795385588640804900207763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150393847451521073200277017 112795385588640804900207763)
    ·
      refine ⟨169193078382961207350311645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112795385588640804900207763 169193078382961207350311645)
      ·
        refine ⟨63447404393610452756366867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169193078382961207350311645 63447404393610452756366867)
        ·
          refine ⟨95171106590415679134550301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63447404393610452756366867 95171106590415679134550301)
          ·
            refine ⟨35689164971405879675456363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95171106590415679134550301 35689164971405879675456363)
            ·
              refine ⟨53533747457108819513184545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35689164971405879675456363 53533747457108819513184545)
              ·
                refine ⟨40150310592831614634888409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53533747457108819513184545 40150310592831614634888409)
                ·
                  refine ⟨30112732944623710976166307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40150310592831614634888409 30112732944623710976166307)
                  ·
                    refine ⟨45169099416935566464249461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30112732944623710976166307 45169099416935566464249461)
                    ·
                      refine ⟨4234603070337709356023387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45169099416935566464249461 4234603070337709356023387)
                      ·
                        rfl

theorem cell23_8246860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_8246860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246860 prefixEnd_8246860 := by exact prefixLift 8246860
  have htrace : WordTrace (prefixWord ++ tailWord_8246860) baseStart_8246860 baseEnd_8246860 := by
    simpa [prefixWord, tailWord_8246860, baseEnd_8246860] using wordTrace_append hprefix tailTrace_8246860
  have hstable : (prefixWord ++ tailWord_8246860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246860).length < 2 ^ (prefixWord ++ tailWord_8246860).sum := by decide
  have hdescent : baseEnd_8246860 < baseStart_8246860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246861 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_8246861 : Nat := 118140960795 + 8246861 * 2 ^ 59
def prefixEnd_8246861 : Nat := 4983230072969 + 3 ^ 40 * 8246861 * 2
def baseEnd_8246861 : Nat := 4234603583818363852110883

theorem tailTrace_8246861 : CollatzResearch.WordTrace tailWord_8246861 prefixEnd_8246861 4234603583818363852110883 := by
  unfold tailWord_8246861
  simp only [CollatzResearch.WordTrace]
  refine ⟨300787731376038523571340437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200525154250692349047560291 300787731376038523571340437)
  ·
    refine ⟨14099424908251805792406583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 300787731376038523571340437 14099424908251805792406583)
    ·
      refine ⟨21149137362377708688609875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14099424908251805792406583 21149137362377708688609875)
      ·
        refine ⟨31723706043566563032914813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21149137362377708688609875 31723706043566563032914813)
        ·
          refine ⟨11896389766337461137343055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31723706043566563032914813 11896389766337461137343055)
          ·
            refine ⟨17844584649506191706014583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11896389766337461137343055 17844584649506191706014583)
            ·
              refine ⟨26766876974259287559021875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17844584649506191706014583 26766876974259287559021875)
              ·
                refine ⟨40150315461388931338532813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26766876974259287559021875 40150315461388931338532813)
                ·
                  refine ⟨15056368298020849251949805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40150315461388931338532813 15056368298020849251949805)
                  ·
                    refine ⟨5646138111757818469481177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15056368298020849251949805 5646138111757818469481177)
                    ·
                      refine ⟨4234603583818363852110883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646138111757818469481177 4234603583818363852110883)
                      ·
                        rfl

theorem cell23_8246861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_8246861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246861 prefixEnd_8246861 := by exact prefixLift 8246861
  have htrace : WordTrace (prefixWord ++ tailWord_8246861) baseStart_8246861 baseEnd_8246861 := by
    simpa [prefixWord, tailWord_8246861, baseEnd_8246861] using wordTrace_append hprefix tailTrace_8246861
  have hstable : (prefixWord ++ tailWord_8246861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246861).length < 2 ^ (prefixWord ++ tailWord_8246861).sum := by decide
  have hdescent : baseEnd_8246861 < baseStart_8246861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246863 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 9]
def baseStart_8246863 : Nat := 118140960795 + 8246863 * 2 ^ 59
def prefixEnd_8246863 : Nat := 4983230072969 + 3 ^ 40 * 8246863 * 2
def baseEnd_8246863 : Nat := 470511623419963649365097

theorem tailTrace_8246863 : CollatzResearch.WordTrace tailWord_8246863 prefixEnd_8246863 470511623419963649365097 := by
  unfold tailWord_8246863
  simp only [CollatzResearch.WordTrace]
  refine ⟨300787804322031277912913243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200525202881354185275275495 300787804322031277912913243)
  ·
    refine ⟨451181706483046916869369865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300787804322031277912913243 451181706483046916869369865)
    ·
      refine ⟨338386279862285187652027399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451181706483046916869369865 338386279862285187652027399)
      ·
        refine ⟨507579419793427781478041099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338386279862285187652027399 507579419793427781478041099)
        ·
          refine ⟨761369129690141672217061649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507579419793427781478041099 761369129690141672217061649)
          ·
            refine ⟨571026847267606254162796237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761369129690141672217061649 571026847267606254162796237)
            ·
              refine ⟨214135067725352345311048589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571026847267606254162796237 214135067725352345311048589)
              ·
                refine ⟨80300650397007129491643221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214135067725352345311048589 80300650397007129491643221)
                ·
                  refine ⟨470511623419963649365097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80300650397007129491643221 470511623419963649365097)
                  ·
                    rfl

theorem cell23_8246863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 9].length) (baseStart_8246863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246863 prefixEnd_8246863 := by exact prefixLift 8246863
  have htrace : WordTrace (prefixWord ++ tailWord_8246863) baseStart_8246863 baseEnd_8246863 := by
    simpa [prefixWord, tailWord_8246863, baseEnd_8246863] using wordTrace_append hprefix tailTrace_8246863
  have hstable : (prefixWord ++ tailWord_8246863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246863).length < 2 ^ (prefixWord ++ tailWord_8246863).sum := by decide
  have hdescent : baseEnd_8246863 < baseStart_8246863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246917 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 2, 5, 2]
def baseStart_8246917 : Nat := 118140960795 + 8246917 * 2 ^ 59
def prefixEnd_8246917 : Nat := 4983230072969 + 3 ^ 40 * 8246917 * 2
def baseEnd_8246917 : Nat := 4234632338735015633010625

theorem tailTrace_8246917 : CollatzResearch.WordTrace tailWord_8246917 prefixEnd_8246917 4234632338735015633010625 := by
  unfold tailWord_8246917
  simp only [CollatzResearch.WordTrace]
  refine ⟨300789773863835645135379005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200526515909223763423586003 300789773863835645135379005)
  ·
    refine ⟨112796165198938366925767127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300789773863835645135379005 112796165198938366925767127)
    ·
      refine ⟨169194247798407550388650691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112796165198938366925767127 169194247798407550388650691)
      ·
        refine ⟨253791371697611325582976037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169194247798407550388650691 253791371697611325582976037)
        ·
          refine ⟨47585882193302123546808007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253791371697611325582976037 47585882193302123546808007)
          ·
            refine ⟨71378823289953185320212011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47585882193302123546808007 71378823289953185320212011)
            ·
              refine ⟨107068234934929777980318017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71378823289953185320212011 107068234934929777980318017)
              ·
                refine ⟨80301176201197333485238513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107068234934929777980318017 80301176201197333485238513)
                ·
                  refine ⟨60225882150898000113928885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80301176201197333485238513 60225882150898000113928885)
                  ·
                    refine ⟨5646176451646687510680833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60225882150898000113928885 5646176451646687510680833)
                    ·
                      refine ⟨4234632338735015633010625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646176451646687510680833 4234632338735015633010625)
                      ·
                        rfl

theorem cell23_8246917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_8246917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246917 prefixEnd_8246917 := by exact prefixLift 8246917
  have htrace : WordTrace (prefixWord ++ tailWord_8246917) baseStart_8246917 baseEnd_8246917 := by
    simpa [prefixWord, tailWord_8246917, baseEnd_8246917] using wordTrace_append hprefix tailTrace_8246917
  have hstable : (prefixWord ++ tailWord_8246917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246917).length < 2 ^ (prefixWord ++ tailWord_8246917).sum := by decide
  have hdescent : baseEnd_8246917 < baseStart_8246917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246947 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 4, 4, 2]
def baseStart_8246947 : Nat := 118140960795 + 8246947 * 2 ^ 59
def prefixEnd_8246947 : Nat := 4983230072969 + 3 ^ 40 * 8246947 * 2
def baseEnd_8246947 : Nat := 4234647743154650515635487

theorem tailTrace_8246947 : CollatzResearch.WordTrace tailWord_8246947 prefixEnd_8246947 4234647743154650515635487 := by
  unfold tailWord_8246947
  simp only [CollatzResearch.WordTrace]
  refine ⟨300790868053726960258971095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200527245369151306839314063 300790868053726960258971095)
  ·
    refine ⟨451186302080590440388456643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300790868053726960258971095 451186302080590440388456643)
    ·
      refine ⟨676779453120885660582684965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451186302080590440388456643 676779453120885660582684965)
      ·
        refine ⟨126896147460166061359253431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 676779453120885660582684965 126896147460166061359253431)
        ·
          refine ⟨190344221190249092038880147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126896147460166061359253431 190344221190249092038880147)
          ·
            refine ⟨285516331785373638058320221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190344221190249092038880147 285516331785373638058320221)
            ·
              refine ⟨107068624419515114271870083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285516331785373638058320221 107068624419515114271870083)
              ·
                refine ⟨160602936629272671407805125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107068624419515114271870083 160602936629272671407805125)
                ·
                  refine ⟨30113050617988625888963461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160602936629272671407805125 30113050617988625888963461)
                  ·
                    refine ⟨5646196990872867354180649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30113050617988625888963461 5646196990872867354180649)
                    ·
                      refine ⟨4234647743154650515635487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646196990872867354180649 4234647743154650515635487)
                      ·
                        rfl

theorem cell23_8246947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_8246947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246947 prefixEnd_8246947 := by exact prefixLift 8246947
  have htrace : WordTrace (prefixWord ++ tailWord_8246947) baseStart_8246947 baseEnd_8246947 := by
    simpa [prefixWord, tailWord_8246947, baseEnd_8246947] using wordTrace_append hprefix tailTrace_8246947
  have hstable : (prefixWord ++ tailWord_8246947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246947).length < 2 ^ (prefixWord ++ tailWord_8246947).sum := by decide
  have hdescent : baseEnd_8246947 < baseStart_8246947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246967 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_8246967 : Nat := 118140960795 + 8246967 * 2 ^ 59
def prefixEnd_8246967 : Nat := 4983230072969 + 3 ^ 40 * 8246967 * 2
def baseEnd_8246967 : Nat := 4234658012767740437385395

theorem tailTrace_8246967 : CollatzResearch.WordTrace tailWord_8246967 prefixEnd_8246967 4234658012767740437385395 := by
  unfold tailWord_8246967
  simp only [CollatzResearch.WordTrace]
  refine ⟨300791597513654503674699155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200527731675769669116466103 300791597513654503674699155)
  ·
    refine ⟨451187396270481755512048733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300791597513654503674699155 451187396270481755512048733)
    ·
      refine ⟨169195273601430658317018275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451187396270481755512048733 169195273601430658317018275)
      ·
        refine ⟨253792910402145987475527413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169195273601430658317018275 253792910402145987475527413)
        ·
          refine ⟨23793085350201186325830695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253792910402145987475527413 23793085350201186325830695)
          ·
            refine ⟨35689628025301779488746043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23793085350201186325830695 35689628025301779488746043)
            ·
              refine ⟨53534442037952669233119065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35689628025301779488746043 53534442037952669233119065)
              ·
                refine ⟨40150831528464501924839299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53534442037952669233119065 40150831528464501924839299)
                ·
                  refine ⟨60226247292696752887258949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40150831528464501924839299 60226247292696752887258949)
                  ·
                    refine ⟨11292421367380641166361053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60226247292696752887258949 11292421367380641166361053)
                    ·
                      refine ⟨4234658012767740437385395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11292421367380641166361053 4234658012767740437385395)
                      ·
                        rfl

theorem cell23_8246967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_8246967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246967 prefixEnd_8246967 := by exact prefixLift 8246967
  have htrace : WordTrace (prefixWord ++ tailWord_8246967) baseStart_8246967 baseEnd_8246967 := by
    simpa [prefixWord, tailWord_8246967, baseEnd_8246967] using wordTrace_append hprefix tailTrace_8246967
  have hstable : (prefixWord ++ tailWord_8246967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246967).length < 2 ^ (prefixWord ++ tailWord_8246967).sum := by decide
  have hdescent : baseEnd_8246967 < baseStart_8246967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246974 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_8246974 : Nat := 118140960795 + 8246974 * 2 ^ 59
def prefixEnd_8246974 : Nat := 4983230072969 + 3 ^ 40 * 8246974 * 2
def baseEnd_8246974 : Nat := 1411553869044107303332621

theorem tailTrace_8246974 : CollatzResearch.WordTrace tailWord_8246974 prefixEnd_8246974 1411553869044107303332621 := by
  unfold tailWord_8246974
  simp only [CollatzResearch.WordTrace]
  refine ⟨37598981603078642983775497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200527901883086095913469317 37598981603078642983775497)
  ·
    refine ⟨28199236202308982237831623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37598981603078642983775497 28199236202308982237831623)
    ·
      refine ⟨42298854303463473356747435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28199236202308982237831623 42298854303463473356747435)
      ·
        refine ⟨63448281455195210035121153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42298854303463473356747435 63448281455195210035121153)
        ·
          refine ⟨47586211091396407526340865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63448281455195210035121153 47586211091396407526340865)
          ·
            refine ⟨35689658318547305644755649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47586211091396407526340865 35689658318547305644755649)
            ·
              refine ⟨26767243738910479233566737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35689658318547305644755649 26767243738910479233566737)
              ·
                refine ⟨20075432804182859425175053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26767243738910479233566737 20075432804182859425175053)
                ·
                  refine ⟨7528287301568572284440645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20075432804182859425175053 7528287301568572284440645)
                  ·
                    refine ⟨1411553869044107303332621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7528287301568572284440645 1411553869044107303332621)
                    ·
                      rfl

theorem cell23_8246974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_8246974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246974 prefixEnd_8246974 := by exact prefixLift 8246974
  have htrace : WordTrace (prefixWord ++ tailWord_8246974) baseStart_8246974 baseEnd_8246974 := by
    simpa [prefixWord, tailWord_8246974, baseEnd_8246974] using wordTrace_append hprefix tailTrace_8246974
  have hstable : (prefixWord ++ tailWord_8246974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246974).length < 2 ^ (prefixWord ++ tailWord_8246974).sum := by decide
  have hdescent : baseEnd_8246974 < baseStart_8246974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8246998 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_8246998 : Nat := 118140960795 + 8246998 * 2 ^ 59
def prefixEnd_8246998 : Nat := 4983230072969 + 3 ^ 40 * 8246998 * 2
def baseEnd_8246998 : Nat := 4234673930668029816097753

theorem tailTrace_8246998 : CollatzResearch.WordTrace tailWord_8246998 prefixEnd_8246998 4234673930668029816097753 := by
  unfold tailWord_8246998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18799545511033887248067353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200528485451028130646051765 18799545511033887248067353)
  ·
    refine ⟨14099659133275415436050515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18799545511033887248067353 14099659133275415436050515)
    ·
      refine ⟨21149488699913123154075773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14099659133275415436050515 21149488699913123154075773)
      ·
        refine ⟨7931058262467421182778415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21149488699913123154075773 7931058262467421182778415)
        ·
          refine ⟨11896587393701131774167623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7931058262467421182778415 11896587393701131774167623)
          ·
            refine ⟨17844881090551697661251435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11896587393701131774167623 17844881090551697661251435)
            ·
              refine ⟨26767321635827546491877153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17844881090551697661251435 26767321635827546491877153)
              ·
                refine ⟨20075491226870659868907865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26767321635827546491877153 20075491226870659868907865)
                ·
                  refine ⟨15056618420152994901680899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20075491226870659868907865 15056618420152994901680899)
                  ·
                    refine ⟨22584927630229492352521349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15056618420152994901680899 22584927630229492352521349)
                    ·
                      refine ⟨4234673930668029816097753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22584927630229492352521349 4234673930668029816097753)
                      ·
                        rfl

theorem cell23_8246998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_8246998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8246998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8246998 prefixEnd_8246998 := by exact prefixLift 8246998
  have htrace : WordTrace (prefixWord ++ tailWord_8246998) baseStart_8246998 baseEnd_8246998 := by
    simpa [prefixWord, tailWord_8246998, baseEnd_8246998] using wordTrace_append hprefix tailTrace_8246998
  have hstable : (prefixWord ++ tailWord_8246998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8246998).length < 2 ^ (prefixWord ++ tailWord_8246998).sum := by decide
  have hdescent : baseEnd_8246998 < baseStart_8246998 := by decide
  rcases family_descends (prefixWord ++ tailWord_8246998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247021 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 6]
def baseStart_8247021 : Nat := 118140960795 + 8247021 * 2 ^ 59
def prefixEnd_8247021 : Nat := 4983230072969 + 3 ^ 40 * 8247021 * 2
def baseEnd_8247021 : Nat := 470520637858120358456683

theorem tailTrace_8247021 : CollatzResearch.WordTrace tailWord_8247021 prefixEnd_8247021 470520637858120358456683 := by
  unfold tailWord_8247021
  simp only [CollatzResearch.WordTrace]
  refine ⟨300793567055458870897164917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200529044703639247264776611 300793567055458870897164917)
  ·
    refine ⟨28199396911449269146609211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300793567055458870897164917 28199396911449269146609211)
    ·
      refine ⟨42299095367173903719913817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28199396911449269146609211 42299095367173903719913817)
      ·
        refine ⟨31724321525380427789935363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42299095367173903719913817 31724321525380427789935363)
        ·
          refine ⟨47586482288070641684903045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31724321525380427789935363 47586482288070641684903045)
          ·
            refine ⟨8922465429013245315919321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47586482288070641684903045 8922465429013245315919321)
            ·
              refine ⟨6691849071759933986939491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8922465429013245315919321 6691849071759933986939491)
              ·
                refine ⟨10037773607639900980409237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691849071759933986939491 10037773607639900980409237)
                ·
                  refine ⟨470520637858120358456683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10037773607639900980409237 470520637858120358456683)
                  ·
                    rfl

theorem cell23_8247021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_8247021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247021 prefixEnd_8247021 := by exact prefixLift 8247021
  have htrace : WordTrace (prefixWord ++ tailWord_8247021) baseStart_8247021 baseEnd_8247021 := by
    simpa [prefixWord, tailWord_8247021, baseEnd_8247021] using wordTrace_append hprefix tailTrace_8247021
  have hstable : (prefixWord ++ tailWord_8247021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247021).length < 2 ^ (prefixWord ++ tailWord_8247021).sum := by decide
  have hdescent : baseEnd_8247021 < baseStart_8247021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247054 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_8247054 : Nat := 118140960795 + 8247054 * 2 ^ 59
def prefixEnd_8247054 : Nat := 4983230072969 + 3 ^ 40 * 8247054 * 2
def baseEnd_8247054 : Nat := 4234702685584681596997495

theorem tailTrace_8247054 : CollatzResearch.WordTrace tailWord_8247054 prefixEnd_8247054 4234702685584681596997495 := by
  unfold tailWord_8247054
  simp only [CollatzResearch.WordTrace]
  refine ⟨37599346333042414691639527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200529847109559545022077477 37599346333042414691639527)
  ·
    refine ⟨56399019499563622037459291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37599346333042414691639527 56399019499563622037459291)
    ·
      refine ⟨84598529249345433056188937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56399019499563622037459291 84598529249345433056188937)
      ·
        refine ⟨63448896937009074792141703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84598529249345433056188937 63448896937009074792141703)
        ·
          refine ⟨95173345405513612188212555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63448896937009074792141703 95173345405513612188212555)
          ·
            refine ⟨142760018108270418282318833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95173345405513612188212555 142760018108270418282318833)
            ·
              refine ⟨107070013581202813711739125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142760018108270418282318833 107070013581202813711739125)
              ·
                refine ⟨10037813773237763785475543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107070013581202813711739125 10037813773237763785475543)
                ·
                  refine ⟨15056720659856645678213315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10037813773237763785475543 15056720659856645678213315)
                  ·
                    refine ⟨22585080989784968517319973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15056720659856645678213315 22585080989784968517319973)
                    ·
                      refine ⟨4234702685584681596997495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22585080989784968517319973 4234702685584681596997495)
                      ·
                        rfl

theorem cell23_8247054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_8247054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247054 prefixEnd_8247054 := by exact prefixLift 8247054
  have htrace : WordTrace (prefixWord ++ tailWord_8247054) baseStart_8247054 baseEnd_8247054 := by
    simpa [prefixWord, tailWord_8247054, baseEnd_8247054] using wordTrace_append hprefix tailTrace_8247054
  have hstable : (prefixWord ++ tailWord_8247054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247054).length < 2 ^ (prefixWord ++ tailWord_8247054).sum := by decide
  have hdescent : baseEnd_8247054 < baseStart_8247054 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247058 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_8247058 : Nat := 118140960795 + 8247058 * 2 ^ 59
def prefixEnd_8247058 : Nat := 4983230072969 + 3 ^ 40 * 8247058 * 2
def baseEnd_8247058 : Nat := 4234704739507299581347477

theorem tailTrace_8247058 : CollatzResearch.WordTrace tailWord_8247058 prefixEnd_8247058 4234704739507299581347477 := by
  unfold tailWord_8247058
  simp only [CollatzResearch.WordTrace]
  refine ⟨75198729139081206554065457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200529944370883217477507885 75198729139081206554065457)
  ·
    refine ⟨56399046854310904915549093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75198729139081206554065457 56399046854310904915549093)
    ·
      refine ⟨10574821285183294671665455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56399046854310904915549093 10574821285183294671665455)
      ·
        refine ⟨15862231927774942007498183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10574821285183294671665455 15862231927774942007498183)
        ·
          refine ⟨23793347891662413011247275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15862231927774942007498183 23793347891662413011247275)
          ·
            refine ⟨35690021837493619516870913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23793347891662413011247275 35690021837493619516870913)
            ·
              refine ⟨26767516378120214637653185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35690021837493619516870913 26767516378120214637653185)
              ·
                refine ⟨20075637283590160978239889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26767516378120214637653185 20075637283590160978239889)
                ·
                  refine ⟨15056727962692620733679917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20075637283590160978239889 15056727962692620733679917)
                  ·
                    refine ⟨5646272986009732775129969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15056727962692620733679917 5646272986009732775129969)
                    ·
                      refine ⟨4234704739507299581347477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646272986009732775129969 4234704739507299581347477)
                      ·
                        rfl

theorem cell23_8247058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_8247058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247058 prefixEnd_8247058 := by exact prefixLift 8247058
  have htrace : WordTrace (prefixWord ++ tailWord_8247058) baseStart_8247058 baseEnd_8247058 := by
    simpa [prefixWord, tailWord_8247058, baseEnd_8247058] using wordTrace_append hprefix tailTrace_8247058
  have hstable : (prefixWord ++ tailWord_8247058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247058).length < 2 ^ (prefixWord ++ tailWord_8247058).sum := by decide
  have hdescent : baseEnd_8247058 < baseStart_8247058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247064 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 2, 4]
def baseStart_8247064 : Nat := 118140960795 + 8247064 * 2 ^ 59
def prefixEnd_8247064 : Nat := 4983230072969 + 3 ^ 40 * 8247064 * 2
def baseEnd_8247064 : Nat := 1411569273463742185957483

theorem tailTrace_8247064 : CollatzResearch.WordTrace tailWord_8247064 prefixEnd_8247064 1411569273463742185957483 := by
  unfold tailWord_8247064
  simp only [CollatzResearch.WordTrace]
  refine ⟨150397567697151544620490123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200530090262868726160653497 150397567697151544620490123)
  ·
    refine ⟨225596351545727316930735185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150397567697151544620490123 225596351545727316930735185)
    ·
      refine ⟨169197263659295487698051389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225596351545727316930735185 169197263659295487698051389)
      ·
        refine ⟨63448973872235807886769271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169197263659295487698051389 63448973872235807886769271)
        ·
          refine ⟨95173460808353711830153907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63448973872235807886769271 95173460808353711830153907)
          ·
            refine ⟨142760191212530567745230861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95173460808353711830153907 142760191212530567745230861)
            ·
              refine ⟨53535071704698962904461573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142760191212530567745230861 53535071704698962904461573)
              ·
                refine ⟨10037825944631055544586545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53535071704698962904461573 10037825944631055544586545)
                ·
                  refine ⟨7528369458473291658439909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10037825944631055544586545 7528369458473291658439909)
                  ·
                    refine ⟨1411569273463742185957483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7528369458473291658439909 1411569273463742185957483)
                    ·
                      rfl

theorem cell23_8247064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_8247064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247064 prefixEnd_8247064 := by exact prefixLift 8247064
  have htrace : WordTrace (prefixWord ++ tailWord_8247064) baseStart_8247064 baseEnd_8247064 := by
    simpa [prefixWord, tailWord_8247064, baseEnd_8247064] using wordTrace_append hprefix tailTrace_8247064
  have hstable : (prefixWord ++ tailWord_8247064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247064).length < 2 ^ (prefixWord ++ tailWord_8247064).sum := by decide
  have hdescent : baseEnd_8247064 < baseStart_8247064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247071 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 3, 2, 2]
def baseStart_8247071 : Nat := 118140960795 + 8247071 * 2 ^ 59
def prefixEnd_8247071 : Nat := 4983230072969 + 3 ^ 40 * 8247071 * 2
def baseEnd_8247071 : Nat := 4234711414755808030484917

theorem tailTrace_8247071 : CollatzResearch.WordTrace tailWord_8247071 prefixEnd_8247071 4234711414755808030484917 := by
  unfold tailWord_8247071
  simp only [CollatzResearch.WordTrace]
  refine ⟨300795390705277729436485067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200530260470185152957656711 300795390705277729436485067)
  ·
    refine ⟨451193086057916594154727601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300795390705277729436485067 451193086057916594154727601)
    ·
      refine ⟨338394814543437445616045701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451193086057916594154727601 338394814543437445616045701)
      ·
        refine ⟨63449027726894521053008569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338394814543437445616045701 63449027726894521053008569)
        ·
          refine ⟨47586770795170890789756427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63449027726894521053008569 47586770795170890789756427)
          ·
            refine ⟨71380156192756336184634641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47586770795170890789756427 71380156192756336184634641)
            ·
              refine ⟨53535117144567252138475981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71380156192756336184634641 53535117144567252138475981)
              ·
                refine ⟨20075668929212719551928493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53535117144567252138475981 20075668929212719551928493)
                ·
                  refine ⟨7528375848454769831973185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20075668929212719551928493 7528375848454769831973185)
                  ·
                    refine ⟨5646281886341077373979889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7528375848454769831973185 5646281886341077373979889)
                    ·
                      refine ⟨4234711414755808030484917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646281886341077373979889 4234711414755808030484917)
                      ·
                        rfl

theorem cell23_8247071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_8247071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247071 prefixEnd_8247071 := by exact prefixLift 8247071
  have htrace : WordTrace (prefixWord ++ tailWord_8247071) baseStart_8247071 baseEnd_8247071 := by
    simpa [prefixWord, tailWord_8247071, baseEnd_8247071] using wordTrace_append hprefix tailTrace_8247071
  have hstable : (prefixWord ++ tailWord_8247071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247071).length < 2 ^ (prefixWord ++ tailWord_8247071).sum := by decide
  have hdescent : baseEnd_8247071 < baseStart_8247071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247074 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_8247074 : Nat := 118140960795 + 8247074 * 2 ^ 59
def prefixEnd_8247074 : Nat := 4983230072969 + 3 ^ 40 * 8247074 * 2
def baseEnd_8247074 : Nat := 4234712955197771518747403

theorem tailTrace_8247074 : CollatzResearch.WordTrace tailWord_8247074 prefixEnd_8247074 4234712955197771518747403 := by
  unfold tailWord_8247074
  simp only [CollatzResearch.WordTrace]
  refine ⟨75198875031066715237211069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200530333416177907299229517 75198875031066715237211069)
  ·
    refine ⟨28199578136650018213954151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75198875031066715237211069 28199578136650018213954151)
    ·
      refine ⟨42299367204975027320931227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28199578136650018213954151 42299367204975027320931227)
      ·
        refine ⟨63449050807462540981396841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42299367204975027320931227 63449050807462540981396841)
        ·
          refine ⟨47586788105596905736047631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63449050807462540981396841 47586788105596905736047631)
          ·
            refine ⟨71380182158395358604071447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47586788105596905736047631 71380182158395358604071447)
            ·
              refine ⟨107070273237593037906107171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71380182158395358604071447 107070273237593037906107171)
              ·
                refine ⟨160605409856389556859160757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107070273237593037906107171 160605409856389556859160757)
                ·
                  refine ⟨15056757174036520955546321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160605409856389556859160757 15056757174036520955546321)
                  ·
                    refine ⟨11292567880527390716659741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15056757174036520955546321 11292567880527390716659741)
                    ·
                      refine ⟨4234712955197771518747403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11292567880527390716659741 4234712955197771518747403)
                      ·
                        rfl

theorem cell23_8247074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_8247074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247074 prefixEnd_8247074 := by exact prefixLift 8247074
  have htrace : WordTrace (prefixWord ++ tailWord_8247074) baseStart_8247074 baseEnd_8247074 := by
    simpa [prefixWord, tailWord_8247074, baseEnd_8247074] using wordTrace_append hprefix tailTrace_8247074
  have hstable : (prefixWord ++ tailWord_8247074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247074).length < 2 ^ (prefixWord ++ tailWord_8247074).sum := by decide
  have hdescent : baseEnd_8247074 < baseStart_8247074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247077 : List Nat := [1, 3, 1, 2, 3, 2, 3, 8]
def baseStart_8247077 : Nat := 118140960795 + 8247077 * 2 ^ 59
def prefixEnd_8247077 : Nat := 4983230072969 + 3 ^ 40 * 8247077 * 2
def baseEnd_8247077 : Nat := 156841277616286481741107

theorem tailTrace_8247077 : CollatzResearch.WordTrace tailWord_8247077 prefixEnd_8247077 156841277616286481741107 := by
  unfold tailWord_8247077
  simp only [CollatzResearch.WordTrace]
  refine ⟨300795609543255992461203485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200530406362170661640802323 300795609543255992461203485)
  ·
    refine ⟨112798353578720997172951307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300795609543255992461203485 112798353578720997172951307)
    ·
      refine ⟨169197530368081495759426961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112798353578720997172951307 169197530368081495759426961)
      ·
        refine ⟨126898147776061121819570221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169197530368081495759426961 126898147776061121819570221)
        ·
          refine ⟨47586805416022920682338833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126898147776061121819570221 47586805416022920682338833)
          ·
            refine ⟨35690104062017190511754125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47586805416022920682338833 35690104062017190511754125)
            ·
              refine ⟨13383789023256446441907797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35690104062017190511754125 13383789023256446441907797)
              ·
                refine ⟨156841277616286481741107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13383789023256446441907797 156841277616286481741107)
                ·
                  rfl

theorem cell23_8247077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 8].length) (baseStart_8247077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247077 prefixEnd_8247077 := by exact prefixLift 8247077
  have htrace : WordTrace (prefixWord ++ tailWord_8247077) baseStart_8247077 baseEnd_8247077 := by
    simpa [prefixWord, tailWord_8247077, baseEnd_8247077] using wordTrace_append hprefix tailTrace_8247077
  have hstable : (prefixWord ++ tailWord_8247077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247077).length < 2 ^ (prefixWord ++ tailWord_8247077).sum := by decide
  have hdescent : baseEnd_8247077 < baseStart_8247077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247084 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_8247084 : Nat := 118140960795 + 8247084 * 2 ^ 59
def prefixEnd_8247084 : Nat := 4983230072969 + 3 ^ 40 * 8247084 * 2
def baseEnd_8247084 : Nat := 4234718090004316479622357

theorem tailTrace_8247084 : CollatzResearch.WordTrace tailWord_8247084 prefixEnd_8247084 4234718090004316479622357 := by
  unfold tailWord_8247084
  simp only [CollatzResearch.WordTrace]
  refine ⟨150397932427115316328354153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200530576569487088437805537 150397932427115316328354153)
  ·
    refine ⟨112798449320336487246265615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150397932427115316328354153 112798449320336487246265615)
    ·
      refine ⟨169197673980504730869398423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112798449320336487246265615 169197673980504730869398423)
      ·
        refine ⟨253796510970757096304097635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169197673980504730869398423 253796510970757096304097635)
        ·
          refine ⟨380694766456135644456146453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253796510970757096304097635 380694766456135644456146453)
          ·
            refine ⟨17845067177631358333881865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 380694766456135644456146453 17845067177631358333881865)
            ·
              refine ⟨13383800383223518750411399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17845067177631358333881865 13383800383223518750411399)
              ·
                refine ⟨20075700574835278125617099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13383800383223518750411399 20075700574835278125617099)
                ·
                  refine ⟨30113550862252917188425649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20075700574835278125617099 30113550862252917188425649)
                  ·
                    refine ⟨22585163146689687891319237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30113550862252917188425649 22585163146689687891319237)
                    ·
                      refine ⟨4234718090004316479622357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22585163146689687891319237 4234718090004316479622357)
                      ·
                        rfl

theorem cell23_8247084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_8247084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247084 prefixEnd_8247084 := by exact prefixLift 8247084
  have htrace : WordTrace (prefixWord ++ tailWord_8247084) baseStart_8247084 baseEnd_8247084 := by
    simpa [prefixWord, tailWord_8247084, baseEnd_8247084] using wordTrace_append hprefix tailTrace_8247084
  have hstable : (prefixWord ++ tailWord_8247084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247084).length < 2 ^ (prefixWord ++ tailWord_8247084).sum := by decide
  have hdescent : baseEnd_8247084 < baseStart_8247084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247087 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 3]
def baseStart_8247087 : Nat := 118140960795 + 8247087 * 2 ^ 59
def prefixEnd_8247087 : Nat := 4983230072969 + 3 ^ 40 * 8247087 * 2
def baseEnd_8247087 : Nat := 4234719630446279967884843

theorem tailTrace_8247087 : CollatzResearch.WordTrace tailWord_8247087 prefixEnd_8247087 4234719630446279967884843 := by
  unfold tailWord_8247087
  simp only [CollatzResearch.WordTrace]
  refine ⟨300795974273219764169067515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200530649515479842779378343 300795974273219764169067515)
  ·
    refine ⟨451193961409829646253601273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300795974273219764169067515 451193961409829646253601273)
    ·
      refine ⟨338395471057372234690200955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451193961409829646253601273 338395471057372234690200955)
      ·
        refine ⟨507593206586058352035301433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338395471057372234690200955 507593206586058352035301433)
        ·
          refine ⟨380694904939543764026476075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507593206586058352035301433 380694904939543764026476075)
          ·
            refine ⟨571042357409315646039714113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380694904939543764026476075 571042357409315646039714113)
            ·
              refine ⟨428281768056986734529785585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571042357409315646039714113 428281768056986734529785585)
              ·
                refine ⟨321211326042740050897339189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428281768056986734529785585 321211326042740050897339189)
                ·
                  refine ⟨30113561816506879771625549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321211326042740050897339189 30113561816506879771625549)
                  ·
                    refine ⟨11292585681190079914359581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30113561816506879771625549 11292585681190079914359581)
                    ·
                      refine ⟨4234719630446279967884843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11292585681190079914359581 4234719630446279967884843)
                      ·
                        rfl

theorem cell23_8247087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_8247087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247087 prefixEnd_8247087 := by exact prefixLift 8247087
  have htrace : WordTrace (prefixWord ++ tailWord_8247087) baseStart_8247087 baseEnd_8247087 := by
    simpa [prefixWord, tailWord_8247087, baseEnd_8247087] using wordTrace_append hprefix tailTrace_8247087
  have hstable : (prefixWord ++ tailWord_8247087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247087).length < 2 ^ (prefixWord ++ tailWord_8247087).sum := by decide
  have hdescent : baseEnd_8247087 < baseStart_8247087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247121 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 3]
def baseStart_8247121 : Nat := 118140960795 + 8247121 * 2 ^ 59
def prefixEnd_8247121 : Nat := 4983230072969 + 3 ^ 40 * 8247121 * 2
def baseEnd_8247121 : Nat := 4234737088788532834859687

theorem tailTrace_8247121 : CollatzResearch.WordTrace tailWord_8247121 prefixEnd_8247121 4234737088788532834859687 := by
  unfold tailWord_8247121
  simp only [CollatzResearch.WordTrace]
  refine ⟨300797214355096587975805217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200531476236731058650536811 300797214355096587975805217)
  ·
    refine ⟨225597910766322440981853913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300797214355096587975805217 225597910766322440981853913)
    ·
      refine ⟨169198433074741830736390435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225597910766322440981853913 169198433074741830736390435)
      ·
        refine ⟨253797649612112746104585653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169198433074741830736390435 253797649612112746104585653)
        ·
          refine ⟨23793529651135569947304905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253797649612112746104585653 23793529651135569947304905)
          ·
            refine ⟨17845147238351677460478679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23793529651135569947304905 17845147238351677460478679)
            ·
              refine ⟨26767720857527516190718019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17845147238351677460478679 26767720857527516190718019)
              ·
                refine ⟨40151581286291274286077029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26767720857527516190718019 40151581286291274286077029)
                ·
                  refine ⟨7528421491179613928639443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40151581286291274286077029 7528421491179613928639443)
                  ·
                    refine ⟨11292632236769420892959165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7528421491179613928639443 11292632236769420892959165)
                    ·
                      refine ⟨4234737088788532834859687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11292632236769420892959165 4234737088788532834859687)
                      ·
                        rfl

theorem cell23_8247121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_8247121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247121 prefixEnd_8247121 := by exact prefixLift 8247121
  have htrace : WordTrace (prefixWord ++ tailWord_8247121) baseStart_8247121 baseEnd_8247121 := by
    simpa [prefixWord, tailWord_8247121, baseEnd_8247121] using wordTrace_append hprefix tailTrace_8247121
  have hstable : (prefixWord ++ tailWord_8247121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247121).length < 2 ^ (prefixWord ++ tailWord_8247121).sum := by decide
  have hdescent : baseEnd_8247121 < baseStart_8247121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247137 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 2, 6]
def baseStart_8247137 : Nat := 118140960795 + 8247137 * 2 ^ 59
def prefixEnd_8247137 : Nat := 4983230072969 + 3 ^ 40 * 8247137 * 2
def baseEnd_8247137 : Nat := 1411581768159668257419871

theorem tailTrace_8247137 : CollatzResearch.WordTrace tailWord_8247137 prefixEnd_8247137 1411581768159668257419871 := by
  unfold tailWord_8247137
  simp only [CollatzResearch.WordTrace]
  refine ⟨300797797923038622708387665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200531865282025748472258443 300797797923038622708387665)
  ·
    refine ⟨225598348442278967031290749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300797797923038622708387665 225598348442278967031290749)
    ·
      refine ⟨84599380665854612636734031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225598348442278967031290749 84599380665854612636734031)
      ·
        refine ⟨126899070998781918955101047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84599380665854612636734031 126899070998781918955101047)
        ·
          refine ⟨190348606498172878432651571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126899070998781918955101047 190348606498172878432651571)
          ·
            refine ⟨285522909747259317648977357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190348606498172878432651571 285522909747259317648977357)
            ·
              refine ⟨107071091155222244118366509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285522909747259317648977357 107071091155222244118366509)
              ·
                refine ⟨40151659183208341544387441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107071091155222244118366509 40151659183208341544387441)
                ·
                  refine ⟨30113744387406256158290581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40151659183208341544387441 30113744387406256158290581)
                  ·
                    refine ⟨1411581768159668257419871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30113744387406256158290581 1411581768159668257419871)
                    ·
                      rfl

theorem cell23_8247137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_8247137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247137 prefixEnd_8247137 := by exact prefixLift 8247137
  have htrace : WordTrace (prefixWord ++ tailWord_8247137) baseStart_8247137 baseEnd_8247137 := by
    simpa [prefixWord, tailWord_8247137, baseEnd_8247137] using wordTrace_append hprefix tailTrace_8247137
  have hstable : (prefixWord ++ tailWord_8247137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247137).length < 2 ^ (prefixWord ++ tailWord_8247137).sum := by decide
  have hdescent : baseEnd_8247137 < baseStart_8247137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247138 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_8247138 : Nat := 118140960795 + 8247138 * 2 ^ 59
def prefixEnd_8247138 : Nat := 4983230072969 + 3 ^ 40 * 8247138 * 2
def baseEnd_8247138 : Nat := 4234745817959659268347109

theorem tailTrace_8247138 : CollatzResearch.WordTrace tailWord_8247138 prefixEnd_8247138 4234745817959659268347109 := by
  unfold tailWord_8247138
  simp only [CollatzResearch.WordTrace]
  refine ⟨75199458599008749969793517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200531889597356666586116045 75199458599008749969793517)
  ·
    refine ⟨28199796974628281238672569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75199458599008749969793517 28199796974628281238672569)
    ·
      refine ⟨21149847730971210929004427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28199796974628281238672569 21149847730971210929004427)
      ·
        refine ⟨31724771596456816393506641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21149847730971210929004427 31724771596456816393506641)
        ·
          refine ⟨23793578697342612295129981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31724771596456816393506641 23793578697342612295129981)
          ·
            refine ⟨8922592011503479610673743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23793578697342612295129981 8922592011503479610673743)
            ·
              refine ⟨13383888017255219416010615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922592011503479610673743 13383888017255219416010615)
              ·
                refine ⟨20075832025882829124015923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13383888017255219416010615 20075832025882829124015923)
                ·
                  refine ⟨30113748038824243686023885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20075832025882829124015923 30113748038824243686023885)
                  ·
                    refine ⟨11292655514559091382258957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30113748038824243686023885 11292655514559091382258957)
                    ·
                      refine ⟨4234745817959659268347109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11292655514559091382258957 4234745817959659268347109)
                      ·
                        rfl

theorem cell23_8247138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_8247138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247138 prefixEnd_8247138 := by exact prefixLift 8247138
  have htrace : WordTrace (prefixWord ++ tailWord_8247138) baseStart_8247138 baseEnd_8247138 := by
    simpa [prefixWord, tailWord_8247138, baseEnd_8247138] using wordTrace_append hprefix tailTrace_8247138
  have hstable : (prefixWord ++ tailWord_8247138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247138).length < 2 ^ (prefixWord ++ tailWord_8247138).sum := by decide
  have hdescent : baseEnd_8247138 < baseStart_8247138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247147 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 5]
def baseStart_8247147 : Nat := 118140960795 + 8247147 * 2 ^ 59
def prefixEnd_8247147 : Nat := 4983230072969 + 3 ^ 40 * 8247147 * 2
def baseEnd_8247147 : Nat := 4234750439285549733134567

theorem tailTrace_8247147 : CollatzResearch.WordTrace tailWord_8247147 prefixEnd_8247147 4234750439285549733134567 := by
  unfold tailWord_8247147
  simp only [CollatzResearch.WordTrace]
  refine ⟨300798162653002394416251695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200532108435334929610834463 300798162653002394416251695)
  ·
    refine ⟨451197243979503591624377543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300798162653002394416251695 451197243979503591624377543)
    ·
      refine ⟨676795865969255387436566315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451197243979503591624377543 676795865969255387436566315)
      ·
        refine ⟨1015193798953883081154849473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676795865969255387436566315 1015193798953883081154849473)
        ·
          refine ⟨761395349215412310866137105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015193798953883081154849473 761395349215412310866137105)
          ·
            refine ⟨571046511911559233149602829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761395349215412310866137105 571046511911559233149602829)
            ·
              refine ⟨214142441966834712431101061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571046511911559233149602829 214142441966834712431101061)
              ·
                refine ⟨40151707868781508580831449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214142441966834712431101061 40151707868781508580831449)
                ·
                  refine ⟨30113780901586131435623587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40151707868781508580831449 30113780901586131435623587)
                  ·
                    refine ⟨45170671352379197153435381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30113780901586131435623587 45170671352379197153435381)
                    ·
                      refine ⟨4234750439285549733134567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45170671352379197153435381 4234750439285549733134567)
                      ·
                        rfl

theorem cell23_8247147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 5].length) (baseStart_8247147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247147 prefixEnd_8247147 := by exact prefixLift 8247147
  have htrace : WordTrace (prefixWord ++ tailWord_8247147) baseStart_8247147 baseEnd_8247147 := by
    simpa [prefixWord, tailWord_8247147, baseEnd_8247147] using wordTrace_append hprefix tailTrace_8247147
  have hstable : (prefixWord ++ tailWord_8247147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247147).length < 2 ^ (prefixWord ++ tailWord_8247147).sum := by decide
  have hdescent : baseEnd_8247147 < baseStart_8247147 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247148 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 1, 3, 2]
def baseStart_8247148 : Nat := 118140960795 + 8247148 * 2 ^ 59
def prefixEnd_8247148 : Nat := 4983230072969 + 3 ^ 40 * 8247148 * 2
def baseEnd_8247148 : Nat := 4234750952766204229222063

theorem tailTrace_8247148 : CollatzResearch.WordTrace tailWord_8247148 prefixEnd_8247148 4234750952766204229222063 := by
  unfold tailWord_8247148
  simp only [CollatzResearch.WordTrace]
  refine ⟨150399099562999385793519049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200532132750665847724692065 150399099562999385793519049)
  ·
    refine ⟨112799324672249539345139287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150399099562999385793519049 112799324672249539345139287)
    ·
      refine ⟨169198987008374309017708931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112799324672249539345139287 169198987008374309017708931)
      ·
        refine ⟨253798480512561463526563397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169198987008374309017708931 253798480512561463526563397)
        ·
          refine ⟨47587215096105274411230637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253798480512561463526563397 47587215096105274411230637)
          ·
            refine ⟨17845205661039477904211489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47587215096105274411230637 17845205661039477904211489)
            ·
              refine ⟨13383904245779608428158617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17845205661039477904211489 13383904245779608428158617)
              ·
                refine ⟨10037928184334706321118963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13383904245779608428158617 10037928184334706321118963)
                ·
                  refine ⟨15056892276502059481678445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10037928184334706321118963 15056892276502059481678445)
                  ·
                    refine ⟨5646334603688272305629417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15056892276502059481678445 5646334603688272305629417)
                    ·
                      refine ⟨4234750952766204229222063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646334603688272305629417 4234750952766204229222063)
                      ·
                        rfl

theorem cell23_8247148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_8247148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247148 prefixEnd_8247148 := by exact prefixLift 8247148
  have htrace : WordTrace (prefixWord ++ tailWord_8247148) baseStart_8247148 baseEnd_8247148 := by
    simpa [prefixWord, tailWord_8247148, baseEnd_8247148] using wordTrace_append hprefix tailTrace_8247148
  have hstable : (prefixWord ++ tailWord_8247148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247148).length < 2 ^ (prefixWord ++ tailWord_8247148).sum := by decide
  have hdescent : baseEnd_8247148 < baseStart_8247148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247161 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 6, 2, 2]
def baseStart_8247161 : Nat := 118140960795 + 8247161 * 2 ^ 59
def prefixEnd_8247161 : Nat := 4983230072969 + 3 ^ 40 * 8247161 * 2
def baseEnd_8247161 : Nat := 4234757628014712678359503

theorem tailTrace_8247161 : CollatzResearch.WordTrace tailWord_8247161 prefixEnd_8247161 4234757628014712678359503 := by
  unfold tailWord_8247161
  simp only [CollatzResearch.WordTrace]
  refine ⟨300798673274951674807261337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200532448849967783204840891 300798673274951674807261337)
  ·
    refine ⟨225599004956213756105446003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300798673274951674807261337 225599004956213756105446003)
    ·
      refine ⟨338398507434320634158169005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225599004956213756105446003 338398507434320634158169005)
      ·
        refine ⟨126899440287870237809313377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338398507434320634158169005 126899440287870237809313377)
        ·
          refine ⟨95174580215902678356985033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126899440287870237809313377 95174580215902678356985033)
          ·
            refine ⟨71380935161927008767738775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95174580215902678356985033 71380935161927008767738775)
            ·
              refine ⟨107071402742890513151608163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71380935161927008767738775 107071402742890513151608163)
              ·
                refine ⟨160607104114335769727412245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107071402742890513151608163 160607104114335769727412245)
                ·
                  refine ⟨7528458005359489205972449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160607104114335769727412245 7528458005359489205972449)
                  ·
                    refine ⟨5646343504019616904479337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7528458005359489205972449 5646343504019616904479337)
                    ·
                      refine ⟨4234757628014712678359503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646343504019616904479337 4234757628014712678359503)
                      ·
                        rfl

theorem cell23_8247161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_8247161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247161 prefixEnd_8247161 := by exact prefixLift 8247161
  have htrace : WordTrace (prefixWord ++ tailWord_8247161) baseStart_8247161 baseEnd_8247161 := by
    simpa [prefixWord, tailWord_8247161, baseEnd_8247161] using wordTrace_append hprefix tailTrace_8247161
  have hstable : (prefixWord ++ tailWord_8247161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247161).length < 2 ^ (prefixWord ++ tailWord_8247161).sum := by decide
  have hdescent : baseEnd_8247161 < baseStart_8247161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247177 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_8247177 : Nat := 118140960795 + 8247177 * 2 ^ 59
def prefixEnd_8247177 : Nat := 4983230072969 + 3 ^ 40 * 8247177 * 2
def baseEnd_8247177 : Nat := 4234765843705184615759429

theorem tailTrace_8247177 : CollatzResearch.WordTrace tailWord_8247177 prefixEnd_8247177 4234765843705184615759429 := by
  unfold tailWord_8247177
  simp only [CollatzResearch.WordTrace]
  refine ⟨300799256842893709539843785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200532837895262473026562523 300799256842893709539843785)
  ·
    refine ⟨225599442632170282154882839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300799256842893709539843785 225599442632170282154882839)
    ·
      refine ⟨338399163948255423232324259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225599442632170282154882839 338399163948255423232324259)
      ·
        refine ⟨507598745922383134848486389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338399163948255423232324259 507598745922383134848486389)
        ·
          refine ⟨47587382430223418892045599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 507598745922383134848486389 47587382430223418892045599)
          ·
            refine ⟨71381073645335128338068399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47587382430223418892045599 71381073645335128338068399)
            ·
              refine ⟨107071610468002692507102599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71381073645335128338068399 107071610468002692507102599)
              ·
                refine ⟨160607415702004038760653899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107071610468002692507102599 160607415702004038760653899)
                ·
                  refine ⟨240911123553006058140980849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160607415702004038760653899 240911123553006058140980849)
                  ·
                    refine ⟨180683342664754543605735637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240911123553006058140980849 180683342664754543605735637)
                    ·
                      refine ⟨4234765843705184615759429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180683342664754543605735637 4234765843705184615759429)
                      ·
                        rfl

theorem cell23_8247177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_8247177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247177 prefixEnd_8247177 := by exact prefixLift 8247177
  have htrace : WordTrace (prefixWord ++ tailWord_8247177) baseStart_8247177 baseEnd_8247177 := by
    simpa [prefixWord, tailWord_8247177, baseEnd_8247177] using wordTrace_append hprefix tailTrace_8247177
  have hstable : (prefixWord ++ tailWord_8247177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247177).length < 2 ^ (prefixWord ++ tailWord_8247177).sum := by decide
  have hdescent : baseEnd_8247177 < baseStart_8247177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247274 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 8]
def baseStart_8247274 : Nat := 118140960795 + 8247274 * 2 ^ 59
def prefixEnd_8247274 : Nat := 4983230072969 + 3 ^ 40 * 8247274 * 2
def baseEnd_8247274 : Nat := 470535072369852304027387

theorem tailTrace_8247274 : CollatzResearch.WordTrace tailWord_8247274 prefixEnd_8247274 470535072369852304027387 := by
  unfold tailWord_8247274
  simp only [CollatzResearch.WordTrace]
  refine ⟨75200698680885573776531219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200535196482361530070749917 75200698680885573776531219)
  ·
    refine ⟨112801048021328360664796829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75200698680885573776531219 112801048021328360664796829)
    ·
      refine ⟨42300393007998135249298811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112801048021328360664796829 42300393007998135249298811)
      ·
        refine ⟨63450589511997202873948217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42300393007998135249298811 63450589511997202873948217)
        ·
          refine ⟨47587942133997902155461163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63450589511997202873948217 47587942133997902155461163)
          ·
            refine ⟨71381913200996853233191745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47587942133997902155461163 71381913200996853233191745)
            ·
              refine ⟨53536434900747639924893809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71381913200996853233191745 53536434900747639924893809)
              ·
                refine ⟨40152326175560729943670357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53536434900747639924893809 40152326175560729943670357)
                ·
                  refine ⟨470535072369852304027387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40152326175560729943670357 470535072369852304027387)
                  ·
                    rfl

theorem cell23_8247274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_8247274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247274 prefixEnd_8247274 := by exact prefixLift 8247274
  have htrace : WordTrace (prefixWord ++ tailWord_8247274) baseStart_8247274 baseEnd_8247274 := by
    simpa [prefixWord, tailWord_8247274, baseEnd_8247274] using wordTrace_append hprefix tailTrace_8247274
  have hstable : (prefixWord ++ tailWord_8247274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247274).length < 2 ^ (prefixWord ++ tailWord_8247274).sum := by decide
  have hdescent : baseEnd_8247274 < baseStart_8247274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247338 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_8247338 : Nat := 118140960795 + 8247338 * 2 ^ 59
def prefixEnd_8247338 : Nat := 4983230072969 + 3 ^ 40 * 8247338 * 2
def baseEnd_8247338 : Nat := 1411616171363519495282063

theorem tailTrace_8247338 : CollatzResearch.WordTrace tailWord_8247338 prefixEnd_8247338 1411616171363519495282063 := by
  unfold tailWord_8247338
  simp only [CollatzResearch.WordTrace]
  refine ⟨75201282248827608509113667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200536752663540289357636445 75201282248827608509113667)
  ·
    refine ⟨112801923373241412763670501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75201282248827608509113667 112801923373241412763670501)
    ·
      refine ⟨21150360632482764893188219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112801923373241412763670501 21150360632482764893188219)
      ·
        refine ⟨31725540948724147339782329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21150360632482764893188219 31725540948724147339782329)
        ·
          refine ⟨23794155711543110504836747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31725540948724147339782329 23794155711543110504836747)
          ·
            refine ⟨35691233567314665757255121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23794155711543110504836747 35691233567314665757255121)
            ·
              refine ⟨26768425175485999317941341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35691233567314665757255121 26768425175485999317941341)
              ·
                refine ⟨10038159440807249744228003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26768425175485999317941341 10038159440807249744228003)
                ·
                  refine ⟨15057239161210874616342005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10038159440807249744228003 15057239161210874616342005)
                  ·
                    refine ⟨1411616171363519495282063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15057239161210874616342005 1411616171363519495282063)
                    ·
                      rfl

theorem cell23_8247338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_8247338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247338 prefixEnd_8247338 := by exact prefixLift 8247338
  have htrace : WordTrace (prefixWord ++ tailWord_8247338) baseStart_8247338 baseEnd_8247338 := by
    simpa [prefixWord, tailWord_8247338, baseEnd_8247338] using wordTrace_append hprefix tailTrace_8247338
  have hstable : (prefixWord ++ tailWord_8247338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247338).length < 2 ^ (prefixWord ++ tailWord_8247338).sum := by decide
  have hdescent : baseEnd_8247338 < baseStart_8247338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247351 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 4, 4]
def baseStart_8247351 : Nat := 118140960795 + 8247351 * 2 ^ 59
def prefixEnd_8247351 : Nat := 4983230072969 + 3 ^ 40 * 8247351 * 2
def baseEnd_8247351 : Nat := 1411618396446355644994543

theorem tailTrace_8247351 : CollatzResearch.WordTrace tailWord_8247351 prefixEnd_8247351 1411618396446355644994543 := by
  unfold tailWord_8247351
  simp only [CollatzResearch.WordTrace]
  refine ⟨300805603144263337256677907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200537068762842224837785271 300805603144263337256677907)
  ·
    refine ⟨451208404716395005885016861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300805603144263337256677907 451208404716395005885016861)
    ·
      refine ⟨169203151768648127206881323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451208404716395005885016861 169203151768648127206881323)
      ·
        refine ⟨253804727652972190810321985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169203151768648127206881323 253804727652972190810321985)
        ·
          refine ⟨190353545739729143107741489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253804727652972190810321985 190353545739729143107741489)
          ·
            refine ⟨142765159304796857330806117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190353545739729143107741489 142765159304796857330806117)
            ·
              refine ⟨26768467369649410749526147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142765159304796857330806117 26768467369649410749526147)
              ·
                refine ⟨40152701054474116124289221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26768467369649410749526147 40152701054474116124289221)
                ·
                  refine ⟨7528631447713896773304229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40152701054474116124289221 7528631447713896773304229)
                  ·
                    refine ⟨1411618396446355644994543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7528631447713896773304229 1411618396446355644994543)
                    ·
                      rfl

theorem cell23_8247351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_8247351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247351 prefixEnd_8247351 := by exact prefixLift 8247351
  have htrace : WordTrace (prefixWord ++ tailWord_8247351) baseStart_8247351 baseEnd_8247351 := by
    simpa [prefixWord, tailWord_8247351, baseEnd_8247351] using wordTrace_append hprefix tailTrace_8247351
  have hstable : (prefixWord ++ tailWord_8247351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247351).length < 2 ^ (prefixWord ++ tailWord_8247351).sum := by decide
  have hdescent : baseEnd_8247351 < baseStart_8247351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247352 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 3, 1, 3]
def baseStart_8247352 : Nat := 118140960795 + 8247352 * 2 ^ 59
def prefixEnd_8247352 : Nat := 4983230072969 + 3 ^ 40 * 8247352 * 2
def baseEnd_8247352 : Nat := 4234855702819721431071125

theorem tailTrace_8247352 : CollatzResearch.WordTrace tailWord_8247352 prefixEnd_8247352 4234855702819721431071125 := by
  unfold tailWord_8247352
  simp only [CollatzResearch.WordTrace]
  refine ⟨150402819808629857213732155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200537093078173142951642873 150402819808629857213732155)
  ·
    refine ⟨225604229712944785820598233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150402819808629857213732155 225604229712944785820598233)
    ·
      refine ⟨169203172284708589365448675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225604229712944785820598233 169203172284708589365448675)
      ·
        refine ⟨253804758427062884048173013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169203172284708589365448675 253804758427062884048173013)
        ·
          refine ⟨5948549025634286344879055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 253804758427062884048173013 5948549025634286344879055)
          ·
            refine ⟨8922823538451429517318583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948549025634286344879055 8922823538451429517318583)
            ·
              refine ⟨13384235307677144275977875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922823538451429517318583 13384235307677144275977875)
              ·
                refine ⟨20076352961515716413966813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13384235307677144275977875 20076352961515716413966813)
                ·
                  refine ⟨7528632360568393655237555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20076352961515716413966813 7528632360568393655237555)
                  ·
                    refine ⟨11292948540852590482856333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7528632360568393655237555 11292948540852590482856333)
                    ·
                      refine ⟨4234855702819721431071125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11292948540852590482856333 4234855702819721431071125)
                      ·
                        rfl

theorem cell23_8247352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_8247352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247352 prefixEnd_8247352 := by exact prefixLift 8247352
  have htrace : WordTrace (prefixWord ++ tailWord_8247352) baseStart_8247352 baseEnd_8247352 := by
    simpa [prefixWord, tailWord_8247352, baseEnd_8247352] using wordTrace_append hprefix tailTrace_8247352
  have hstable : (prefixWord ++ tailWord_8247352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247352).length < 2 ^ (prefixWord ++ tailWord_8247352).sum := by decide
  have hdescent : baseEnd_8247352 < baseStart_8247352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247388 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_8247388 : Nat := 118140960795 + 8247388 * 2 ^ 59
def prefixEnd_8247388 : Nat := 4983230072969 + 3 ^ 40 * 8247388 * 2
def baseEnd_8247388 : Nat := 4234874188123283290220959

theorem tailTrace_8247388 : CollatzResearch.WordTrace tailWord_8247388 prefixEnd_8247388 4234874188123283290220959 := by
  unfold tailWord_8247388
  simp only [CollatzResearch.WordTrace]
  refine ⟨150403476322564646287887409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200537968430086195050516545 150403476322564646287887409)
  ·
    refine ⟨112802607241923484715915557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150403476322564646287887409 112802607241923484715915557)
    ·
      refine ⟨21150488857860653384234167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112802607241923484715915557 21150488857860653384234167)
      ·
        refine ⟨31725733286790980076351251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21150488857860653384234167 31725733286790980076351251)
        ·
          refine ⟨47588599930186470114526877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31725733286790980076351251 47588599930186470114526877)
          ·
            refine ⟨17845724973819926292947579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47588599930186470114526877 17845724973819926292947579)
            ·
              refine ⟨26768587460729889439421369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17845724973819926292947579 26768587460729889439421369)
              ·
                refine ⟨20076440595547417079566027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26768587460729889439421369 20076440595547417079566027)
                ·
                  refine ⟨30114660893321125619349041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20076440595547417079566027 30114660893321125619349041)
                  ·
                    refine ⟨22585995669990844214511781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30114660893321125619349041 22585995669990844214511781)
                    ·
                      refine ⟨4234874188123283290220959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22585995669990844214511781 4234874188123283290220959)
                      ·
                        rfl

theorem cell23_8247388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_8247388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247388 prefixEnd_8247388 := by exact prefixLift 8247388
  have htrace : WordTrace (prefixWord ++ tailWord_8247388) baseStart_8247388 baseEnd_8247388 := by
    simpa [prefixWord, tailWord_8247388, baseEnd_8247388] using wordTrace_append hprefix tailTrace_8247388
  have hstable : (prefixWord ++ tailWord_8247388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247388).length < 2 ^ (prefixWord ++ tailWord_8247388).sum := by decide
  have hdescent : baseEnd_8247388 < baseStart_8247388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247425 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_8247425 : Nat := 118140960795 + 8247425 * 2 ^ 59
def prefixEnd_8247425 : Nat := 4983230072969 + 3 ^ 40 * 8247425 * 2
def baseEnd_8247425 : Nat := 4234893186907499645458289

theorem tailTrace_8247425 : CollatzResearch.WordTrace tailWord_8247425 prefixEnd_8247425 4234893186907499645458289 := by
  unfold tailWord_8247425
  simp only [CollatzResearch.WordTrace]
  refine ⟨300808302145995247894871729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200538868097330165263247819 300808302145995247894871729)
  ·
    refine ⟨225606226609496435921153797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300808302145995247894871729 225606226609496435921153797)
    ·
      refine ⟨42301167489280581735216337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225606226609496435921153797 42301167489280581735216337)
      ·
        refine ⟨31725875616960436301412253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42301167489280581735216337 31725875616960436301412253)
        ·
          refine ⟨11897203356360163613029595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31725875616960436301412253 11897203356360163613029595)
          ·
            refine ⟨17845805034540245419544393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11897203356360163613029595 17845805034540245419544393)
            ·
              refine ⟨13384353775905184064658295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17845805034540245419544393 13384353775905184064658295)
              ·
                refine ⟨20076530663857776096987443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13384353775905184064658295 20076530663857776096987443)
                ·
                  refine ⟨30114795995786664145481165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20076530663857776096987443 30114795995786664145481165)
                  ·
                    refine ⟨11293048498419999054555437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30114795995786664145481165 11293048498419999054555437)
                    ·
                      refine ⟨4234893186907499645458289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11293048498419999054555437 4234893186907499645458289)
                      ·
                        rfl

theorem cell23_8247425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_8247425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247425 prefixEnd_8247425 := by exact prefixLift 8247425
  have htrace : WordTrace (prefixWord ++ tailWord_8247425) baseStart_8247425 baseEnd_8247425 := by
    simpa [prefixWord, tailWord_8247425, baseEnd_8247425] using wordTrace_append hprefix tailTrace_8247425
  have hstable : (prefixWord ++ tailWord_8247425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247425).length < 2 ^ (prefixWord ++ tailWord_8247425).sum := by decide
  have hdescent : baseEnd_8247425 < baseStart_8247425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247458 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_8247458 : Nat := 118140960795 + 8247458 * 2 ^ 59
def prefixEnd_8247458 : Nat := 4983230072969 + 3 ^ 40 * 8247458 * 2
def baseEnd_8247458 : Nat := 1411636710589699338781879

theorem tailTrace_8247458 : CollatzResearch.WordTrace tailWord_8247458 prefixEnd_8247458 1411636710589699338781879 := by
  unfold tailWord_8247458
  simp only [CollatzResearch.WordTrace]
  refine ⟨75202376438718923632705757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200539670503250463020548685 75202376438718923632705757)
  ·
    refine ⟨28200891164519596362264659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75202376438718923632705757 28200891164519596362264659)
    ·
      refine ⟨42301336746779394543396989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28200891164519596362264659 42301336746779394543396989)
      ·
        refine ⟨15863001280042272953773871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42301336746779394543396989 15863001280042272953773871)
        ·
          refine ⟨23794501920063409430660807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15863001280042272953773871 23794501920063409430660807)
          ·
            refine ⟨35691752880095114145991211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23794501920063409430660807 35691752880095114145991211)
            ·
              refine ⟨53537629320142671218986817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35691752880095114145991211 53537629320142671218986817)
              ·
                refine ⟨40153221990107003414240113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53537629320142671218986817 40153221990107003414240113)
                ·
                  refine ⟨30114916492580252560680085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40153221990107003414240113 30114916492580252560680085)
                  ·
                    refine ⟨1411636710589699338781879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30114916492580252560680085 1411636710589699338781879)
                    ·
                      rfl

theorem cell23_8247458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_8247458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247458 prefixEnd_8247458 := by exact prefixLift 8247458
  have htrace : WordTrace (prefixWord ++ tailWord_8247458) baseStart_8247458 baseEnd_8247458 := by
    simpa [prefixWord, tailWord_8247458, baseEnd_8247458] using wordTrace_append hprefix tailTrace_8247458
  have hstable : (prefixWord ++ tailWord_8247458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247458).length < 2 ^ (prefixWord ++ tailWord_8247458).sum := by decide
  have hdescent : baseEnd_8247458 < baseStart_8247458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247461 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_8247461 : Nat := 118140960795 + 8247461 * 2 ^ 59
def prefixEnd_8247461 : Nat := 4983230072969 + 3 ^ 40 * 8247461 * 2
def baseEnd_8247461 : Nat := 4234911672211061504608123

theorem tailTrace_8247461 : CollatzResearch.WordTrace tailWord_8247461 prefixEnd_8247461 4234911672211061504608123 := by
  unfold tailWord_8247461
  simp only [CollatzResearch.WordTrace]
  refine ⟨300809615173864826043182237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200539743449243217362121491 300809615173864826043182237)
  ·
    refine ⟨112803605690199309766193339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300809615173864826043182237 112803605690199309766193339)
    ·
      refine ⟨169205408535298964649290009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112803605690199309766193339 169205408535298964649290009)
      ·
        refine ⟨126904056401474223486967507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169205408535298964649290009 126904056401474223486967507)
        ·
          refine ⟨190356084602211335230451261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126904056401474223486967507 190356084602211335230451261)
          ·
            refine ⟨71383531725829250711419223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190356084602211335230451261 71383531725829250711419223)
            ·
              refine ⟨107075297588743876067128835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71383531725829250711419223 107075297588743876067128835)
              ·
                refine ⟨160612946383115814100693253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107075297588743876067128835 160612946383115814100693253)
                ·
                  refine ⟨30114927446834215143879985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160612946383115814100693253 30114927446834215143879985)
                  ·
                    refine ⟨22586195585125661357909989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30114927446834215143879985 22586195585125661357909989)
                    ·
                      refine ⟨4234911672211061504608123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22586195585125661357909989 4234911672211061504608123)
                      ·
                        rfl

theorem cell23_8247461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_8247461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247461 prefixEnd_8247461 := by exact prefixLift 8247461
  have htrace : WordTrace (prefixWord ++ tailWord_8247461) baseStart_8247461 baseEnd_8247461 := by
    simpa [prefixWord, tailWord_8247461, baseEnd_8247461] using wordTrace_append hprefix tailTrace_8247461
  have hstable : (prefixWord ++ tailWord_8247461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247461).length < 2 ^ (prefixWord ++ tailWord_8247461).sum := by decide
  have hdescent : baseEnd_8247461 < baseStart_8247461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247476 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_8247476 : Nat := 118140960795 + 8247476 * 2 ^ 59
def prefixEnd_8247476 : Nat := 4983230072969 + 3 ^ 40 * 8247476 * 2
def baseEnd_8247476 : Nat := 4234919374420878945920555

theorem tailTrace_8247476 : CollatzResearch.WordTrace tailWord_8247476 prefixEnd_8247476 4234919374420878945920555 := by
  unfold tailWord_8247476
  simp only [CollatzResearch.WordTrace]
  refine ⟨150405081134405241802489141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200540108179206989069985521 150405081134405241802489141)
  ·
    refine ⟨14100476356350491418983357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150405081134405241802489141 14100476356350491418983357)
    ·
      refine ⟨5287678633631434282118759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14100476356350491418983357 5287678633631434282118759)
      ·
        refine ⟨7931517950447151423178139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5287678633631434282118759 7931517950447151423178139)
        ·
          refine ⟨11897276925670727134767209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7931517950447151423178139 11897276925670727134767209)
          ·
            refine ⟨8922957694253045351075407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11897276925670727134767209 8922957694253045351075407)
            ·
              refine ⟨13384436541379568026613111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922957694253045351075407 13384436541379568026613111)
              ·
                refine ⟨20076654812069352039919667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13384436541379568026613111 20076654812069352039919667)
                ·
                  refine ⟨30114982218104028059879501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20076654812069352039919667 30114982218104028059879501)
                  ·
                    refine ⟨11293118331789010522454813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30114982218104028059879501 11293118331789010522454813)
                    ·
                      refine ⟨4234919374420878945920555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11293118331789010522454813 4234919374420878945920555)
                      ·
                        rfl

theorem cell23_8247476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_8247476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247476 prefixEnd_8247476 := by exact prefixLift 8247476
  have htrace : WordTrace (prefixWord ++ tailWord_8247476) baseStart_8247476 baseEnd_8247476 := by
    simpa [prefixWord, tailWord_8247476, baseEnd_8247476] using wordTrace_append hprefix tailTrace_8247476
  have hstable : (prefixWord ++ tailWord_8247476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247476).length < 2 ^ (prefixWord ++ tailWord_8247476).sum := by decide
  have hdescent : baseEnd_8247476 < baseStart_8247476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247511 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_8247511 : Nat := 118140960795 + 8247511 * 2 ^ 59
def prefixEnd_8247511 : Nat := 4983230072969 + 3 ^ 40 * 8247511 * 2
def baseEnd_8247511 : Nat := 4234937346243786308982893

theorem tailTrace_8247511 : CollatzResearch.WordTrace tailWord_8247511 prefixEnd_8247511 4234937346243786308982893 := by
  unfold tailWord_8247511
  simp only [CollatzResearch.WordTrace]
  refine ⟨300811438823683684582502387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200540959215789123055001591 300811438823683684582502387)
  ·
    refine ⟨451217158235525526873753581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300811438823683684582502387 451217158235525526873753581)
    ·
      refine ⟨169206434338322072577657593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451217158235525526873753581 169206434338322072577657593)
      ·
        refine ⟨126904825753741554433243195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169206434338322072577657593 126904825753741554433243195)
        ·
          refine ⟨190357238630612331649864793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126904825753741554433243195 190357238630612331649864793)
          ·
            refine ⟨142767928972959248737398595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190357238630612331649864793 142767928972959248737398595)
            ·
              refine ⟨214151893459438873106097893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142767928972959248737398595 214151893459438873106097893)
              ·
                refine ⟨40153480023644788707393355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214151893459438873106097893 40153480023644788707393355)
                ·
                  refine ⟨60230220035467183061090033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40153480023644788707393355 60230220035467183061090033)
                  ·
                    refine ⟨45172665026600387295817525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60230220035467183061090033 45172665026600387295817525)
                    ·
                      refine ⟨4234937346243786308982893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45172665026600387295817525 4234937346243786308982893)
                      ·
                        rfl

theorem cell23_8247511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_8247511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247511 prefixEnd_8247511 := by exact prefixLift 8247511
  have htrace : WordTrace (prefixWord ++ tailWord_8247511) baseStart_8247511 baseEnd_8247511 := by
    simpa [prefixWord, tailWord_8247511, baseEnd_8247511] using wordTrace_append hprefix tailTrace_8247511
  have hstable : (prefixWord ++ tailWord_8247511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247511).length < 2 ^ (prefixWord ++ tailWord_8247511).sum := by decide
  have hdescent : baseEnd_8247511 < baseStart_8247511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247528 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_8247528 : Nat := 118140960795 + 8247528 * 2 ^ 59
def prefixEnd_8247528 : Nat := 4983230072969 + 3 ^ 40 * 8247528 * 2
def baseEnd_8247528 : Nat := 4234946075414912742470315

theorem tailTrace_8247528 : CollatzResearch.WordTrace tailWord_8247528 prefixEnd_8247528 4234946075414912742470315 := by
  unfold tailWord_8247528
  simp only [CollatzResearch.WordTrace]
  refine ⟨150406029432311048242935619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200541372576414730990580825 150406029432311048242935619)
  ·
    refine ⟨225609044148466572364403429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150406029432311048242935619 225609044148466572364403429)
    ·
      refine ⟨42301695777837482318325643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225609044148466572364403429 42301695777837482318325643)
      ·
        refine ⟨63452543666756223477488465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42301695777837482318325643 63452543666756223477488465)
        ·
          refine ⟨47589407750067167608116349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63452543666756223477488465 47589407750067167608116349)
          ·
            refine ⟨17846027906275187853043631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47589407750067167608116349 17846027906275187853043631)
            ·
              refine ⟨26769041859412781779565447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17846027906275187853043631 26769041859412781779565447)
              ·
                refine ⟨40153562789119172669348171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26769041859412781779565447 40153562789119172669348171)
                ·
                  refine ⟨60230344183678759004022257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40153562789119172669348171 60230344183678759004022257)
                  ·
                    refine ⟨45172758137759069253016693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60230344183678759004022257 45172758137759069253016693)
                    ·
                      refine ⟨4234946075414912742470315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45172758137759069253016693 4234946075414912742470315)
                      ·
                        rfl

theorem cell23_8247528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_8247528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247528 prefixEnd_8247528 := by exact prefixLift 8247528
  have htrace : WordTrace (prefixWord ++ tailWord_8247528) baseStart_8247528 baseEnd_8247528 := by
    simpa [prefixWord, tailWord_8247528, baseEnd_8247528] using wordTrace_append hprefix tailTrace_8247528
  have hstable : (prefixWord ++ tailWord_8247528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247528).length < 2 ^ (prefixWord ++ tailWord_8247528).sum := by decide
  have hdescent : baseEnd_8247528 < baseStart_8247528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247533 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_8247533 : Nat := 118140960795 + 8247533 * 2 ^ 59
def prefixEnd_8247533 : Nat := 4983230072969 + 3 ^ 40 * 8247533 * 2
def baseEnd_8247533 : Nat := 4234948642818185222907793

theorem tailTrace_8247533 : CollatzResearch.WordTrace tailWord_8247533 prefixEnd_8247533 4234948642818185222907793 := by
  unfold tailWord_8247533
  simp only [CollatzResearch.WordTrace]
  refine ⟨300812241229603982339803253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200541494153069321559868835 300812241229603982339803253)
  ·
    refine ⟨28201147615275373344356555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300812241229603982339803253 28201147615275373344356555)
    ·
      refine ⟨42301721422913060016534833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28201147615275373344356555 42301721422913060016534833)
      ·
        refine ⟨31726291067184795012401125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42301721422913060016534833 31726291067184795012401125)
        ·
          refine ⟨5948679575097149064825211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31726291067184795012401125 5948679575097149064825211)
          ·
            refine ⟨8923019362645723597237817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948679575097149064825211 8923019362645723597237817)
            ·
              refine ⟨6692264521984292697928363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8923019362645723597237817 6692264521984292697928363)
              ·
                refine ⟨10038396782976439046892545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6692264521984292697928363 10038396782976439046892545)
                ·
                  refine ⟨7528797587232329285169409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10038396782976439046892545 7528797587232329285169409)
                  ·
                    refine ⟨5646598190424246963877057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7528797587232329285169409 5646598190424246963877057)
                    ·
                      refine ⟨4234948642818185222907793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646598190424246963877057 4234948642818185222907793)
                      ·
                        rfl

theorem cell23_8247533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_8247533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247533 prefixEnd_8247533 := by exact prefixLift 8247533
  have htrace : WordTrace (prefixWord ++ tailWord_8247533) baseStart_8247533 baseEnd_8247533 := by
    simpa [prefixWord, tailWord_8247533, baseEnd_8247533] using wordTrace_append hprefix tailTrace_8247533
  have hstable : (prefixWord ++ tailWord_8247533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247533).length < 2 ^ (prefixWord ++ tailWord_8247533).sum := by decide
  have hdescent : baseEnd_8247533 < baseStart_8247533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247575 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_8247575 : Nat := 118140960795 + 8247575 * 2 ^ 59
def prefixEnd_8247575 : Nat := 4983230072969 + 3 ^ 40 * 8247575 * 2
def baseEnd_8247575 : Nat := 4234970209005674058582599

theorem tailTrace_8247575 : CollatzResearch.WordTrace tailWord_8247575 prefixEnd_8247575 4234970209005674058582599 := by
  unfold tailWord_8247575
  simp only [CollatzResearch.WordTrace]
  refine ⟨300813773095451823512832179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200542515396967882341888119 300813773095451823512832179)
  ·
    refine ⟨451220659643177735269248269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300813773095451823512832179 451220659643177735269248269)
    ·
      refine ⟨169207747366191650725968101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451220659643177735269248269 169207747366191650725968101)
      ·
        refine ⟨31726452631160934511119019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169207747366191650725968101 31726452631160934511119019)
        ·
          refine ⟨47589678946741401766678529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31726452631160934511119019 47589678946741401766678529)
          ·
            refine ⟨35692259210056051325008897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47589678946741401766678529 35692259210056051325008897)
            ·
              refine ⟨26769194407542038493756673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35692259210056051325008897 26769194407542038493756673)
              ·
                refine ⟨20076895805656528870317505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26769194407542038493756673 20076895805656528870317505)
                ·
                  refine ⟨15057671854242396652738129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20076895805656528870317505 15057671854242396652738129)
                  ·
                    refine ⟨11293253890681797489553597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15057671854242396652738129 11293253890681797489553597)
                    ·
                      refine ⟨4234970209005674058582599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11293253890681797489553597 4234970209005674058582599)
                      ·
                        rfl

theorem cell23_8247575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_8247575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247575 prefixEnd_8247575 := by exact prefixLift 8247575
  have htrace : WordTrace (prefixWord ++ tailWord_8247575) baseStart_8247575 baseEnd_8247575 := by
    simpa [prefixWord, tailWord_8247575, baseEnd_8247575] using wordTrace_append hprefix tailTrace_8247575
  have hstable : (prefixWord ++ tailWord_8247575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247575).length < 2 ^ (prefixWord ++ tailWord_8247575).sum := by decide
  have hdescent : baseEnd_8247575 < baseStart_8247575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247608 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 3, 5]
def baseStart_8247608 : Nat := 118140960795 + 8247608 * 2 ^ 59
def prefixEnd_8247608 : Nat := 4983230072969 + 3 ^ 40 * 8247608 * 2
def baseEnd_8247608 : Nat := 1411662384622424143156649

theorem tailTrace_8247608 : CollatzResearch.WordTrace tailWord_8247608 prefixEnd_8247608 1411662384622424143156649 := by
  unfold tailWord_8247608
  simp only [CollatzResearch.WordTrace]
  refine ⟨150407488352166135074391739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200543317802888180099188985 150407488352166135074391739)
  ·
    refine ⟨225611232528249202611587609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150407488352166135074391739 225611232528249202611587609)
    ·
      refine ⟨169208424396186901958690707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225611232528249202611587609 169208424396186901958690707)
      ·
        refine ⟨253812636594280352938036061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169208424396186901958690707 253812636594280352938036061)
        ·
          refine ⟨95179738722855132351763523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253812636594280352938036061 95179738722855132351763523)
          ·
            refine ⟨142769608084282698527645285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95179738722855132351763523 142769608084282698527645285)
            ·
              refine ⟨26769301515803005973933491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142769608084282698527645285 26769301515803005973933491)
              ·
                refine ⟨40153952273704508960900237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26769301515803005973933491 40153952273704508960900237)
                ·
                  refine ⟨15057732102639190860337589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40153952273704508960900237 15057732102639190860337589)
                  ·
                    refine ⟨1411662384622424143156649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15057732102639190860337589 1411662384622424143156649)
                    ·
                      rfl

theorem cell23_8247608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_8247608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247608 prefixEnd_8247608 := by exact prefixLift 8247608
  have htrace : WordTrace (prefixWord ++ tailWord_8247608) baseStart_8247608 baseEnd_8247608 := by
    simpa [prefixWord, tailWord_8247608, baseEnd_8247608] using wordTrace_append hprefix tailTrace_8247608
  have hstable : (prefixWord ++ tailWord_8247608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247608).length < 2 ^ (prefixWord ++ tailWord_8247608).sum := by decide
  have hdescent : baseEnd_8247608 < baseStart_8247608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247615 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 1, 5, 2]
def baseStart_8247615 : Nat := 118140960795 + 8247615 * 2 ^ 59
def prefixEnd_8247615 : Nat := 4983230072969 + 3 ^ 40 * 8247615 * 2
def baseEnd_8247615 : Nat := 4234990748231853902082415

theorem tailTrace_8247615 : CollatzResearch.WordTrace tailWord_8247615 prefixEnd_8247615 4234990748231853902082415 := by
  unfold tailWord_8247615
  simp only [CollatzResearch.WordTrace]
  refine ⟨300815232015306910344288299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200543488010204606896192199 300815232015306910344288299)
  ·
    refine ⟨451222848022960365516432449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300815232015306910344288299 451222848022960365516432449)
    ·
      refine ⟨338417136017220274137324337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451222848022960365516432449 338417136017220274137324337)
      ·
        refine ⟨253812852012915205602993253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338417136017220274137324337 253812852012915205602993253)
        ·
          refine ⟨47589909752421601050561235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253812852012915205602993253 47589909752421601050561235)
          ·
            refine ⟨71384864628632401575841853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47589909752421601050561235 71384864628632401575841853)
            ·
              refine ⟨26769324235737150590940695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71384864628632401575841853 26769324235737150590940695)
              ·
                refine ⟨40153986353605725886411043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26769324235737150590940695 40153986353605725886411043)
                ·
                  refine ⟨60230979530408588829616565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40153986353605725886411043 60230979530408588829616565)
                  ·
                    refine ⟨5646654330975805202776553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60230979530408588829616565 5646654330975805202776553)
                    ·
                      refine ⟨4234990748231853902082415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646654330975805202776553 4234990748231853902082415)
                      ·
                        rfl

theorem cell23_8247615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_8247615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247615 prefixEnd_8247615 := by exact prefixLift 8247615
  have htrace : WordTrace (prefixWord ++ tailWord_8247615) baseStart_8247615 baseEnd_8247615 := by
    simpa [prefixWord, tailWord_8247615, baseEnd_8247615] using wordTrace_append hprefix tailTrace_8247615
  have hstable : (prefixWord ++ tailWord_8247615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247615).length < 2 ^ (prefixWord ++ tailWord_8247615).sum := by decide
  have hdescent : baseEnd_8247615 < baseStart_8247615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247655 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 1, 6]
def baseStart_8247655 : Nat := 118140960795 + 8247655 * 2 ^ 59
def prefixEnd_8247655 : Nat := 4983230072969 + 3 ^ 40 * 8247655 * 2
def baseEnd_8247655 : Nat := 1411670429152677915194077

theorem tailTrace_8247655 : CollatzResearch.WordTrace tailWord_8247655 prefixEnd_8247655 1411670429152677915194077 := by
  unfold tailWord_8247655
  simp only [CollatzResearch.WordTrace]
  refine ⟨300816690935161997175744419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200544460623441331450496279 300816690935161997175744419)
  ·
    refine ⟨451225036402742995763616629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300816690935161997175744419 451225036402742995763616629)
    ·
      refine ⟨42302347162757155852839059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 451225036402742995763616629 42302347162757155852839059)
      ·
        refine ⟨63453520744135733779258589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42302347162757155852839059 63453520744135733779258589)
        ·
          refine ⟨23795070279050900167221971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63453520744135733779258589 23795070279050900167221971)
          ·
            refine ⟨35692605418576350250832957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23795070279050900167221971 35692605418576350250832957)
            ·
              refine ⟨13384727031966131344062359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35692605418576350250832957 13384727031966131344062359)
              ·
                refine ⟨20077090547949197016093539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13384727031966131344062359 20077090547949197016093539)
                ·
                  refine ⟨30115635821923795524140309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20077090547949197016093539 30115635821923795524140309)
                  ·
                    refine ⟨1411670429152677915194077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30115635821923795524140309 1411670429152677915194077)
                    ·
                      rfl

theorem cell23_8247655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_8247655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247655 prefixEnd_8247655 := by exact prefixLift 8247655
  have htrace : WordTrace (prefixWord ++ tailWord_8247655) baseStart_8247655 baseEnd_8247655 := by
    simpa [prefixWord, tailWord_8247655, baseEnd_8247655] using wordTrace_append hprefix tailTrace_8247655
  have hstable : (prefixWord ++ tailWord_8247655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247655).length < 2 ^ (prefixWord ++ tailWord_8247655).sum := by decide
  have hdescent : baseEnd_8247655 < baseStart_8247655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247765 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_8247765 : Nat := 118140960795 + 8247765 * 2 ^ 59
def prefixEnd_8247765 : Nat := 4983230072969 + 3 ^ 40 * 8247765 * 2
def baseEnd_8247765 : Nat := 4235067770330028315206725

theorem tailTrace_8247765 : CollatzResearch.WordTrace tailWord_8247765 prefixEnd_8247765 4235067770330028315206725 := by
  unfold tailWord_8247765
  simp only [CollatzResearch.WordTrace]
  refine ⟨300820702964763485962248749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200547135309842323974832499 300820702964763485962248749)
  ·
    refine ⟨112807763611786307235843281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300820702964763485962248749 112807763611786307235843281)
    ·
      refine ⟨84605822708839730426882461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112807763611786307235843281 84605822708839730426882461)
      ·
        refine ⟨31727183515814898910080923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84605822708839730426882461 31727183515814898910080923)
        ·
          refine ⟨47590775273722348365121385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31727183515814898910080923 47590775273722348365121385)
          ·
            refine ⟨35693081455291761273841039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47590775273722348365121385 35693081455291761273841039)
            ·
              refine ⟨53539622182937641910761559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35693081455291761273841039 53539622182937641910761559)
              ·
                refine ⟨80309433274406462866142339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53539622182937641910761559 80309433274406462866142339)
                ·
                  refine ⟨120464149911609694299213509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80309433274406462866142339 120464149911609694299213509)
                  ·
                    refine ⟨22587028108426817681102533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120464149911609694299213509 22587028108426817681102533)
                    ·
                      refine ⟨4235067770330028315206725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22587028108426817681102533 4235067770330028315206725)
                      ·
                        rfl

theorem cell23_8247765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_8247765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247765 prefixEnd_8247765 := by exact prefixLift 8247765
  have htrace : WordTrace (prefixWord ++ tailWord_8247765) baseStart_8247765 baseEnd_8247765 := by
    simpa [prefixWord, tailWord_8247765, baseEnd_8247765] using wordTrace_append hprefix tailTrace_8247765
  have hstable : (prefixWord ++ tailWord_8247765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247765).length < 2 ^ (prefixWord ++ tailWord_8247765).sum := by decide
  have hdescent : baseEnd_8247765 < baseStart_8247765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247769 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 2, 2, 2]
def baseStart_8247769 : Nat := 118140960795 + 8247769 * 2 ^ 59
def prefixEnd_8247769 : Nat := 4983230072969 + 3 ^ 40 * 8247769 * 2
def baseEnd_8247769 : Nat := 4235069824252646299556707

theorem tailTrace_8247769 : CollatzResearch.WordTrace tailWord_8247769 prefixEnd_8247769 4235069824252646299556707 := by
  unfold tailWord_8247769
  simp only [CollatzResearch.WordTrace]
  refine ⟨300820848856748994645394361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200547232571165996430262907 300820848856748994645394361)
  ·
    refine ⟨225615636642561745984045771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300820848856748994645394361 225615636642561745984045771)
    ·
      refine ⟨338423454963842618976068657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225615636642561745984045771 338423454963842618976068657)
      ·
        refine ⟨253817591222881964232051493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338423454963842618976068657 253817591222881964232051493)
        ·
          refine ⟨47590798354290368293509655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253817591222881964232051493 47590798354290368293509655)
          ·
            refine ⟨71386197531435552440264483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47590798354290368293509655 71386197531435552440264483)
            ·
              refine ⟨107079296297153328660396725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71386197531435552440264483 107079296297153328660396725)
              ·
                refine ⟨10038684027858124561912193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107079296297153328660396725 10038684027858124561912193)
                ·
                  refine ⟨7529013020893593421434145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10038684027858124561912193 7529013020893593421434145)
                  ·
                    refine ⟨5646759765670195066075609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7529013020893593421434145 5646759765670195066075609)
                    ·
                      refine ⟨4235069824252646299556707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646759765670195066075609 4235069824252646299556707)
                      ·
                        rfl

theorem cell23_8247769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_8247769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247769 prefixEnd_8247769 := by exact prefixLift 8247769
  have htrace : WordTrace (prefixWord ++ tailWord_8247769) baseStart_8247769 baseEnd_8247769 := by
    simpa [prefixWord, tailWord_8247769, baseEnd_8247769] using wordTrace_append hprefix tailTrace_8247769
  have hstable : (prefixWord ++ tailWord_8247769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247769).length < 2 ^ (prefixWord ++ tailWord_8247769).sum := by decide
  have hdescent : baseEnd_8247769 < baseStart_8247769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247775 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 7]
def baseStart_8247775 : Nat := 118140960795 + 8247775 * 2 ^ 59
def prefixEnd_8247775 : Nat := 4983230072969 + 3 ^ 40 * 8247775 * 2
def baseEnd_8247775 : Nat := 470563656126285919564631

theorem tailTrace_8247775 : CollatzResearch.WordTrace tailWord_8247775 prefixEnd_8247775 470563656126285919564631 := by
  unfold tailWord_8247775
  simp only [CollatzResearch.WordTrace]
  refine ⟨300821067694727257670112779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200547378463151505113408519 300821067694727257670112779)
  ·
    refine ⟨451231601542090886505169169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300821067694727257670112779 451231601542090886505169169)
    ·
      refine ⟨338423701156568164878876877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451231601542090886505169169 338423701156568164878876877)
      ·
        refine ⟨126908887933713061829578829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338423701156568164878876877 126908887933713061829578829)
        ·
          refine ⟨47590832975142398186092061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126908887933713061829578829 47590832975142398186092061)
          ·
            refine ⟨17846562365678399319784523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47590832975142398186092061 17846562365678399319784523)
            ·
              refine ⟨26769843548517598979676785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17846562365678399319784523 26769843548517598979676785)
              ·
                refine ⟨20077382661388199234757589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26769843548517598979676785 20077382661388199234757589)
                ·
                  refine ⟨470563656126285919564631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20077382661388199234757589 470563656126285919564631)
                  ·
                    rfl

theorem cell23_8247775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 7].length) (baseStart_8247775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247775 prefixEnd_8247775 := by exact prefixLift 8247775
  have htrace : WordTrace (prefixWord ++ tailWord_8247775) baseStart_8247775 baseEnd_8247775 := by
    simpa [prefixWord, tailWord_8247775, baseEnd_8247775] using wordTrace_append hprefix tailTrace_8247775
  have hstable : (prefixWord ++ tailWord_8247775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247775).length < 2 ^ (prefixWord ++ tailWord_8247775).sum := by decide
  have hdescent : baseEnd_8247775 < baseStart_8247775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247792 : List Nat := [2, 1, 1, 1, 3, 3, 4, 3, 5]
def baseStart_8247792 : Nat := 118140960795 + 8247792 * 2 ^ 59
def prefixEnd_8247792 : Nat := 4983230072969 + 3 ^ 40 * 8247792 * 2
def baseEnd_8247792 : Nat := 470564626034188856618789

theorem tailTrace_8247792 : CollatzResearch.WordTrace tailWord_8247792 prefixEnd_8247792 470564626034188856618789 := by
  unfold tailWord_8247792
  simp only [CollatzResearch.WordTrace]
  refine ⟨150410843867832834786740815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200547791823777113048987753 150410843867832834786740815)
  ·
    refine ⟨225616265801749252180111223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150410843867832834786740815 225616265801749252180111223)
    ·
      refine ⟨338424398702623878270166835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225616265801749252180111223 338424398702623878270166835)
      ·
        refine ⟨507636598053935817405250253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338424398702623878270166835 507636598053935817405250253)
        ·
          refine ⟨190363724270225931526968845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507636598053935817405250253 190363724270225931526968845)
          ·
            refine ⟨71386396601334724322613317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190363724270225931526968845 71386396601334724322613317)
            ·
              refine ⟨13384949362750260810489997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71386396601334724322613317 13384949362750260810489997)
              ·
                refine ⟨5019356011031347803933749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13384949362750260810489997 5019356011031347803933749)
                ·
                  refine ⟨470564626034188856618789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5019356011031347803933749 470564626034188856618789)
                  ·
                    rfl

theorem cell23_8247792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 5].length) (baseStart_8247792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247792 prefixEnd_8247792 := by exact prefixLift 8247792
  have htrace : WordTrace (prefixWord ++ tailWord_8247792) baseStart_8247792 baseEnd_8247792 := by
    simpa [prefixWord, tailWord_8247792, baseEnd_8247792] using wordTrace_append hprefix tailTrace_8247792
  have hstable : (prefixWord ++ tailWord_8247792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247792).length < 2 ^ (prefixWord ++ tailWord_8247792).sum := by decide
  have hdescent : baseEnd_8247792 < baseStart_8247792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247805 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_8247805 : Nat := 118140960795 + 8247805 * 2 ^ 59
def prefixEnd_8247805 : Nat := 4983230072969 + 3 ^ 40 * 8247805 * 2
def baseEnd_8247805 : Nat := 1411696103185402719568847

theorem tailTrace_8247805 : CollatzResearch.WordTrace tailWord_8247805 prefixEnd_8247805 1411696103185402719568847 := by
  unfold tailWord_8247805
  simp only [CollatzResearch.WordTrace]
  refine ⟨300822161884618572793704869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200548107923079048529136579 300822161884618572793704869)
  ·
    refine ⟨56404155353365982398819663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300822161884618572793704869 56404155353365982398819663)
    ·
      refine ⟨84606233030048973598229495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56404155353365982398819663 84606233030048973598229495)
      ·
        refine ⟨126909349545073460397344243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84606233030048973598229495 126909349545073460397344243)
        ·
          refine ⟨190364024317610190596016365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126909349545073460397344243 190364024317610190596016365)
          ·
            refine ⟨71386509119103821473506137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190364024317610190596016365 71386509119103821473506137)
            ·
              refine ⟨53539881839327866105129603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71386509119103821473506137 53539881839327866105129603)
              ·
                refine ⟨80309822758991799157694405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53539881839327866105129603 80309822758991799157694405)
                ·
                  refine ⟨15058091767310962342067701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80309822758991799157694405 15058091767310962342067701)
                  ·
                    refine ⟨1411696103185402719568847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15058091767310962342067701 1411696103185402719568847)
                    ·
                      rfl

theorem cell23_8247805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_8247805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247805 prefixEnd_8247805 := by exact prefixLift 8247805
  have htrace : WordTrace (prefixWord ++ tailWord_8247805) baseStart_8247805 baseEnd_8247805 := by
    simpa [prefixWord, tailWord_8247805, baseEnd_8247805] using wordTrace_append hprefix tailTrace_8247805
  have hstable : (prefixWord ++ tailWord_8247805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247805).length < 2 ^ (prefixWord ++ tailWord_8247805).sum := by decide
  have hdescent : baseEnd_8247805 < baseStart_8247805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247825 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_8247825 : Nat := 118140960795 + 8247825 * 2 ^ 59
def prefixEnd_8247825 : Nat := 4983230072969 + 3 ^ 40 * 8247825 * 2
def baseEnd_8247825 : Nat := 4235098579169298080456449

theorem tailTrace_8247825 : CollatzResearch.WordTrace tailWord_8247825 prefixEnd_8247825 4235098579169298080456449 := by
  unfold tailWord_8247825
  simp only [CollatzResearch.WordTrace]
  refine ⟨300822891344546116209432929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200548594229697410806288619 300822891344546116209432929)
  ·
    refine ⟨225617168508409587157074697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300822891344546116209432929 225617168508409587157074697)
    ·
      refine ⟨169212876381307190367806023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225617168508409587157074697 169212876381307190367806023)
      ·
        refine ⟨253819314571960785551709035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169212876381307190367806023 253819314571960785551709035)
        ·
          refine ⟨380728971857941178327563553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253819314571960785551709035 380728971857941178327563553)
          ·
            refine ⟨285546728893455883745672665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380728971857941178327563553 285546728893455883745672665)
            ·
              refine ⟨214160046670091912809254499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285546728893455883745672665 214160046670091912809254499)
              ·
                refine ⟨321240070005137869213881749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214160046670091912809254499 321240070005137869213881749)
                ·
                  refine ⟨15058128281490837619400707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 321240070005137869213881749 15058128281490837619400707)
                  ·
                    refine ⟨22587192422236256429101061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15058128281490837619400707 22587192422236256429101061)
                    ·
                      refine ⟨4235098579169298080456449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22587192422236256429101061 4235098579169298080456449)
                      ·
                        rfl

theorem cell23_8247825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_8247825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247825 prefixEnd_8247825 := by exact prefixLift 8247825
  have htrace : WordTrace (prefixWord ++ tailWord_8247825) baseStart_8247825 baseEnd_8247825 := by
    simpa [prefixWord, tailWord_8247825, baseEnd_8247825] using wordTrace_append hprefix tailTrace_8247825
  have hstable : (prefixWord ++ tailWord_8247825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247825).length < 2 ^ (prefixWord ++ tailWord_8247825).sum := by decide
  have hdescent : baseEnd_8247825 < baseStart_8247825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247842 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_8247842 : Nat := 118140960795 + 8247842 * 2 ^ 59
def prefixEnd_8247842 : Nat := 4983230072969 + 3 ^ 40 * 8247842 * 2
def baseEnd_8247842 : Nat := 4235107308340424513943871

theorem tailTrace_8247842 : CollatzResearch.WordTrace tailWord_8247842 prefixEnd_8247842 4235107308340424513943871 := by
  unfold tailWord_8247842
  simp only [CollatzResearch.WordTrace]
  refine ⟨75205877846371132028200445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200549007590323018741867853 75205877846371132028200445)
  ·
    refine ⟨28202204192389174510575167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75205877846371132028200445 28202204192389174510575167)
    ·
      refine ⟨42303306288583761765862751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28202204192389174510575167 42303306288583761765862751)
      ·
        refine ⟨63454959432875642648794127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42303306288583761765862751 63454959432875642648794127)
        ·
          refine ⟨95182439149313463973191191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63454959432875642648794127 95182439149313463973191191)
          ·
            refine ⟨142773658723970195959786787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95182439149313463973191191 142773658723970195959786787)
            ·
              refine ⟨214160488085955293939680181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142773658723970195959786787 214160488085955293939680181)
              ·
                refine ⟨20077545758058308806845017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214160488085955293939680181 20077545758058308806845017)
                ·
                  refine ⟨15058159318543731605133763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20077545758058308806845017 15058159318543731605133763)
                  ·
                    refine ⟨22587238977815597407700645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15058159318543731605133763 22587238977815597407700645)
                    ·
                      refine ⟨4235107308340424513943871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22587238977815597407700645 4235107308340424513943871)
                      ·
                        rfl

theorem cell23_8247842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_8247842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247842 prefixEnd_8247842 := by exact prefixLift 8247842
  have htrace : WordTrace (prefixWord ++ tailWord_8247842) baseStart_8247842 baseEnd_8247842 := by
    simpa [prefixWord, tailWord_8247842, baseEnd_8247842] using wordTrace_append hprefix tailTrace_8247842
  have hstable : (prefixWord ++ tailWord_8247842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247842).length < 2 ^ (prefixWord ++ tailWord_8247842).sum := by decide
  have hdescent : baseEnd_8247842 < baseStart_8247842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247865 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 8]
def baseStart_8247865 : Nat := 118140960795 + 8247865 * 2 ^ 59
def prefixEnd_8247865 : Nat := 4983230072969 + 3 ^ 40 * 8247865 * 2
def baseEnd_8247865 : Nat := 470568790932830880439585

theorem tailTrace_8247865 : CollatzResearch.WordTrace tailWord_8247865 prefixEnd_8247865 470568790932830880439585 := by
  unfold tailWord_8247865
  simp only [CollatzResearch.WordTrace]
  refine ⟨300824350264401203040889049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200549566842934135360592699 300824350264401203040889049)
  ·
    refine ⟨225618262698300902280666787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300824350264401203040889049 225618262698300902280666787)
    ·
      refine ⟨338427394047451353421000181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225618262698300902280666787 338427394047451353421000181)
      ·
        refine ⟨31727568191948564383218767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338427394047451353421000181 31727568191948564383218767)
        ·
          refine ⟨47591352287922846574828151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31727568191948564383218767 47591352287922846574828151)
          ·
            refine ⟨71387028431884269862242227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47591352287922846574828151 71387028431884269862242227)
            ·
              refine ⟨107080542647826404793363341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71387028431884269862242227 107080542647826404793363341)
              ·
                refine ⟨40155203492934901797511253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107080542647826404793363341 40155203492934901797511253)
                ·
                  refine ⟨470568790932830880439585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40155203492934901797511253 470568790932830880439585)
                  ·
                    rfl

theorem cell23_8247865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 8].length) (baseStart_8247865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247865 prefixEnd_8247865 := by exact prefixLift 8247865
  have htrace : WordTrace (prefixWord ++ tailWord_8247865) baseStart_8247865 baseEnd_8247865 := by
    simpa [prefixWord, tailWord_8247865, baseEnd_8247865] using wordTrace_append hprefix tailTrace_8247865
  have hstable : (prefixWord ++ tailWord_8247865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247865).length < 2 ^ (prefixWord ++ tailWord_8247865).sum := by decide
  have hdescent : baseEnd_8247865 < baseStart_8247865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247869 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_8247869 : Nat := 118140960795 + 8247869 * 2 ^ 59
def prefixEnd_8247869 : Nat := 4983230072969 + 3 ^ 40 * 8247869 * 2
def baseEnd_8247869 : Nat := 1411707057439365302768749

theorem tailTrace_8247869 : CollatzResearch.WordTrace tailWord_8247869 prefixEnd_8247869 1411707057439365302768749 := by
  unfold tailWord_8247869
  simp only [CollatzResearch.WordTrace]
  refine ⟨300824496156386711724034661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200549664104257807816023107 300824496156386711724034661)
  ·
    refine ⟨56404593029322508448256499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300824496156386711724034661 56404593029322508448256499)
    ·
      refine ⟨84606889543983762672384749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56404593029322508448256499 84606889543983762672384749)
      ·
        refine ⟨31727583578993911002144281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84606889543983762672384749 31727583578993911002144281)
        ·
          refine ⟨23795687684245433251608211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31727583578993911002144281 23795687684245433251608211)
          ·
            refine ⟨35693531526368149877412317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23795687684245433251608211 35693531526368149877412317)
            ·
              refine ⟨13385074322388056204029619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35693531526368149877412317 13385074322388056204029619)
              ·
                refine ⟨20077611483582084306044429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13385074322388056204029619 20077611483582084306044429)
                ·
                  refine ⟨7529104306343281614766661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20077611483582084306044429 7529104306343281614766661)
                  ·
                    refine ⟨1411707057439365302768749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7529104306343281614766661 1411707057439365302768749)
                    ·
                      rfl

theorem cell23_8247869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_8247869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247869 prefixEnd_8247869 := by exact prefixLift 8247869
  have htrace : WordTrace (prefixWord ++ tailWord_8247869) baseStart_8247869 baseEnd_8247869 := by
    simpa [prefixWord, tailWord_8247869, baseEnd_8247869] using wordTrace_append hprefix tailTrace_8247869
  have hstable : (prefixWord ++ tailWord_8247869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247869).length < 2 ^ (prefixWord ++ tailWord_8247869).sum := by decide
  have hdescent : baseEnd_8247869 < baseStart_8247869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247882 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 6]
def baseStart_8247882 : Nat := 118140960795 + 8247882 * 2 ^ 59
def prefixEnd_8247882 : Nat := 4983230072969 + 3 ^ 40 * 8247882 * 2
def baseEnd_8247882 : Nat := 470569760840733817493743

theorem tailTrace_8247882 : CollatzResearch.WordTrace tailWord_8247882 prefixEnd_8247882 470569760840733817493743 := by
  unfold tailWord_8247882
  simp only [CollatzResearch.WordTrace]
  refine ⟨75206242576334903736064475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200549980203559743296171933 75206242576334903736064475)
  ·
    refine ⟨112809363864502355604096713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75206242576334903736064475 112809363864502355604096713)
    ·
      refine ⟨84607022898376766703072535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112809363864502355604096713 84607022898376766703072535)
      ·
        refine ⟨126910534347565150054608803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84607022898376766703072535 126910534347565150054608803)
        ·
          refine ⟨190365801521347725081913205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126910534347565150054608803 190365801521347725081913205)
          ·
            refine ⟨17846793892626349226429363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190365801521347725081913205 17846793892626349226429363)
            ·
              refine ⟨26770190838939523839644045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17846793892626349226429363 26770190838939523839644045)
              ·
                refine ⟨10038821564602321439866517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26770190838939523839644045 10038821564602321439866517)
                ·
                  refine ⟨470569760840733817493743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10038821564602321439866517 470569760840733817493743)
                  ·
                    rfl

theorem cell23_8247882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_8247882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247882 prefixEnd_8247882 := by exact prefixLift 8247882
  have htrace : WordTrace (prefixWord ++ tailWord_8247882) baseStart_8247882 baseEnd_8247882 := by
    simpa [prefixWord, tailWord_8247882, baseEnd_8247882] using wordTrace_append hprefix tailTrace_8247882
  have hstable : (prefixWord ++ tailWord_8247882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247882).length < 2 ^ (prefixWord ++ tailWord_8247882).sum := by decide
  have hdescent : baseEnd_8247882 < baseStart_8247882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247919 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 2, 3, 2]
def baseStart_8247919 : Nat := 118140960795 + 8247919 * 2 ^ 59
def prefixEnd_8247919 : Nat := 4983230072969 + 3 ^ 40 * 8247919 * 2
def baseEnd_8247919 : Nat := 4235146846350820712681017

theorem tailTrace_8247919 : CollatzResearch.WordTrace tailWord_8247919 prefixEnd_8247919 4235146846350820712681017 := by
  unfold tailWord_8247919
  simp only [CollatzResearch.WordTrace]
  refine ⟨300826319806205570263354811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200550879870803713508903207 300826319806205570263354811)
  ·
    refine ⟨451239479709308355395032217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300826319806205570263354811 451239479709308355395032217)
    ·
      refine ⟨338429609781981266546274163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451239479709308355395032217 338429609781981266546274163)
      ·
        refine ⟨507644414672971899819411245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338429609781981266546274163 507644414672971899819411245)
        ·
          refine ⟨190366655502364462432279217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507644414672971899819411245 190366655502364462432279217)
          ·
            refine ⟨142774991626773346824209413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190366655502364462432279217 142774991626773346824209413)
            ·
              refine ⟨26770310930020002529539265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142774991626773346824209413 26770310930020002529539265)
              ·
                refine ⟨20077733197515001897154449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26770310930020002529539265 20077733197515001897154449)
                ·
                  refine ⟨15058299898136251422865837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20077733197515001897154449 15058299898136251422865837)
                  ·
                    refine ⟨5646862461801094283574689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15058299898136251422865837 5646862461801094283574689)
                    ·
                      refine ⟨4235146846350820712681017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646862461801094283574689 4235146846350820712681017)
                      ·
                        rfl

theorem cell23_8247919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 3, 2].length) (baseStart_8247919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247919 prefixEnd_8247919 := by exact prefixLift 8247919
  have htrace : WordTrace (prefixWord ++ tailWord_8247919) baseStart_8247919 baseEnd_8247919 := by
    simpa [prefixWord, tailWord_8247919, baseEnd_8247919] using wordTrace_append hprefix tailTrace_8247919
  have hstable : (prefixWord ++ tailWord_8247919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247919).length < 2 ^ (prefixWord ++ tailWord_8247919).sum := by decide
  have hdescent : baseEnd_8247919 < baseStart_8247919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247920 : List Nat := [2, 1, 1, 1, 8, 1, 2, 2, 1, 4]
def baseStart_8247920 : Nat := 118140960795 + 8247920 * 2 ^ 59
def prefixEnd_8247920 : Nat := 4983230072969 + 3 ^ 40 * 8247920 * 2
def baseEnd_8247920 : Nat := 1411715786610491736256171

theorem tailTrace_8247920 : CollatzResearch.WordTrace tailWord_8247920 prefixEnd_8247920 1411715786610491736256171 := by
  unfold tailWord_8247920
  simp only [CollatzResearch.WordTrace]
  refine ⟨150413178139600973717070607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200550904186134631622760809 150413178139600973717070607)
  ·
    refine ⟨225619767209401460575605911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150413178139600973717070607 225619767209401460575605911)
    ·
      refine ⟨338429650814102190863408867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225619767209401460575605911 338429650814102190863408867)
      ·
        refine ⟨507644476221153286295113301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338429650814102190863408867 507644476221153286295113301)
        ·
          refine ⟨5948958705716640073770859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 507644476221153286295113301 5948958705716640073770859)
          ·
            refine ⟨8923438058574960110656289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5948958705716640073770859 8923438058574960110656289)
            ·
              refine ⟨6692578543931220082992217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8923438058574960110656289 6692578543931220082992217)
              ·
                refine ⟨5019433907948415062244163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6692578543931220082992217 5019433907948415062244163)
                ·
                  refine ⟨7529150861922622593366245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019433907948415062244163 7529150861922622593366245)
                  ·
                    refine ⟨1411715786610491736256171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7529150861922622593366245 1411715786610491736256171)
                    ·
                      rfl

theorem cell23_8247920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 4].length) (baseStart_8247920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247920 prefixEnd_8247920 := by exact prefixLift 8247920
  have htrace : WordTrace (prefixWord ++ tailWord_8247920) baseStart_8247920 baseEnd_8247920 := by
    simpa [prefixWord, tailWord_8247920, baseEnd_8247920] using wordTrace_append hprefix tailTrace_8247920
  have hstable : (prefixWord ++ tailWord_8247920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247920).length < 2 ^ (prefixWord ++ tailWord_8247920).sum := by decide
  have hdescent : baseEnd_8247920 < baseStart_8247920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247932 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_8247932 : Nat := 118140960795 + 8247932 * 2 ^ 59
def prefixEnd_8247932 : Nat := 4983230072969 + 3 ^ 40 * 8247932 * 2
def baseEnd_8247932 : Nat := 4235153521599329161818457

theorem tailTrace_8247932 : CollatzResearch.WordTrace tailWord_8247932 prefixEnd_8247932 4235153521599329161818457 := by
  unfold tailWord_8247932
  simp only [CollatzResearch.WordTrace]
  refine ⟨150413396977579236741789025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200551195970105648989052033 150413396977579236741789025)
  ·
    refine ⟨112810047733184427556341769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150413396977579236741789025 112810047733184427556341769)
    ·
      refine ⟨84607535799888320667256327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112810047733184427556341769 84607535799888320667256327)
      ·
        refine ⟨126911303699832481000884491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84607535799888320667256327 126911303699832481000884491)
        ·
          refine ⟨190366955549748721501326737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126911303699832481000884491 190366955549748721501326737)
          ·
            refine ⟨142775216662311541125995053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190366955549748721501326737 142775216662311541125995053)
            ·
              refine ⟨53540706248366827922248145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142775216662311541125995053 53540706248366827922248145)
              ·
                refine ⟨40155529686275120941686109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53540706248366827922248145 40155529686275120941686109)
                ·
                  refine ⟨15058323632353170353132291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40155529686275120941686109 15058323632353170353132291)
                  ·
                    refine ⟨22587485448529755529698437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15058323632353170353132291 22587485448529755529698437)
                    ·
                      refine ⟨4235153521599329161818457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22587485448529755529698437 4235153521599329161818457)
                      ·
                        rfl

theorem cell23_8247932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_8247932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247932 prefixEnd_8247932 := by exact prefixLift 8247932
  have htrace : WordTrace (prefixWord ++ tailWord_8247932) baseStart_8247932 baseEnd_8247932 := by
    simpa [prefixWord, tailWord_8247932, baseEnd_8247932] using wordTrace_append hprefix tailTrace_8247932
  have hstable : (prefixWord ++ tailWord_8247932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247932).length < 2 ^ (prefixWord ++ tailWord_8247932).sum := by decide
  have hdescent : baseEnd_8247932 < baseStart_8247932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247966 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_8247966 : Nat := 118140960795 + 8247966 * 2 ^ 59
def prefixEnd_8247966 : Nat := 4983230072969 + 3 ^ 40 * 8247966 * 2
def baseEnd_8247966 : Nat := 4235170979941582028793301

theorem tailTrace_8247966 : CollatzResearch.WordTrace tailWord_8247966 prefixEnd_8247966 4235170979941582028793301 := by
  unfold tailWord_8247966
  simp only [CollatzResearch.WordTrace]
  refine ⟨37603504254629412161289469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200552022691356864860210501 37603504254629412161289469)
  ·
    refine ⟨14101314095486029560483551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37603504254629412161289469 14101314095486029560483551)
    ·
      refine ⟨21151971143229044340725327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14101314095486029560483551 21151971143229044340725327)
      ·
        refine ⟨31727956714843566511087991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21151971143229044340725327 31727956714843566511087991)
        ·
          refine ⟨47591935072265349766631987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31727956714843566511087991 47591935072265349766631987)
          ·
            refine ⟨71387902608398024649947981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47591935072265349766631987 71387902608398024649947981)
            ·
              refine ⟨26770463478149259243730493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71387902608398024649947981 26770463478149259243730493)
              ·
                refine ⟨10038923804305972216398935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26770463478149259243730493 10038923804305972216398935)
                ·
                  refine ⟨15058385706458958324598403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10038923804305972216398935 15058385706458958324598403)
                  ·
                    refine ⟨22587578559688437486897605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15058385706458958324598403 22587578559688437486897605)
                    ·
                      refine ⟨4235170979941582028793301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22587578559688437486897605 4235170979941582028793301)
                      ·
                        rfl

theorem cell23_8247966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_8247966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247966 prefixEnd_8247966 := by exact prefixLift 8247966
  have htrace : WordTrace (prefixWord ++ tailWord_8247966) baseStart_8247966 baseEnd_8247966 := by
    simpa [prefixWord, tailWord_8247966, baseEnd_8247966] using wordTrace_append hprefix tailTrace_8247966
  have hstable : (prefixWord ++ tailWord_8247966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247966).length < 2 ^ (prefixWord ++ tailWord_8247966).sum := by decide
  have hdescent : baseEnd_8247966 < baseStart_8247966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247983 : List Nat := [1, 1, 2, 1, 2, 5, 2, 4, 1, 2, 2]
def baseStart_8247983 : Nat := 118140960795 + 8247983 * 2 ^ 59
def prefixEnd_8247983 : Nat := 4983230072969 + 3 ^ 40 * 8247983 * 2
def baseEnd_8247983 : Nat := 4235179709112708462280723

theorem tailTrace_8247983 : CollatzResearch.WordTrace tailWord_8247983 prefixEnd_8247983 4235179709112708462280723 := by
  unfold tailWord_8247983
  simp only [CollatzResearch.WordTrace]
  refine ⟨300828654077973709193684603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200552436051982472795789735 300828654077973709193684603)
  ·
    refine ⟨451242981116960563790526905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300828654077973709193684603 451242981116960563790526905)
    ·
      refine ⟨338432235837720422842895179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451242981116960563790526905 338432235837720422842895179)
      ·
        refine ⟨507648353756580634264342769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338432235837720422842895179 507648353756580634264342769)
        ·
          refine ⟨380736265317435475698257077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507648353756580634264342769 380736265317435475698257077)
          ·
            refine ⟨35694024873509575846711601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380736265317435475698257077 35694024873509575846711601)
            ·
              refine ⟨26770518655132181885033701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35694024873509575846711601 26770518655132181885033701)
              ·
                refine ⟨5019472247837284103443819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26770518655132181885033701 5019472247837284103443819)
                ·
                  refine ⟨7529208371755926155165729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019472247837284103443819 7529208371755926155165729)
                  ·
                    refine ⟨5646906278816944616374297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7529208371755926155165729 5646906278816944616374297)
                    ·
                      refine ⟨4235179709112708462280723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646906278816944616374297 4235179709112708462280723)
                      ·
                        rfl

theorem cell23_8247983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 2, 2].length) (baseStart_8247983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247983 prefixEnd_8247983 := by exact prefixLift 8247983
  have htrace : WordTrace (prefixWord ++ tailWord_8247983) baseStart_8247983 baseEnd_8247983 := by
    simpa [prefixWord, tailWord_8247983, baseEnd_8247983] using wordTrace_append hprefix tailTrace_8247983
  have hstable : (prefixWord ++ tailWord_8247983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247983).length < 2 ^ (prefixWord ++ tailWord_8247983).sum := by decide
  have hdescent : baseEnd_8247983 < baseStart_8247983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8247999 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 3]
def baseStart_8247999 : Nat := 118140960795 + 8247999 * 2 ^ 59
def prefixEnd_8247999 : Nat := 4983230072969 + 3 ^ 40 * 8247999 * 2
def baseEnd_8247999 : Nat := 4235187924803180399680649

theorem tailTrace_8247999 : CollatzResearch.WordTrace tailWord_8247999 prefixEnd_8247999 4235187924803180399680649 := by
  unfold tailWord_8247999
  simp only [CollatzResearch.WordTrace]
  refine ⟨300829237645915743926267051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200552825097277162617511367 300829237645915743926267051)
  ·
    refine ⟨451243856468873615889400577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300829237645915743926267051 451243856468873615889400577)
    ·
      refine ⟨338432892351655211917050433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451243856468873615889400577 338432892351655211917050433)
      ·
        refine ⟨253824669263741408937787825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338432892351655211917050433 253824669263741408937787825)
        ·
          refine ⟨190368501947806056703340869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253824669263741408937787825 190368501947806056703340869)
          ·
            refine ⟨35694094115213635631876413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190368501947806056703340869 35694094115213635631876413)
            ·
              refine ⟨13385285293205113361953655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35694094115213635631876413 13385285293205113361953655)
              ·
                refine ⟨20077927939807670042930483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13385285293205113361953655 20077927939807670042930483)
                ·
                  refine ⟨30116891909711505064395725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20077927939807670042930483 30116891909711505064395725)
                  ·
                    refine ⟨11293834466141814399148397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30116891909711505064395725 11293834466141814399148397)
                    ·
                      refine ⟨4235187924803180399680649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11293834466141814399148397 4235187924803180399680649)
                      ·
                        rfl

theorem cell23_8247999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_8247999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8247999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8247999 prefixEnd_8247999 := by exact prefixLift 8247999
  have htrace : WordTrace (prefixWord ++ tailWord_8247999) baseStart_8247999 baseEnd_8247999 := by
    simpa [prefixWord, tailWord_8247999, baseEnd_8247999] using wordTrace_append hprefix tailTrace_8247999
  have hstable : (prefixWord ++ tailWord_8247999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8247999).length < 2 ^ (prefixWord ++ tailWord_8247999).sum := by decide
  have hdescent : baseEnd_8247999 < baseStart_8247999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8247999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248026 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2]
def baseStart_8248026 : Nat := 118140960795 + 8248026 * 2 ^ 59
def prefixEnd_8248026 : Nat := 4983230072969 + 3 ^ 40 * 8248026 * 2
def baseEnd_8248026 : Nat := 4235201788780851794043025

theorem tailTrace_8248026 : CollatzResearch.WordTrace tailWord_8248026 prefixEnd_8248026 4235201788780851794043025 := by
  unfold tailWord_8248026
  simp only [CollatzResearch.WordTrace]
  refine ⟨75207555604204481884374983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200553481611211951691666621 75207555604204481884374983)
  ·
    refine ⟨112811333406306722826562475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75207555604204481884374983 112811333406306722826562475)
    ·
      refine ⟨169217000109460084239843713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112811333406306722826562475 169217000109460084239843713)
      ·
        refine ⟨126912750082095063179882785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169217000109460084239843713 126912750082095063179882785)
        ·
          refine ⟨95184562561571297384912089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126912750082095063179882785 95184562561571297384912089)
          ·
            refine ⟨71388421921178473038684067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95184562561571297384912089 71388421921178473038684067)
            ·
              refine ⟨107082632881767709558026101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71388421921178473038684067 107082632881767709558026101)
              ·
                refine ⟨10038996832665722771064947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107082632881767709558026101 10038996832665722771064947)
                ·
                  refine ⟨15058495248998584156597421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10038996832665722771064947 15058495248998584156597421)
                  ·
                    refine ⟨5646935718374469058724033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15058495248998584156597421 5646935718374469058724033)
                    ·
                      refine ⟨4235201788780851794043025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5646935718374469058724033 4235201788780851794043025)
                      ·
                        rfl

theorem cell23_8248026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_8248026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248026 prefixEnd_8248026 := by exact prefixLift 8248026
  have htrace : WordTrace (prefixWord ++ tailWord_8248026) baseStart_8248026 baseEnd_8248026 := by
    simpa [prefixWord, tailWord_8248026, baseEnd_8248026] using wordTrace_append hprefix tailTrace_8248026
  have hstable : (prefixWord ++ tailWord_8248026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248026).length < 2 ^ (prefixWord ++ tailWord_8248026).sum := by decide
  have hdescent : baseEnd_8248026 < baseStart_8248026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248042 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_8248042 : Nat := 118140960795 + 8248042 * 2 ^ 59
def prefixEnd_8248042 : Nat := 4983230072969 + 3 ^ 40 * 8248042 * 2
def baseEnd_8248042 : Nat := 4235210004471323731442951

theorem tailTrace_8248042 : CollatzResearch.WordTrace tailWord_8248042 prefixEnd_8248042 4235210004471323731442951 := by
  unfold tailWord_8248042
  simp only [CollatzResearch.WordTrace]
  refine ⟨75207701496189990567520595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200553870656506641513388253 75207701496189990567520595)
  ·
    refine ⟨112811552244284985851280893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75207701496189990567520595 112811552244284985851280893)
    ·
      refine ⟨42304332091606869694230335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112811552244284985851280893 42304332091606869694230335)
      ·
        refine ⟨63456498137410304541345503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42304332091606869694230335 63456498137410304541345503)
        ·
          refine ⟨95184747206115456812018255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63456498137410304541345503 95184747206115456812018255)
          ·
            refine ⟨142777120809173185218027383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95184747206115456812018255 142777120809173185218027383)
            ·
              refine ⟨214165681213759777827041075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142777120809173185218027383 214165681213759777827041075)
              ·
                refine ⟨321248521820639666740561613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214165681213759777827041075 321248521820639666740561613)
                ·
                  refine ⟨120468195682739875027710605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321248521820639666740561613 120468195682739875027710605)
                  ·
                    refine ⟨45175573381027453135391477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120468195682739875027710605 45175573381027453135391477)
                    ·
                      refine ⟨4235210004471323731442951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45175573381027453135391477 4235210004471323731442951)
                      ·
                        rfl

theorem cell23_8248042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_8248042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248042 prefixEnd_8248042 := by exact prefixLift 8248042
  have htrace : WordTrace (prefixWord ++ tailWord_8248042) baseStart_8248042 baseEnd_8248042 := by
    simpa [prefixWord, tailWord_8248042, baseEnd_8248042] using wordTrace_append hprefix tailTrace_8248042
  have hstable : (prefixWord ++ tailWord_8248042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248042).length < 2 ^ (prefixWord ++ tailWord_8248042).sum := by decide
  have hdescent : baseEnd_8248042 < baseStart_8248042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248050 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_8248050 : Nat := 118140960795 + 8248050 * 2 ^ 59
def prefixEnd_8248050 : Nat := 4983230072969 + 3 ^ 40 * 8248050 * 2
def baseEnd_8248050 : Nat := 4235214112316559700142915

theorem tailTrace_8248050 : CollatzResearch.WordTrace tailWord_8248050 prefixEnd_8248050 4235214112316559700142915 := by
  unfold tailWord_8248050
  simp only [CollatzResearch.WordTrace]
  refine ⟨75207774442182744909093401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200554065179153986424249069 75207774442182744909093401)
  ·
    refine ⟨56405830831637058681820051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75207774442182744909093401 56405830831637058681820051)
    ·
      refine ⟨84608746247455588022730077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56405830831637058681820051 84608746247455588022730077)
      ·
        refine ⟨31728279842795845508523779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84608746247455588022730077 31728279842795845508523779)
        ·
          refine ⟨47592419764193768262785669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31728279842795845508523779 47592419764193768262785669)
          ·
            refine ⟨8923578705786331549272313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47592419764193768262785669 8923578705786331549272313)
            ·
              refine ⟨6692684029339748661954235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8923578705786331549272313 6692684029339748661954235)
              ·
                refine ⟨10039026044009622992931353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6692684029339748661954235 10039026044009622992931353)
                ·
                  refine ⟨7529269533007217244698515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10039026044009622992931353 7529269533007217244698515)
                  ·
                    refine ⟨11293904299510825867047773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7529269533007217244698515 11293904299510825867047773)
                    ·
                      refine ⟨4235214112316559700142915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11293904299510825867047773 4235214112316559700142915)
                      ·
                        rfl

theorem cell23_8248050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_8248050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248050 prefixEnd_8248050 := by exact prefixLift 8248050
  have htrace : WordTrace (prefixWord ++ tailWord_8248050) baseStart_8248050 baseEnd_8248050 := by
    simpa [prefixWord, tailWord_8248050, baseEnd_8248050] using wordTrace_append hprefix tailTrace_8248050
  have hstable : (prefixWord ++ tailWord_8248050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248050).length < 2 ^ (prefixWord ++ tailWord_8248050).sum := by decide
  have hdescent : baseEnd_8248050 < baseStart_8248050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248079 : List Nat := [1, 1, 2, 1, 1, 1, 6, 5, 5]
def baseStart_8248079 : Nat := 118140960795 + 8248079 * 2 ^ 59
def prefixEnd_8248079 : Nat := 4983230072969 + 3 ^ 40 * 8248079 * 2
def baseEnd_8248079 : Nat := 470581000361726676297809

theorem tailTrace_8248079 : CollatzResearch.WordTrace tailWord_8248079 prefixEnd_8248079 470581000361726676297809 := by
  unfold tailWord_8248079
  simp only [CollatzResearch.WordTrace]
  refine ⟨300832155485625917589179291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200554770323750611726119527 300832155485625917589179291)
  ·
    refine ⟨451248233228438876383768937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300832155485625917589179291 451248233228438876383768937)
    ·
      refine ⟨338436174921329157287826703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451248233228438876383768937 338436174921329157287826703)
      ·
        refine ⟨507654262381993735931740055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338436174921329157287826703 507654262381993735931740055)
        ·
          refine ⟨761481393572990603897610083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507654262381993735931740055 761481393572990603897610083)
          ·
            refine ⟨1142222090359485905846415125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761481393572990603897610083 1142222090359485905846415125)
            ·
              refine ⟨53541660485600901836550709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1142222090359485905846415125 53541660485600901836550709)
              ·
                refine ⟨5019530670525084547176629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53541660485600901836550709 5019530670525084547176629)
                ·
                  refine ⟨470581000361726676297809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5019530670525084547176629 470581000361726676297809)
                  ·
                    rfl

theorem cell23_8248079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 5].length) (baseStart_8248079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248079 prefixEnd_8248079 := by exact prefixLift 8248079
  have htrace : WordTrace (prefixWord ++ tailWord_8248079) baseStart_8248079 baseEnd_8248079 := by
    simpa [prefixWord, tailWord_8248079, baseEnd_8248079] using wordTrace_append hprefix tailTrace_8248079
  have hstable : (prefixWord ++ tailWord_8248079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248079).length < 2 ^ (prefixWord ++ tailWord_8248079).sum := by decide
  have hdescent : baseEnd_8248079 < baseStart_8248079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248096 : List Nat := [2, 1, 1, 5, 1, 3, 1, 4, 5]
def baseStart_8248096 : Nat := 118140960795 + 8248096 * 2 ^ 59
def prefixEnd_8248096 : Nat := 4983230072969 + 3 ^ 40 * 8248096 * 2
def baseEnd_8248096 : Nat := 470581970269629613351967

theorem tailTrace_8248096 : CollatzResearch.WordTrace tailWord_8248096 prefixEnd_8248096 470581970269629613351967 := by
  unfold tailWord_8248096
  simp only [CollatzResearch.WordTrace]
  refine ⟨150416387763282164746274071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200555183684376219661698761 150416387763282164746274071)
  ·
    refine ⟨225624581644923247119411107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150416387763282164746274071 225624581644923247119411107)
    ·
      refine ⟨338436872467384870679116661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225624581644923247119411107 338436872467384870679116661)
      ·
        refine ⟨31728456793817331626167187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338436872467384870679116661 31728456793817331626167187)
        ·
          refine ⟨47592685190725997439250781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31728456793817331626167187 47592685190725997439250781)
          ·
            refine ⟨17847256946522249039719043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47592685190725997439250781 17847256946522249039719043)
            ·
              refine ⟨26770885419783373559578565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17847256946522249039719043 26770885419783373559578565)
              ·
                refine ⟨5019541016209382542420981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26770885419783373559578565 5019541016209382542420981)
                ·
                  refine ⟨470581970269629613351967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5019541016209382542420981 470581970269629613351967)
                  ·
                    rfl

theorem cell23_8248096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 5].length) (baseStart_8248096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248096 prefixEnd_8248096 := by exact prefixLift 8248096
  have htrace : WordTrace (prefixWord ++ tailWord_8248096) baseStart_8248096 baseEnd_8248096 := by
    simpa [prefixWord, tailWord_8248096, baseEnd_8248096] using wordTrace_append hprefix tailTrace_8248096
  have hstable : (prefixWord ++ tailWord_8248096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248096).length < 2 ^ (prefixWord ++ tailWord_8248096).sum := by decide
  have hdescent : baseEnd_8248096 < baseStart_8248096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248126 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_8248126 : Nat := 118140960795 + 8248126 * 2 ^ 59
def prefixEnd_8248126 : Nat := 4983230072969 + 3 ^ 40 * 8248126 * 2
def baseEnd_8248126 : Nat := 1411751045615433800930855

theorem tailTrace_8248126 : CollatzResearch.WordTrace tailWord_8248126 prefixEnd_8248126 1411751045615433800930855 := by
  unfold tailWord_8248126
  simp only [CollatzResearch.WordTrace]
  refine ⟨37604233714556955577017529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200555913144303763077426821 37604233714556955577017529)
  ·
    refine ⟨28203175285917716682763147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37604233714556955577017529 28203175285917716682763147)
    ·
      refine ⟨42304762928876575024144721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28203175285917716682763147 42304762928876575024144721)
      ·
        refine ⟨31728572196657431268108541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42304762928876575024144721 31728572196657431268108541)
        ·
          refine ⟨11898214573746536725540703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31728572196657431268108541 11898214573746536725540703)
          ·
            refine ⟨17847321860619805088311055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11898214573746536725540703 17847321860619805088311055)
            ·
              refine ⟨26770982790929707632466583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17847321860619805088311055 26770982790929707632466583)
              ·
                refine ⟨40156474186394561448699875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26770982790929707632466583 40156474186394561448699875)
                ·
                  refine ⟨60234711279591842173049813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40156474186394561448699875 60234711279591842173049813)
                  ·
                    refine ⟨1411751045615433800930855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60234711279591842173049813 1411751045615433800930855)
                    ·
                      rfl

theorem cell23_8248126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_8248126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248126 prefixEnd_8248126 := by exact prefixLift 8248126
  have htrace : WordTrace (prefixWord ++ tailWord_8248126) baseStart_8248126 baseEnd_8248126 := by
    simpa [prefixWord, tailWord_8248126, baseEnd_8248126] using wordTrace_append hprefix tailTrace_8248126
  have hstable : (prefixWord ++ tailWord_8248126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248126).length < 2 ^ (prefixWord ++ tailWord_8248126).sum := by decide
  have hdescent : baseEnd_8248126 < baseStart_8248126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248146 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_8248146 : Nat := 118140960795 + 8248146 * 2 ^ 59
def prefixEnd_8248146 : Nat := 4983230072969 + 3 ^ 40 * 8248146 * 2
def baseEnd_8248146 : Nat := 4235263406459391324542473

theorem tailTrace_8248146 : CollatzResearch.WordTrace tailWord_8248146 prefixEnd_8248146 4235263406459391324542473 := by
  unfold tailWord_8248146
  simp only [CollatzResearch.WordTrace]
  refine ⟨75208649794095797007967073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200556399450922125354578861 75208649794095797007967073)
  ·
    refine ⟨56406487345571847755975305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75208649794095797007967073 56406487345571847755975305)
    ·
      refine ⟨42304865509178885816981479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56406487345571847755975305 42304865509178885816981479)
      ·
        refine ⟨63457298263768328725472219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42304865509178885816981479 63457298263768328725472219)
        ·
          refine ⟨95185947395652493088208329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63457298263768328725472219 95185947395652493088208329)
          ·
            refine ⟨71389460546739369816156247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95185947395652493088208329 71389460546739369816156247)
            ·
              refine ⟨107084190820109054724234371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71389460546739369816156247 107084190820109054724234371)
              ·
                refine ⟨160626286230163582086351557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107084190820109054724234371 160626286230163582086351557)
                ·
                  refine ⟨30117428668155671641190917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160626286230163582086351557 30117428668155671641190917)
                  ·
                    refine ⟨5647017875279188432723297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30117428668155671641190917 5647017875279188432723297)
                    ·
                      refine ⟨4235263406459391324542473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5647017875279188432723297 4235263406459391324542473)
                      ·
                        rfl

theorem cell23_8248146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_8248146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248146 prefixEnd_8248146 := by exact prefixLift 8248146
  have htrace : WordTrace (prefixWord ++ tailWord_8248146) baseStart_8248146 baseEnd_8248146 := by
    simpa [prefixWord, tailWord_8248146, baseEnd_8248146] using wordTrace_append hprefix tailTrace_8248146
  have hstable : (prefixWord ++ tailWord_8248146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248146).length < 2 ^ (prefixWord ++ tailWord_8248146).sum := by decide
  have hdescent : baseEnd_8248146 < baseStart_8248146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248213 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_8248213 : Nat := 118140960795 + 8248213 * 2 ^ 59
def prefixEnd_8248213 : Nat := 4983230072969 + 3 ^ 40 * 8248213 * 2
def baseEnd_8248213 : Nat := 4235297809663242562404665

theorem tailTrace_8248213 : CollatzResearch.WordTrace tailWord_8248213 prefixEnd_8248213 4235297809663242562404665 := by
  unfold tailWord_8248213
  simp only [CollatzResearch.WordTrace]
  refine ⟨300837042867140458474557293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200558028578093638983038195 300837042867140458474557293)
  ·
    refine ⟨112813891075177671927958985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300837042867140458474557293 112813891075177671927958985)
    ·
      refine ⟨84610418306383253945969239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112813891075177671927958985 84610418306383253945969239)
      ·
        refine ⟨126915627459574880918953859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84610418306383253945969239 126915627459574880918953859)
        ·
          refine ⟨190373441189362321378430789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126915627459574880918953859 190373441189362321378430789)
          ·
            refine ⟨35695020223005435258455773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190373441189362321378430789 35695020223005435258455773)
            ·
              refine ⟨13385632583627038221920915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35695020223005435258455773 13385632583627038221920915)
              ·
                refine ⟨20078448875440557332881373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13385632583627038221920915 20078448875440557332881373)
                ·
                  refine ⟨7529418328290208999830515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20078448875440557332881373 7529418328290208999830515)
                  ·
                    refine ⟨11294127492435313499745773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7529418328290208999830515 11294127492435313499745773)
                    ·
                      refine ⟨4235297809663242562404665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11294127492435313499745773 4235297809663242562404665)
                      ·
                        rfl

theorem cell23_8248213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_8248213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248213 prefixEnd_8248213 := by exact prefixLift 8248213
  have htrace : WordTrace (prefixWord ++ tailWord_8248213) baseStart_8248213 baseEnd_8248213 := by
    simpa [prefixWord, tailWord_8248213, baseEnd_8248213] using wordTrace_append hprefix tailTrace_8248213
  have hstable : (prefixWord ++ tailWord_8248213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248213).length < 2 ^ (prefixWord ++ tailWord_8248213).sum := by decide
  have hdescent : baseEnd_8248213 < baseStart_8248213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248220 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 6]
def baseStart_8248220 : Nat := 118140960795 + 8248220 * 2 ^ 59
def prefixEnd_8248220 : Nat := 4983230072969 + 3 ^ 40 * 8248220 * 2
def baseEnd_8248220 : Nat := 470589044891980448335237

theorem tailTrace_8248220 : CollatzResearch.WordTrace tailWord_8248220 prefixEnd_8248220 470589044891980448335237 := by
  unfold tailWord_8248220
  simp only [CollatzResearch.WordTrace]
  refine ⟨150418649089057549335031057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200558198785410065780041409 150418649089057549335031057)
  ·
    refine ⟨112813986816793162001273293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150418649089057549335031057 112813986816793162001273293)
    ·
      refine ⟨42305245056297435750477485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112813986816793162001273293 42305245056297435750477485)
      ·
        refine ⟨15864466896111538406429057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42305245056297435750477485 15864466896111538406429057)
        ·
          refine ⟨11898350172083653804821793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15864466896111538406429057 11898350172083653804821793)
          ·
            refine ⟨8923762629062740353616345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11898350172083653804821793 8923762629062740353616345)
            ·
              refine ⟨6692821971797055265212259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8923762629062740353616345 6692821971797055265212259)
              ·
                refine ⟨10039232957695582897818389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6692821971797055265212259 10039232957695582897818389)
                ·
                  refine ⟨470589044891980448335237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10039232957695582897818389 470589044891980448335237)
                  ·
                    rfl

theorem cell23_8248220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_8248220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248220 prefixEnd_8248220 := by exact prefixLift 8248220
  have htrace : WordTrace (prefixWord ++ tailWord_8248220) baseStart_8248220 baseEnd_8248220 := by
    simpa [prefixWord, tailWord_8248220, baseEnd_8248220] using wordTrace_append hprefix tailTrace_8248220
  have hstable : (prefixWord ++ tailWord_8248220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248220).length < 2 ^ (prefixWord ++ tailWord_8248220).sum := by decide
  have hdescent : baseEnd_8248220 < baseStart_8248220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248256 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 5]
def baseStart_8248256 : Nat := 118140960795 + 8248256 * 2 ^ 59
def prefixEnd_8248256 : Nat := 4983230072969 + 3 ^ 40 * 8248256 * 2
def baseEnd_8248256 : Nat := 4235319889331385894166967

theorem tailTrace_8248256 : CollatzResearch.WordTrace tailWord_8248256 prefixEnd_8248256 4235319889331385894166967 := by
  unfold tailWord_8248256
  simp only [CollatzResearch.WordTrace]
  refine ⟨150419305602992338409186311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200559074137323117878915081 150419305602992338409186311)
  ·
    refine ⟨225628958404488507613779467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150419305602992338409186311 225628958404488507613779467)
    ·
      refine ⟨338443437606732761420669201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225628958404488507613779467 338443437606732761420669201)
      ·
        refine ⟨253832578205049571065501901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338443437606732761420669201 253832578205049571065501901)
        ·
          refine ⟨95187216826893589149563213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253832578205049571065501901 95187216826893589149563213)
          ·
            refine ⟨35695206310085095931086205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95187216826893589149563213 35695206310085095931086205)
            ·
              refine ⟨13385702366281910974157327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35695206310085095931086205 13385702366281910974157327)
              ·
                refine ⟨20078553549422866461235991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13385702366281910974157327 20078553549422866461235991)
                ·
                  refine ⟨30117830324134299691853987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20078553549422866461235991 30117830324134299691853987)
                  ·
                    refine ⟨45176745486201449537780981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30117830324134299691853987 45176745486201449537780981)
                    ·
                      refine ⟨4235319889331385894166967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45176745486201449537780981 4235319889331385894166967)
                      ·
                        rfl

theorem cell23_8248256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_8248256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248256 prefixEnd_8248256 := by exact prefixLift 8248256
  have htrace : WordTrace (prefixWord ++ tailWord_8248256) baseStart_8248256 baseEnd_8248256 := by
    simpa [prefixWord, tailWord_8248256, baseEnd_8248256] using wordTrace_append hprefix tailTrace_8248256
  have hstable : (prefixWord ++ tailWord_8248256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248256).length < 2 ^ (prefixWord ++ tailWord_8248256).sum := by decide
  have hdescent : baseEnd_8248256 < baseStart_8248256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248264 : List Nat := [2, 1, 3, 1, 5, 2, 2, 2, 1, 1, 3]
def baseStart_8248264 : Nat := 118140960795 + 8248264 * 2 ^ 59
def prefixEnd_8248264 : Nat := 4983230072969 + 3 ^ 40 * 8248264 * 2
def baseEnd_8248264 : Nat := 4235323997176621862866931

theorem tailTrace_8248264 : CollatzResearch.WordTrace tailWord_8248264 prefixEnd_8248264 4235323997176621862866931 := by
  unfold tailWord_8248264
  simp only [CollatzResearch.WordTrace]
  refine ⟨150419451494977847092331923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200559268659970462789775897 150419451494977847092331923)
  ·
    refine ⟨225629177242466770638497885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150419451494977847092331923 225629177242466770638497885)
    ·
      refine ⟨84610941465925038989436707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225629177242466770638497885 84610941465925038989436707)
      ·
        refine ⟨126916412198887558484155061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84610941465925038989436707 126916412198887558484155061)
        ·
          refine ⟨11898413643645708607889537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126916412198887558484155061 11898413643645708607889537)
          ·
            refine ⟨8923810232734281455917153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11898413643645708607889537 8923810232734281455917153)
            ·
              refine ⟨6692857674550711091937865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8923810232734281455917153 6692857674550711091937865)
              ·
                refine ⟨5019643255913033318953399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6692857674550711091937865 5019643255913033318953399)
                ·
                  refine ⟨7529464883869549978430099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019643255913033318953399 7529464883869549978430099)
                  ·
                    refine ⟨11294197325804324967645149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7529464883869549978430099 11294197325804324967645149)
                    ·
                      refine ⟨4235323997176621862866931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11294197325804324967645149 4235323997176621862866931)
                      ·
                        rfl

theorem cell23_8248264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_8248264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248264 prefixEnd_8248264 := by exact prefixLift 8248264
  have htrace : WordTrace (prefixWord ++ tailWord_8248264) baseStart_8248264 baseEnd_8248264 := by
    simpa [prefixWord, tailWord_8248264, baseEnd_8248264] using wordTrace_append hprefix tailTrace_8248264
  have hstable : (prefixWord ++ tailWord_8248264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248264).length < 2 ^ (prefixWord ++ tailWord_8248264).sum := by decide
  have hdescent : baseEnd_8248264 < baseStart_8248264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248276 : List Nat := [2, 4, 1, 2, 1, 2, 3, 8]
def baseStart_8248276 : Nat := 118140960795 + 8248276 * 2 ^ 59
def prefixEnd_8248276 : Nat := 4983230072969 + 3 ^ 40 * 8248276 * 2
def baseEnd_8248276 : Nat := 156864079960906511700625

theorem tailTrace_8248276 : CollatzResearch.WordTrace tailWord_8248276 prefixEnd_8248276 156864079960906511700625 := by
  unfold tailWord_8248276
  simp only [CollatzResearch.WordTrace]
  refine ⟨150419670332956110117050341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200559560443941480156067121 150419670332956110117050341)
  ·
    refine ⟨28203688187429270646946939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150419670332956110117050341 28203688187429270646946939)
    ·
      refine ⟨42305532281143905970420409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28203688187429270646946939 42305532281143905970420409)
      ·
        refine ⟨31729149210857929477815307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42305532281143905970420409 31729149210857929477815307)
        ·
          refine ⟨47593723816286894216722961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31729149210857929477815307 47593723816286894216722961)
          ·
            refine ⟨35695292862215170662542221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47593723816286894216722961 35695292862215170662542221)
            ·
              refine ⟨13385734823330688998453333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35695292862215170662542221 13385734823330688998453333)
              ·
                refine ⟨156864079960906511700625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13385734823330688998453333 156864079960906511700625)
                ·
                  rfl

theorem cell23_8248276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 8].length) (baseStart_8248276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248276 prefixEnd_8248276 := by exact prefixLift 8248276
  have htrace : WordTrace (prefixWord ++ tailWord_8248276) baseStart_8248276 baseEnd_8248276 := by
    simpa [prefixWord, tailWord_8248276, baseEnd_8248276] using wordTrace_append hprefix tailTrace_8248276
  have hstable : (prefixWord ++ tailWord_8248276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248276).length < 2 ^ (prefixWord ++ tailWord_8248276).sum := by decide
  have hdescent : baseEnd_8248276 < baseStart_8248276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248289 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 4, 7]
def baseStart_8248289 : Nat := 118140960795 + 8248289 * 2 ^ 59
def prefixEnd_8248289 : Nat := 4983230072969 + 3 ^ 40 * 8248289 * 2
def baseEnd_8248289 : Nat := 1411778944730994755018105

theorem tailTrace_8248289 : CollatzResearch.WordTrace tailWord_8248289 prefixEnd_8248289 1411778944730994755018105 := by
  unfold tailWord_8248289
  simp only [CollatzResearch.WordTrace]
  refine ⟨300839814814865123454323921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200559876543243415636215947 300839814814865123454323921)
  ·
    refine ⟨225629861111148842590742941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300839814814865123454323921 225629861111148842590742941)
    ·
      refine ⟨84611197916680815971528603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225629861111148842590742941 84611197916680815971528603)
      ·
        refine ⟨126916796875021223957292905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84611197916680815971528603 126916796875021223957292905)
        ·
          refine ⟨95187597656265917967969679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126916796875021223957292905 95187597656265917967969679)
          ·
            refine ⟨142781396484398876951954519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95187597656265917967969679 142781396484398876951954519)
            ·
              refine ⟨214172094726598315427931779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142781396484398876951954519 214172094726598315427931779)
              ·
                refine ⟨321258142089897473141897669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214172094726598315427931779 321258142089897473141897669)
                ·
                  refine ⟨60235901641855776214105813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321258142089897473141897669 60235901641855776214105813)
                  ·
                    refine ⟨1411778944730994755018105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60235901641855776214105813 1411778944730994755018105)
                    ·
                      rfl

theorem cell23_8248289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_8248289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248289 prefixEnd_8248289 := by exact prefixLift 8248289
  have htrace : WordTrace (prefixWord ++ tailWord_8248289) baseStart_8248289 baseEnd_8248289 := by
    simpa [prefixWord, tailWord_8248289, baseEnd_8248289] using wordTrace_append hprefix tailTrace_8248289
  have hstable : (prefixWord ++ tailWord_8248289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248289).length < 2 ^ (prefixWord ++ tailWord_8248289).sum := by decide
  have hdescent : baseEnd_8248289 < baseStart_8248289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248290 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_8248290 : Nat := 118140960795 + 8248290 * 2 ^ 59
def prefixEnd_8248290 : Nat := 4983230072969 + 3 ^ 40 * 8248290 * 2
def baseEnd_8248290 : Nat := 4235337347673638761141811

theorem tailTrace_8248290 : CollatzResearch.WordTrace tailWord_8248290 prefixEnd_8248290 4235337347673638761141811 := by
  unfold tailWord_8248290
  simp only [CollatzResearch.WordTrace]
  refine ⟨75209962821965375156277581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200559900858574333750073549 75209962821965375156277581)
  ·
    refine ⟨28203736058237015683604093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75209962821965375156277581 28203736058237015683604093)
    ·
      refine ⟨10576401021838880881351535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28203736058237015683604093 10576401021838880881351535)
      ·
        refine ⟨15864601532758321322027303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10576401021838880881351535 15864601532758321322027303)
        ·
          refine ⟨23796902299137481983040955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15864601532758321322027303 23796902299137481983040955)
          ·
            refine ⟨35695353448706222974561433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23796902299137481983040955 35695353448706222974561433)
            ·
              refine ⟨26771515086529667230921075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35695353448706222974561433 26771515086529667230921075)
              ·
                refine ⟨40157272629794500846381613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26771515086529667230921075 40157272629794500846381613)
                ·
                  refine ⟨15058977236172937817393105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40157272629794500846381613 15058977236172937817393105)
                  ·
                    refine ⟨11294232927129703363044829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15058977236172937817393105 11294232927129703363044829)
                    ·
                      refine ⟨4235337347673638761141811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11294232927129703363044829 4235337347673638761141811)
                      ·
                        rfl

theorem cell23_8248290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_8248290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248290 prefixEnd_8248290 := by exact prefixLift 8248290
  have htrace : WordTrace (prefixWord ++ tailWord_8248290) baseStart_8248290 baseEnd_8248290 := by
    simpa [prefixWord, tailWord_8248290, baseEnd_8248290] using wordTrace_append hprefix tailTrace_8248290
  have hstable : (prefixWord ++ tailWord_8248290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248290).length < 2 ^ (prefixWord ++ tailWord_8248290).sum := by decide
  have hdescent : baseEnd_8248290 < baseStart_8248290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248346 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_8248346 : Nat := 118140960795 + 8248346 * 2 ^ 59
def prefixEnd_8248346 : Nat := 4983230072969 + 3 ^ 40 * 8248346 * 2
def baseEnd_8248346 : Nat := 4235366102590290542041553

theorem tailTrace_8248346 : CollatzResearch.WordTrace tailWord_8248346 prefixEnd_8248346 4235366102590290542041553 := by
  unfold tailWord_8248346
  simp only [CollatzResearch.WordTrace]
  refine ⟨75210473443914655547287223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200561262517105748126099261 75210473443914655547287223)
  ·
    refine ⟨112815710165871983320930835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75210473443914655547287223 112815710165871983320930835)
    ·
      refine ⟨169223565248807974981396253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112815710165871983320930835 169223565248807974981396253)
      ·
        refine ⟨63458836968302990618023595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169223565248807974981396253 63458836968302990618023595)
        ·
          refine ⟨95188255452454485927035393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63458836968302990618023595 95188255452454485927035393)
          ·
            refine ⟨71391191589340864445276545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95188255452454485927035393 71391191589340864445276545)
            ·
              refine ⟨53543393692005648333957409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71391191589340864445276545 53543393692005648333957409)
              ·
                refine ⟨40157545269004236250468057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53543393692005648333957409 40157545269004236250468057)
                ·
                  refine ⟨30118158951753177187851043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40157545269004236250468057 30118158951753177187851043)
                  ·
                    refine ⟨45177238427629765781776565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30118158951753177187851043 45177238427629765781776565)
                    ·
                      refine ⟨4235366102590290542041553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45177238427629765781776565 4235366102590290542041553)
                      ·
                        rfl

theorem cell23_8248346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_8248346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248346 prefixEnd_8248346 := by exact prefixLift 8248346
  have htrace : WordTrace (prefixWord ++ tailWord_8248346) baseStart_8248346 baseEnd_8248346 := by
    simpa [prefixWord, tailWord_8248346, baseEnd_8248346] using wordTrace_append hprefix tailTrace_8248346
  have hstable : (prefixWord ++ tailWord_8248346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248346).length < 2 ^ (prefixWord ++ tailWord_8248346).sum := by decide
  have hdescent : baseEnd_8248346 < baseStart_8248346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248396 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_8248396 : Nat := 118140960795 + 8248396 * 2 ^ 59
def prefixEnd_8248396 : Nat := 4983230072969 + 3 ^ 40 * 8248396 * 2
def baseEnd_8248396 : Nat := 1411797258874338448805441

theorem tailTrace_8248396 : CollatzResearch.WordTrace tailWord_8248396 prefixEnd_8248396 1411797258874338448805441 := by
  unfold tailWord_8248396
  simp only [CollatzResearch.WordTrace]
  refine ⟨150421858712738740364234521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200562478283651653818979361 150421858712738740364234521)
  ·
    refine ⟨112816394034554055273175891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150421858712738740364234521 112816394034554055273175891)
    ·
      refine ⟨169224591051831082909763837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112816394034554055273175891 169224591051831082909763837)
      ·
        refine ⟨63459221644436656091161439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169224591051831082909763837 63459221644436656091161439)
        ·
          refine ⟨95188832466654984136742159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63459221644436656091161439 95188832466654984136742159)
          ·
            refine ⟨142783248699982476205113239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95188832466654984136742159 142783248699982476205113239)
            ·
              refine ⟨214174873049973714307669859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142783248699982476205113239 214174873049973714307669859)
              ·
                refine ⟨321262309574960571461504789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214174873049973714307669859 321262309574960571461504789)
                ·
                  refine ⟨15059170761326276787258037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 321262309574960571461504789 15059170761326276787258037)
                  ·
                    refine ⟨1411797258874338448805441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15059170761326276787258037 1411797258874338448805441)
                    ·
                      rfl

theorem cell23_8248396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_8248396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248396 prefixEnd_8248396 := by exact prefixLift 8248396
  have htrace : WordTrace (prefixWord ++ tailWord_8248396) baseStart_8248396 baseEnd_8248396 := by
    simpa [prefixWord, tailWord_8248396, baseEnd_8248396] using wordTrace_append hprefix tailTrace_8248396
  have hstable : (prefixWord ++ tailWord_8248396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248396).length < 2 ^ (prefixWord ++ tailWord_8248396).sum := by decide
  have hdescent : baseEnd_8248396 < baseStart_8248396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248477 : List Nat := [1, 4, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_8248477 : Nat := 118140960795 + 8248477 * 2 ^ 59
def prefixEnd_8248477 : Nat := 4983230072969 + 3 ^ 40 * 8248477 * 2
def baseEnd_8248477 : Nat := 1411811122852009843167817

theorem tailTrace_8248477 : CollatzResearch.WordTrace tailWord_8248477 prefixEnd_8248477 1411811122852009843167817 := by
  unfold tailWord_8248477
  simp only [CollatzResearch.WordTrace]
  refine ⟨300846671738184031562167685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200564447825456021041445123 300846671738184031562167685)
  ·
    refine ⟨56408750950909505917906441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300846671738184031562167685 56408750950909505917906441)
    ·
      refine ⟨42306563213182129438429831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56408750950909505917906441 42306563213182129438429831)
      ·
        refine ⟨63459844819773194157644747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42306563213182129438429831 63459844819773194157644747)
        ·
          refine ⟨95189767229659791236467121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63459844819773194157644747 95189767229659791236467121)
          ·
            refine ⟨71392325422244843427350341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95189767229659791236467121 71392325422244843427350341)
            ·
              refine ⟨13386061016670908142628189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71392325422244843427350341 13386061016670908142628189)
              ·
                refine ⟨5019772881251590553485571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13386061016670908142628189 5019772881251590553485571)
                ·
                  refine ⟨7529659321877385830228357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019772881251590553485571 7529659321877385830228357)
                  ·
                    refine ⟨1411811122852009843167817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7529659321877385830228357 1411811122852009843167817)
                    ·
                      rfl

theorem cell23_8248477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_8248477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248477 prefixEnd_8248477 := by exact prefixLift 8248477
  have htrace : WordTrace (prefixWord ++ tailWord_8248477) baseStart_8248477 baseEnd_8248477 := by
    simpa [prefixWord, tailWord_8248477, baseEnd_8248477] using wordTrace_append hprefix tailTrace_8248477
  have hstable : (prefixWord ++ tailWord_8248477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248477).length < 2 ^ (prefixWord ++ tailWord_8248477).sum := by decide
  have hdescent : baseEnd_8248477 < baseStart_8248477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248490 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 8]
def baseStart_8248490 : Nat := 118140960795 + 8248490 * 2 ^ 59
def prefixEnd_8248490 : Nat := 4983230072969 + 3 ^ 40 * 8248490 * 2
def baseEnd_8248490 : Nat := 470604449311615330960099

theorem tailTrace_8248490 : CollatzResearch.WordTrace tailWord_8248490 prefixEnd_8248490 470604449311615330960099 := by
  unfold tailWord_8248490
  simp only [CollatzResearch.WordTrace]
  refine ⟨75211786471784233695597731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200564763924757956521593949 75211786471784233695597731)
  ·
    refine ⟨112817679707676350543396597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75211786471784233695597731 112817679707676350543396597)
    ·
      refine ⟨10576657472594657863443431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112817679707676350543396597 10576657472594657863443431)
      ·
        refine ⟨15864986208891986795165147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10576657472594657863443431 15864986208891986795165147)
        ·
          refine ⟨23797479313337980192747721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15864986208891986795165147 23797479313337980192747721)
          ·
            refine ⟨17848109485003485144560791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23797479313337980192747721 17848109485003485144560791)
            ·
              refine ⟨26772164227505227716841187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17848109485003485144560791 26772164227505227716841187)
              ·
                refine ⟨40158246341257841575261781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26772164227505227716841187 40158246341257841575261781)
                ·
                  refine ⟨470604449311615330960099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40158246341257841575261781 470604449311615330960099)
                  ·
                    rfl

theorem cell23_8248490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_8248490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248490 prefixEnd_8248490 := by exact prefixLift 8248490
  have htrace : WordTrace (prefixWord ++ tailWord_8248490) baseStart_8248490 baseEnd_8248490 := by
    simpa [prefixWord, tailWord_8248490, baseEnd_8248490] using wordTrace_append hprefix tailTrace_8248490
  have hstable : (prefixWord ++ tailWord_8248490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248490).length < 2 ^ (prefixWord ++ tailWord_8248490).sum := by decide
  have hdescent : baseEnd_8248490 < baseStart_8248490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248496 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_8248496 : Nat := 118140960795 + 8248496 * 2 ^ 59
def prefixEnd_8248496 : Nat := 4983230072969 + 3 ^ 40 * 8248496 * 2
def baseEnd_8248496 : Nat := 4235443124688464955165863

theorem tailTrace_8248496 : CollatzResearch.WordTrace tailWord_8248496 prefixEnd_8248496 4235443124688464955165863 := by
  unfold tailWord_8248496
  simp only [CollatzResearch.WordTrace]
  refine ⟨150423682362557598903554671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200564909816743465204739561 150423682362557598903554671)
  ·
    refine ⟨225635523543836398355332007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150423682362557598903554671 225635523543836398355332007)
    ·
      refine ⟨338453285315754597532998011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225635523543836398355332007 338453285315754597532998011)
      ·
        refine ⟨507679927973631896299497017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338453285315754597532998011 507679927973631896299497017)
        ·
          refine ⟨380759945980223922224622763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507679927973631896299497017 380759945980223922224622763)
          ·
            refine ⟨571139918970335883336934145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380759945980223922224622763 571139918970335883336934145)
            ·
              refine ⟨428354939227751912502700609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571139918970335883336934145 428354939227751912502700609)
              ·
                refine ⟨321266204420813934377025457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428354939227751912502700609 321266204420813934377025457)
                ·
                  refine ⟨240949653315610450782769093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321266204420813934377025457 240949653315610450782769093)
                  ·
                    refine ⟨45178059996676959521769205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240949653315610450782769093 45178059996676959521769205)
                    ·
                      refine ⟨4235443124688464955165863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45178059996676959521769205 4235443124688464955165863)
                      ·
                        rfl

theorem cell23_8248496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_8248496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248496 prefixEnd_8248496 := by exact prefixLift 8248496
  have htrace : WordTrace (prefixWord ++ tailWord_8248496) baseStart_8248496 baseEnd_8248496 := by
    simpa [prefixWord, tailWord_8248496, baseEnd_8248496] using wordTrace_append hprefix tailTrace_8248496
  have hstable : (prefixWord ++ tailWord_8248496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248496).length < 2 ^ (prefixWord ++ tailWord_8248496).sum := by decide
  have hdescent : baseEnd_8248496 < baseStart_8248496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248543 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_8248543 : Nat := 118140960795 + 8248543 * 2 ^ 59
def prefixEnd_8248543 : Nat := 4983230072969 + 3 ^ 40 * 8248543 * 2
def baseEnd_8248543 : Nat := 4235467258279226271278147

theorem tailTrace_8248543 : CollatzResearch.WordTrace tailWord_8248543 prefixEnd_8248543 4235467258279226271278147 := by
  unfold tailWord_8248543
  simp only [CollatzResearch.WordTrace]
  refine ⟨300849078955944924834070283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200566052637296616556046855 300849078955944924834070283)
  ·
    refine ⟨451273618433917387251105425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300849078955944924834070283 451273618433917387251105425)
    ·
      refine ⟨338455213825438040438329069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451273618433917387251105425 338455213825438040438329069)
      ·
        refine ⟨126920705184539265164373401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338455213825438040438329069 126920705184539265164373401)
        ·
          refine ⟨95190528888404448873280051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126920705184539265164373401 95190528888404448873280051)
          ·
            refine ⟨142785793332606673309920077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95190528888404448873280051 142785793332606673309920077)
            ·
              refine ⟨53544672499727502491220029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142785793332606673309920077 53544672499727502491220029)
              ·
                refine ⟨20079252187397813434207511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53544672499727502491220029 20079252187397813434207511)
                ·
                  refine ⟨30118878281096720151311267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20079252187397813434207511 30118878281096720151311267)
                  ·
                    refine ⟨45178317421645080226966901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30118878281096720151311267 45178317421645080226966901)
                    ·
                      refine ⟨4235467258279226271278147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45178317421645080226966901 4235467258279226271278147)
                      ·
                        rfl

theorem cell23_8248543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_8248543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248543 prefixEnd_8248543 := by exact prefixLift 8248543
  have htrace : WordTrace (prefixWord ++ tailWord_8248543) baseStart_8248543 baseEnd_8248543 := by
    simpa [prefixWord, tailWord_8248543, baseEnd_8248543] using wordTrace_append hprefix tailTrace_8248543
  have hstable : (prefixWord ++ tailWord_8248543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248543).length < 2 ^ (prefixWord ++ tailWord_8248543).sum := by decide
  have hdescent : baseEnd_8248543 < baseStart_8248543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248551 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_8248551 : Nat := 118140960795 + 8248551 * 2 ^ 59
def prefixEnd_8248551 : Nat := 4983230072969 + 3 ^ 40 * 8248551 * 2
def baseEnd_8248551 : Nat := 4235471366124462239978111

theorem tailTrace_8248551 : CollatzResearch.WordTrace tailWord_8248551 prefixEnd_8248551 4235471366124462239978111 := by
  unfold tailWord_8248551
  simp only [CollatzResearch.WordTrace]
  refine ⟨300849370739915942200361507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200566247159943961466907671 300849370739915942200361507)
  ·
    refine ⟨451274056109873913300542261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300849370739915942200361507 451274056109873913300542261)
    ·
      refine ⟨42306942760300679371925837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 451274056109873913300542261 42306942760300679371925837)
      ·
        refine ⟨15865103535112754764472189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42306942760300679371925837 15865103535112754764472189)
        ·
          refine ⟨5949413825667283036677071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15865103535112754764472189 5949413825667283036677071)
          ·
            refine ⟨8924120738500924555015607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949413825667283036677071 8924120738500924555015607)
            ·
              refine ⟨13386181107751386832523411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8924120738500924555015607 13386181107751386832523411)
              ·
                refine ⟨20079271661627080248785117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13386181107751386832523411 20079271661627080248785117)
                ·
                  refine ⟨7529726873110155093294419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20079271661627080248785117 7529726873110155093294419)
                  ·
                    refine ⟨11294590309665232639941629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7529726873110155093294419 11294590309665232639941629)
                    ·
                      refine ⟨4235471366124462239978111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11294590309665232639941629 4235471366124462239978111)
                      ·
                        rfl

theorem cell23_8248551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_8248551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248551 prefixEnd_8248551 := by exact prefixLift 8248551
  have htrace : WordTrace (prefixWord ++ tailWord_8248551) baseStart_8248551 baseEnd_8248551 := by
    simpa [prefixWord, tailWord_8248551, baseEnd_8248551] using wordTrace_append hprefix tailTrace_8248551
  have hstable : (prefixWord ++ tailWord_8248551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248551).length < 2 ^ (prefixWord ++ tailWord_8248551).sum := by decide
  have hdescent : baseEnd_8248551 < baseStart_8248551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248563 : List Nat := [1, 1, 1, 2, 2, 6, 2, 8]
def baseStart_8248563 : Nat := 118140960795 + 8248563 * 2 ^ 59
def prefixEnd_8248563 : Nat := 4983230072969 + 3 ^ 40 * 8248563 * 2
def baseEnd_8248563 : Nat := 156869538070085784926965

theorem tailTrace_8248563 : CollatzResearch.WordTrace tailWord_8248563 prefixEnd_8248563 156869538070085784926965 := by
  unfold tailWord_8248563
  simp only [CollatzResearch.WordTrace]
  refine ⟨300849808415872468249798343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200566538943914978833198895 300849808415872468249798343)
  ·
    refine ⟨451274712623808702374697515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300849808415872468249798343 451274712623808702374697515)
    ·
      refine ⟨676912068935713053562046273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451274712623808702374697515 676912068935713053562046273)
      ·
        refine ⟨507684051701784790171534705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676912068935713053562046273 507684051701784790171534705)
        ·
          refine ⟨380763038776338592628651029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507684051701784790171534705 380763038776338592628651029)
          ·
            refine ⟨17848267442640871529468017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 380763038776338592628651029 17848267442640871529468017)
            ·
              refine ⟨13386200581980653647101013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17848267442640871529468017 13386200581980653647101013)
              ·
                refine ⟨156869538070085784926965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13386200581980653647101013 156869538070085784926965)
                ·
                  rfl

theorem cell23_8248563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 8].length) (baseStart_8248563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248563 prefixEnd_8248563 := by exact prefixLift 8248563
  have htrace : WordTrace (prefixWord ++ tailWord_8248563) baseStart_8248563 baseEnd_8248563 := by
    simpa [prefixWord, tailWord_8248563, baseEnd_8248563] using wordTrace_append hprefix tailTrace_8248563
  have hstable : (prefixWord ++ tailWord_8248563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248563).length < 2 ^ (prefixWord ++ tailWord_8248563).sum := by decide
  have hdescent : baseEnd_8248563 < baseStart_8248563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248574 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_8248574 : Nat := 118140960795 + 8248574 * 2 ^ 59
def prefixEnd_8248574 : Nat := 4983230072969 + 3 ^ 40 * 8248574 * 2
def baseEnd_8248574 : Nat := 4235483176179515649990505

theorem tailTrace_8248574 : CollatzResearch.WordTrace tailWord_8248574 prefixEnd_8248574 4235483176179515649990505 := by
  unfold tailWord_8248574
  simp only [CollatzResearch.WordTrace]
  refine ⟨37606276202354077141056097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200566806412555078085632517 37606276202354077141056097)
  ·
    refine ⟨28204707151765557855792073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37606276202354077141056097 28204707151765557855792073)
    ·
      refine ⟨21153530363824168391844055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28204707151765557855792073 21153530363824168391844055)
      ·
        refine ⟨31730295545736252587766083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21153530363824168391844055 31730295545736252587766083)
        ·
          refine ⟨47595443318604378881649125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31730295545736252587766083 47595443318604378881649125)
          ·
            refine ⟨8924145622238321040309211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47595443318604378881649125 8924145622238321040309211)
            ·
              refine ⟨13386218433357481560463817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8924145622238321040309211 13386218433357481560463817)
              ·
                refine ⟨10039663825018111170347863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13386218433357481560463817 10039663825018111170347863)
                ·
                  refine ⟨15059495737527166755521795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10039663825018111170347863 15059495737527166755521795)
                  ·
                    refine ⟨22589243606290750133282693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15059495737527166755521795 22589243606290750133282693)
                    ·
                      refine ⟨4235483176179515649990505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22589243606290750133282693 4235483176179515649990505)
                      ·
                        rfl

theorem cell23_8248574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_8248574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248574 prefixEnd_8248574 := by exact prefixLift 8248574
  have htrace : WordTrace (prefixWord ++ tailWord_8248574) baseStart_8248574 baseEnd_8248574 := by
    simpa [prefixWord, tailWord_8248574, baseEnd_8248574] using wordTrace_append hprefix tailTrace_8248574
  have hstable : (prefixWord ++ tailWord_8248574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248574).length < 2 ^ (prefixWord ++ tailWord_8248574).sum := by decide
  have hdescent : baseEnd_8248574 < baseStart_8248574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248577 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_8248577 : Nat := 118140960795 + 8248577 * 2 ^ 59
def prefixEnd_8248577 : Nat := 4983230072969 + 3 ^ 40 * 8248577 * 2
def baseEnd_8248577 : Nat := 4235484716621479138252991

theorem tailTrace_8248577 : CollatzResearch.WordTrace tailWord_8248577 prefixEnd_8248577 4235484716621479138252991 := by
  unfold tailWord_8248577
  simp only [CollatzResearch.WordTrace]
  refine ⟨300850319037821748640807985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200566879358547832427205323 300850319037821748640807985)
  ·
    refine ⟨225637739278366311480605989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300850319037821748640807985 225637739278366311480605989)
    ·
      refine ⟨42307076114693683402613623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225637739278366311480605989 42307076114693683402613623)
      ·
        refine ⟨63460614172040525103920435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42307076114693683402613623 63460614172040525103920435)
        ·
          refine ⟨95190921258060787655880653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63460614172040525103920435 95190921258060787655880653)
          ·
            refine ⟨35696595471772795370955245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95190921258060787655880653 35696595471772795370955245)
            ·
              refine ⟨13386223301914798264108217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35696595471772795370955245 13386223301914798264108217)
              ·
                refine ⟨10039667476436098698081163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13386223301914798264108217 10039667476436098698081163)
                ·
                  refine ⟨15059501214654148047121745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10039667476436098698081163 15059501214654148047121745)
                  ·
                    refine ⟨11294625910990611035341309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15059501214654148047121745 11294625910990611035341309)
                    ·
                      refine ⟨4235484716621479138252991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11294625910990611035341309 4235484716621479138252991)
                      ·
                        rfl

theorem cell23_8248577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_8248577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248577 prefixEnd_8248577 := by exact prefixLift 8248577
  have htrace : WordTrace (prefixWord ++ tailWord_8248577) baseStart_8248577 baseEnd_8248577 := by
    simpa [prefixWord, tailWord_8248577, baseEnd_8248577] using wordTrace_append hprefix tailTrace_8248577
  have hstable : (prefixWord ++ tailWord_8248577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248577).length < 2 ^ (prefixWord ++ tailWord_8248577).sum := by decide
  have hdescent : baseEnd_8248577 < baseStart_8248577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248590 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_8248590 : Nat := 118140960795 + 8248590 * 2 ^ 59
def prefixEnd_8248590 : Nat := 4983230072969 + 3 ^ 40 * 8248590 * 2
def baseEnd_8248590 : Nat := 4235491391869987587390431

theorem tailTrace_8248590 : CollatzResearch.WordTrace tailWord_8248590 prefixEnd_8248590 4235491391869987587390431 := by
  unfold tailWord_8248590
  simp only [CollatzResearch.WordTrace]
  refine ⟨37606349148346831482628903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200567195457849767907354149 37606349148346831482628903)
  ·
    refine ⟨56409523722520247223943355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37606349148346831482628903 56409523722520247223943355)
    ·
      refine ⟨84614285583780370835915033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56409523722520247223943355 84614285583780370835915033)
      ·
        refine ⟨63460714187835278126936275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84614285583780370835915033 63460714187835278126936275)
        ·
          refine ⟨95191071281752917190404413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63460714187835278126936275 95191071281752917190404413)
          ·
            refine ⟨35696651730657343946401655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95191071281752917190404413 35696651730657343946401655)
            ·
              refine ⟨53544977595986015919602483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35696651730657343946401655 53544977595986015919602483)
              ·
                refine ⟨80317466393979023879403725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53544977595986015919602483 80317466393979023879403725)
                ·
                  refine ⟨30119049897742133954776397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80317466393979023879403725 30119049897742133954776397)
                  ·
                    refine ⟨11294643711653300233041149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30119049897742133954776397 11294643711653300233041149)
                    ·
                      refine ⟨4235491391869987587390431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11294643711653300233041149 4235491391869987587390431)
                      ·
                        rfl

theorem cell23_8248590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_8248590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248590 prefixEnd_8248590 := by exact prefixLift 8248590
  have htrace : WordTrace (prefixWord ++ tailWord_8248590) baseStart_8248590 baseEnd_8248590 := by
    simpa [prefixWord, tailWord_8248590, baseEnd_8248590] using wordTrace_append hprefix tailTrace_8248590
  have hstable : (prefixWord ++ tailWord_8248590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248590).length < 2 ^ (prefixWord ++ tailWord_8248590).sum := by decide
  have hdescent : baseEnd_8248590 < baseStart_8248590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248643 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 4]
def baseStart_8248643 : Nat := 118140960795 + 8248643 * 2 ^ 59
def prefixEnd_8248643 : Nat := 4983230072969 + 3 ^ 40 * 8248643 * 2
def baseEnd_8248643 : Nat := 4235518606344675880027687

theorem tailTrace_8248643 : CollatzResearch.WordTrace tailWord_8248643 prefixEnd_8248643 4235518606344675880027687 := by
  unfold tailWord_8248643
  simp only [CollatzResearch.WordTrace]
  refine ⟨300852726255582641912710583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200568484170388427941807055 300852726255582641912710583)
  ·
    refine ⟨451279089383373962869065875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300852726255582641912710583 451279089383373962869065875)
    ·
      refine ⟨676918634075060944303598813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451279089383373962869065875 676918634075060944303598813)
      ·
        refine ⟨253844487778147854113849555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 676918634075060944303598813 253844487778147854113849555)
        ·
          refine ⟨380766731667221781170774333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253844487778147854113849555 380766731667221781170774333)
          ·
            refine ⟨142787524375208167939040375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380766731667221781170774333 142787524375208167939040375)
            ·
              refine ⟨214181286562812251908560563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142787524375208167939040375 214181286562812251908560563)
              ·
                refine ⟨321271929844218377862840845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214181286562812251908560563 321271929844218377862840845)
                ·
                  refine ⟨120476973691581891698565317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321271929844218377862840845 120476973691581891698565317)
                  ·
                    refine ⟨22589432567171604693480997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120476973691581891698565317 22589432567171604693480997)
                    ·
                      refine ⟨4235518606344675880027687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22589432567171604693480997 4235518606344675880027687)
                      ·
                        rfl

theorem cell23_8248643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_8248643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248643 prefixEnd_8248643 := by exact prefixLift 8248643
  have htrace : WordTrace (prefixWord ++ tailWord_8248643) baseStart_8248643 baseEnd_8248643 := by
    simpa [prefixWord, tailWord_8248643, baseEnd_8248643] using wordTrace_append hprefix tailTrace_8248643
  have hstable : (prefixWord ++ tailWord_8248643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248643).length < 2 ^ (prefixWord ++ tailWord_8248643).sum := by decide
  have hdescent : baseEnd_8248643 < baseStart_8248643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248647 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_8248647 : Nat := 118140960795 + 8248647 * 2 ^ 59
def prefixEnd_8248647 : Nat := 4983230072969 + 3 ^ 40 * 8248647 * 2
def baseEnd_8248647 : Nat := 4235520660267293864377669

theorem tailTrace_8248647 : CollatzResearch.WordTrace tailWord_8248647 prefixEnd_8248647 4235520660267293864377669 := by
  unfold tailWord_8248647
  simp only [CollatzResearch.WordTrace]
  refine ⟨300852872147568150595856195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200568581431712100397237463 300852872147568150595856195)
  ·
    refine ⟨451279308221352225893784293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300852872147568150595856195 451279308221352225893784293)
    ·
      refine ⟨84614870291503542355084555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451279308221352225893784293 84614870291503542355084555)
      ·
        refine ⟨126922305437255313532626833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84614870291503542355084555 126922305437255313532626833)
        ·
          refine ⟨95191729077941485149470125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126922305437255313532626833 95191729077941485149470125)
          ·
            refine ⟨35696898404228056931051297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95191729077941485149470125 35696898404228056931051297)
            ·
              refine ⟨26772673803171042698288473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35696898404228056931051297 26772673803171042698288473)
              ·
                refine ⟨20079505352378282023716355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26772673803171042698288473 20079505352378282023716355)
                ·
                  refine ⟨30119258028567423035574533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20079505352378282023716355 30119258028567423035574533)
                  ·
                    refine ⟨5647360880356391819170225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30119258028567423035574533 5647360880356391819170225)
                    ·
                      refine ⟨4235520660267293864377669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5647360880356391819170225 4235520660267293864377669)
                      ·
                        rfl

theorem cell23_8248647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_8248647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248647 prefixEnd_8248647 := by exact prefixLift 8248647
  have htrace : WordTrace (prefixWord ++ tailWord_8248647) baseStart_8248647 baseEnd_8248647 := by
    simpa [prefixWord, tailWord_8248647, baseEnd_8248647] using wordTrace_append hprefix tailTrace_8248647
  have hstable : (prefixWord ++ tailWord_8248647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248647).length < 2 ^ (prefixWord ++ tailWord_8248647).sum := by decide
  have hdescent : baseEnd_8248647 < baseStart_8248647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248660 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_8248660 : Nat := 118140960795 + 8248660 * 2 ^ 59
def prefixEnd_8248660 : Nat := 4983230072969 + 3 ^ 40 * 8248660 * 2
def baseEnd_8248660 : Nat := 4235527335515802313515109

theorem tailTrace_8248660 : CollatzResearch.WordTrace tailWord_8248660 prefixEnd_8248660 4235527335515802313515109 := by
  unfold tailWord_8248660
  simp only [CollatzResearch.WordTrace]
  refine ⟨150426673148260526908039717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200568897531014035877386289 150426673148260526908039717)
  ·
    refine ⟨28205001215298848795257447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150426673148260526908039717 28205001215298848795257447)
    ·
      refine ⟨42307501822948273192886171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28205001215298848795257447 42307501822948273192886171)
      ·
        refine ⟨63461252734422409789329257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42307501822948273192886171 63461252734422409789329257)
        ·
          refine ⟨47595939550816807341996943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63461252734422409789329257 47595939550816807341996943)
          ·
            refine ⟨71393909326225211012995415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47595939550816807341996943 71393909326225211012995415)
            ·
              refine ⟨107090863989337816519493123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71393909326225211012995415 107090863989337816519493123)
              ·
                refine ⟨160636295984006724779239685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107090863989337816519493123 160636295984006724779239685)
                ·
                  refine ⟨30119305497001260896107441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160636295984006724779239685 30119305497001260896107441)
                  ·
                    refine ⟨22589479122750945672080581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30119305497001260896107441 22589479122750945672080581)
                    ·
                      refine ⟨4235527335515802313515109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22589479122750945672080581 4235527335515802313515109)
                      ·
                        rfl

theorem cell23_8248660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_8248660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248660 prefixEnd_8248660 := by exact prefixLift 8248660
  have htrace : WordTrace (prefixWord ++ tailWord_8248660) baseStart_8248660 baseEnd_8248660 := by
    simpa [prefixWord, tailWord_8248660, baseEnd_8248660] using wordTrace_append hprefix tailTrace_8248660
  have hstable : (prefixWord ++ tailWord_8248660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248660).length < 2 ^ (prefixWord ++ tailWord_8248660).sum := by decide
  have hdescent : baseEnd_8248660 < baseStart_8248660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248700 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_8248700 : Nat := 118140960795 + 8248700 * 2 ^ 59
def prefixEnd_8248700 : Nat := 4983230072969 + 3 ^ 40 * 8248700 * 2
def baseEnd_8248700 : Nat := 1411849291580660719004975

theorem tailTrace_8248700 : CollatzResearch.WordTrace tailWord_8248700 prefixEnd_8248700 1411849291580660719004975 := by
  unfold tailWord_8248700
  simp only [CollatzResearch.WordTrace]
  refine ⟨150427402608188070323767777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200569870144250760431690369 150427402608188070323767777)
  ·
    refine ⟨112820551956141052742825833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150427402608188070323767777 112820551956141052742825833)
    ·
      refine ⟨84615413967105789557119375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112820551956141052742825833 84615413967105789557119375)
      ·
        refine ⟨126923120950658684335679063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84615413967105789557119375 126923120950658684335679063)
        ·
          refine ⟨190384681425988026503518595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126923120950658684335679063 190384681425988026503518595)
          ·
            refine ⟨285577022138982039755277893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190384681425988026503518595 285577022138982039755277893)
            ·
              refine ⟨53545691651059132454114605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285577022138982039755277893 53545691651059132454114605)
              ·
                refine ⟨20079634369147174670292977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53545691651059132454114605 20079634369147174670292977)
                ·
                  refine ⟨15059725776860381002719733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20079634369147174670292977 15059725776860381002719733)
                  ·
                    refine ⟨1411849291580660719004975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15059725776860381002719733 1411849291580660719004975)
                    ·
                      rfl

theorem cell23_8248700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_8248700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248700 prefixEnd_8248700 := by exact prefixLift 8248700
  have htrace : WordTrace (prefixWord ++ tailWord_8248700) baseStart_8248700 baseEnd_8248700 := by
    simpa [prefixWord, tailWord_8248700, baseEnd_8248700] using wordTrace_append hprefix tailTrace_8248700
  have hstable : (prefixWord ++ tailWord_8248700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248700).length < 2 ^ (prefixWord ++ tailWord_8248700).sum := by decide
  have hdescent : baseEnd_8248700 < baseStart_8248700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248732 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_8248732 : Nat := 118140960795 + 8248732 * 2 ^ 59
def prefixEnd_8248732 : Nat := 4983230072969 + 3 ^ 40 * 8248732 * 2
def baseEnd_8248732 : Nat := 4235564306122926031814779

theorem tailTrace_8248732 : CollatzResearch.WordTrace tailWord_8248732 prefixEnd_8248732 4235564306122926031814779 := by
  unfold tailWord_8248732
  simp only [CollatzResearch.WordTrace]
  refine ⟨150427986176130105056350225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200570648234840140075133633 150427986176130105056350225)
  ·
    refine ⟨112820989632097578792262669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150427986176130105056350225 112820989632097578792262669)
    ·
      refine ⟨42307871112036592047098501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112820989632097578792262669 42307871112036592047098501)
      ·
        refine ⟨7932725833506861008830969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42307871112036592047098501 7932725833506861008830969)
        ·
          refine ⟨5949544375130145756623227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7932725833506861008830969 5949544375130145756623227)
          ·
            refine ⟨8924316562695218634934841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949544375130145756623227 8924316562695218634934841)
            ·
              refine ⟨6693237422021413976201131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8924316562695218634934841 6693237422021413976201131)
              ·
                refine ⟨10039856133032120964301697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693237422021413976201131 10039856133032120964301697)
                ·
                  refine ⟨7529892099774090723226273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10039856133032120964301697 7529892099774090723226273)
                  ·
                    refine ⟨5647419074830568042419705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7529892099774090723226273 5647419074830568042419705)
                    ·
                      refine ⟨4235564306122926031814779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5647419074830568042419705 4235564306122926031814779)
                      ·
                        rfl

theorem cell23_8248732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_8248732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248732 prefixEnd_8248732 := by exact prefixLift 8248732
  have htrace : WordTrace (prefixWord ++ tailWord_8248732) baseStart_8248732 baseEnd_8248732 := by
    simpa [prefixWord, tailWord_8248732, baseEnd_8248732] using wordTrace_append hprefix tailTrace_8248732
  have hstable : (prefixWord ++ tailWord_8248732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248732).length < 2 ^ (prefixWord ++ tailWord_8248732).sum := by decide
  have hdescent : baseEnd_8248732 < baseStart_8248732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248807 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 3, 5]
def baseStart_8248807 : Nat := 118140960795 + 8248807 * 2 ^ 59
def prefixEnd_8248807 : Nat := 4983230072969 + 3 ^ 40 * 8248807 * 2
def baseEnd_8248807 : Nat := 1411867605724004412792311

theorem tailTrace_8248807 : CollatzResearch.WordTrace tailWord_8248807 prefixEnd_8248807 1411867605724004412792311 := by
  unfold tailWord_8248807
  simp only [CollatzResearch.WordTrace]
  refine ⟨300858707826988497921680675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200572471884658998614453783 300858707826988497921680675)
  ·
    refine ⟨451288061740482746882521013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300858707826988497921680675 451288061740482746882521013)
    ·
      refine ⟨42308255788170257520236345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 451288061740482746882521013 42308255788170257520236345)
      ·
        refine ⟨31731191841127693140177259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42308255788170257520236345 31731191841127693140177259)
        ·
          refine ⟨47596787761691539710265889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31731191841127693140177259 47596787761691539710265889)
          ·
            refine ⟨35697590821268654782699417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47596787761691539710265889 35697590821268654782699417)
            ·
              refine ⟨26773193115951491087024563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35697590821268654782699417 26773193115951491087024563)
              ·
                refine ⟨40159789673927236630536845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26773193115951491087024563 40159789673927236630536845)
                ·
                  refine ⟨15059921127722713736451317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40159789673927236630536845 15059921127722713736451317)
                  ·
                    refine ⟨1411867605724004412792311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15059921127722713736451317 1411867605724004412792311)
                    ·
                      rfl

theorem cell23_8248807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_8248807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248807 prefixEnd_8248807 := by exact prefixLift 8248807
  have htrace : WordTrace (prefixWord ++ tailWord_8248807) baseStart_8248807 baseEnd_8248807 := by
    simpa [prefixWord, tailWord_8248807, baseEnd_8248807] using wordTrace_append hprefix tailTrace_8248807
  have hstable : (prefixWord ++ tailWord_8248807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248807).length < 2 ^ (prefixWord ++ tailWord_8248807).sum := by decide
  have hdescent : baseEnd_8248807 < baseStart_8248807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248814 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_8248814 : Nat := 118140960795 + 8248814 * 2 ^ 59
def prefixEnd_8248814 : Nat := 4983230072969 + 3 ^ 40 * 8248814 * 2
def baseEnd_8248814 : Nat := 4235606411536594710989401

theorem tailTrace_8248814 : CollatzResearch.WordTrace tailWord_8248814 prefixEnd_8248814 4235606411536594710989401 := by
  unfold tailWord_8248814
  simp only [CollatzResearch.WordTrace]
  refine ⟨37607370392245392264648187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200572642091975425411456997 37607370392245392264648187)
  ·
    refine ⟨56411055588368088396972281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37607370392245392264648187 56411055588368088396972281)
    ·
      refine ⟨42308291691276066297729211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56411055588368088396972281 42308291691276066297729211)
      ·
        refine ⟨63462437536914099446593817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42308291691276066297729211 63462437536914099446593817)
        ·
          refine ⟨47596828152685574584945363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63462437536914099446593817 47596828152685574584945363)
          ·
            refine ⟨71395242229028361877418045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47596828152685574584945363 71395242229028361877418045)
            ·
              refine ⟨26773215835885635704031767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71395242229028361877418045 26773215835885635704031767)
              ·
                refine ⟨40159823753828453556047651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26773215835885635704031767 40159823753828453556047651)
                ·
                  refine ⟨60239735630742680334071477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40159823753828453556047651 60239735630742680334071477)
                  ·
                    refine ⟨5647475215382126281319201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60239735630742680334071477 5647475215382126281319201)
                    ·
                      refine ⟨4235606411536594710989401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5647475215382126281319201 4235606411536594710989401)
                      ·
                        rfl

theorem cell23_8248814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_8248814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248814 prefixEnd_8248814 := by exact prefixLift 8248814
  have htrace : WordTrace (prefixWord ++ tailWord_8248814) baseStart_8248814 baseEnd_8248814 := by
    simpa [prefixWord, tailWord_8248814, baseEnd_8248814] using wordTrace_append hprefix tailTrace_8248814
  have hstable : (prefixWord ++ tailWord_8248814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248814).length < 2 ^ (prefixWord ++ tailWord_8248814).sum := by decide
  have hdescent : baseEnd_8248814 < baseStart_8248814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248824 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 1, 5]
def baseStart_8248824 : Nat := 118140960795 + 8248824 * 2 ^ 59
def prefixEnd_8248824 : Nat := 4983230072969 + 3 ^ 40 * 8248824 * 2
def baseEnd_8248824 : Nat := 1411870515447713223954785

theorem tailTrace_8248824 : CollatzResearch.WordTrace tailWord_8248824 prefixEnd_8248824 1411870515447713223954785 := by
  unfold tailWord_8248824
  simp only [CollatzResearch.WordTrace]
  refine ⟨150429663933963454912524763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200572885245284606550033017 150429663933963454912524763)
  ·
    refine ⟨225644495900945182368787145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150429663933963454912524763 225644495900945182368787145)
    ·
      refine ⟨169233371925708886776590359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225644495900945182368787145 169233371925708886776590359)
      ·
        refine ⟨253850057888563330164885539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169233371925708886776590359 253850057888563330164885539)
        ·
          refine ⟨380775086832844995247328309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253850057888563330164885539 380775086832844995247328309)
          ·
            refine ⟨35697664390579218304437029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380775086832844995247328309 35697664390579218304437029)
            ·
              refine ⟨6693312073233603432081943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35697664390579218304437029 6693312073233603432081943)
              ·
                refine ⟨10039968109850405148122915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693312073233603432081943 10039968109850405148122915)
                ·
                  refine ⟨15059952164775607722184373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10039968109850405148122915 15059952164775607722184373)
                  ·
                    refine ⟨1411870515447713223954785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15059952164775607722184373 1411870515447713223954785)
                    ·
                      rfl

theorem cell23_8248824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_8248824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248824 prefixEnd_8248824 := by exact prefixLift 8248824
  have htrace : WordTrace (prefixWord ++ tailWord_8248824) baseStart_8248824 baseEnd_8248824 := by
    simpa [prefixWord, tailWord_8248824, baseEnd_8248824] using wordTrace_append hprefix tailTrace_8248824
  have hstable : (prefixWord ++ tailWord_8248824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248824).length < 2 ^ (prefixWord ++ tailWord_8248824).sum := by decide
  have hdescent : baseEnd_8248824 < baseStart_8248824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248827 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 4]
def baseStart_8248827 : Nat := 118140960795 + 8248827 * 2 ^ 59
def prefixEnd_8248827 : Nat := 4983230072969 + 3 ^ 40 * 8248827 * 2
def baseEnd_8248827 : Nat := 4235613086785103160126841

theorem tailTrace_8248827 : CollatzResearch.WordTrace tailWord_8248827 prefixEnd_8248827 4235613086785103160126841 := by
  unfold tailWord_8248827
  simp only [CollatzResearch.WordTrace]
  refine ⟨300859437286916041337408735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200572958191277360891605823 300859437286916041337408735)
  ·
    refine ⟨451289155930374062006113103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300859437286916041337408735 451289155930374062006113103)
    ·
      refine ⟨676933733895561093009169655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451289155930374062006113103 676933733895561093009169655)
      ·
        refine ⟨1015400600843341639513754483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676933733895561093009169655 1015400600843341639513754483)
        ·
          refine ⟨1523100901265012459270631725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015400600843341639513754483 1523100901265012459270631725)
          ·
            refine ⟨571162837974379672226486897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1523100901265012459270631725 571162837974379672226486897)
            ·
              refine ⟨428372128480784754169865173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571162837974379672226486897 428372128480784754169865173)
              ·
                refine ⟨10039971761268392675856215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 428372128480784754169865173 10039971761268392675856215)
                ·
                  refine ⟨15059957641902589013784323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10039971761268392675856215 15059957641902589013784323)
                  ·
                    refine ⟨22589936462853883520676485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15059957641902589013784323 22589936462853883520676485)
                    ·
                      refine ⟨4235613086785103160126841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22589936462853883520676485 4235613086785103160126841)
                      ·
                        rfl

theorem cell23_8248827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 4].length) (baseStart_8248827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248827 prefixEnd_8248827 := by exact prefixLift 8248827
  have htrace : WordTrace (prefixWord ++ tailWord_8248827) baseStart_8248827 baseEnd_8248827 := by
    simpa [prefixWord, tailWord_8248827, baseEnd_8248827] using wordTrace_append hprefix tailTrace_8248827
  have hstable : (prefixWord ++ tailWord_8248827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248827).length < 2 ^ (prefixWord ++ tailWord_8248827).sum := by decide
  have hdescent : baseEnd_8248827 < baseStart_8248827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248861 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_8248861 : Nat := 118140960795 + 8248861 * 2 ^ 59
def prefixEnd_8248861 : Nat := 4983230072969 + 3 ^ 40 * 8248861 * 2
def baseEnd_8248861 : Nat := 4235630545127356027101685

theorem tailTrace_8248861 : CollatzResearch.WordTrace tailWord_8248861 prefixEnd_8248861 4235630545127356027101685 := by
  unfold tailWord_8248861
  simp only [CollatzResearch.WordTrace]
  refine ⟨300860677368792865144146437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200573784912528576762764291 300860677368792865144146437)
  ·
    refine ⟨56411377006648662214527457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300860677368792865144146437 56411377006648662214527457)
    ·
      refine ⟨42308532754986496660895593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56411377006648662214527457 42308532754986496660895593)
      ·
        refine ⟨31731399566239872495671695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42308532754986496660895593 31731399566239872495671695)
        ·
          refine ⟨47597099349359808743507543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31731399566239872495671695 47597099349359808743507543)
          ·
            refine ⟨71395649024039713115261315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47597099349359808743507543 71395649024039713115261315)
            ·
              refine ⟨107093473536059569672891973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71395649024039713115261315 107093473536059569672891973)
              ·
                refine ⟨20080026288011169313667245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107093473536059569672891973 20080026288011169313667245)
                ·
                  refine ⟨7530009858004188492625217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20080026288011169313667245 7530009858004188492625217)
                  ·
                    refine ⟨5647507393503141369468913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7530009858004188492625217 5647507393503141369468913)
                    ·
                      refine ⟨4235630545127356027101685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5647507393503141369468913 4235630545127356027101685)
                      ·
                        rfl

theorem cell23_8248861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_8248861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248861 prefixEnd_8248861 := by exact prefixLift 8248861
  have htrace : WordTrace (prefixWord ++ tailWord_8248861) baseStart_8248861 baseEnd_8248861 := by
    simpa [prefixWord, tailWord_8248861, baseEnd_8248861] using wordTrace_append hprefix tailTrace_8248861
  have hstable : (prefixWord ++ tailWord_8248861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248861).length < 2 ^ (prefixWord ++ tailWord_8248861).sum := by decide
  have hdescent : baseEnd_8248861 < baseStart_8248861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248867 : List Nat := [1, 1, 1, 4, 5, 1, 1, 9]
def baseStart_8248867 : Nat := 118140960795 + 8248867 * 2 ^ 59
def prefixEnd_8248867 : Nat := 4983230072969 + 3 ^ 40 * 8248867 * 2
def baseEnd_8248867 : Nat := 156875319481899370504691

theorem tailTrace_8248867 : CollatzResearch.WordTrace tailWord_8248867 prefixEnd_8248867 156875319481899370504691 := by
  unfold tailWord_8248867
  simp only [CollatzResearch.WordTrace]
  refine ⟨300860896206771128168864855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200573930804514085445909903 300860896206771128168864855)
  ·
    refine ⟨451291344310156692253297283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300860896206771128168864855 451291344310156692253297283)
    ·
      refine ⟨676937016465235038379945925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451291344310156692253297283 676937016465235038379945925)
      ·
        refine ⟨126925690587231569696239861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 676937016465235038379945925 126925690587231569696239861)
        ·
          refine ⟨11899283492552959659022487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126925690587231569696239861 11899283492552959659022487)
          ·
            refine ⟨17848925238829439488533731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11899283492552959659022487 17848925238829439488533731)
            ·
              refine ⟨26773387858244159232800597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17848925238829439488533731 26773387858244159232800597)
              ·
                refine ⟨156875319481899370504691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26773387858244159232800597 156875319481899370504691)
                ·
                  rfl

theorem cell23_8248867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 9].length) (baseStart_8248867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248867 prefixEnd_8248867 := by exact prefixLift 8248867
  have htrace : WordTrace (prefixWord ++ tailWord_8248867) baseStart_8248867 baseEnd_8248867 := by
    simpa [prefixWord, tailWord_8248867, baseEnd_8248867] using wordTrace_append hprefix tailTrace_8248867
  have hstable : (prefixWord ++ tailWord_8248867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248867).length < 2 ^ (prefixWord ++ tailWord_8248867).sum := by decide
  have hdescent : baseEnd_8248867 < baseStart_8248867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248872 : List Nat := [2, 1, 5, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_8248872 : Nat := 118140960795 + 8248872 * 2 ^ 59
def prefixEnd_8248872 : Nat := 4983230072969 + 3 ^ 40 * 8248872 * 2
def baseEnd_8248872 : Nat := 4235636193414555484064135

theorem tailTrace_8248872 : CollatzResearch.WordTrace tailWord_8248872 prefixEnd_8248872 4235636193414555484064135 := by
  unfold tailWord_8248872
  simp only [CollatzResearch.WordTrace]
  refine ⟨150430539285876507011398435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200574052381168676015197913 150430539285876507011398435)
  ·
    refine ⟨225645808928814760517097653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150430539285876507011398435 225645808928814760517097653)
    ·
      refine ⟨21154294587076383798477905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225645808928814760517097653 21154294587076383798477905)
      ·
        refine ⟨15865720940307287848858429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21154294587076383798477905 15865720940307287848858429)
        ·
          refine ⟨5949645352615232943321911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15865720940307287848858429 5949645352615232943321911)
          ·
            refine ⟨8924468028922849414982867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949645352615232943321911 8924468028922849414982867)
            ·
              refine ⟨13386702043384274122474301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8924468028922849414982867 13386702043384274122474301)
              ·
                refine ⟨5020013266269102795927863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13386702043384274122474301 5020013266269102795927863)
                ·
                  refine ⟨7530019899403654193891795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020013266269102795927863 7530019899403654193891795)
                  ·
                    refine ⟨11295029849105481290837693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7530019899403654193891795 11295029849105481290837693)
                    ·
                      refine ⟨4235636193414555484064135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11295029849105481290837693 4235636193414555484064135)
                      ·
                        rfl

theorem cell23_8248872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_8248872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248872 prefixEnd_8248872 := by exact prefixLift 8248872
  have htrace : WordTrace (prefixWord ++ tailWord_8248872) baseStart_8248872 baseEnd_8248872 := by
    simpa [prefixWord, tailWord_8248872, baseEnd_8248872] using wordTrace_append hprefix tailTrace_8248872
  have hstable : (prefixWord ++ tailWord_8248872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248872).length < 2 ^ (prefixWord ++ tailWord_8248872).sum := by decide
  have hdescent : baseEnd_8248872 < baseStart_8248872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248880 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 1, 9]
def baseStart_8248880 : Nat := 118140960795 + 8248880 * 2 ^ 59
def prefixEnd_8248880 : Nat := 4983230072969 + 3 ^ 40 * 8248880 * 2
def baseEnd_8248880 : Nat := 1411880100419930484254699

theorem tailTrace_8248880 : CollatzResearch.WordTrace tailWord_8248880 prefixEnd_8248880 1411880100419930484254699 := by
  unfold tailWord_8248880
  simp only [CollatzResearch.WordTrace]
  refine ⟨150430685177862015694544047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200574246903816020926058729 150430685177862015694544047)
  ·
    refine ⟨225646027766793023541816071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150430685177862015694544047 225646027766793023541816071)
    ·
      refine ⟨338469041650189535312724107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225646027766793023541816071 338469041650189535312724107)
      ·
        refine ⟨507703562475284302969086161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338469041650189535312724107 507703562475284302969086161)
        ·
          refine ⟨380777671856463227226814621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507703562475284302969086161 380777671856463227226814621)
          ·
            refine ⟨142791626946173710210055483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380777671856463227226814621 142791626946173710210055483)
            ·
              refine ⟨214187440419260565315083225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142791626946173710210055483 214187440419260565315083225)
              ·
                refine ⟨160640580314445423986312419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214187440419260565315083225 160640580314445423986312419)
                ·
                  refine ⟨240960870471668135979468629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160640580314445423986312419 240960870471668135979468629)
                  ·
                    refine ⟨1411880100419930484254699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 240960870471668135979468629 1411880100419930484254699)
                    ·
                      rfl

theorem cell23_8248880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_8248880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248880 prefixEnd_8248880 := by exact prefixLift 8248880
  have htrace : WordTrace (prefixWord ++ tailWord_8248880) baseStart_8248880 baseEnd_8248880 := by
    simpa [prefixWord, tailWord_8248880, baseEnd_8248880] using wordTrace_append hprefix tailTrace_8248880
  have hstable : (prefixWord ++ tailWord_8248880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248880).length < 2 ^ (prefixWord ++ tailWord_8248880).sum := by decide
  have hdescent : baseEnd_8248880 < baseStart_8248880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248895 : List Nat := [1, 1, 2, 2, 3, 4, 3, 2, 1, 2, 2]
def baseStart_8248895 : Nat := 118140960795 + 8248895 * 2 ^ 59
def prefixEnd_8248895 : Nat := 4983230072969 + 3 ^ 40 * 8248895 * 2
def baseEnd_8248895 : Nat := 4235648003469608894076529

theorem tailTrace_8248895 : CollatzResearch.WordTrace tailWord_8248895 prefixEnd_8248895 4235648003469608894076529 := by
  unfold tailWord_8248895
  simp only [CollatzResearch.WordTrace]
  refine ⟨300861917450669688950884139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200574611633779792633922759 300861917450669688950884139)
  ·
    refine ⟨451292876176004533426326209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300861917450669688950884139 451292876176004533426326209)
    ·
      refine ⟨338469657132003400069744657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451292876176004533426326209 338469657132003400069744657)
      ·
        refine ⟨253852242849002550052308493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338469657132003400069744657 253852242849002550052308493)
        ·
          refine ⟨95194591068375956269615685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253852242849002550052308493 95194591068375956269615685)
          ·
            refine ⟨17848985825320491800552941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95194591068375956269615685 17848985825320491800552941)
            ·
              refine ⟨6693369684495184425207353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17848985825320491800552941 6693369684495184425207353)
              ·
                refine ⟨5020027263371388318905515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6693369684495184425207353 5020027263371388318905515)
                ·
                  refine ⟨7530040895057082478358273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020027263371388318905515 7530040895057082478358273)
                  ·
                    refine ⟨5647530671292811858768705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7530040895057082478358273 5647530671292811858768705)
                    ·
                      refine ⟨4235648003469608894076529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5647530671292811858768705 4235648003469608894076529)
                      ·
                        rfl

theorem cell23_8248895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 2, 2].length) (baseStart_8248895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248895 prefixEnd_8248895 := by exact prefixLift 8248895
  have htrace : WordTrace (prefixWord ++ tailWord_8248895) baseStart_8248895 baseEnd_8248895 := by
    simpa [prefixWord, tailWord_8248895, baseEnd_8248895] using wordTrace_append hprefix tailTrace_8248895
  have hstable : (prefixWord ++ tailWord_8248895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248895).length < 2 ^ (prefixWord ++ tailWord_8248895).sum := by decide
  have hdescent : baseEnd_8248895 < baseStart_8248895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248897 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 2, 7]
def baseStart_8248897 : Nat := 118140960795 + 8248897 * 2 ^ 59
def prefixEnd_8248897 : Nat := 4983230072969 + 3 ^ 40 * 8248897 * 2
def baseEnd_8248897 : Nat := 1411883010143639295417173

theorem tailTrace_8248897 : CollatzResearch.WordTrace tailWord_8248897 prefixEnd_8248897 1411883010143639295417173 := by
  unfold tailWord_8248897
  simp only [CollatzResearch.WordTrace]
  refine ⟨300861990396662443292456945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200574660264441628861637963 300861990396662443292456945)
  ·
    refine ⟨225646492797496832469342709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300861990396662443292456945 225646492797496832469342709)
    ·
      refine ⟨21154358699765328044000879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225646492797496832469342709 21154358699765328044000879)
      ·
        refine ⟨31731538049647992066001319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21154358699765328044000879 31731538049647992066001319)
        ·
          refine ⟨47597307074471988099001979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31731538049647992066001319 47597307074471988099001979)
          ·
            refine ⟨71395960611707982148502969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47597307074471988099001979 71395960611707982148502969)
            ·
              refine ⟨53546970458780986611377227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71395960611707982148502969 53546970458780986611377227)
              ·
                refine ⟨80320455688171479917065841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53546970458780986611377227 80320455688171479917065841)
                ·
                  refine ⟨60240341766128609937799381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80320455688171479917065841 60240341766128609937799381)
                  ·
                    refine ⟨1411883010143639295417173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60240341766128609937799381 1411883010143639295417173)
                    ·
                      rfl

theorem cell23_8248897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_8248897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248897 prefixEnd_8248897 := by exact prefixLift 8248897
  have htrace : WordTrace (prefixWord ++ tailWord_8248897) baseStart_8248897 baseEnd_8248897 := by
    simpa [prefixWord, tailWord_8248897, baseEnd_8248897] using wordTrace_append hprefix tailTrace_8248897
  have hstable : (prefixWord ++ tailWord_8248897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248897).length < 2 ^ (prefixWord ++ tailWord_8248897).sum := by decide
  have hdescent : baseEnd_8248897 < baseStart_8248897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248937 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_8248937 : Nat := 118140960795 + 8248937 * 2 ^ 59
def prefixEnd_8248937 : Nat := 4983230072969 + 3 ^ 40 * 8248937 * 2
def baseEnd_8248937 : Nat := 4235669569657097729751335

theorem tailTrace_8248937 : CollatzResearch.WordTrace tailWord_8248937 prefixEnd_8248937 4235669569657097729751335 := by
  unfold tailWord_8248937
  simp only [CollatzResearch.WordTrace]
  refine ⟨300863449316517530123913065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200575632877678353415942043 300863449316517530123913065)
  ·
    refine ⟨225647586987388147592934799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300863449316517530123913065 225647586987388147592934799)
    ·
      refine ⟨338471380481082221389402199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225647586987388147592934799 338471380481082221389402199)
      ·
        refine ⟨507707070721623332084103299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338471380481082221389402199 507707070721623332084103299)
        ·
          refine ⟨761560606082434998126154949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507707070721623332084103299 761560606082434998126154949)
          ·
            refine ⟨142792613640456562148654053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 761560606082434998126154949 142792613640456562148654053)
            ·
              refine ⟨26773615057585605402872635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142792613640456562148654053 26773615057585605402872635)
              ·
                refine ⟨40160422586378408104308953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26773615057585605402872635 40160422586378408104308953)
                ·
                  refine ⟨30120316939783806078231715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40160422586378408104308953 30120316939783806078231715)
                  ·
                    refine ⟨45180475409675709117347573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30120316939783806078231715 45180475409675709117347573)
                    ·
                      refine ⟨4235669569657097729751335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45180475409675709117347573 4235669569657097729751335)
                      ·
                        rfl

theorem cell23_8248937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_8248937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248937 prefixEnd_8248937 := by exact prefixLift 8248937
  have htrace : WordTrace (prefixWord ++ tailWord_8248937) baseStart_8248937 baseEnd_8248937 := by
    simpa [prefixWord, tailWord_8248937, baseEnd_8248937] using wordTrace_append hprefix tailTrace_8248937
  have hstable : (prefixWord ++ tailWord_8248937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248937).length < 2 ^ (prefixWord ++ tailWord_8248937).sum := by decide
  have hdescent : baseEnd_8248937 < baseStart_8248937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248974 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_8248974 : Nat := 118140960795 + 8248974 * 2 ^ 59
def prefixEnd_8248974 : Nat := 4983230072969 + 3 ^ 40 * 8248974 * 2
def baseEnd_8248974 : Nat := 470632063160146009443185

theorem tailTrace_8248974 : CollatzResearch.WordTrace tailWord_8248974 prefixEnd_8248974 470632063160146009443185 := by
  unfold tailWord_8248974
  simp only [CollatzResearch.WordTrace]
  refine ⟨37608099852172935680376247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200576532544922323628673317 37608099852172935680376247)
  ·
    refine ⟨56412149778259403520564371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37608099852172935680376247 56412149778259403520564371)
    ·
      refine ⟨84618224667389105280846557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56412149778259403520564371 84618224667389105280846557)
      ·
        refine ⟨31731834250270914480317459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84618224667389105280846557 31731834250270914480317459)
        ·
          refine ⟨47597751375406371720476189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31731834250270914480317459 47597751375406371720476189)
          ·
            refine ⟨17849156765777389395178571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47597751375406371720476189 17849156765777389395178571)
            ·
              refine ⟨26773735148666084092767857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17849156765777389395178571 26773735148666084092767857)
              ·
                refine ⟨20080301361499563069575893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26773735148666084092767857 20080301361499563069575893)
                ·
                  refine ⟨470632063160146009443185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20080301361499563069575893 470632063160146009443185)
                  ·
                    rfl

theorem cell23_8248974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_8248974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248974 prefixEnd_8248974 := by exact prefixLift 8248974
  have htrace : WordTrace (prefixWord ++ tailWord_8248974) baseStart_8248974 baseEnd_8248974 := by
    simpa [prefixWord, tailWord_8248974, baseEnd_8248974] using wordTrace_append hprefix tailTrace_8248974
  have hstable : (prefixWord ++ tailWord_8248974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248974).length < 2 ^ (prefixWord ++ tailWord_8248974).sum := by decide
  have hdescent : baseEnd_8248974 < baseStart_8248974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8248997 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_8248997 : Nat := 118140960795 + 8248997 * 2 ^ 59
def prefixEnd_8248997 : Nat := 4983230072969 + 3 ^ 40 * 8248997 * 2
def baseEnd_8248997 : Nat := 4235700378496367495001059

theorem tailTrace_8248997 : CollatzResearch.WordTrace tailWord_8248997 prefixEnd_8248997 4235700378496367495001059 := by
  unfold tailWord_8248997
  simp only [CollatzResearch.WordTrace]
  refine ⟨300865637696300160371097245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200577091797533440247398163 300865637696300160371097245)
  ·
    refine ⟨112824614136112560139161467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300865637696300160371097245 112824614136112560139161467)
    ·
      refine ⟨169236921204168840208742201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112824614136112560139161467 169236921204168840208742201)
      ·
        refine ⟨126927690903126630156556651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169236921204168840208742201 126927690903126630156556651)
        ·
          refine ⟨190391536354689945234834977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126927690903126630156556651 190391536354689945234834977)
          ·
            refine ⟨142793652266017458926126233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190391536354689945234834977 142793652266017458926126233)
            ·
              refine ⟨107095239199513094194594675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142793652266017458926126233 107095239199513094194594675)
              ·
                refine ⟨160642858799269641291892013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107095239199513094194594675 160642858799269641291892013)
                ·
                  refine ⟨60241072049726115484459505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160642858799269641291892013 60241072049726115484459505)
                  ·
                    refine ⟨45180804037294586613344629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60241072049726115484459505 45180804037294586613344629)
                    ·
                      refine ⟨4235700378496367495001059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45180804037294586613344629 4235700378496367495001059)
                      ·
                        rfl

theorem cell23_8248997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_8248997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8248997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8248997 prefixEnd_8248997 := by exact prefixLift 8248997
  have htrace : WordTrace (prefixWord ++ tailWord_8248997) baseStart_8248997 baseEnd_8248997 := by
    simpa [prefixWord, tailWord_8248997, baseEnd_8248997] using wordTrace_append hprefix tailTrace_8248997
  have hstable : (prefixWord ++ tailWord_8248997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8248997).length < 2 ^ (prefixWord ++ tailWord_8248997).sum := by decide
  have hdescent : baseEnd_8248997 < baseStart_8248997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8248997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249047 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 10]
def baseStart_8249047 : Nat := 118140960795 + 8249047 * 2 ^ 59
def prefixEnd_8249047 : Nat := 4983230072969 + 3 ^ 40 * 8249047 * 2
def baseEnd_8249047 : Nat := 470636228058788033263981

theorem tailTrace_8249047 : CollatzResearch.WordTrace tailWord_8249047 prefixEnd_8249047 470636228058788033263981 := by
  unfold tailWord_8249047
  simp only [CollatzResearch.WordTrace]
  refine ⟨300867461346119018910417395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200578307564079345940278263 300867461346119018910417395)
  ·
    refine ⟨451301192019178528365626093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300867461346119018910417395 451301192019178528365626093)
    ·
      refine ⟨169237947007191948137109785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451301192019178528365626093 169237947007191948137109785)
      ·
        refine ⟨126928460255393961102832339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169237947007191948137109785 126928460255393961102832339)
        ·
          refine ⟨190392690383090941654248509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126928460255393961102832339 190392690383090941654248509)
          ·
            refine ⟨71397258893659103120343191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190392690383090941654248509 71397258893659103120343191)
            ·
              refine ⟨107095888340488654680514787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71397258893659103120343191 107095888340488654680514787)
              ·
                refine ⟨160643832510732982020772181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107095888340488654680514787 160643832510732982020772181)
                ·
                  refine ⟨470636228058788033263981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 160643832510732982020772181 470636228058788033263981)
                  ·
                    rfl

theorem cell23_8249047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 10].length) (baseStart_8249047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249047 prefixEnd_8249047 := by exact prefixLift 8249047
  have htrace : WordTrace (prefixWord ++ tailWord_8249047) baseStart_8249047 baseEnd_8249047 := by
    simpa [prefixWord, tailWord_8249047, baseEnd_8249047] using wordTrace_append hprefix tailTrace_8249047
  have hstable : (prefixWord ++ tailWord_8249047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249047).length < 2 ^ (prefixWord ++ tailWord_8249047).sum := by decide
  have hdescent : baseEnd_8249047 < baseStart_8249047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249061 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_8249061 : Nat := 118140960795 + 8249061 * 2 ^ 59
def prefixEnd_8249061 : Nat := 4983230072969 + 3 ^ 40 * 8249061 * 2
def baseEnd_8249061 : Nat := 4235733241258255244600765

theorem tailTrace_8249061 : CollatzResearch.WordTrace tailWord_8249061 prefixEnd_8249061 4235733241258255244600765 := by
  unfold tailWord_8249061
  simp only [CollatzResearch.WordTrace]
  refine ⟨300867971968068299301427037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200578647978712199534284691 300867971968068299301427037)
  ·
    refine ⟨112825489488025612238035139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300867971968068299301427037 112825489488025612238035139)
    ·
      refine ⟨169238234232038418357052709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112825489488025612238035139 169238234232038418357052709)
      ·
        refine ⟨31732168918507203441947383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169238234232038418357052709 31732168918507203441947383)
        ·
          refine ⟨47598253377760805162921075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31732168918507203441947383 47598253377760805162921075)
          ·
            refine ⟨71397380066641207744381613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47598253377760805162921075 71397380066641207744381613)
            ·
              refine ⟨26774017524990452904143105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71397380066641207744381613 26774017524990452904143105)
              ·
                refine ⟨20080513143742839678107329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26774017524990452904143105 20080513143742839678107329)
                ·
                  refine ⟨15060384857807129758580497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20080513143742839678107329 15060384857807129758580497)
                  ·
                    refine ⟨11295288643355347318935373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15060384857807129758580497 11295288643355347318935373)
                    ·
                      refine ⟨4235733241258255244600765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11295288643355347318935373 4235733241258255244600765)
                      ·
                        rfl

theorem cell23_8249061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_8249061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249061 prefixEnd_8249061 := by exact prefixLift 8249061
  have htrace : WordTrace (prefixWord ++ tailWord_8249061) baseStart_8249061 baseEnd_8249061 := by
    simpa [prefixWord, tailWord_8249061, baseEnd_8249061] using wordTrace_append hprefix tailTrace_8249061
  have hstable : (prefixWord ++ tailWord_8249061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249061).length < 2 ^ (prefixWord ++ tailWord_8249061).sum := by decide
  have hdescent : baseEnd_8249061 < baseStart_8249061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249064 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 8]
def baseStart_8249064 : Nat := 118140960795 + 8249064 * 2 ^ 59
def prefixEnd_8249064 : Nat := 4983230072969 + 3 ^ 40 * 8249064 * 2
def baseEnd_8249064 : Nat := 470637197966690970318139

theorem tailTrace_8249064 : CollatzResearch.WordTrace tailWord_8249064 prefixEnd_8249064 470637197966690970318139 := by
  unfold tailWord_8249064
  simp only [CollatzResearch.WordTrace]
  refine ⟨150434040693528715406893123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200578720924704953875857497 150434040693528715406893123)
  ·
    refine ⟨225651061040293073110339685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150434040693528715406893123 225651061040293073110339685)
    ·
      refine ⟨42309573945054951208188691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225651061040293073110339685 42309573945054951208188691)
      ·
        refine ⟨63464360917582426812283037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42309573945054951208188691 63464360917582426812283037)
        ·
          refine ⟨23799135344093410054606139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63464360917582426812283037 23799135344093410054606139)
          ·
            refine ⟨35698703016140115081909209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23799135344093410054606139 35698703016140115081909209)
            ·
              refine ⟨26774027262105086311431907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35698703016140115081909209 26774027262105086311431907)
              ·
                refine ⟨40161040893157629467147861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26774027262105086311431907 40161040893157629467147861)
                ·
                  refine ⟨470637197966690970318139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40161040893157629467147861 470637197966690970318139)
                  ·
                    rfl

theorem cell23_8249064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 8].length) (baseStart_8249064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249064 prefixEnd_8249064 := by exact prefixLift 8249064
  have htrace : WordTrace (prefixWord ++ tailWord_8249064) baseStart_8249064 baseEnd_8249064 := by
    simpa [prefixWord, tailWord_8249064, baseEnd_8249064] using wordTrace_append hprefix tailTrace_8249064
  have hstable : (prefixWord ++ tailWord_8249064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249064).length < 2 ^ (prefixWord ++ tailWord_8249064).sum := by decide
  have hdescent : baseEnd_8249064 < baseStart_8249064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249067 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 8]
def baseStart_8249067 : Nat := 118140960795 + 8249067 * 2 ^ 59
def prefixEnd_8249067 : Nat := 4983230072969 + 3 ^ 40 * 8249067 * 2
def baseEnd_8249067 : Nat := 4235736322142182221125737

theorem tailTrace_8249067 : CollatzResearch.WordTrace tailWord_8249067 prefixEnd_8249067 4235736322142182221125737 := by
  unfold tailWord_8249067
  simp only [CollatzResearch.WordTrace]
  refine ⟨300868190806046562326145455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200578793870697708217430303 300868190806046562326145455)
  ·
    refine ⟨451302286209069843489218183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300868190806046562326145455 451302286209069843489218183)
    ·
      refine ⟨676953429313604765233827275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451302286209069843489218183 676953429313604765233827275)
      ·
        refine ⟨1015430143970407147850740913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676953429313604765233827275 1015430143970407147850740913)
        ·
          refine ⟨761572607977805360888055685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015430143970407147850740913 761572607977805360888055685)
          ·
            refine ⟨142794863995838505166510441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 761572607977805360888055685 142794863995838505166510441)
            ·
              refine ⟨107096147996878878874882831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142794863995838505166510441 107096147996878878874882831)
              ·
                refine ⟨160644221995318318312324247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107096147996878878874882831 160644221995318318312324247)
                ·
                  refine ⟨240966332992977477468486371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160644221995318318312324247 240966332992977477468486371)
                  ·
                    refine ⟨361449499489466216202729557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 240966332992977477468486371 361449499489466216202729557)
                    ·
                      refine ⟨4235736322142182221125737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 361449499489466216202729557 4235736322142182221125737)
                      ·
                        rfl

theorem cell23_8249067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_8249067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249067 prefixEnd_8249067 := by exact prefixLift 8249067
  have htrace : WordTrace (prefixWord ++ tailWord_8249067) baseStart_8249067 baseEnd_8249067 := by
    simpa [prefixWord, tailWord_8249067, baseEnd_8249067] using wordTrace_append hprefix tailTrace_8249067
  have hstable : (prefixWord ++ tailWord_8249067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249067).length < 2 ^ (prefixWord ++ tailWord_8249067).sum := by decide
  have hdescent : baseEnd_8249067 < baseStart_8249067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249091 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 3]
def baseStart_8249091 : Nat := 118140960795 + 8249091 * 2 ^ 59
def prefixEnd_8249091 : Nat := 4983230072969 + 3 ^ 40 * 8249091 * 2
def baseEnd_8249091 : Nat := 4235748645677890127225627

theorem tailTrace_8249091 : CollatzResearch.WordTrace tailWord_8249091 prefixEnd_8249091 4235748645677890127225627 := by
  unfold tailWord_8249091
  simp only [CollatzResearch.WordTrace]
  refine ⟨300869066157959614425019127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200579377438639742950012751 300869066157959614425019127)
  ·
    refine ⟨451303599236939421637528691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300869066157959614425019127 451303599236939421637528691)
    ·
      refine ⟨676955398855409132456293037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451303599236939421637528691 676955398855409132456293037)
      ·
        refine ⟨253858274570778424671109889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 676955398855409132456293037 253858274570778424671109889)
        ·
          refine ⟨190393705928083818503332417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253858274570778424671109889 190393705928083818503332417)
          ·
            refine ⟨142795279446062863877499313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190393705928083818503332417 142795279446062863877499313)
            ·
              refine ⟨107096459584547147908124485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142795279446062863877499313 107096459584547147908124485)
              ·
                refine ⟨20080586172102590232773341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107096459584547147908124485 20080586172102590232773341)
                ·
                  refine ⟨7530219814538471337290003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20080586172102590232773341 7530219814538471337290003)
                  ·
                    refine ⟨11295329721807707005935005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7530219814538471337290003 11295329721807707005935005)
                    ·
                      refine ⟨4235748645677890127225627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11295329721807707005935005 4235748645677890127225627)
                      ·
                        rfl

theorem cell23_8249091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_8249091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249091 prefixEnd_8249091 := by exact prefixLift 8249091
  have htrace : WordTrace (prefixWord ++ tailWord_8249091) baseStart_8249091 baseEnd_8249091 := by
    simpa [prefixWord, tailWord_8249091, baseEnd_8249091] using wordTrace_append hprefix tailTrace_8249091
  have hstable : (prefixWord ++ tailWord_8249091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249091).length < 2 ^ (prefixWord ++ tailWord_8249091).sum := by decide
  have hdescent : baseEnd_8249091 < baseStart_8249091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249125 : List Nat := [1, 3, 1, 2, 3, 3, 1, 4, 1, 1, 3]
def baseStart_8249125 : Nat := 118140960795 + 8249125 * 2 ^ 59
def prefixEnd_8249125 : Nat := 4983230072969 + 3 ^ 40 * 8249125 * 2
def baseEnd_8249125 : Nat := 4235766104020142994200471

theorem tailTrace_8249125 : CollatzResearch.WordTrace tailWord_8249125 prefixEnd_8249125 4235766104020142994200471 := by
  unfold tailWord_8249125
  simp only [CollatzResearch.WordTrace]
  refine ⟨300870306239836438231756829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200580204159890958821171219 300870306239836438231756829)
  ·
    refine ⟨112826364839938664336908811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300870306239836438231756829 112826364839938664336908811)
    ·
      refine ⟨169239547259907996505363217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112826364839938664336908811 169239547259907996505363217)
      ·
        refine ⟨126929660444930997379022413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169239547259907996505363217 126929660444930997379022413)
        ·
          refine ⟨47598622666849124017133405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126929660444930997379022413 47598622666849124017133405)
          ·
            refine ⟨17849483500068421506425027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47598622666849124017133405 17849483500068421506425027)
            ·
              refine ⟨26774225250102632259637541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17849483500068421506425027 26774225250102632259637541)
              ·
                refine ⟨5020167234394243548682039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26774225250102632259637541 5020167234394243548682039)
                ·
                  refine ⟨7530250851591365323023059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020167234394243548682039 7530250851591365323023059)
                  ·
                    refine ⟨11295376277387047984534589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7530250851591365323023059 11295376277387047984534589)
                    ·
                      refine ⟨4235766104020142994200471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11295376277387047984534589 4235766104020142994200471)
                      ·
                        rfl

theorem cell23_8249125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_8249125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249125 prefixEnd_8249125 := by exact prefixLift 8249125
  have htrace : WordTrace (prefixWord ++ tailWord_8249125) baseStart_8249125 baseEnd_8249125 := by
    simpa [prefixWord, tailWord_8249125, baseEnd_8249125] using wordTrace_append hprefix tailTrace_8249125
  have hstable : (prefixWord ++ tailWord_8249125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249125).length < 2 ^ (prefixWord ++ tailWord_8249125).sum := by decide
  have hdescent : baseEnd_8249125 < baseStart_8249125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249148 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_8249148 : Nat := 118140960795 + 8249148 * 2 ^ 59
def prefixEnd_8249148 : Nat := 4983230072969 + 3 ^ 40 * 8249148 * 2
def baseEnd_8249148 : Nat := 4235777914075196404212865

theorem tailTrace_8249148 : CollatzResearch.WordTrace tailWord_8249148 prefixEnd_8249148 4235777914075196404212865 := by
  unfold tailWord_8249148
  simp only [CollatzResearch.WordTrace]
  refine ⟨150435572559376556579922049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200580763412502075439896065 150435572559376556579922049)
  ·
    refine ⟨112826679419532417434941537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150435572559376556579922049 112826679419532417434941537)
    ·
      refine ⟨84620009564649313076206153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112826679419532417434941537 84620009564649313076206153)
      ·
        refine ⟨63465007173486984807154615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84620009564649313076206153 63465007173486984807154615)
        ·
          refine ⟨95197510760230477210731923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63465007173486984807154615 95197510760230477210731923)
          ·
            refine ⟨142796266140345715816097885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95197510760230477210731923 142796266140345715816097885)
            ·
              refine ⟨53548599802629643431036707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142796266140345715816097885 53548599802629643431036707)
              ·
                refine ⟨80322899703944465146555061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53548599802629643431036707 80322899703944465146555061)
                ·
                  refine ⟨7530271847244793607489537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80322899703944465146555061 7530271847244793607489537)
                  ·
                    refine ⟨5647703885433595205617153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7530271847244793607489537 5647703885433595205617153)
                    ·
                      refine ⟨4235777914075196404212865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5647703885433595205617153 4235777914075196404212865)
                      ·
                        rfl

theorem cell23_8249148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_8249148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249148 prefixEnd_8249148 := by exact prefixLift 8249148
  have htrace : WordTrace (prefixWord ++ tailWord_8249148) baseStart_8249148 baseEnd_8249148 := by
    simpa [prefixWord, tailWord_8249148, baseEnd_8249148] using wordTrace_append hprefix tailTrace_8249148
  have hstable : (prefixWord ++ tailWord_8249148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249148).length < 2 ^ (prefixWord ++ tailWord_8249148).sum := by decide
  have hdescent : baseEnd_8249148 < baseStart_8249148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249165 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_8249165 : Nat := 118140960795 + 8249165 * 2 ^ 59
def prefixEnd_8249165 : Nat := 4983230072969 + 3 ^ 40 * 8249165 * 2
def baseEnd_8249165 : Nat := 4235786643246322837700287

theorem tailTrace_8249165 : CollatzResearch.WordTrace tailWord_8249165 prefixEnd_8249165 4235786643246322837700287 := by
  unfold tailWord_8249165
  simp only [CollatzResearch.WordTrace]
  refine ⟨300871765159691525063212949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200581176773127683375475299 300871765159691525063212949)
  ·
    refine ⟨14103363991860540237338107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 300871765159691525063212949 14103363991860540237338107)
    ·
      refine ⟨21155045987790810356007161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14103363991860540237338107 21155045987790810356007161)
      ·
        refine ⟨15866284490843107767005371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21155045987790810356007161 15866284490843107767005371)
        ·
          refine ⟨23799426736264661650508057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15866284490843107767005371 23799426736264661650508057)
          ·
            refine ⟨17849570052198496237881043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23799426736264661650508057 17849570052198496237881043)
            ·
              refine ⟨26774355078297744356821565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17849570052198496237881043 26774355078297744356821565)
              ·
                refine ⟨10040383154361654133808087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26774355078297744356821565 10040383154361654133808087)
                ·
                  refine ⟨15060574731542481200712131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10040383154361654133808087 15060574731542481200712131)
                  ·
                    refine ⟨22590862097313721801068197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15060574731542481200712131 22590862097313721801068197)
                    ·
                      refine ⟨4235786643246322837700287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22590862097313721801068197 4235786643246322837700287)
                      ·
                        rfl

theorem cell23_8249165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_8249165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249165 prefixEnd_8249165 := by exact prefixLift 8249165
  have htrace : WordTrace (prefixWord ++ tailWord_8249165) baseStart_8249165 baseEnd_8249165 := by
    simpa [prefixWord, tailWord_8249165, baseEnd_8249165] using wordTrace_append hprefix tailTrace_8249165
  have hstable : (prefixWord ++ tailWord_8249165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249165).length < 2 ^ (prefixWord ++ tailWord_8249165).sum := by decide
  have hdescent : baseEnd_8249165 < baseStart_8249165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249175 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 2, 4]
def baseStart_8249175 : Nat := 118140960795 + 8249175 * 2 ^ 59
def prefixEnd_8249175 : Nat := 4983230072969 + 3 ^ 40 * 8249175 * 2
def baseEnd_8249175 : Nat := 1411930592684289266191747

theorem tailTrace_8249175 : CollatzResearch.WordTrace tailWord_8249175 prefixEnd_8249175 1411930592684289266191747 := by
  unfold tailWord_8249175
  simp only [CollatzResearch.WordTrace]
  refine ⟨300872129889655296771076979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200581419926436864514051319 300872129889655296771076979)
  ·
    refine ⟨451308194834482945156615469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300872129889655296771076979 451308194834482945156615469)
    ·
      refine ⟨169240573062931104433730801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451308194834482945156615469 169240573062931104433730801)
      ·
        refine ⟨126930429797198328325298101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169240573062931104433730801 126930429797198328325298101)
        ·
          refine ⟨11899727793487343280496697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126930429797198328325298101 11899727793487343280496697)
          ·
            refine ⟨8924795845115507460372523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11899727793487343280496697 8924795845115507460372523)
            ·
              refine ⟨13387193767673261190558785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8924795845115507460372523 13387193767673261190558785)
              ·
                refine ⟨10040395325754945892919089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13387193767673261190558785 10040395325754945892919089)
                ·
                  refine ⟨7530296494316209419689317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10040395325754945892919089 7530296494316209419689317)
                  ·
                    refine ⟨1411930592684289266191747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7530296494316209419689317 1411930592684289266191747)
                    ·
                      rfl

theorem cell23_8249175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_8249175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249175 prefixEnd_8249175 := by exact prefixLift 8249175
  have htrace : WordTrace (prefixWord ++ tailWord_8249175) baseStart_8249175 baseEnd_8249175 := by
    simpa [prefixWord, tailWord_8249175, baseEnd_8249175] using wordTrace_append hprefix tailTrace_8249175
  have hstable : (prefixWord ++ tailWord_8249175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249175).length < 2 ^ (prefixWord ++ tailWord_8249175).sum := by decide
  have hdescent : baseEnd_8249175 < baseStart_8249175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249249 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_8249249 : Nat := 118140960795 + 8249249 * 2 ^ 59
def prefixEnd_8249249 : Nat := 4983230072969 + 3 ^ 40 * 8249249 * 2
def baseEnd_8249249 : Nat := 4235829775621300509049901

theorem tailTrace_8249249 : CollatzResearch.WordTrace tailWord_8249249 prefixEnd_8249249 4235829775621300509049901 := by
  unfold tailWord_8249249
  simp only [CollatzResearch.WordTrace]
  refine ⟨300874828891387207409270801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200583219260924804939513867 300874828891387207409270801)
  ·
    refine ⟨225656121668540405556953101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300874828891387207409270801 225656121668540405556953101)
    ·
      refine ⟨84621045625702652083857413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225656121668540405556953101 84621045625702652083857413)
      ·
        refine ⟨15866446054819247265723265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84621045625702652083857413 15866446054819247265723265)
        ·
          refine ⟨11899834541114435449292449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15866446054819247265723265 11899834541114435449292449)
          ·
            refine ⟨8924875905835826586969337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11899834541114435449292449 8924875905835826586969337)
            ·
              refine ⟨6693656929376869940227003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8924875905835826586969337 6693656929376869940227003)
              ·
                refine ⟨10040485394065304910340505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693656929376869940227003 10040485394065304910340505)
                ·
                  refine ⟨7530364045548978682755379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10040485394065304910340505 7530364045548978682755379)
                  ·
                    refine ⟨11295546068323468024133069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7530364045548978682755379 11295546068323468024133069)
                    ·
                      refine ⟨4235829775621300509049901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11295546068323468024133069 4235829775621300509049901)
                      ·
                        rfl

theorem cell23_8249249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_8249249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249249 prefixEnd_8249249 := by exact prefixLift 8249249
  have htrace : WordTrace (prefixWord ++ tailWord_8249249) baseStart_8249249 baseEnd_8249249 := by
    simpa [prefixWord, tailWord_8249249, baseEnd_8249249] using wordTrace_append hprefix tailTrace_8249249
  have hstable : (prefixWord ++ tailWord_8249249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249249).length < 2 ^ (prefixWord ++ tailWord_8249249).sum := by decide
  have hdescent : baseEnd_8249249 < baseStart_8249249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249264 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_8249264 : Nat := 118140960795 + 8249264 * 2 ^ 59
def prefixEnd_8249264 : Nat := 4983230072969 + 3 ^ 40 * 8249264 * 2
def baseEnd_8249264 : Nat := 4235837477831117950362331

theorem tailTrace_8249264 : CollatzResearch.WordTrace tailWord_8249264 prefixEnd_8249264 4235837477831117950362331 := by
  unfold tailWord_8249264
  simp only [CollatzResearch.WordTrace]
  refine ⟨150437687993166432485533423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200583583990888576647377897 150437687993166432485533423)
  ·
    refine ⟨225656531989749648728300135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150437687993166432485533423 225656531989749648728300135)
    ·
      refine ⟨338484797984624473092450203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225656531989749648728300135 338484797984624473092450203)
      ·
        refine ⟨507727196976936709638675305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338484797984624473092450203 507727196976936709638675305)
        ·
          refine ⟨380795397732702532229006479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507727196976936709638675305 380795397732702532229006479)
          ·
            refine ⟨571193096599053798343509719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380795397732702532229006479 571193096599053798343509719)
            ·
              refine ⟨856789644898580697515264579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571193096599053798343509719 856789644898580697515264579)
              ·
                refine ⟨1285184467347871046272896869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856789644898580697515264579 1285184467347871046272896869)
                ·
                  refine ⟨240972087627725821176168163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285184467347871046272896869 240972087627725821176168163)
                  ·
                    refine ⟨361458131441588731764252245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 240972087627725821176168163 361458131441588731764252245)
                    ·
                      refine ⟨4235837477831117950362331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 361458131441588731764252245 4235837477831117950362331)
                      ·
                        rfl

theorem cell23_8249264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_8249264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249264 prefixEnd_8249264 := by exact prefixLift 8249264
  have htrace : WordTrace (prefixWord ++ tailWord_8249264) baseStart_8249264 baseEnd_8249264 := by
    simpa [prefixWord, tailWord_8249264, baseEnd_8249264] using wordTrace_append hprefix tailTrace_8249264
  have hstable : (prefixWord ++ tailWord_8249264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249264).length < 2 ^ (prefixWord ++ tailWord_8249264).sum := by decide
  have hdescent : baseEnd_8249264 < baseStart_8249264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249271 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_8249271 : Nat := 118140960795 + 8249271 * 2 ^ 59
def prefixEnd_8249271 : Nat := 4983230072969 + 3 ^ 40 * 8249271 * 2
def baseEnd_8249271 : Nat := 4235841072195699422974799

theorem tailTrace_8249271 : CollatzResearch.WordTrace tailWord_8249271 prefixEnd_8249271 4235841072195699422974799 := by
  unfold tailWord_8249271
  simp only [CollatzResearch.WordTrace]
  refine ⟨300875631297307505166571667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200583754198205003444381111 300875631297307505166571667)
  ·
    refine ⟨451313446945961257749857501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300875631297307505166571667 451313446945961257749857501)
    ·
      refine ⟨169242542604735471656196563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451313446945961257749857501 169242542604735471656196563)
      ·
        refine ⟨253863813907103207484294845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169242542604735471656196563 253863813907103207484294845)
        ·
          refine ⟨95198930215163702806610567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253863813907103207484294845 95198930215163702806610567)
          ·
            refine ⟨142798395322745554209915851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95198930215163702806610567 142798395322745554209915851)
            ·
              refine ⟨214197592984118331314873777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142798395322745554209915851 214197592984118331314873777)
              ·
                refine ⟨160648194738088748486155333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214197592984118331314873777 160648194738088748486155333)
                ·
                  refine ⟨30121536513391640341154125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160648194738088748486155333 30121536513391640341154125)
                  ·
                    refine ⟨11295576192521865127932797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30121536513391640341154125 11295576192521865127932797)
                    ·
                      refine ⟨4235841072195699422974799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11295576192521865127932797 4235841072195699422974799)
                      ·
                        rfl

theorem cell23_8249271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_8249271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249271 prefixEnd_8249271 := by exact prefixLift 8249271
  have htrace : WordTrace (prefixWord ++ tailWord_8249271) baseStart_8249271 baseEnd_8249271 := by
    simpa [prefixWord, tailWord_8249271, baseEnd_8249271] using wordTrace_append hprefix tailTrace_8249271
  have hstable : (prefixWord ++ tailWord_8249271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249271).length < 2 ^ (prefixWord ++ tailWord_8249271).sum := by decide
  have hdescent : baseEnd_8249271 < baseStart_8249271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249291 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 2, 5]
def baseStart_8249291 : Nat := 118140960795 + 8249291 * 2 ^ 59
def prefixEnd_8249291 : Nat := 4983230072969 + 3 ^ 40 * 8249291 * 2
def baseEnd_8249291 : Nat := 1411950447269596448241569

theorem tailTrace_8249291 : CollatzResearch.WordTrace tailWord_8249291 prefixEnd_8249291 1411950447269596448241569 := by
  unfold tailWord_8249291
  simp only [CollatzResearch.WordTrace]
  refine ⟨300876360757235048582299727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200584240504823365721533151 300876360757235048582299727)
  ·
    refine ⟨451314541135852572873449591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300876360757235048582299727 451314541135852572873449591)
    ·
      refine ⟨676971811703778859310174387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451314541135852572873449591 676971811703778859310174387)
      ·
        refine ⟨1015457717555668288965261581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676971811703778859310174387 1015457717555668288965261581)
        ·
          refine ⟨380796644083375608361973093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1015457717555668288965261581 380796644083375608361973093)
          ·
            refine ⟨71399370765632926567869955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380796644083375608361973093 71399370765632926567869955)
            ·
              refine ⟨107099056148449389851804933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71399370765632926567869955 107099056148449389851804933)
              ·
                refine ⟨20081073027834260597213425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107099056148449389851804933 20081073027834260597213425)
                ·
                  refine ⟨15060804770875695447910069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20081073027834260597213425 15060804770875695447910069)
                  ·
                    refine ⟨1411950447269596448241569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15060804770875695447910069 1411950447269596448241569)
                    ·
                      rfl

theorem cell23_8249291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 5].length) (baseStart_8249291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249291 prefixEnd_8249291 := by exact prefixLift 8249291
  have htrace : WordTrace (prefixWord ++ tailWord_8249291) baseStart_8249291 baseEnd_8249291 := by
    simpa [prefixWord, tailWord_8249291, baseEnd_8249291] using wordTrace_append hprefix tailTrace_8249291
  have hstable : (prefixWord ++ tailWord_8249291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249291).length < 2 ^ (prefixWord ++ tailWord_8249291).sum := by decide
  have hdescent : baseEnd_8249291 < baseStart_8249291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249325 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_8249325 : Nat := 118140960795 + 8249325 * 2 ^ 59
def prefixEnd_8249325 : Nat := 4983230072969 + 3 ^ 40 * 8249325 * 2
def baseEnd_8249325 : Nat := 1411956266717014070566517

theorem tailTrace_8249325 : CollatzResearch.WordTrace tailWord_8249325 prefixEnd_8249325 1411956266717014070566517 := by
  unfold tailWord_8249325
  simp only [CollatzResearch.WordTrace]
  refine ⟨300877600839111872389037429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200585067226074581592691619 300877600839111872389037429)
  ·
    refine ⟨28207275078666738036472259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300877600839111872389037429 28207275078666738036472259)
    ·
      refine ⟨42310912618000107054708389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28207275078666738036472259 42310912618000107054708389)
      ·
        refine ⟨7933296115875020072757823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42310912618000107054708389 7933296115875020072757823)
        ·
          refine ⟨11899944173812530109136735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7933296115875020072757823 11899944173812530109136735)
          ·
            refine ⟨17849916260718795163705103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11899944173812530109136735 17849916260718795163705103)
            ·
              refine ⟨26774874391078192745557655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17849916260718795163705103 26774874391078192745557655)
              ·
                refine ⟨40162311586617289118336483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26774874391078192745557655 40162311586617289118336483)
                ·
                  refine ⟨60243467379925933677504725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40162311586617289118336483 60243467379925933677504725)
                  ·
                    refine ⟨1411956266717014070566517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60243467379925933677504725 1411956266717014070566517)
                    ·
                      rfl

theorem cell23_8249325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_8249325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249325 prefixEnd_8249325 := by exact prefixLift 8249325
  have htrace : WordTrace (prefixWord ++ tailWord_8249325) baseStart_8249325 baseEnd_8249325 := by
    simpa [prefixWord, tailWord_8249325, baseEnd_8249325] using wordTrace_append hprefix tailTrace_8249325
  have hstable : (prefixWord ++ tailWord_8249325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249325).length < 2 ^ (prefixWord ++ tailWord_8249325).sum := by decide
  have hdescent : baseEnd_8249325 < baseStart_8249325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249328 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 4]
def baseStart_8249328 : Nat := 118140960795 + 8249328 * 2 ^ 59
def prefixEnd_8249328 : Nat := 4983230072969 + 3 ^ 40 * 8249328 * 2
def baseEnd_8249328 : Nat := 4235870340593005699962037

theorem tailTrace_8249328 : CollatzResearch.WordTrace tailWord_8249328 prefixEnd_8249328 4235870340593005699962037 := by
  unfold tailWord_8249328
  simp only [CollatzResearch.WordTrace]
  refine ⟨150438855129050501950698319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200585140172067335934264425 150438855129050501950698319)
  ·
    refine ⟨225658282693575752926047479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150438855129050501950698319 225658282693575752926047479)
    ·
      refine ⟨338487424040363629389071219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225658282693575752926047479 338487424040363629389071219)
      ·
        refine ⟨507731136060545444083606829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338487424040363629389071219 507731136060545444083606829)
        ·
          refine ⟨190399176022704541531352561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507731136060545444083606829 190399176022704541531352561)
          ·
            refine ⟨142799382017028406148514421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190399176022704541531352561 142799382017028406148514421)
            ·
              refine ⟨13387442064096413076423227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142799382017028406148514421 13387442064096413076423227)
              ·
                refine ⟨20081163096144619614634841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13387442064096413076423227 20081163096144619614634841)
                ·
                  refine ⟨15060872322108464710976131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20081163096144619614634841 15060872322108464710976131)
                  ·
                    refine ⟨22591308483162697066464197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15060872322108464710976131 22591308483162697066464197)
                    ·
                      refine ⟨4235870340593005699962037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22591308483162697066464197 4235870340593005699962037)
                      ·
                        rfl

theorem cell23_8249328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_8249328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249328 prefixEnd_8249328 := by exact prefixLift 8249328
  have htrace : WordTrace (prefixWord ++ tailWord_8249328) baseStart_8249328 baseEnd_8249328 := by
    simpa [prefixWord, tailWord_8249328, baseEnd_8249328] using wordTrace_append hprefix tailTrace_8249328
  have hstable : (prefixWord ++ tailWord_8249328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249328).length < 2 ^ (prefixWord ++ tailWord_8249328).sum := by decide
  have hdescent : baseEnd_8249328 < baseStart_8249328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249341 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_8249341 : Nat := 118140960795 + 8249341 * 2 ^ 59
def prefixEnd_8249341 : Nat := 4983230072969 + 3 ^ 40 * 8249341 * 2
def baseEnd_8249341 : Nat := 4235877015841514149099477

theorem tailTrace_8249341 : CollatzResearch.WordTrace tailWord_8249341 prefixEnd_8249341 4235877015841514149099477 := by
  unfold tailWord_8249341
  simp only [CollatzResearch.WordTrace]
  refine ⟨300878184407053907121619877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200585456271369271414413251 300878184407053907121619877)
  ·
    refine ⟨56414659576322607585303727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300878184407053907121619877 56414659576322607585303727)
    ·
      refine ⟨84621989364483911377955591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56414659576322607585303727 84621989364483911377955591)
      ·
        refine ⟨126932984046725867066933387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84621989364483911377955591 126932984046725867066933387)
        ·
          refine ⟨190399476070088800600400081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126932984046725867066933387 190399476070088800600400081)
          ·
            refine ⟨142799607052566600450300061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190399476070088800600400081 142799607052566600450300061)
            ·
              refine ⟨53549852644712475168862523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142799607052566600450300061 53549852644712475168862523)
              ·
                refine ⟨80324778967068712753293785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53549852644712475168862523 80324778967068712753293785)
                ·
                  refine ⟨60243584225301534564970339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80324778967068712753293785 60243584225301534564970339)
                  ·
                    refine ⟨90365376337952301847455509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60243584225301534564970339 90365376337952301847455509)
                    ·
                      refine ⟨4235877015841514149099477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90365376337952301847455509 4235877015841514149099477)
                      ·
                        rfl

theorem cell23_8249341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_8249341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249341 prefixEnd_8249341 := by exact prefixLift 8249341
  have htrace : WordTrace (prefixWord ++ tailWord_8249341) baseStart_8249341 baseEnd_8249341 := by
    simpa [prefixWord, tailWord_8249341, baseEnd_8249341] using wordTrace_append hprefix tailTrace_8249341
  have hstable : (prefixWord ++ tailWord_8249341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249341).length < 2 ^ (prefixWord ++ tailWord_8249341).sum := by decide
  have hdescent : baseEnd_8249341 < baseStart_8249341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249355 : List Nat := [1, 1, 1, 1, 6, 1, 1, 6, 1, 4]
def baseStart_8249355 : Nat := 118140960795 + 8249355 * 2 ^ 59
def prefixEnd_8249355 : Nat := 4983230072969 + 3 ^ 40 * 8249355 * 2
def baseEnd_8249355 : Nat := 1411961401523559031441471

theorem tailTrace_8249355 : CollatzResearch.WordTrace tailWord_8249355 prefixEnd_8249355 1411961401523559031441471 := by
  unfold tailWord_8249355
  simp only [CollatzResearch.WordTrace]
  refine ⟨300878695029003187512629519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200585796686002125008419679 300878695029003187512629519)
  ·
    refine ⟨451318042543504781268944279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300878695029003187512629519 451318042543504781268944279)
    ·
      refine ⟨676977063815257171903416419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451318042543504781268944279 676977063815257171903416419)
      ·
        refine ⟨1015465595722885757855124629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676977063815257171903416419 1015465595722885757855124629)
        ·
          refine ⟨47599949799510269899458967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1015465595722885757855124629 47599949799510269899458967)
          ·
            refine ⟨71399924699265404849188451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47599949799510269899458967 71399924699265404849188451)
            ·
              refine ⟨107099887048898107273782677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71399924699265404849188451 107099887048898107273782677)
              ·
                refine ⟨5020307205417098778458563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107099887048898107273782677 5020307205417098778458563)
                ·
                  refine ⟨7530460808125648167687845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020307205417098778458563 7530460808125648167687845)
                  ·
                    refine ⟨1411961401523559031441471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7530460808125648167687845 1411961401523559031441471)
                    ·
                      rfl

theorem cell23_8249355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 4].length) (baseStart_8249355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249355 prefixEnd_8249355 := by exact prefixLift 8249355
  have htrace : WordTrace (prefixWord ++ tailWord_8249355) baseStart_8249355 baseEnd_8249355 := by
    simpa [prefixWord, tailWord_8249355, baseEnd_8249355] using wordTrace_append hprefix tailTrace_8249355
  have hstable : (prefixWord ++ tailWord_8249355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249355).length < 2 ^ (prefixWord ++ tailWord_8249355).sum := by decide
  have hdescent : baseEnd_8249355 < baseStart_8249355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249378 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_8249378 : Nat := 118140960795 + 8249378 * 2 ^ 59
def prefixEnd_8249378 : Nat := 4983230072969 + 3 ^ 40 * 8249378 * 2
def baseEnd_8249378 : Nat := 4235896014625730504336807

theorem tailTrace_8249378 : CollatzResearch.WordTrace tailWord_8249378 prefixEnd_8249378 4235896014625730504336807 := by
  unfold tailWord_8249378
  simp only [CollatzResearch.WordTrace]
  refine ⟨75219883476979965610179197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200586355938613241627144525 75219883476979965610179197)
  ·
    refine ⟨28207456303867487103817199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75219883476979965610179197 28207456303867487103817199)
    ·
      refine ⟨42311184455801230655725799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28207456303867487103817199 42311184455801230655725799)
      ·
        refine ⟨63466776683701845983588699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42311184455801230655725799 63466776683701845983588699)
        ·
          refine ⟨95200165025552768975383049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63466776683701845983588699 95200165025552768975383049)
          ·
            refine ⟨71400123769164576731537287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95200165025552768975383049 71400123769164576731537287)
            ·
              refine ⟨107100185653746865097305931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71400123769164576731537287 107100185653746865097305931)
              ·
                refine ⟨160650278480620297645958897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107100185653746865097305931 160650278480620297645958897)
                ·
                  refine ⟨120487708860465223234469173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160650278480620297645958897 120487708860465223234469173)
                  ·
                    refine ⟨11295722705668614678231485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120487708860465223234469173 11295722705668614678231485)
                    ·
                      refine ⟨4235896014625730504336807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11295722705668614678231485 4235896014625730504336807)
                      ·
                        rfl

theorem cell23_8249378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_8249378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249378 prefixEnd_8249378 := by exact prefixLift 8249378
  have htrace : WordTrace (prefixWord ++ tailWord_8249378) baseStart_8249378 baseEnd_8249378 := by
    simpa [prefixWord, tailWord_8249378, baseEnd_8249378] using wordTrace_append hprefix tailTrace_8249378
  have hstable : (prefixWord ++ tailWord_8249378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249378).length < 2 ^ (prefixWord ++ tailWord_8249378).sum := by decide
  have hdescent : baseEnd_8249378 < baseStart_8249378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249406 : List Nat := [4, 2, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_8249406 : Nat := 118140960795 + 8249406 * 2 ^ 59
def prefixEnd_8249406 : Nat := 4983230072969 + 3 ^ 40 * 8249406 * 2
def baseEnd_8249406 : Nat := 1411970130694685464928893

theorem tailTrace_8249406 : CollatzResearch.WordTrace tailWord_8249406 prefixEnd_8249406 1411970130694685464928893 := by
  unfold tailWord_8249406
  simp only [CollatzResearch.WordTrace]
  refine ⟨37610069393977302902842009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200587036767878948815157381 37610069393977302902842009)
  ·
    refine ⟨28207552045482977177131507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37610069393977302902842009 28207552045482977177131507)
    ·
      refine ⟨42311328068224465765697261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28207552045482977177131507 42311328068224465765697261)
      ·
        refine ⟨15866748025584174662136473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42311328068224465765697261 15866748025584174662136473)
        ·
          refine ⟨11900061019188130996602355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15866748025584174662136473 11900061019188130996602355)
          ·
            refine ⟨17850091528782196494903533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11900061019188130996602355 17850091528782196494903533)
            ·
              refine ⟨6693784323293323685588825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17850091528782196494903533 6693784323293323685588825)
              ·
                refine ⟨5020338242469992764191619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6693784323293323685588825 5020338242469992764191619)
                ·
                  refine ⟨7530507363704989146287429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020338242469992764191619 7530507363704989146287429)
                  ·
                    refine ⟨1411970130694685464928893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7530507363704989146287429 1411970130694685464928893)
                    ·
                      rfl

theorem cell23_8249406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_8249406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249406 prefixEnd_8249406 := by exact prefixLift 8249406
  have htrace : WordTrace (prefixWord ++ tailWord_8249406) baseStart_8249406 baseEnd_8249406 := by
    simpa [prefixWord, tailWord_8249406, baseEnd_8249406] using wordTrace_append hprefix tailTrace_8249406
  have hstable : (prefixWord ++ tailWord_8249406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249406).length < 2 ^ (prefixWord ++ tailWord_8249406).sum := by decide
  have hdescent : baseEnd_8249406 < baseStart_8249406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249411 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 5, 6]
def baseStart_8249411 : Nat := 118140960795 + 8249411 * 2 ^ 59
def prefixEnd_8249411 : Nat := 4983230072969 + 3 ^ 40 * 8249411 * 2
def baseEnd_8249411 : Nat := 1411970986495776291741385

theorem tailTrace_8249411 : CollatzResearch.WordTrace tailWord_8249411 prefixEnd_8249411 1411970986495776291741385 := by
  unfold tailWord_8249411
  simp only [CollatzResearch.WordTrace]
  refine ⟨300880737516800309076668087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200587158344533539384445391 300880737516800309076668087)
  ·
    refine ⟨451321106275200463615002131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300880737516800309076668087 451321106275200463615002131)
    ·
      refine ⟨676981659412800695422503197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451321106275200463615002131 676981659412800695422503197)
      ·
        refine ⟨253868122279800260783438699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 676981659412800695422503197 253868122279800260783438699)
        ·
          refine ⟨380802183419700391175158049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253868122279800260783438699 380802183419700391175158049)
          ·
            refine ⟨285601637564775293381368537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380802183419700391175158049 285601637564775293381368537)
            ·
              refine ⟨214201228173581470036026403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285601637564775293381368537 214201228173581470036026403)
              ·
                refine ⟨321301842260372205054039605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214201228173581470036026403 321301842260372205054039605)
                ·
                  refine ⟨30122047711909894223816213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321301842260372205054039605 30122047711909894223816213)
                  ·
                    refine ⟨1411970986495776291741385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30122047711909894223816213 1411970986495776291741385)
                    ·
                      rfl

theorem cell23_8249411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 6].length) (baseStart_8249411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249411 prefixEnd_8249411 := by exact prefixLift 8249411
  have htrace : WordTrace (prefixWord ++ tailWord_8249411) baseStart_8249411 baseEnd_8249411 := by
    simpa [prefixWord, tailWord_8249411, baseEnd_8249411] using wordTrace_append hprefix tailTrace_8249411
  have hstable : (prefixWord ++ tailWord_8249411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249411).length < 2 ^ (prefixWord ++ tailWord_8249411).sum := by decide
  have hdescent : baseEnd_8249411 < baseStart_8249411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249418 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_8249418 : Nat := 118140960795 + 8249418 * 2 ^ 59
def prefixEnd_8249418 : Nat := 4983230072969 + 3 ^ 40 * 8249418 * 2
def baseEnd_8249418 : Nat := 4235916553851910347836623

theorem tailTrace_8249418 : CollatzResearch.WordTrace tailWord_8249418 prefixEnd_8249418 4235916553851910347836623 := by
  unfold tailWord_8249418
  simp only [CollatzResearch.WordTrace]
  refine ⟨75220248206943737318043227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200587328551849966181448605 75220248206943737318043227)
  ·
    refine ⟨112830372310415605977064841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75220248206943737318043227 112830372310415605977064841)
    ·
      refine ⟨84622779232811704482798631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112830372310415605977064841 84622779232811704482798631)
      ·
        refine ⟨126934168849217556724197947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84622779232811704482798631 126934168849217556724197947)
        ·
          refine ⟨190401253273826335086296921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126934168849217556724197947 190401253273826335086296921)
          ·
            refine ⟨142800939955369751314722691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190401253273826335086296921 142800939955369751314722691)
            ·
              refine ⟨214201409933054626972084037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142800939955369751314722691 214201409933054626972084037)
              ·
                refine ⟨40162764362447742557265757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214201409933054626972084037 40162764362447742557265757)
                ·
                  refine ⟨15061036635917903458974659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40162764362447742557265757 15061036635917903458974659)
                  ·
                    refine ⟨22591554953876855188461989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15061036635917903458974659 22591554953876855188461989)
                    ·
                      refine ⟨4235916553851910347836623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22591554953876855188461989 4235916553851910347836623)
                      ·
                        rfl

theorem cell23_8249418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_8249418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249418 prefixEnd_8249418 := by exact prefixLift 8249418
  have htrace : WordTrace (prefixWord ++ tailWord_8249418) baseStart_8249418 baseEnd_8249418 := by
    simpa [prefixWord, tailWord_8249418, baseEnd_8249418] using wordTrace_append hprefix tailTrace_8249418
  have hstable : (prefixWord ++ tailWord_8249418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249418).length < 2 ^ (prefixWord ++ tailWord_8249418).sum := by decide
  have hdescent : baseEnd_8249418 < baseStart_8249418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249428 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_8249428 : Nat := 118140960795 + 8249428 * 2 ^ 59
def prefixEnd_8249428 : Nat := 4983230072969 + 3 ^ 40 * 8249428 * 2
def baseEnd_8249428 : Nat := 1411973896219485102903859

theorem tailTrace_8249428 : CollatzResearch.WordTrace tailWord_8249428 prefixEnd_8249428 1411973896219485102903859 := by
  unfold tailWord_8249428
  simp only [CollatzResearch.WordTrace]
  refine ⟨150440678778869360490018469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200587571705159147320024625 150440678778869360490018469)
  ·
    refine ⟨28207627271038005091878463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150440678778869360490018469 28207627271038005091878463)
    ·
      refine ⟨42311440906557007637817695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28207627271038005091878463 42311440906557007637817695)
      ·
        refine ⟨63467161359835511456726543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42311440906557007637817695 63467161359835511456726543)
        ·
          refine ⟨95200742039753267185089815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63467161359835511456726543 95200742039753267185089815)
          ·
            refine ⟨142801113059629900777634723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95200742039753267185089815 142801113059629900777634723)
            ·
              refine ⟨214201669589444851166452085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142801113059629900777634723 214201669589444851166452085)
              ·
                refine ⟨20081406524010454796854883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214201669589444851166452085 20081406524010454796854883)
                ·
                  refine ⟨30122109786015682195282325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20081406524010454796854883 30122109786015682195282325)
                  ·
                    refine ⟨1411973896219485102903859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30122109786015682195282325 1411973896219485102903859)
                    ·
                      rfl

theorem cell23_8249428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_8249428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249428 prefixEnd_8249428 := by exact prefixLift 8249428
  have htrace : WordTrace (prefixWord ++ tailWord_8249428) baseStart_8249428 baseEnd_8249428 := by
    simpa [prefixWord, tailWord_8249428, baseEnd_8249428] using wordTrace_append hprefix tailTrace_8249428
  have hstable : (prefixWord ++ tailWord_8249428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249428).length < 2 ^ (prefixWord ++ tailWord_8249428).sum := by decide
  have hdescent : baseEnd_8249428 < baseStart_8249428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249452 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 4]
def baseStart_8249452 : Nat := 118140960795 + 8249452 * 2 ^ 59
def prefixEnd_8249452 : Nat := 4983230072969 + 3 ^ 40 * 8249452 * 2
def baseEnd_8249452 : Nat := 4235934012194163214811467

theorem tailTrace_8249452 : CollatzResearch.WordTrace tailWord_8249452 prefixEnd_8249452 4235934012194163214811467 := by
  unfold tailWord_8249452
  simp only [CollatzResearch.WordTrace]
  refine ⟨150441116454825886539455305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200588155273101182052607073 150441116454825886539455305)
  ·
    refine ⟨112830837341119414904591479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150441116454825886539455305 112830837341119414904591479)
    ·
      refine ⟨169246256011679122356887219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112830837341119414904591479 169246256011679122356887219)
      ·
        refine ⟨253869384017518683535330829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169246256011679122356887219 253869384017518683535330829)
        ·
          refine ⟨95201019006569506325749061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253869384017518683535330829 95201019006569506325749061)
          ·
            refine ⟨17850191063731782436077949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95201019006569506325749061 17850191063731782436077949)
            ·
              refine ⟨6693821648899418413529231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17850191063731782436077949 6693821648899418413529231)
              ·
                refine ⟨10040732473349127620293847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693821648899418413529231 10040732473349127620293847)
                ·
                  refine ⟨15061098710023691430440771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10040732473349127620293847 15061098710023691430440771)
                  ·
                    refine ⟨22591648065035537145661157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15061098710023691430440771 22591648065035537145661157)
                    ·
                      refine ⟨4235934012194163214811467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22591648065035537145661157 4235934012194163214811467)
                      ·
                        rfl

theorem cell23_8249452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_8249452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249452 prefixEnd_8249452 := by exact prefixLift 8249452
  have htrace : WordTrace (prefixWord ++ tailWord_8249452) baseStart_8249452 baseEnd_8249452 := by
    simpa [prefixWord, tailWord_8249452, baseEnd_8249452] using wordTrace_append hprefix tailTrace_8249452
  have hstable : (prefixWord ++ tailWord_8249452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249452).length < 2 ^ (prefixWord ++ tailWord_8249452).sum := by decide
  have hdescent : baseEnd_8249452 < baseStart_8249452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249455 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 5]
def baseStart_8249455 : Nat := 118140960795 + 8249455 * 2 ^ 59
def prefixEnd_8249455 : Nat := 4983230072969 + 3 ^ 40 * 8249455 * 2
def baseEnd_8249455 : Nat := 4235935552636126703073953

theorem tailTrace_8249455 : CollatzResearch.WordTrace tailWord_8249455 prefixEnd_8249455 4235935552636126703073953 := by
  unfold tailWord_8249455
  simp only [CollatzResearch.WordTrace]
  refine ⟨300882342328640904591269819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200588228219093936394179879 300882342328640904591269819)
  ·
    refine ⟨451323513492961356886904729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300882342328640904591269819 451323513492961356886904729)
    ·
      refine ⟨338492635119721017665178547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451323513492961356886904729 338492635119721017665178547)
      ·
        refine ⟨507738952679581526497767821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338492635119721017665178547 507738952679581526497767821)
        ·
          refine ⟨190402107254843072436662933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507738952679581526497767821 190402107254843072436662933)
          ·
            refine ⟨8925098777570769020468575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190402107254843072436662933 8925098777570769020468575)
            ·
              refine ⟨13387648166356153530702863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925098777570769020468575 13387648166356153530702863)
              ·
                refine ⟨20081472249534230296054295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13387648166356153530702863 20081472249534230296054295)
                ·
                  refine ⟨30122208374301345444081443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20081472249534230296054295 30122208374301345444081443)
                  ·
                    refine ⟨45183312561452018166122165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30122208374301345444081443 45183312561452018166122165)
                    ·
                      refine ⟨4235935552636126703073953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45183312561452018166122165 4235935552636126703073953)
                      ·
                        rfl

theorem cell23_8249455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 5].length) (baseStart_8249455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249455 prefixEnd_8249455 := by exact prefixLift 8249455
  have htrace : WordTrace (prefixWord ++ tailWord_8249455) baseStart_8249455 baseEnd_8249455 := by
    simpa [prefixWord, tailWord_8249455, baseEnd_8249455] using wordTrace_append hprefix tailTrace_8249455
  have hstable : (prefixWord ++ tailWord_8249455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249455).length < 2 ^ (prefixWord ++ tailWord_8249455).sum := by decide
  have hdescent : baseEnd_8249455 < baseStart_8249455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249462 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_8249462 : Nat := 118140960795 + 8249462 * 2 ^ 59
def prefixEnd_8249462 : Nat := 4983230072969 + 3 ^ 40 * 8249462 * 2
def baseEnd_8249462 : Nat := 1411979715666902725228807

theorem tailTrace_8249462 : CollatzResearch.WordTrace tailWord_8249462 prefixEnd_8249462 1411979715666902725228807 := by
  unfold tailWord_8249462
  simp only [CollatzResearch.WordTrace]
  refine ⟨18805162352475971549173415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200588398426410363191183093 18805162352475971549173415)
  ·
    refine ⟨28207743528713957323760123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18805162352475971549173415 28207743528713957323760123)
    ·
      refine ⟨42311615293070935985640185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28207743528713957323760123 42311615293070935985640185)
      ·
        refine ⟨31733711469803201989230139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42311615293070935985640185 31733711469803201989230139)
        ·
          refine ⟨47600567204704802983845209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31733711469803201989230139 47600567204704802983845209)
          ·
            refine ⟨35700425403528602237883907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47600567204704802983845209 35700425403528602237883907)
            ·
              refine ⟨53550638105292903356825861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35700425403528602237883907 53550638105292903356825861)
              ·
                refine ⟨10040744644742419379404849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53550638105292903356825861 10040744644742419379404849)
                ·
                  refine ⟨7530558483556814534553637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10040744644742419379404849 7530558483556814534553637)
                  ·
                    refine ⟨1411979715666902725228807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7530558483556814534553637 1411979715666902725228807)
                    ·
                      rfl

theorem cell23_8249462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_8249462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249462 prefixEnd_8249462 := by exact prefixLift 8249462
  have htrace : WordTrace (prefixWord ++ tailWord_8249462) baseStart_8249462 baseEnd_8249462 := by
    simpa [prefixWord, tailWord_8249462, baseEnd_8249462] using wordTrace_append hprefix tailTrace_8249462
  have hstable : (prefixWord ++ tailWord_8249462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249462).length < 2 ^ (prefixWord ++ tailWord_8249462).sum := by decide
  have hdescent : baseEnd_8249462 < baseStart_8249462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249506 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_8249506 : Nat := 118140960795 + 8249506 * 2 ^ 59
def prefixEnd_8249506 : Nat := 4983230072969 + 3 ^ 40 * 8249506 * 2
def baseEnd_8249506 : Nat := 4235961740149506003536219

theorem tailTrace_8249506 : CollatzResearch.WordTrace tailWord_8249506 prefixEnd_8249506 4235961740149506003536219 := by
  unfold tailWord_8249506
  simp only [CollatzResearch.WordTrace]
  refine ⟨75221050612864035075344093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200589468300970760200917581 75221050612864035075344093)
  ·
    refine ⟨28207893979824013153254035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75221050612864035075344093 28207893979824013153254035)
    ·
      refine ⟨42311840969736019729881053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28207893979824013153254035 42311840969736019729881053)
      ·
        refine ⟨15866940363651007398705395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42311840969736019729881053 15866940363651007398705395)
        ·
          refine ⟨23800410545476511098058093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15866940363651007398705395 23800410545476511098058093)
          ·
            refine ⟨8925153954553691661771785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23800410545476511098058093 8925153954553691661771785)
            ·
              refine ⟨6693865465915268746328839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8925153954553691661771785 6693865465915268746328839)
              ·
                refine ⟨10040798198872903119493259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693865465915268746328839 10040798198872903119493259)
                ·
                  refine ⟨15061197298309354679239889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10040798198872903119493259 15061197298309354679239889)
                  ·
                    refine ⟨11295897973732016009429917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15061197298309354679239889 11295897973732016009429917)
                    ·
                      refine ⟨4235961740149506003536219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11295897973732016009429917 4235961740149506003536219)
                      ·
                        rfl

theorem cell23_8249506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_8249506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249506 prefixEnd_8249506 := by exact prefixLift 8249506
  have htrace : WordTrace (prefixWord ++ tailWord_8249506) baseStart_8249506 baseEnd_8249506 := by
    simpa [prefixWord, tailWord_8249506, baseEnd_8249506] using wordTrace_append hprefix tailTrace_8249506
  have hstable : (prefixWord ++ tailWord_8249506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249506).length < 2 ^ (prefixWord ++ tailWord_8249506).sum := by decide
  have hdescent : baseEnd_8249506 < baseStart_8249506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249632 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_8249632 : Nat := 118140960795 + 8249632 * 2 ^ 59
def prefixEnd_8249632 : Nat := 4983230072969 + 3 ^ 40 * 8249632 * 2
def baseEnd_8249632 : Nat := 4236026438711972510560639

theorem tailTrace_8249632 : CollatzResearch.WordTrace tailWord_8249632 prefixEnd_8249632 4236026438711972510560639 := by
  unfold tailWord_8249632
  simp only [CollatzResearch.WordTrace]
  refine ⟨150444399024499831910231575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200592532032666442546975433 150444399024499831910231575)
  ·
    refine ⟨225666598536749747865347363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150444399024499831910231575 225666598536749747865347363)
    ·
      refine ⟨338499897805124621798021045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225666598536749747865347363 338499897805124621798021045)
      ·
        refine ⟨31734365419230433293564473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338499897805124621798021045 31734365419230433293564473)
        ·
          refine ⟨23800774064422824970173355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31734365419230433293564473 23800774064422824970173355)
          ·
            refine ⟨35701161096634237455260033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23800774064422824970173355 35701161096634237455260033)
            ·
              refine ⟨26775870822475678091445025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35701161096634237455260033 26775870822475678091445025)
              ·
                refine ⟨20081903116856758568583769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26775870822475678091445025 20081903116856758568583769)
                ·
                  refine ⟨15061427337642568926437827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20081903116856758568583769 15061427337642568926437827)
                  ·
                    refine ⟨22592141006463853389656741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15061427337642568926437827 22592141006463853389656741)
                    ·
                      refine ⟨4236026438711972510560639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22592141006463853389656741 4236026438711972510560639)
                      ·
                        rfl

theorem cell23_8249632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_8249632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249632 prefixEnd_8249632 := by exact prefixLift 8249632
  have htrace : WordTrace (prefixWord ++ tailWord_8249632) baseStart_8249632 baseEnd_8249632 := by
    simpa [prefixWord, tailWord_8249632, baseEnd_8249632] using wordTrace_append hprefix tailTrace_8249632
  have hstable : (prefixWord ++ tailWord_8249632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249632).length < 2 ^ (prefixWord ++ tailWord_8249632).sum := by decide
  have hdescent : baseEnd_8249632 < baseStart_8249632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249649 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 2, 4, 2]
def baseStart_8249649 : Nat := 118140960795 + 8249649 * 2 ^ 59
def prefixEnd_8249649 : Nat := 4983230072969 + 3 ^ 40 * 8249649 * 2
def baseEnd_8249649 : Nat := 4236035167883098944048061

theorem tailTrace_8249649 : CollatzResearch.WordTrace tailWord_8249649 prefixEnd_8249649 4236035167883098944048061 := by
  unfold tailWord_8249649
  simp only [CollatzResearch.WordTrace]
  refine ⟨300889418089938075723832001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200592945393292050482554667 300889418089938075723832001)
  ·
    refine ⟨225667063567453556792874001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300889418089938075723832001 225667063567453556792874001)
    ·
      refine ⟨169250297675590167594655501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225667063567453556792874001 169250297675590167594655501)
      ·
        refine ⟨63468861628346312847995813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169250297675590167594655501 63468861628346312847995813)
        ·
          refine ⟨11900411555314933658999215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63468861628346312847995813 11900411555314933658999215)
          ·
            refine ⟨17850617332972400488498823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11900411555314933658999215 17850617332972400488498823)
            ·
              refine ⟨26775925999458600732748235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17850617332972400488498823 26775925999458600732748235)
              ·
                refine ⟨40163888999187901099122353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26775925999458600732748235 40163888999187901099122353)
                ·
                  refine ⟨30122916749390925824341765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40163888999187901099122353 30122916749390925824341765)
                  ·
                    refine ⟨5648046890510798592064081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30122916749390925824341765 5648046890510798592064081)
                    ·
                      refine ⟨4236035167883098944048061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648046890510798592064081 4236035167883098944048061)
                      ·
                        rfl

theorem cell23_8249649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_8249649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249649 prefixEnd_8249649 := by exact prefixLift 8249649
  have htrace : WordTrace (prefixWord ++ tailWord_8249649) baseStart_8249649 baseEnd_8249649 := by
    simpa [prefixWord, tailWord_8249649, baseEnd_8249649] using wordTrace_append hprefix tailTrace_8249649
  have hstable : (prefixWord ++ tailWord_8249649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249649).length < 2 ^ (prefixWord ++ tailWord_8249649).sum := by decide
  have hdescent : baseEnd_8249649 < baseStart_8249649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249699 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 3]
def baseStart_8249699 : Nat := 118140960795 + 8249699 * 2 ^ 59
def prefixEnd_8249699 : Nat := 4983230072969 + 3 ^ 40 * 8249699 * 2
def baseEnd_8249699 : Nat := 4236060841915823748422831

theorem tailTrace_8249699 : CollatzResearch.WordTrace tailWord_8249699 prefixEnd_8249699 4236060841915823748422831 := by
  unfold tailWord_8249699
  simp only [CollatzResearch.WordTrace]
  refine ⟨300891241739756934263152151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200594161159837956175434767 300891241739756934263152151)
  ·
    refine ⟨451336862609635401394728227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300891241739756934263152151 451336862609635401394728227)
    ·
      refine ⟨677005293914453102092092341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451336862609635401394728227 677005293914453102092092341)
      ·
        refine ⟨63469246304479978321133657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 677005293914453102092092341 63469246304479978321133657)
        ·
          refine ⟨47601934728359983740850243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63469246304479978321133657 47601934728359983740850243)
          ·
            refine ⟨71402902092539975611275365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47601934728359983740850243 71402902092539975611275365)
            ·
              refine ⟨13388044142351245427114131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71402902092539975611275365 13388044142351245427114131)
              ·
                refine ⟨20082066213526868140671197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13388044142351245427114131 20082066213526868140671197)
                ·
                  refine ⟨7530774830072575552751699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20082066213526868140671197 7530774830072575552751699)
                  ·
                    refine ⟨11296162245108863329127549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7530774830072575552751699 11296162245108863329127549)
                    ·
                      refine ⟨4236060841915823748422831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11296162245108863329127549 4236060841915823748422831)
                      ·
                        rfl

theorem cell23_8249699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_8249699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249699 prefixEnd_8249699 := by exact prefixLift 8249699
  have htrace : WordTrace (prefixWord ++ tailWord_8249699) baseStart_8249699 baseEnd_8249699 := by
    simpa [prefixWord, tailWord_8249699, baseEnd_8249699] using wordTrace_append hprefix tailTrace_8249699
  have hstable : (prefixWord ++ tailWord_8249699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249699).length < 2 ^ (prefixWord ++ tailWord_8249699).sum := by decide
  have hdescent : baseEnd_8249699 < baseStart_8249699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249732 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_8249732 : Nat := 118140960795 + 8249732 * 2 ^ 59
def prefixEnd_8249732 : Nat := 4983230072969 + 3 ^ 40 * 8249732 * 2
def baseEnd_8249732 : Nat := 1412025928925807373103393

theorem tailTrace_8249732 : CollatzResearch.WordTrace tailWord_8249732 prefixEnd_8249732 1412025928925807373103393 := by
  unfold tailWord_8249732
  simp only [CollatzResearch.WordTrace]
  refine ⟨150446222674318690449551725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200594963565758253932735633 150446222674318690449551725)
  ·
    refine ⟨56417333502869508918581897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150446222674318690449551725 56417333502869508918581897)
    ·
      refine ⟨42313000127152131688936423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56417333502869508918581897 42313000127152131688936423)
      ·
        refine ⟨63469500190728197533404635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42313000127152131688936423 63469500190728197533404635)
        ·
          refine ⟨95204250286092296300106953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63469500190728197533404635 95204250286092296300106953)
          ·
            refine ⟨71403187714569222225080215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95204250286092296300106953 71403187714569222225080215)
            ·
              refine ⟨107104781571853833337620323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71403187714569222225080215 107104781571853833337620323)
              ·
                refine ⟨160657172357780750006430485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107104781571853833337620323 160657172357780750006430485)
                ·
                  refine ⟨7530804954270972656551429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160657172357780750006430485 7530804954270972656551429)
                  ·
                    refine ⟨1412025928925807373103393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7530804954270972656551429 1412025928925807373103393)
                    ·
                      rfl

theorem cell23_8249732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_8249732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249732 prefixEnd_8249732 := by exact prefixLift 8249732
  have htrace : WordTrace (prefixWord ++ tailWord_8249732) baseStart_8249732 baseEnd_8249732 := by
    simpa [prefixWord, tailWord_8249732, baseEnd_8249732] using wordTrace_append hprefix tailTrace_8249732
  have hstable : (prefixWord ++ tailWord_8249732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249732).length < 2 ^ (prefixWord ++ tailWord_8249732).sum := by decide
  have hdescent : baseEnd_8249732 < baseStart_8249732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249752 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_8249752 : Nat := 118140960795 + 8249752 * 2 ^ 59
def prefixEnd_8249752 : Nat := 4983230072969 + 3 ^ 40 * 8249752 * 2
def baseEnd_8249752 : Nat := 4236088056390512041060087

theorem tailTrace_8249752 : CollatzResearch.WordTrace tailWord_8249752 prefixEnd_8249752 4236088056390512041060087 := by
  unfold tailWord_8249752
  simp only [CollatzResearch.WordTrace]
  refine ⟨150446587404282462157415755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200595449872376616209887673 150446587404282462157415755)
  ·
    refine ⟨225669881106423693236123633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150446587404282462157415755 225669881106423693236123633)
    ·
      refine ⟨169252410829817769927092725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225669881106423693236123633 169252410829817769927092725)
      ·
        refine ⟨15867413515295415930664943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169252410829817769927092725 15867413515295415930664943)
        ·
          refine ⟨23801120272943123895997415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15867413515295415930664943 23801120272943123895997415)
          ·
            refine ⟨35701680409414685843996123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23801120272943123895997415 35701680409414685843996123)
            ·
              refine ⟨53552520614122028765994185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35701680409414685843996123 53552520614122028765994185)
              ·
                refine ⟨40164390460591521574495639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53552520614122028765994185 40164390460591521574495639)
                ·
                  refine ⟨60246585690887282361743459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40164390460591521574495639 60246585690887282361743459)
                  ·
                    refine ⟨90369878536330923542615189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60246585690887282361743459 90369878536330923542615189)
                    ·
                      refine ⟨4236088056390512041060087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90369878536330923542615189 4236088056390512041060087)
                      ·
                        rfl

theorem cell23_8249752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_8249752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249752 prefixEnd_8249752 := by exact prefixLift 8249752
  have htrace : WordTrace (prefixWord ++ tailWord_8249752) baseStart_8249752 baseEnd_8249752 := by
    simpa [prefixWord, tailWord_8249752, baseEnd_8249752] using wordTrace_append hprefix tailTrace_8249752
  have hstable : (prefixWord ++ tailWord_8249752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249752).length < 2 ^ (prefixWord ++ tailWord_8249752).sum := by decide
  have hdescent : baseEnd_8249752 < baseStart_8249752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249762 : List Nat := [3, 3, 1, 2, 1, 1, 4, 8]
def baseStart_8249762 : Nat := 118140960795 + 8249762 * 2 ^ 59
def prefixEnd_8249762 : Nat := 4983230072969 + 3 ^ 40 * 8249762 * 2
def baseEnd_8249762 : Nat := 156892340414705814886483

theorem tailTrace_8249762 : CollatzResearch.WordTrace tailWord_8249762 prefixEnd_8249762 156892340414705814886483 := by
  unfold tailWord_8249762
  simp only [CollatzResearch.WordTrace]
  refine ⟨75223384884632174005673885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200595693025685797348463693 75223384884632174005673885)
  ·
    refine ⟨28208769331737065252127707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75223384884632174005673885 28208769331737065252127707)
    ·
      refine ⟨42313153997605597878191561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28208769331737065252127707 42313153997605597878191561)
      ·
        refine ⟨31734865498204198408643671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42313153997605597878191561 31734865498204198408643671)
        ·
          refine ⟨47602298247306297612965507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31734865498204198408643671 47602298247306297612965507)
          ·
            refine ⟨71403447370959446419448261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47602298247306297612965507 71403447370959446419448261)
            ·
              refine ⟨13388146382054896203646549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71403447370959446419448261 13388146382054896203646549)
              ·
                refine ⟨156892340414705814886483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13388146382054896203646549 156892340414705814886483)
                ·
                  rfl

theorem cell23_8249762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 8].length) (baseStart_8249762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249762 prefixEnd_8249762 := by exact prefixLift 8249762
  have htrace : WordTrace (prefixWord ++ tailWord_8249762) baseStart_8249762 baseEnd_8249762 := by
    simpa [prefixWord, tailWord_8249762, baseEnd_8249762] using wordTrace_append hprefix tailTrace_8249762
  have hstable : (prefixWord ++ tailWord_8249762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249762).length < 2 ^ (prefixWord ++ tailWord_8249762).sum := by decide
  have hdescent : baseEnd_8249762 < baseStart_8249762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249765 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_8249765 : Nat := 118140960795 + 8249765 * 2 ^ 59
def prefixEnd_8249765 : Nat := 4983230072969 + 3 ^ 40 * 8249765 * 2
def baseEnd_8249765 : Nat := 4236094731639020490197527

theorem tailTrace_8249765 : CollatzResearch.WordTrace tailWord_8249765 prefixEnd_8249765 4236094731639020490197527 := by
  unfold tailWord_8249765
  simp only [CollatzResearch.WordTrace]
  refine ⟨300893648957517827535054749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200595765971678551690036499 300893648957517827535054749)
  ·
    refine ⟨112835118359069185325645531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300893648957517827535054749 112835118359069185325645531)
    ·
      refine ⟨169252677538603777988468297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112835118359069185325645531 169252677538603777988468297)
      ·
        refine ⟨126939508153952833491351223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169252677538603777988468297 126939508153952833491351223)
        ·
          refine ⟨190409262230929250237026835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126939508153952833491351223 190409262230929250237026835)
          ·
            refine ⟨285613893346393875355540253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190409262230929250237026835 285613893346393875355540253)
            ·
              refine ⟨107105210004897703258327595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285613893346393875355540253 107105210004897703258327595)
              ·
                refine ⟨160657815007346554887491393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107105210004897703258327595 160657815007346554887491393)
                ·
                  refine ⟨120493361255509916165618545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160657815007346554887491393 120493361255509916165618545)
                  ·
                    refine ⟨90370020941632437124213909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120493361255509916165618545 90370020941632437124213909)
                    ·
                      refine ⟨4236094731639020490197527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90370020941632437124213909 4236094731639020490197527)
                      ·
                        rfl

theorem cell23_8249765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_8249765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249765 prefixEnd_8249765 := by exact prefixLift 8249765
  have htrace : WordTrace (prefixWord ++ tailWord_8249765) baseStart_8249765 baseEnd_8249765 := by
    simpa [prefixWord, tailWord_8249765, baseEnd_8249765] using wordTrace_append hprefix tailTrace_8249765
  have hstable : (prefixWord ++ tailWord_8249765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249765).length < 2 ^ (prefixWord ++ tailWord_8249765).sum := by decide
  have hdescent : baseEnd_8249765 < baseStart_8249765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249770 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_8249770 : Nat := 118140960795 + 8249770 * 2 ^ 59
def prefixEnd_8249770 : Nat := 4983230072969 + 3 ^ 40 * 8249770 * 2
def baseEnd_8249770 : Nat := 1412032433014097656878335

theorem tailTrace_8249770 : CollatzResearch.WordTrace tailWord_8249770 prefixEnd_8249770 1412032433014097656878335 := by
  unfold tailWord_8249770
  simp only [CollatzResearch.WordTrace]
  refine ⟨75223457830624928347246691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200595887548333142259324509 75223457830624928347246691)
  ·
    refine ⟨112835186745937392520870037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75223457830624928347246691 112835186745937392520870037)
    ·
      refine ⟨5289149378715815274415783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112835186745937392520870037 5289149378715815274415783)
      ·
        refine ⟨7933724068073722911623675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5289149378715815274415783 7933724068073722911623675)
        ·
          refine ⟨11900586102110584367435513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7933724068073722911623675 11900586102110584367435513)
          ·
            refine ⟨8925439576582938275576635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11900586102110584367435513 8925439576582938275576635)
            ·
              refine ⟨13388159364874407413364953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925439576582938275576635 13388159364874407413364953)
              ·
                refine ⟨10041119523655805560023715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13388159364874407413364953 10041119523655805560023715)
                ·
                  refine ⟨15061679285483708340035573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10041119523655805560023715 15061679285483708340035573)
                  ·
                    refine ⟨1412032433014097656878335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15061679285483708340035573 1412032433014097656878335)
                    ·
                      rfl

theorem cell23_8249770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_8249770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249770 prefixEnd_8249770 := by exact prefixLift 8249770
  have htrace : WordTrace (prefixWord ++ tailWord_8249770) baseStart_8249770 baseEnd_8249770 := by
    simpa [prefixWord, tailWord_8249770, baseEnd_8249770] using wordTrace_append hprefix tailTrace_8249770
  have hstable : (prefixWord ++ tailWord_8249770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249770).length < 2 ^ (prefixWord ++ tailWord_8249770).sum := by decide
  have hdescent : baseEnd_8249770 < baseStart_8249770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249772 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_8249772 : Nat := 118140960795 + 8249772 * 2 ^ 59
def prefixEnd_8249772 : Nat := 4983230072969 + 3 ^ 40 * 8249772 * 2
def baseEnd_8249772 : Nat := 4236098326003601962809995

theorem tailTrace_8249772 : CollatzResearch.WordTrace tailWord_8249772 prefixEnd_8249772 4236098326003601962809995 := by
  unfold tailWord_8249772
  simp only [CollatzResearch.WordTrace]
  refine ⟨150446952134246233865279785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200595936178994978487039713 150446952134246233865279785)
  ·
    refine ⟨112835214100684675398959839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150446952134246233865279785 112835214100684675398959839)
    ·
      refine ⟨169252821151027013098439759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112835214100684675398959839 169252821151027013098439759)
      ·
        refine ⟨253879231726540519647659639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169252821151027013098439759 253879231726540519647659639)
        ·
          refine ⟨380818847589810779471489459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253879231726540519647659639 380818847589810779471489459)
          ·
            refine ⟨571228271384716169207234189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380818847589810779471489459 571228271384716169207234189)
            ·
              refine ⟨214210601769268563452712821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571228271384716169207234189 214210601769268563452712821)
              ·
                refine ⟨20082243915868927823691827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214210601769268563452712821 20082243915868927823691827)
                ·
                  refine ⟨30123365873803391735537741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20082243915868927823691827 30123365873803391735537741)
                  ·
                    refine ⟨11296262202676271900826653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30123365873803391735537741 11296262202676271900826653)
                    ·
                      refine ⟨4236098326003601962809995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11296262202676271900826653 4236098326003601962809995)
                      ·
                        rfl

theorem cell23_8249772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_8249772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249772 prefixEnd_8249772 := by exact prefixLift 8249772
  have htrace : WordTrace (prefixWord ++ tailWord_8249772) baseStart_8249772 baseEnd_8249772 := by
    simpa [prefixWord, tailWord_8249772, baseEnd_8249772] using wordTrace_append hprefix tailTrace_8249772
  have hstable : (prefixWord ++ tailWord_8249772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249772).length < 2 ^ (prefixWord ++ tailWord_8249772).sum := by decide
  have hdescent : baseEnd_8249772 < baseStart_8249772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249773 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_8249773 : Nat := 118140960795 + 8249773 * 2 ^ 59
def prefixEnd_8249773 : Nat := 4983230072969 + 3 ^ 40 * 8249773 * 2
def baseEnd_8249773 : Nat := 4236098839484256458897491

theorem tailTrace_8249773 : CollatzResearch.WordTrace tailWord_8249773 prefixEnd_8249773 4236098839484256458897491 := by
  unfold tailWord_8249773
  simp only [CollatzResearch.WordTrace]
  refine ⟨300893940741488844901345973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200595960494325896600897315 300893940741488844901345973)
  ·
    refine ⟨28208806944514579209501185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300893940741488844901345973 28208806944514579209501185)
    ·
      refine ⟨21156605208385934407125889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28208806944514579209501185 21156605208385934407125889)
      ·
        refine ⟨15867453906289450805344417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21156605208385934407125889 15867453906289450805344417)
        ·
          refine ⟨11900590429717088104008313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15867453906289450805344417 11900590429717088104008313)
          ·
            refine ⟨8925442822287816078006235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11900590429717088104008313 8925442822287816078006235)
            ·
              refine ⟨13388164233431724117009353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8925442822287816078006235 13388164233431724117009353)
              ·
                refine ⟨10041123175073793087757015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13388164233431724117009353 10041123175073793087757015)
                ·
                  refine ⟨15061684762610689631635523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10041123175073793087757015 15061684762610689631635523)
                  ·
                    refine ⟨22592527143916034447453285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15061684762610689631635523 22592527143916034447453285)
                    ·
                      refine ⟨4236098839484256458897491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22592527143916034447453285 4236098839484256458897491)
                      ·
                        rfl

theorem cell23_8249773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_8249773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249773 prefixEnd_8249773 := by exact prefixLift 8249773
  have htrace : WordTrace (prefixWord ++ tailWord_8249773) baseStart_8249773 baseEnd_8249773 := by
    simpa [prefixWord, tailWord_8249773, baseEnd_8249773] using wordTrace_append hprefix tailTrace_8249773
  have hstable : (prefixWord ++ tailWord_8249773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249773).length < 2 ^ (prefixWord ++ tailWord_8249773).sum := by decide
  have hdescent : baseEnd_8249773 < baseStart_8249773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249789 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_8249789 : Nat := 118140960795 + 8249789 * 2 ^ 59
def prefixEnd_8249789 : Nat := 4983230072969 + 3 ^ 40 * 8249789 * 2
def baseEnd_8249789 : Nat := 4236107055174728396297417

theorem tailTrace_8249789 : CollatzResearch.WordTrace tailWord_8249789 prefixEnd_8249789 4236107055174728396297417 := by
  unfold tailWord_8249789
  simp only [CollatzResearch.WordTrace]
  refine ⟨300894524309430879633928421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200596349539620586422618947 300894524309430879633928421)
  ·
    refine ⟨56417723308018289931361579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300894524309430879633928421 56417723308018289931361579)
    ·
      refine ⟨84626584962027434897042369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56417723308018289931361579 84626584962027434897042369)
      ·
        refine ⟨63469938721520576172781777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84626584962027434897042369 63469938721520576172781777)
        ·
          refine ⟨47602454041140432129586333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63469938721520576172781777 47602454041140432129586333)
          ·
            refine ⟨17850920265427662048594875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47602454041140432129586333 17850920265427662048594875)
            ·
              refine ⟨26776380398141493072892313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17850920265427662048594875 26776380398141493072892313)
              ·
                refine ⟨20082285298606119804669235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26776380398141493072892313 20082285298606119804669235)
                ·
                  refine ⟨30123427947909179707003853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20082285298606119804669235 30123427947909179707003853)
                  ·
                    refine ⟨11296285480465942390126445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30123427947909179707003853 11296285480465942390126445)
                    ·
                      refine ⟨4236107055174728396297417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11296285480465942390126445 4236107055174728396297417)
                      ·
                        rfl

theorem cell23_8249789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_8249789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249789 prefixEnd_8249789 := by exact prefixLift 8249789
  have htrace : WordTrace (prefixWord ++ tailWord_8249789) baseStart_8249789 baseEnd_8249789 := by
    simpa [prefixWord, tailWord_8249789, baseEnd_8249789] using wordTrace_append hprefix tailTrace_8249789
  have hstable : (prefixWord ++ tailWord_8249789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249789).length < 2 ^ (prefixWord ++ tailWord_8249789).sum := by decide
  have hdescent : baseEnd_8249789 < baseStart_8249789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249846 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_8249846 : Nat := 118140960795 + 8249846 * 2 ^ 59
def prefixEnd_8249846 : Nat := 4983230072969 + 3 ^ 40 * 8249846 * 2
def baseEnd_8249846 : Nat := 4236136323572034673284655

theorem tailTrace_8249846 : CollatzResearch.WordTrace tailWord_8249846 prefixEnd_8249846 4236136323572034673284655 := by
  unfold tailWord_8249846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18806037704389023648047087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200597735513482918912502261 18806037704389023648047087)
  ·
    refine ⟨28209056556583535472070631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18806037704389023648047087 28209056556583535472070631)
    ·
      refine ⟨42313584834875303208105947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28209056556583535472070631 42313584834875303208105947)
      ·
        refine ⟨63470377252312954812158921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42313584834875303208105947 63470377252312954812158921)
        ·
          refine ⟨47602782939234716109119191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63470377252312954812158921 47602782939234716109119191)
          ·
            refine ⟨71404174408852074163678787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47602782939234716109119191 71404174408852074163678787)
            ·
              refine ⟨107106261613278111245518181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71404174408852074163678787 107106261613278111245518181)
              ·
                refine ⟨20082424052489645858534659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107106261613278111245518181 20082424052489645858534659)
                ·
                  refine ⟨30123636078734468787801989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20082424052489645858534659 30123636078734468787801989)
                  ·
                    refine ⟨5648181764762712897712873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30123636078734468787801989 5648181764762712897712873)
                    ·
                      refine ⟨4236136323572034673284655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648181764762712897712873 4236136323572034673284655)
                      ·
                        rfl

theorem cell23_8249846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_8249846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249846 prefixEnd_8249846 := by exact prefixLift 8249846
  have htrace : WordTrace (prefixWord ++ tailWord_8249846) baseStart_8249846 baseEnd_8249846 := by
    simpa [prefixWord, tailWord_8249846, baseEnd_8249846] using wordTrace_append hprefix tailTrace_8249846
  have hstable : (prefixWord ++ tailWord_8249846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249846).length < 2 ^ (prefixWord ++ tailWord_8249846).sum := by decide
  have hdescent : baseEnd_8249846 < baseStart_8249846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249863 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_8249863 : Nat := 118140960795 + 8249863 * 2 ^ 59
def prefixEnd_8249863 : Nat := 4983230072969 + 3 ^ 40 * 8249863 * 2
def baseEnd_8249863 : Nat := 4236145052743161106772077

theorem tailTrace_8249863 : CollatzResearch.WordTrace tailWord_8249863 prefixEnd_8249863 4236145052743161106772077 := by
  unfold tailWord_8249863
  simp only [CollatzResearch.WordTrace]
  refine ⟨300897223311162790272122243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200598148874108526848081495 300897223311162790272122243)
  ·
    refine ⟨451345834966744185408183365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300897223311162790272122243 451345834966744185408183365)
    ·
      refine ⟨84627344056264534764034381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451345834966744185408183365 84627344056264534764034381)
      ·
        refine ⟨31735254021099200536512893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84627344056264534764034381 31735254021099200536512893)
        ·
          refine ⟨11900720257912200201192335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31735254021099200536512893 11900720257912200201192335)
          ·
            refine ⟨17851080386868300301788503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11900720257912200201192335 17851080386868300301788503)
            ·
              refine ⟨26776620580302450452682755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17851080386868300301788503 26776620580302450452682755)
              ·
                refine ⟨40164930870453675679024133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26776620580302450452682755 40164930870453675679024133)
                ·
                  refine ⟨7530924538210064189817025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40164930870453675679024133 7530924538210064189817025)
                  ·
                    refine ⟨5648193403657548142362769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7530924538210064189817025 5648193403657548142362769)
                    ·
                      refine ⟨4236145052743161106772077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648193403657548142362769 4236145052743161106772077)
                      ·
                        rfl

theorem cell23_8249863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_8249863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249863 prefixEnd_8249863 := by exact prefixLift 8249863
  have htrace : WordTrace (prefixWord ++ tailWord_8249863) baseStart_8249863 baseEnd_8249863 := by
    simpa [prefixWord, tailWord_8249863, baseEnd_8249863] using wordTrace_append hprefix tailTrace_8249863
  have hstable : (prefixWord ++ tailWord_8249863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249863).length < 2 ^ (prefixWord ++ tailWord_8249863).sum := by decide
  have hdescent : baseEnd_8249863 < baseStart_8249863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249876 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_8249876 : Nat := 118140960795 + 8249876 * 2 ^ 59
def prefixEnd_8249876 : Nat := 4983230072969 + 3 ^ 40 * 8249876 * 2
def baseEnd_8249876 : Nat := 4236151727991669555909517

theorem tailTrace_8249876 : CollatzResearch.WordTrace tailWord_8249876 prefixEnd_8249876 4236151727991669555909517 := by
  unfold tailWord_8249876
  simp only [CollatzResearch.WordTrace]
  refine ⟨150448848730057846746172741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200598464973410462328230321 150448848730057846746172741)
  ·
    refine ⟨28209159136885846264907389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150448848730057846746172741 28209159136885846264907389)
    ·
      refine ⟨10578434676332192349340271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28209159136885846264907389 10578434676332192349340271)
      ·
        refine ⟨15867652014498288524010407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10578434676332192349340271 15867652014498288524010407)
        ·
          refine ⟨23801478021747432786015611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15867652014498288524010407 23801478021747432786015611)
          ·
            refine ⟨35702217032621149179023417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23801478021747432786015611 35702217032621149179023417)
            ·
              refine ⟨26776662774465861884267563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35702217032621149179023417 26776662774465861884267563)
              ·
                refine ⟨40164994161698792826401345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26776662774465861884267563 40164994161698792826401345)
                ·
                  refine ⟨30123745621274094619801009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40164994161698792826401345 30123745621274094619801009)
                  ·
                    refine ⟨22592809215955570964850757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30123745621274094619801009 22592809215955570964850757)
                    ·
                      refine ⟨4236151727991669555909517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22592809215955570964850757 4236151727991669555909517)
                      ·
                        rfl

theorem cell23_8249876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_8249876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249876 prefixEnd_8249876 := by exact prefixLift 8249876
  have htrace : WordTrace (prefixWord ++ tailWord_8249876) baseStart_8249876 baseEnd_8249876 := by
    simpa [prefixWord, tailWord_8249876, baseEnd_8249876] using wordTrace_append hprefix tailTrace_8249876
  have hstable : (prefixWord ++ tailWord_8249876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249876).length < 2 ^ (prefixWord ++ tailWord_8249876).sum := by decide
  have hdescent : baseEnd_8249876 < baseStart_8249876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249880 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 2, 2, 2]
def baseStart_8249880 : Nat := 118140960795 + 8249880 * 2 ^ 59
def prefixEnd_8249880 : Nat := 4983230072969 + 3 ^ 40 * 8249880 * 2
def baseEnd_8249880 : Nat := 4236153781914287540259499

theorem tailTrace_8249880 : CollatzResearch.WordTrace tailWord_8249880 prefixEnd_8249880 4236153781914287540259499 := by
  unfold tailWord_8249880
  simp only [CollatzResearch.WordTrace]
  refine ⟨150448921676050601087745547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200598562234734134783660729 150448921676050601087745547)
  ·
    refine ⟨225673382514075901631618321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150448921676050601087745547 225673382514075901631618321)
    ·
      refine ⟨169255036885556926223713741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225673382514075901631618321 169255036885556926223713741)
      ·
        refine ⟨63470638832083847333892653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169255036885556926223713741 63470638832083847333892653)
        ·
          refine ⟨23801489562031442750209745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63470638832083847333892653 23801489562031442750209745)
          ·
            refine ⟨17851117171523582062657309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23801489562031442750209745 17851117171523582062657309)
            ·
              refine ⟨6694168939321343273496491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17851117171523582062657309 6694168939321343273496491)
              ·
                refine ⟨10041253408982014910244737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6694168939321343273496491 10041253408982014910244737)
                ·
                  refine ⟨7530940056736511182683553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10041253408982014910244737 7530940056736511182683553)
                  ·
                    refine ⟨5648205042552383387012665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7530940056736511182683553 5648205042552383387012665)
                    ·
                      refine ⟨4236153781914287540259499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648205042552383387012665 4236153781914287540259499)
                      ·
                        rfl

theorem cell23_8249880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_8249880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249880 prefixEnd_8249880 := by exact prefixLift 8249880
  have htrace : WordTrace (prefixWord ++ tailWord_8249880) baseStart_8249880 baseEnd_8249880 := by
    simpa [prefixWord, tailWord_8249880, baseEnd_8249880] using wordTrace_append hprefix tailTrace_8249880
  have hstable : (prefixWord ++ tailWord_8249880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249880).length < 2 ^ (prefixWord ++ tailWord_8249880).sum := by decide
  have hdescent : baseEnd_8249880 < baseStart_8249880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249882 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_8249882 : Nat := 118140960795 + 8249882 * 2 ^ 59
def prefixEnd_8249882 : Nat := 4983230072969 + 3 ^ 40 * 8249882 * 2
def baseEnd_8249882 : Nat := 1412051602958532177478163

theorem tailTrace_8249882 : CollatzResearch.WordTrace tailWord_8249882 prefixEnd_8249882 1412051602958532177478163 := by
  unfold tailWord_8249882
  simp only [CollatzResearch.WordTrace]
  refine ⟨75224479074523489129265975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200598610865395971011375933 75224479074523489129265975)
  ·
    refine ⟨112836718611785233693898963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75224479074523489129265975 112836718611785233693898963)
    ·
      refine ⟨169255077917677850540848445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112836718611785233693898963 169255077917677850540848445)
      ·
        refine ⟨63470654219129193952818167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169255077917677850540848445 63470654219129193952818167)
        ·
          refine ⟨95205981328693790929227251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63470654219129193952818167 95205981328693790929227251)
          ·
            refine ⟨142808971993040686393840877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95205981328693790929227251 142808971993040686393840877)
            ·
              refine ⟨53553364497390257397690329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142808971993040686393840877 53553364497390257397690329)
              ·
                refine ⟨40165023373042693048267747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53553364497390257397690329 40165023373042693048267747)
                ·
                  refine ⟨60247535059564039572401621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40165023373042693048267747 60247535059564039572401621)
                  ·
                    refine ⟨1412051602958532177478163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60247535059564039572401621 1412051602958532177478163)
                    ·
                      rfl

theorem cell23_8249882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_8249882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249882 prefixEnd_8249882 := by exact prefixLift 8249882
  have htrace : WordTrace (prefixWord ++ tailWord_8249882) baseStart_8249882 baseEnd_8249882 := by
    simpa [prefixWord, tailWord_8249882, baseEnd_8249882] using wordTrace_append hprefix tailTrace_8249882
  have hstable : (prefixWord ++ tailWord_8249882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249882).length < 2 ^ (prefixWord ++ tailWord_8249882).sum := by decide
  have hdescent : baseEnd_8249882 < baseStart_8249882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249919 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_8249919 : Nat := 118140960795 + 8249919 * 2 ^ 59
def prefixEnd_8249919 : Nat := 4983230072969 + 3 ^ 40 * 8249919 * 2
def baseEnd_8249919 : Nat := 4236173807659812887671819

theorem tailTrace_8249919 : CollatzResearch.WordTrace tailWord_8249919 prefixEnd_8249919 4236173807659812887671819 := by
  unfold tailWord_8249919
  simp only [CollatzResearch.WordTrace]
  refine ⟨300899265798959911836160811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200599510532639941224107207 300899265798959911836160811)
  ·
    refine ⟨451348898698439867754241217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300899265798959911836160811 451348898698439867754241217)
    ·
      refine ⟨338511674023829900815680913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451348898698439867754241217 338511674023829900815680913)
      ·
        refine ⟨253883755517872425611760685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338511674023829900815680913 253883755517872425611760685)
        ·
          refine ⟨95206408319202159604410257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253883755517872425611760685 95206408319202159604410257)
          ·
            refine ⟨71404806239401619703307693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95206408319202159604410257 71404806239401619703307693)
            ·
              refine ⟨26776802339775607388740385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71404806239401619703307693 26776802339775607388740385)
              ·
                refine ⟨20082601754831705541555289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26776802339775607388740385 20082601754831705541555289)
                ·
                  refine ⟨15061951316123779156166467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20082601754831705541555289 15061951316123779156166467)
                  ·
                    refine ⟨22592926974185668734249701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15061951316123779156166467 22592926974185668734249701)
                    ·
                      refine ⟨4236173807659812887671819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22592926974185668734249701 4236173807659812887671819)
                      ·
                        rfl

theorem cell23_8249919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_8249919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249919 prefixEnd_8249919 := by exact prefixLift 8249919
  have htrace : WordTrace (prefixWord ++ tailWord_8249919) baseStart_8249919 baseEnd_8249919 := by
    simpa [prefixWord, tailWord_8249919, baseEnd_8249919] using wordTrace_append hprefix tailTrace_8249919
  have hstable : (prefixWord ++ tailWord_8249919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249919).length < 2 ^ (prefixWord ++ tailWord_8249919).sum := by decide
  have hdescent : baseEnd_8249919 < baseStart_8249919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249926 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_8249926 : Nat := 118140960795 + 8249926 * 2 ^ 59
def prefixEnd_8249926 : Nat := 4983230072969 + 3 ^ 40 * 8249926 * 2
def baseEnd_8249926 : Nat := 4236177402024394360284287

theorem tailTrace_8249926 : CollatzResearch.WordTrace tailWord_8249926 prefixEnd_8249926 4236177402024394360284287 := by
  unfold tailWord_8249926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9403110034685454750989551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 200599680739956368021110421 9403110034685454750989551)
  ·
    refine ⟨14104665052028182126484327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9403110034685454750989551 14104665052028182126484327)
    ·
      refine ⟨21156997578042273189726491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14104665052028182126484327 21156997578042273189726491)
      ·
        refine ⟨31735496367063409784589737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21156997578042273189726491 31735496367063409784589737)
        ·
          refine ⟨23801622275297557338442303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31735496367063409784589737 23801622275297557338442303)
          ·
            refine ⟨35702433412946336007663455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23801622275297557338442303 35702433412946336007663455)
            ·
              refine ⟨53553650119419504011495183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35702433412946336007663455 53553650119419504011495183)
              ·
                refine ⟨80330475179129256017242775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53553650119419504011495183 80330475179129256017242775)
                ·
                  refine ⟨120495712768693884025864163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80330475179129256017242775 120495712768693884025864163)
                  ·
                    refine ⟨180743569153040826038796245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120495712768693884025864163 180743569153040826038796245)
                    ·
                      refine ⟨4236177402024394360284287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180743569153040826038796245 4236177402024394360284287)
                      ·
                        rfl

theorem cell23_8249926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_8249926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249926 prefixEnd_8249926 := by exact prefixLift 8249926
  have htrace : WordTrace (prefixWord ++ tailWord_8249926) baseStart_8249926 baseEnd_8249926 := by
    simpa [prefixWord, tailWord_8249926, baseEnd_8249926] using wordTrace_append hprefix tailTrace_8249926
  have hstable : (prefixWord ++ tailWord_8249926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249926).length < 2 ^ (prefixWord ++ tailWord_8249926).sum := by decide
  have hdescent : baseEnd_8249926 < baseStart_8249926 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249956 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_8249956 : Nat := 118140960795 + 8249956 * 2 ^ 59
def prefixEnd_8249956 : Nat := 4983230072969 + 3 ^ 40 * 8249956 * 2
def baseEnd_8249956 : Nat := 4236192806444029242909149

theorem tailTrace_8249956 : CollatzResearch.WordTrace tailWord_8249956 prefixEnd_8249956 4236192806444029242909149 := by
  unfold tailWord_8249956
  simp only [CollatzResearch.WordTrace]
  refine ⟨150450307649912933577628861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200600410199883911436838481 150450307649912933577628861)
  ·
    refine ⟨56418865368717350091610823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150450307649912933577628861 56418865368717350091610823)
    ·
      refine ⟨84628298053076025137416235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56418865368717350091610823 84628298053076025137416235)
      ·
        refine ⟨126942447079614037706124353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84628298053076025137416235 126942447079614037706124353)
        ·
          refine ⟨95206835309710528279593265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126942447079614037706124353 95206835309710528279593265)
          ·
            refine ⟨71405126482282896209694949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95206835309710528279593265 71405126482282896209694949)
            ·
              refine ⟨13388461215428043039317803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71405126482282896209694949 13388461215428043039317803)
              ·
                refine ⟨20082691823142064558976705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13388461215428043039317803 20082691823142064558976705)
                ·
                  refine ⟨15062018867356548419232529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20082691823142064558976705 15062018867356548419232529)
                  ·
                    refine ⟨11296514150517411314424397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15062018867356548419232529 11296514150517411314424397)
                    ·
                      refine ⟨4236192806444029242909149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11296514150517411314424397 4236192806444029242909149)
                      ·
                        rfl

theorem cell23_8249956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_8249956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249956 prefixEnd_8249956 := by exact prefixLift 8249956
  have htrace : WordTrace (prefixWord ++ tailWord_8249956) baseStart_8249956 baseEnd_8249956 := by
    simpa [prefixWord, tailWord_8249956, baseEnd_8249956] using wordTrace_append hprefix tailTrace_8249956
  have hstable : (prefixWord ++ tailWord_8249956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249956).length < 2 ^ (prefixWord ++ tailWord_8249956).sum := by decide
  have hdescent : baseEnd_8249956 < baseStart_8249956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8249989 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_8249989 : Nat := 118140960795 + 8249989 * 2 ^ 59
def prefixEnd_8249989 : Nat := 4983230072969 + 3 ^ 40 * 8249989 * 2
def baseEnd_8249989 : Nat := 1412069917101875871265499

theorem tailTrace_8249989 : CollatzResearch.WordTrace tailWord_8249989 prefixEnd_8249989 1412069917101875871265499 := by
  unfold tailWord_8249989
  simp only [CollatzResearch.WordTrace]
  refine ⟨300901818908706313791209021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200601212605804209194139347 300901818908706313791209021)
  ·
    refine ⟨112838182090764867671703383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300901818908706313791209021 112838182090764867671703383)
    ·
      refine ⟨169257273136147301507555075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112838182090764867671703383 169257273136147301507555075)
      ·
        refine ⟨253885909704220952261332613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169257273136147301507555075 253885909704220952261332613)
        ·
          refine ⟨47603608069541428548999865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253885909704220952261332613 47603608069541428548999865)
          ·
            refine ⟨35702706052156071411749899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47603608069541428548999865 35702706052156071411749899)
            ·
              refine ⟨53554059078234107117624849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35702706052156071411749899 53554059078234107117624849)
              ·
                refine ⟨40165544308675580338218637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53554059078234107117624849 40165544308675580338218637)
                ·
                  refine ⟨15062079115753342626831989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40165544308675580338218637 15062079115753342626831989)
                  ·
                    refine ⟨1412069917101875871265499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15062079115753342626831989 1412069917101875871265499)
                    ·
                      rfl

theorem cell23_8249989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_8249989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8249989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8249989 prefixEnd_8249989 := by exact prefixLift 8249989
  have htrace : WordTrace (prefixWord ++ tailWord_8249989) baseStart_8249989 baseEnd_8249989 := by
    simpa [prefixWord, tailWord_8249989, baseEnd_8249989] using wordTrace_append hprefix tailTrace_8249989
  have hstable : (prefixWord ++ tailWord_8249989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8249989).length < 2 ^ (prefixWord ++ tailWord_8249989).sum := by decide
  have hdescent : baseEnd_8249989 < baseStart_8249989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8249989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250009 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_8250009 : Nat := 118140960795 + 8250009 * 2 ^ 59
def prefixEnd_8250009 : Nat := 4983230072969 + 3 ^ 40 * 8250009 * 2
def baseEnd_8250009 : Nat := 4236220020918717535546405

theorem tailTrace_8250009 : CollatzResearch.WordTrace tailWord_8250009 prefixEnd_8250009 4236220020918717535546405 := by
  unfold tailWord_8250009
  simp only [CollatzResearch.WordTrace]
  refine ⟨300902548368633857206937081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200601698912422571471291387 300902548368633857206937081)
  ·
    refine ⟨225676911276475392905202811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300902548368633857206937081 225676911276475392905202811)
    ·
      refine ⟨338515366914713089357804217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225676911276475392905202811 338515366914713089357804217)
      ·
        refine ⟨253886525186034817018353163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338515366914713089357804217 253886525186034817018353163)
        ·
          refine ⟨380829787779052225527529745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253886525186034817018353163 380829787779052225527529745)
          ·
            refine ⟨285622340834289169145647309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380829787779052225527529745 285622340834289169145647309)
            ·
              refine ⟨107108377812858438429617741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285622340834289169145647309 107108377812858438429617741)
              ·
                refine ⟨40165641679821914411106653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107108377812858438429617741 40165641679821914411106653)
                ·
                  refine ⟨15062115629933217904164995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40165641679821914411106653 15062115629933217904164995)
                  ·
                    refine ⟨22593173444899826856247493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15062115629933217904164995 22593173444899826856247493)
                    ·
                      refine ⟨4236220020918717535546405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22593173444899826856247493 4236220020918717535546405)
                      ·
                        rfl

theorem cell23_8250009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_8250009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250009 prefixEnd_8250009 := by exact prefixLift 8250009
  have htrace : WordTrace (prefixWord ++ tailWord_8250009) baseStart_8250009 baseEnd_8250009 := by
    simpa [prefixWord, tailWord_8250009, baseEnd_8250009] using wordTrace_append hprefix tailTrace_8250009
  have hstable : (prefixWord ++ tailWord_8250009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250009).length < 2 ^ (prefixWord ++ tailWord_8250009).sum := by decide
  have hdescent : baseEnd_8250009 < baseStart_8250009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250013 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_8250013 : Nat := 118140960795 + 8250013 * 2 ^ 59
def prefixEnd_8250013 : Nat := 4983230072969 + 3 ^ 40 * 8250013 * 2
def baseEnd_8250013 : Nat := 4236222074841335519896387

theorem tailTrace_8250013 : CollatzResearch.WordTrace tailWord_8250013 prefixEnd_8250013 4236222074841335519896387 := by
  unfold tailWord_8250013
  simp only [CollatzResearch.WordTrace]
  refine ⟨300902694260619365890082693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200601796173746243926721795 300902694260619365890082693)
  ·
    refine ⟨56419255173866131104390505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300902694260619365890082693 56419255173866131104390505)
    ·
      refine ⟨42314441380399598328292879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56419255173866131104390505 42314441380399598328292879)
      ·
        refine ⟨63471662070599397492439319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42314441380399598328292879 63471662070599397492439319)
        ·
          refine ⟨95207493105899096238658979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63471662070599397492439319 95207493105899096238658979)
          ·
            refine ⟨142811239658848644357988469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95207493105899096238658979 142811239658848644357988469)
            ·
              refine ⟨13388553718017060408561419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142811239658848644357988469 13388553718017060408561419)
              ·
                refine ⟨20082830577025590612842129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13388553718017060408561419 20082830577025590612842129)
                ·
                  refine ⟨15062122932769192959631597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20082830577025590612842129 15062122932769192959631597)
                  ·
                    refine ⟨5648296099788447359861849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15062122932769192959631597 5648296099788447359861849)
                    ·
                      refine ⟨4236222074841335519896387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648296099788447359861849 4236222074841335519896387)
                      ·
                        rfl

theorem cell23_8250013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_8250013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250013 prefixEnd_8250013 := by exact prefixLift 8250013
  have htrace : WordTrace (prefixWord ++ tailWord_8250013) baseStart_8250013 baseEnd_8250013 := by
    simpa [prefixWord, tailWord_8250013, baseEnd_8250013] using wordTrace_append hprefix tailTrace_8250013
  have hstable : (prefixWord ++ tailWord_8250013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250013).length < 2 ^ (prefixWord ++ tailWord_8250013).sum := by decide
  have hdescent : baseEnd_8250013 < baseStart_8250013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250020 : List Nat := [2, 3, 1, 2, 2, 1, 4, 3, 1, 1, 3]
def baseStart_8250020 : Nat := 118140960795 + 8250020 * 2 ^ 59
def prefixEnd_8250020 : Nat := 4983230072969 + 3 ^ 40 * 8250020 * 2
def baseEnd_8250020 : Nat := 4236225669205916992508855

theorem tailTrace_8250020 : CollatzResearch.WordTrace tailWord_8250020 prefixEnd_8250020 4236225669205916992508855 := by
  unfold tailWord_8250020
  simp only [CollatzResearch.WordTrace]
  refine ⟨150451474785797003042793757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200601966381062670723725009 150451474785797003042793757)
  ·
    refine ⟨56419303044673876141047659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150451474785797003042793757 56419303044673876141047659)
    ·
      refine ⟨84628954567010814211571489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56419303044673876141047659 84628954567010814211571489)
      ·
        refine ⟨63471715925258110658678617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84628954567010814211571489 63471715925258110658678617)
        ·
          refine ⟨47603786943943582994008963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63471715925258110658678617 47603786943943582994008963)
          ·
            refine ⟨71405680415915374491013445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47603786943943582994008963 71405680415915374491013445)
            ·
              refine ⟨13388565077984132717065021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71405680415915374491013445 13388565077984132717065021)
              ·
                refine ⟨5020711904244049768899383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13388565077984132717065021 5020711904244049768899383)
                ·
                  refine ⟨7531067856366074653349075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020711904244049768899383 7531067856366074653349075)
                  ·
                    refine ⟨11296601784549111980023613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7531067856366074653349075 11296601784549111980023613)
                    ·
                      refine ⟨4236225669205916992508855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11296601784549111980023613 4236225669205916992508855)
                      ·
                        rfl

theorem cell23_8250020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_8250020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250020 prefixEnd_8250020 := by exact prefixLift 8250020
  have htrace : WordTrace (prefixWord ++ tailWord_8250020) baseStart_8250020 baseEnd_8250020 := by
    simpa [prefixWord, tailWord_8250020, baseEnd_8250020] using wordTrace_append hprefix tailTrace_8250020
  have hstable : (prefixWord ++ tailWord_8250020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250020).length < 2 ^ (prefixWord ++ tailWord_8250020).sum := by decide
  have hdescent : baseEnd_8250020 < baseStart_8250020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250046 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_8250046 : Nat := 118140960795 + 8250046 * 2 ^ 59
def prefixEnd_8250046 : Nat := 4983230072969 + 3 ^ 40 * 8250046 * 2
def baseEnd_8250046 : Nat := 4236239019702933890783735

theorem tailTrace_8250046 : CollatzResearch.WordTrace tailWord_8250046 prefixEnd_8250046 4236239019702933890783735 := by
  unfold tailWord_8250046
  simp only [CollatzResearch.WordTrace]
  refine ⟨37612987233687476565754249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200602598579666541684022661 37612987233687476565754249)
  ·
    refine ⟨28209740425265607424315687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37612987233687476565754249 28209740425265607424315687)
    ·
      refine ⟨42314610637898411136473531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28209740425265607424315687 42314610637898411136473531)
      ·
        refine ⟨63471915956847616704710297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42314610637898411136473531 63471915956847616704710297)
        ·
          refine ⟨47603936967635712528532723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63471915956847616704710297 47603936967635712528532723)
          ·
            refine ⟨71405905451453568792799085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47603936967635712528532723 71405905451453568792799085)
            ·
              refine ⟨26777214544295088297299657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71405905451453568792799085 26777214544295088297299657)
              ·
                refine ⟨20082910908221316222974743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26777214544295088297299657 20082910908221316222974743)
                ·
                  refine ⟨30124366362331974334462115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20082910908221316222974743 30124366362331974334462115)
                  ·
                    refine ⟨45186549543497961501693173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30124366362331974334462115 45186549543497961501693173)
                    ·
                      refine ⟨4236239019702933890783735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45186549543497961501693173 4236239019702933890783735)
                      ·
                        rfl

theorem cell23_8250046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_8250046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250046 prefixEnd_8250046 := by exact prefixLift 8250046
  have htrace : WordTrace (prefixWord ++ tailWord_8250046) baseStart_8250046 baseEnd_8250046 := by
    simpa [prefixWord, tailWord_8250046, baseEnd_8250046] using wordTrace_append hprefix tailTrace_8250046
  have hstable : (prefixWord ++ tailWord_8250046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250046).length < 2 ^ (prefixWord ++ tailWord_8250046).sum := by decide
  have hdescent : baseEnd_8250046 < baseStart_8250046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250056 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_8250056 : Nat := 118140960795 + 8250056 * 2 ^ 59
def prefixEnd_8250056 : Nat := 4983230072969 + 3 ^ 40 * 8250056 * 2
def baseEnd_8250056 : Nat := 4236244154509478851658689

theorem tailTrace_8250056 : CollatzResearch.WordTrace tailWord_8250056 prefixEnd_8250056 4236244154509478851658689 := by
  unfold tailWord_8250056
  simp only [CollatzResearch.WordTrace]
  refine ⟨150452131299731792116949011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200602841732975722822598681 150452131299731792116949011)
  ·
    refine ⟨225678196949597688175423517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150452131299731792116949011 225678196949597688175423517)
    ·
      refine ⟨84629323856099133065783819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225678196949597688175423517 84629323856099133065783819)
      ·
        refine ⟨126943985784148699598675729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84629323856099133065783819 126943985784148699598675729)
        ·
          refine ⟨95207989338111524699006797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126943985784148699598675729 95207989338111524699006797)
          ·
            refine ⟨35702996001791821762127549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95207989338111524699006797 35702996001791821762127549)
            ·
              refine ⟨13388623500671933160797831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35702996001791821762127549 13388623500671933160797831)
              ·
                refine ⟨20082935251007899741196747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13388623500671933160797831 20082935251007899741196747)
                ·
                  refine ⟨30124402876511849611795121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20082935251007899741196747 30124402876511849611795121)
                  ·
                    refine ⟨22593302157383887208846341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30124402876511849611795121 22593302157383887208846341)
                    ·
                      refine ⟨4236244154509478851658689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22593302157383887208846341 4236244154509478851658689)
                      ·
                        rfl

theorem cell23_8250056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_8250056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250056 prefixEnd_8250056 := by exact prefixLift 8250056
  have htrace : WordTrace (prefixWord ++ tailWord_8250056) baseStart_8250056 baseEnd_8250056 := by
    simpa [prefixWord, tailWord_8250056, baseEnd_8250056] using wordTrace_append hprefix tailTrace_8250056
  have hstable : (prefixWord ++ tailWord_8250056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250056).length < 2 ^ (prefixWord ++ tailWord_8250056).sum := by decide
  have hdescent : baseEnd_8250056 < baseStart_8250056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250060 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 3, 2, 2]
def baseStart_8250060 : Nat := 118140960795 + 8250060 * 2 ^ 59
def prefixEnd_8250060 : Nat := 4983230072969 + 3 ^ 40 * 8250060 * 2
def baseEnd_8250060 : Nat := 4236246208432096836008671

theorem tailTrace_8250060 : CollatzResearch.WordTrace tailWord_8250060 prefixEnd_8250060 4236246208432096836008671 := by
  unfold tailWord_8250060
  simp only [CollatzResearch.WordTrace]
  refine ⟨150452204245724546458521817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200602938994299395278029089 150452204245724546458521817)
  ·
    refine ⟨112839153184293409843891363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150452204245724546458521817 112839153184293409843891363)
    ·
      refine ⟨169258729776440114765837045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112839153184293409843891363 169258729776440114765837045)
      ·
        refine ⟨15868005916541260759297223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169258729776440114765837045 15868005916541260759297223)
        ·
          refine ⟨23802008874811891138945835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15868005916541260759297223 23802008874811891138945835)
          ·
            refine ⟨35703013312217836708418753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23802008874811891138945835 35703013312217836708418753)
            ·
              refine ⟨26777259984163377531314065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35703013312217836708418753 26777259984163377531314065)
              ·
                refine ⟨20082944988122533148485549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26777259984163377531314065 20082944988122533148485549)
                ·
                  refine ⟨7531104370545949930682081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20082944988122533148485549 7531104370545949930682081)
                  ·
                    refine ⟨5648328277909462448011561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7531104370545949930682081 5648328277909462448011561)
                    ·
                      refine ⟨4236246208432096836008671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648328277909462448011561 4236246208432096836008671)
                      ·
                        rfl

theorem cell23_8250060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_8250060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250060 prefixEnd_8250060 := by exact prefixLift 8250060
  have htrace : WordTrace (prefixWord ++ tailWord_8250060) baseStart_8250060 baseEnd_8250060 := by
    simpa [prefixWord, tailWord_8250060, baseEnd_8250060] using wordTrace_append hprefix tailTrace_8250060
  have hstable : (prefixWord ++ tailWord_8250060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250060).length < 2 ^ (prefixWord ++ tailWord_8250060).sum := by decide
  have hdescent : baseEnd_8250060 < baseStart_8250060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250066 : List Nat := [3, 2, 2, 2, 3, 1, 1, 9]
def baseStart_8250066 : Nat := 118140960795 + 8250066 * 2 ^ 59
def prefixEnd_8250066 : Nat := 4983230072969 + 3 ^ 40 * 8250066 * 2
def baseEnd_8250066 : Nat := 156898121826519400464209

theorem tailTrace_8250066 : CollatzResearch.WordTrace tailWord_8250066 prefixEnd_8250066 156898121826519400464209 := by
  unfold tailWord_8250066
  simp only [CollatzResearch.WordTrace]
  refine ⟨75226156832356838985440513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200603084886284903961174701 75226156832356838985440513)
  ·
    refine ⟨56419617624267629239080385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75226156832356838985440513 56419617624267629239080385)
    ·
      refine ⟨42314713218200721929310289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56419617624267629239080385 42314713218200721929310289)
      ·
        refine ⟨31736034913650541446982717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42314713218200721929310289 31736034913650541446982717)
        ·
          refine ⟨11901013092618953042618519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31736034913650541446982717 11901013092618953042618519)
          ·
            refine ⟨17851519638928429563927779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901013092618953042618519 17851519638928429563927779)
            ·
              refine ⟨26777279458392644345891669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17851519638928429563927779 26777279458392644345891669)
              ·
                refine ⟨156898121826519400464209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26777279458392644345891669 156898121826519400464209)
                ·
                  rfl

theorem cell23_8250066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 9].length) (baseStart_8250066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250066 prefixEnd_8250066 := by exact prefixLift 8250066
  have htrace : WordTrace (prefixWord ++ tailWord_8250066) baseStart_8250066 baseEnd_8250066 := by
    simpa [prefixWord, tailWord_8250066, baseEnd_8250066] using wordTrace_append hprefix tailTrace_8250066
  have hstable : (prefixWord ++ tailWord_8250066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250066).length < 2 ^ (prefixWord ++ tailWord_8250066).sum := by decide
  have hdescent : baseEnd_8250066 < baseStart_8250066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250093 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_8250093 : Nat := 118140960795 + 8250093 * 2 ^ 59
def prefixEnd_8250093 : Nat := 4983230072969 + 3 ^ 40 * 8250093 * 2
def baseEnd_8250093 : Nat := 4236263153293695206896019

theorem tailTrace_8250093 : CollatzResearch.WordTrace tailWord_8250093 prefixEnd_8250093 4236263153293695206896019 := by
  unfold tailWord_8250093
  simp only [CollatzResearch.WordTrace]
  refine ⟨300905612100329539552994933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200603741400219693035329955 300905612100329539552994933)
  ·
    refine ⟨28209901134405894333093275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300905612100329539552994933 28209901134405894333093275)
    ·
      refine ⟨42314851701608841499639913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28209901134405894333093275 42314851701608841499639913)
      ·
        refine ⟨31736138776206631124729935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42314851701608841499639913 31736138776206631124729935)
        ·
          refine ⟨47604208164309946687094903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31736138776206631124729935 47604208164309946687094903)
          ·
            refine ⟨71406312246464920030642355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47604208164309946687094903 71406312246464920030642355)
            ·
              refine ⟨107109468369697380045963533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71406312246464920030642355 107109468369697380045963533)
              ·
                refine ⟨40166050638636517517236325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107109468369697380045963533 40166050638636517517236325)
                ·
                  refine ⟨7531134494744347034481811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40166050638636517517236325 7531134494744347034481811)
                  ·
                    refine ⟨11296701742116520551722717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7531134494744347034481811 11296701742116520551722717)
                    ·
                      refine ⟨4236263153293695206896019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11296701742116520551722717 4236263153293695206896019)
                      ·
                        rfl

theorem cell23_8250093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_8250093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250093 prefixEnd_8250093 := by exact prefixLift 8250093
  have htrace : WordTrace (prefixWord ++ tailWord_8250093) baseStart_8250093 baseEnd_8250093 := by
    simpa [prefixWord, tailWord_8250093, baseEnd_8250093] using wordTrace_append hprefix tailTrace_8250093
  have hstable : (prefixWord ++ tailWord_8250093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250093).length < 2 ^ (prefixWord ++ tailWord_8250093).sum := by decide
  have hdescent : baseEnd_8250093 < baseStart_8250093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250094 : List Nat := [4, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_8250094 : Nat := 118140960795 + 8250094 * 2 ^ 59
def prefixEnd_8250094 : Nat := 4983230072969 + 3 ^ 40 * 8250094 * 2
def baseEnd_8250094 : Nat := 4236263666774349702983515

theorem tailTrace_8250094 : CollatzResearch.WordTrace tailWord_8250094 prefixEnd_8250094 4236263666774349702983515 := by
  unfold tailWord_8250094
  simp only [CollatzResearch.WordTrace]
  refine ⟨37613206071665739590472667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200603765715550611149187557 37613206071665739590472667)
  ·
    refine ⟨56419809107498609385709001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37613206071665739590472667 56419809107498609385709001)
    ·
      refine ⟨42314856830623957039281751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56419809107498609385709001 42314856830623957039281751)
      ·
        refine ⟨63472285245935935558922627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42314856830623957039281751 63472285245935935558922627)
        ·
          refine ⟨95208427868903903338383941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63472285245935935558922627 95208427868903903338383941)
          ·
            refine ⟨17851580225419481875946989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95208427868903903338383941 17851580225419481875946989)
            ·
              refine ⟨6694342584532305703480121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17851580225419481875946989 6694342584532305703480121)
              ·
                refine ⟨5020756938399229277610091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6694342584532305703480121 5020756938399229277610091)
                ·
                  refine ⟨7531135407598843916415137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020756938399229277610091 7531135407598843916415137)
                  ·
                    refine ⟨5648351555699132937311353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7531135407598843916415137 5648351555699132937311353)
                    ·
                      refine ⟨4236263666774349702983515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648351555699132937311353 4236263666774349702983515)
                      ·
                        rfl

theorem cell23_8250094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_8250094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250094 prefixEnd_8250094 := by exact prefixLift 8250094
  have htrace : WordTrace (prefixWord ++ tailWord_8250094) baseStart_8250094 baseEnd_8250094 := by
    simpa [prefixWord, tailWord_8250094, baseEnd_8250094] using wordTrace_append hprefix tailTrace_8250094
  have hstable : (prefixWord ++ tailWord_8250094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250094).length < 2 ^ (prefixWord ++ tailWord_8250094).sum := by decide
  have hdescent : baseEnd_8250094 < baseStart_8250094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250099 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 4]
def baseStart_8250099 : Nat := 118140960795 + 8250099 * 2 ^ 59
def prefixEnd_8250099 : Nat := 4983230072969 + 3 ^ 40 * 8250099 * 2
def baseEnd_8250099 : Nat := 4236266234177622183420991

theorem tailTrace_8250099 : CollatzResearch.WordTrace tailWord_8250099 prefixEnd_8250099 4236266234177622183420991 := by
  unfold tailWord_8250099
  simp only [CollatzResearch.WordTrace]
  refine ⟨300905830938307802577713351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200603887292205201718475567 300905830938307802577713351)
  ·
    refine ⟨451358746407461703866570027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300905830938307802577713351 451358746407461703866570027)
    ·
      refine ⟨677038119611192555799855041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451358746407461703866570027 677038119611192555799855041)
      ·
        refine ⟨507778589708394416849891281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677038119611192555799855041 507778589708394416849891281)
        ·
          refine ⟨380833942281295812637418461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507778589708394416849891281 380833942281295812637418461)
          ·
            refine ⟨142812728355485929739031923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380833942281295812637418461 142812728355485929739031923)
            ·
              refine ⟨214219092533228894608547885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142812728355485929739031923 214219092533228894608547885)
              ·
                refine ⟨80332159699960835478205457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214219092533228894608547885 80332159699960835478205457)
                ·
                  refine ⟨60249119774970626608654093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80332159699960835478205457 60249119774970626608654093)
                  ·
                    refine ⟨22593419915613984978245285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60249119774970626608654093 22593419915613984978245285)
                    ·
                      refine ⟨4236266234177622183420991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22593419915613984978245285 4236266234177622183420991)
                      ·
                        rfl

theorem cell23_8250099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_8250099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250099 prefixEnd_8250099 := by exact prefixLift 8250099
  have htrace : WordTrace (prefixWord ++ tailWord_8250099) baseStart_8250099 baseEnd_8250099 := by
    simpa [prefixWord, tailWord_8250099, baseEnd_8250099] using wordTrace_append hprefix tailTrace_8250099
  have hstable : (prefixWord ++ tailWord_8250099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250099).length < 2 ^ (prefixWord ++ tailWord_8250099).sum := by decide
  have hdescent : baseEnd_8250099 < baseStart_8250099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250100 : List Nat := [2, 6, 1, 1, 2, 1, 2, 8]
def baseStart_8250100 : Nat := 118140960795 + 8250100 * 2 ^ 59
def prefixEnd_8250100 : Nat := 4983230072969 + 3 ^ 40 * 8250100 * 2
def baseEnd_8250100 : Nat := 156898768431788025166981

theorem tailTrace_8250100 : CollatzResearch.WordTrace tailWord_8250100 prefixEnd_8250100 156898768431788025166981 := by
  unfold tailWord_8250100
  simp only [CollatzResearch.WordTrace]
  refine ⟨150452933705652089874249877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200603911607536119832333169 150452933705652089874249877)
  ·
    refine ⟨7052481267452441712855463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150452933705652089874249877 7052481267452441712855463)
    ·
      refine ⟨10578721901178662569283195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7052481267452441712855463 10578721901178662569283195)
      ·
        refine ⟨15868082851767993853924793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10578721901178662569283195 15868082851767993853924793)
        ·
          refine ⟨11901062138825995390443595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15868082851767993853924793 11901062138825995390443595)
          ·
            refine ⟨17851593208238993085665393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901062138825995390443595 17851593208238993085665393)
            ·
              refine ⟨13388694906179244814249045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17851593208238993085665393 13388694906179244814249045)
              ·
                refine ⟨156898768431788025166981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13388694906179244814249045 156898768431788025166981)
                ·
                  rfl

theorem cell23_8250100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 8].length) (baseStart_8250100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250100 prefixEnd_8250100 := by exact prefixLift 8250100
  have htrace : WordTrace (prefixWord ++ tailWord_8250100) baseStart_8250100 baseEnd_8250100 := by
    simpa [prefixWord, tailWord_8250100, baseEnd_8250100] using wordTrace_append hprefix tailTrace_8250100
  have hstable : (prefixWord ++ tailWord_8250100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250100).length < 2 ^ (prefixWord ++ tailWord_8250100).sum := by decide
  have hdescent : baseEnd_8250100 < baseStart_8250100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250109 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_8250109 : Nat := 118140960795 + 8250109 * 2 ^ 59
def prefixEnd_8250109 : Nat := 4983230072969 + 3 ^ 40 * 8250109 * 2
def baseEnd_8250109 : Nat := 1412090456328055714765315

theorem tailTrace_8250109 : CollatzResearch.WordTrace tailWord_8250109 prefixEnd_8250109 1412090456328055714765315 := by
  unfold tailWord_8250109
  simp only [CollatzResearch.WordTrace]
  refine ⟨300906195668271574285577381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200604130445514382857051587 300906195668271574285577381)
  ·
    refine ⟨56419911687800920178545759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300906195668271574285577381 56419911687800920178545759)
    ·
      refine ⟨84629867531701380267818639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56419911687800920178545759 84629867531701380267818639)
      ·
        refine ⟨126944801297552070401727959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84629867531701380267818639 126944801297552070401727959)
        ·
          refine ⟨190417201946328105602591939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126944801297552070401727959 190417201946328105602591939)
          ·
            refine ⟨285625802919492158403887909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190417201946328105602591939 285625802919492158403887909)
            ·
              refine ⟨53554838047404779700728983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285625802919492158403887909 53554838047404779700728983)
              ·
                refine ⟨80332257071107169551093475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53554838047404779700728983 80332257071107169551093475)
                ·
                  refine ⟨120498385606660754326640213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80332257071107169551093475 120498385606660754326640213)
                  ·
                    refine ⟨1412090456328055714765315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120498385606660754326640213 1412090456328055714765315)
                    ·
                      rfl

theorem cell23_8250109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_8250109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250109 prefixEnd_8250109 := by exact prefixLift 8250109
  have htrace : WordTrace (prefixWord ++ tailWord_8250109) baseStart_8250109 baseEnd_8250109 := by
    simpa [prefixWord, tailWord_8250109, baseEnd_8250109] using wordTrace_append hprefix tailTrace_8250109
  have hstable : (prefixWord ++ tailWord_8250109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250109).length < 2 ^ (prefixWord ++ tailWord_8250109).sum := by decide
  have hdescent : baseEnd_8250109 < baseStart_8250109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250120 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_8250120 : Nat := 118140960795 + 8250120 * 2 ^ 59
def prefixEnd_8250120 : Nat := 4983230072969 + 3 ^ 40 * 8250120 * 2
def baseEnd_8250120 : Nat := 4236277017271366601258395

theorem tailTrace_8250120 : CollatzResearch.WordTrace tailWord_8250120 prefixEnd_8250120 4236277017271366601258395 := by
  unfold tailWord_8250120
  simp only [CollatzResearch.WordTrace]
  refine ⟨150453298435615861582113907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200604397914154482109485209 150453298435615861582113907)
  ·
    refine ⟨225679947653423792373170861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150453298435615861582113907 225679947653423792373170861)
    ·
      refine ⟨84629980370033922139939073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225679947653423792373170861 84629980370033922139939073)
      ·
        refine ⟨63472485277525441604954305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84629980370033922139939073 63472485277525441604954305)
        ·
          refine ⟨47604363958144081203715729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63472485277525441604954305 47604363958144081203715729)
          ·
            refine ⟨35703272968608060902786797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47604363958144081203715729 35703272968608060902786797)
            ·
              refine ⟨13388727363228022838545049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35703272968608060902786797 13388727363228022838545049)
              ·
                refine ⟨10041545522421017128908787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13388727363228022838545049 10041545522421017128908787)
                ·
                  refine ⟨15062318283631525693363181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10041545522421017128908787 15062318283631525693363181)
                  ·
                    refine ⟨5648369356361822135011193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15062318283631525693363181 5648369356361822135011193)
                    ·
                      refine ⟨4236277017271366601258395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648369356361822135011193 4236277017271366601258395)
                      ·
                        rfl

theorem cell23_8250120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_8250120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250120 prefixEnd_8250120 := by exact prefixLift 8250120
  have htrace : WordTrace (prefixWord ++ tailWord_8250120) baseStart_8250120 baseEnd_8250120 := by
    simpa [prefixWord, tailWord_8250120, baseEnd_8250120] using wordTrace_append hprefix tailTrace_8250120
  have hstable : (prefixWord ++ tailWord_8250120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250120).length < 2 ^ (prefixWord ++ tailWord_8250120).sum := by decide
  have hdescent : baseEnd_8250120 < baseStart_8250120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250133 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_8250133 : Nat := 118140960795 + 8250133 * 2 ^ 59
def prefixEnd_8250133 : Nat := 4983230072969 + 3 ^ 40 * 8250133 * 2
def baseEnd_8250133 : Nat := 4236283692519875050395835

theorem tailTrace_8250133 : CollatzResearch.WordTrace tailWord_8250133 prefixEnd_8250133 4236283692519875050395835 := by
  unfold tailWord_8250133
  simp only [CollatzResearch.WordTrace]
  refine ⟨300907071020184626384451053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200604714013456417589634035 300907071020184626384451053)
  ·
    refine ⟨112840151632569234894169145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300907071020184626384451053 112840151632569234894169145)
    ·
      refine ⟨84630113724426926170626859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112840151632569234894169145 84630113724426926170626859)
      ·
        refine ⟨126945170586640389255940289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84630113724426926170626859 126945170586640389255940289)
        ·
          refine ⟨95208877939980291941955217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126945170586640389255940289 95208877939980291941955217)
          ·
            refine ⟨71406658454985218956466413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95208877939980291941955217 71406658454985218956466413)
            ·
              refine ⟨26777496920619457108674905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71406658454985218956466413 26777496920619457108674905)
              ·
                refine ⟨20083122690464592831506179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26777496920619457108674905 20083122690464592831506179)
                ·
                  refine ⟨30124684035696889247259269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20083122690464592831506179 30124684035696889247259269)
                  ·
                    refine ⟨5648378256693166733861113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30124684035696889247259269 5648378256693166733861113)
                    ·
                      refine ⟨4236283692519875050395835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648378256693166733861113 4236283692519875050395835)
                      ·
                        rfl

theorem cell23_8250133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_8250133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250133 prefixEnd_8250133 := by exact prefixLift 8250133
  have htrace : WordTrace (prefixWord ++ tailWord_8250133) baseStart_8250133 baseEnd_8250133 := by
    simpa [prefixWord, tailWord_8250133, baseEnd_8250133] using wordTrace_append hprefix tailTrace_8250133
  have hstable : (prefixWord ++ tailWord_8250133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250133).length < 2 ^ (prefixWord ++ tailWord_8250133).sum := by decide
  have hdescent : baseEnd_8250133 < baseStart_8250133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250173 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 7]
def baseStart_8250173 : Nat := 118140960795 + 8250173 * 2 ^ 59
def prefixEnd_8250173 : Nat := 4983230072969 + 3 ^ 40 * 8250173 * 2
def baseEnd_8250173 : Nat := 470700470194006099321739

theorem tailTrace_8250173 : CollatzResearch.WordTrace tailWord_8250173 prefixEnd_8250173 470700470194006099321739 := by
  unfold tailWord_8250173
  simp only [CollatzResearch.WordTrace]
  refine ⟨300908529940039713215907173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200605686626693142143938115 300908529940039713215907173)
  ·
    refine ⟨56420349363757446227982595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300908529940039713215907173 56420349363757446227982595)
    ·
      refine ⟨84630524045636169341973893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56420349363757446227982595 84630524045636169341973893)
      ·
        refine ⟨15868223258556781751620105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84630524045636169341973893 15868223258556781751620105)
        ·
          refine ⟨11901167443917586313715079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15868223258556781751620105 11901167443917586313715079)
          ·
            refine ⟨17851751165876379470572619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901167443917586313715079 17851751165876379470572619)
            ·
              refine ⟨26777626748814569205858929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17851751165876379470572619 26777626748814569205858929)
              ·
                refine ⟨20083220061610926904394197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26777626748814569205858929 20083220061610926904394197)
                ·
                  refine ⟨470700470194006099321739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20083220061610926904394197 470700470194006099321739)
                  ·
                    rfl

theorem cell23_8250173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_8250173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250173 prefixEnd_8250173 := by exact prefixLift 8250173
  have htrace : WordTrace (prefixWord ++ tailWord_8250173) baseStart_8250173 baseEnd_8250173 := by
    simpa [prefixWord, tailWord_8250173, baseEnd_8250173] using wordTrace_append hprefix tailTrace_8250173
  have hstable : (prefixWord ++ tailWord_8250173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250173).length < 2 ^ (prefixWord ++ tailWord_8250173).sum := by decide
  have hdescent : baseEnd_8250173 < baseStart_8250173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250186 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_8250186 : Nat := 118140960795 + 8250186 * 2 ^ 59
def prefixEnd_8250186 : Nat := 4983230072969 + 3 ^ 40 * 8250186 * 2
def baseEnd_8250186 : Nat := 1412103635664854447677697

theorem tailTrace_8250186 : CollatzResearch.WordTrace tailWord_8250186 prefixEnd_8250186 1412103635664854447677697 := by
  unfold tailWord_8250186
  simp only [CollatzResearch.WordTrace]
  refine ⟨75227251022248154109032603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200606002725995077624086941 75227251022248154109032603)
  ·
    refine ⟨112840876533372231163548905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75227251022248154109032603 112840876533372231163548905)
    ·
      refine ⟨84630657400029173372661679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112840876533372231163548905 84630657400029173372661679)
      ·
        refine ⟨126945986100043760058992519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84630657400029173372661679 126945986100043760058992519)
        ·
          refine ⟨190418979150065640088488779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126945986100043760058992519 190418979150065640088488779)
          ·
            refine ⟨285628468725098460132733169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190418979150065640088488779 285628468725098460132733169)
            ·
              refine ⟨214221351543823845099549877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285628468725098460132733169 214221351543823845099549877)
              ·
                refine ⟨20083251707233485478082801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214221351543823845099549877 20083251707233485478082801)
                ·
                  refine ⟨15062438780425114108562101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20083251707233485478082801 15062438780425114108562101)
                  ·
                    refine ⟨1412103635664854447677697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15062438780425114108562101 1412103635664854447677697)
                    ·
                      rfl

theorem cell23_8250186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_8250186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250186 prefixEnd_8250186 := by exact prefixLift 8250186
  have htrace : WordTrace (prefixWord ++ tailWord_8250186) baseStart_8250186 baseEnd_8250186 := by
    simpa [prefixWord, tailWord_8250186, baseEnd_8250186] using wordTrace_append hprefix tailTrace_8250186
  have hstable : (prefixWord ++ tailWord_8250186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250186).length < 2 ^ (prefixWord ++ tailWord_8250186).sum := by decide
  have hdescent : baseEnd_8250186 < baseStart_8250186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250233 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 3, 4]
def baseStart_8250233 : Nat := 118140960795 + 8250233 * 2 ^ 59
def prefixEnd_8250233 : Nat := 4983230072969 + 3 ^ 40 * 8250233 * 2
def baseEnd_8250233 : Nat := 1412111680195108219715125

theorem tailTrace_8250233 : CollatzResearch.WordTrace tailWord_8250233 prefixEnd_8250233 1412111680195108219715125 := by
  unfold tailWord_8250233
  simp only [CollatzResearch.WordTrace]
  refine ⟨300910718319822343463091353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200607145546548228975394235 300910718319822343463091353)
  ·
    refine ⟨225683038739866757597318515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300910718319822343463091353 225683038739866757597318515)
    ·
      refine ⟨338524558109800136395977773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225683038739866757597318515 338524558109800136395977773)
      ·
        refine ⟨126946709291175051148491665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338524558109800136395977773 126946709291175051148491665)
        ·
          refine ⟨95210031968381288361368749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126946709291175051148491665 95210031968381288361368749)
          ·
            refine ⟨35703761988142983135513281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95210031968381288361368749 35703761988142983135513281)
            ·
              refine ⟨26777821491107237351634961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35703761988142983135513281 26777821491107237351634961)
              ·
                refine ⟨20083366118330428013726221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26777821491107237351634961 20083366118330428013726221)
                ·
                  refine ⟨7531262294373910505147333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20083366118330428013726221 7531262294373910505147333)
                  ·
                    refine ⟨1412111680195108219715125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7531262294373910505147333 1412111680195108219715125)
                    ·
                      rfl

theorem cell23_8250233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 4].length) (baseStart_8250233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250233 prefixEnd_8250233 := by exact prefixLift 8250233
  have htrace : WordTrace (prefixWord ++ tailWord_8250233) baseStart_8250233 baseEnd_8250233 := by
    simpa [prefixWord, tailWord_8250233, baseEnd_8250233] using wordTrace_append hprefix tailTrace_8250233
  have hstable : (prefixWord ++ tailWord_8250233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250233).length < 2 ^ (prefixWord ++ tailWord_8250233).sum := by decide
  have hdescent : baseEnd_8250233 < baseStart_8250233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250243 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 3]
def baseStart_8250243 : Nat := 118140960795 + 8250243 * 2 ^ 59
def prefixEnd_8250243 : Nat := 4983230072969 + 3 ^ 40 * 8250243 * 2
def baseEnd_8250243 : Nat := 4236340175391869620020329

theorem tailTrace_8250243 : CollatzResearch.WordTrace tailWord_8250243 prefixEnd_8250243 4236340175391869620020329 := by
  unfold tailWord_8250243
  simp only [CollatzResearch.WordTrace]
  refine ⟨300911083049786115170955383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200607388699857410113970255 300911083049786115170955383)
  ·
    refine ⟨451366624574679172756433075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300911083049786115170955383 451366624574679172756433075)
    ·
      refine ⟨677049936862018759134649613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451366624574679172756433075 677049936862018759134649613)
      ·
        refine ⟨253893726323257034675493605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677049936862018759134649613 253893726323257034675493605)
        ·
          refine ⟨47605073685610694001655051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253893726323257034675493605 47605073685610694001655051)
          ·
            refine ⟨71407610528416041002482577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47605073685610694001655051 71407610528416041002482577)
            ·
              refine ⟨53555707896312030751861933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71407610528416041002482577 53555707896312030751861933)
              ·
                refine ⟨20083390461117011531948225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53555707896312030751861933 20083390461117011531948225)
                ·
                  refine ⟨15062542845837758648961169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20083390461117011531948225 15062542845837758648961169)
                  ·
                    refine ⟨11296907134378318986720877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15062542845837758648961169 11296907134378318986720877)
                    ·
                      refine ⟨4236340175391869620020329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11296907134378318986720877 4236340175391869620020329)
                      ·
                        rfl

theorem cell23_8250243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_8250243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250243 prefixEnd_8250243 := by exact prefixLift 8250243
  have htrace : WordTrace (prefixWord ++ tailWord_8250243) baseStart_8250243 baseEnd_8250243 := by
    simpa [prefixWord, tailWord_8250243, baseEnd_8250243] using wordTrace_append hprefix tailTrace_8250243
  have hstable : (prefixWord ++ tailWord_8250243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250243).length < 2 ^ (prefixWord ++ tailWord_8250243).sum := by decide
  have hdescent : baseEnd_8250243 < baseStart_8250243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250256 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 3]
def baseStart_8250256 : Nat := 118140960795 + 8250256 * 2 ^ 59
def prefixEnd_8250256 : Nat := 4983230072969 + 3 ^ 40 * 8250256 * 2
def baseEnd_8250256 : Nat := 4236346850640378069157769

theorem tailTrace_8250256 : CollatzResearch.WordTrace tailWord_8250256 prefixEnd_8250256 4236346850640378069157769 := by
  unfold tailWord_8250256
  simp only [CollatzResearch.WordTrace]
  refine ⟨150455778599369509195589311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200607704799159345594119081 150455778599369509195589311)
  ·
    refine ⟨225683667899054263793383967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150455778599369509195589311 225683667899054263793383967)
    ·
      refine ⟨338525501848581395690075951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225683667899054263793383967 338525501848581395690075951)
      ·
        refine ⟨507788252772872093535113927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338525501848581395690075951 507788252772872093535113927)
        ·
          refine ⟨761682379159308140302670891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507788252772872093535113927 761682379159308140302670891)
          ·
            refine ⟨1142523568738962210454006337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761682379159308140302670891 1142523568738962210454006337)
            ·
              refine ⟨856892676554221657840504753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142523568738962210454006337 856892676554221657840504753)
              ·
                refine ⟨642669507415666243380378565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856892676554221657840504753 642669507415666243380378565)
                ·
                  refine ⟨120500532640437420633820981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 642669507415666243380378565 120500532640437420633820981)
                  ·
                    refine ⟨11296924935041008184420717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120500532640437420633820981 11296924935041008184420717)
                    ·
                      refine ⟨4236346850640378069157769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11296924935041008184420717 4236346850640378069157769)
                      ·
                        rfl

theorem cell23_8250256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_8250256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250256 prefixEnd_8250256 := by exact prefixLift 8250256
  have htrace : WordTrace (prefixWord ++ tailWord_8250256) baseStart_8250256 baseEnd_8250256 := by
    simpa [prefixWord, tailWord_8250256, baseEnd_8250256] using wordTrace_append hprefix tailTrace_8250256
  have hstable : (prefixWord ++ tailWord_8250256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250256).length < 2 ^ (prefixWord ++ tailWord_8250256).sum := by decide
  have hdescent : baseEnd_8250256 < baseStart_8250256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250260 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_8250260 : Nat := 118140960795 + 8250260 * 2 ^ 59
def prefixEnd_8250260 : Nat := 4983230072969 + 3 ^ 40 * 8250260 * 2
def baseEnd_8250260 : Nat := 4236348904562996053507751

theorem tailTrace_8250260 : CollatzResearch.WordTrace tailWord_8250260 prefixEnd_8250260 4236348904562996053507751 := by
  unfold tailWord_8250260
  simp only [CollatzResearch.WordTrace]
  refine ⟨150455851545362263537162117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200607802060483018049549489 150455851545362263537162117)
  ·
    refine ⟨28210472164755424413217897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150455851545362263537162117 28210472164755424413217897)
    ·
      refine ⟨21157854123566568309913423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28210472164755424413217897 21157854123566568309913423)
      ·
        refine ⟨31736781185349852464870135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21157854123566568309913423 31736781185349852464870135)
        ·
          refine ⟨47605171778024778697305203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31736781185349852464870135 47605171778024778697305203)
          ·
            refine ⟨71407757667037168045957805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47605171778024778697305203 71407757667037168045957805)
            ·
              refine ⟨26777909125138938017234177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71407757667037168045957805 26777909125138938017234177)
              ·
                refine ⟨20083431843854203512925633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26777909125138938017234177 20083431843854203512925633)
                ·
                  refine ⟨15062573882890652634694225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20083431843854203512925633 15062573882890652634694225)
                  ·
                    refine ⟨11296930412167989476020669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15062573882890652634694225 11296930412167989476020669)
                    ·
                      refine ⟨4236348904562996053507751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11296930412167989476020669 4236348904562996053507751)
                      ·
                        rfl

theorem cell23_8250260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_8250260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250260 prefixEnd_8250260 := by exact prefixLift 8250260
  have htrace : WordTrace (prefixWord ++ tailWord_8250260) baseStart_8250260 baseEnd_8250260 := by
    simpa [prefixWord, tailWord_8250260, baseEnd_8250260] using wordTrace_append hprefix tailTrace_8250260
  have hstable : (prefixWord ++ tailWord_8250260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250260).length < 2 ^ (prefixWord ++ tailWord_8250260).sum := by decide
  have hdescent : baseEnd_8250260 < baseStart_8250260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250293 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_8250293 : Nat := 118140960795 + 8250293 * 2 ^ 59
def prefixEnd_8250293 : Nat := 4983230072969 + 3 ^ 40 * 8250293 * 2
def baseEnd_8250293 : Nat := 1412121949808198141465033

theorem tailTrace_8250293 : CollatzResearch.WordTrace tailWord_8250293 prefixEnd_8250293 1412121949808198141465033 := by
  unfold tailWord_8250293
  simp only [CollatzResearch.WordTrace]
  refine ⟨300912906699604973710275533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200608604466403315806850355 300912906699604973710275533)
  ·
    refine ⟨112842340012351865141353325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300912906699604973710275533 112842340012351865141353325)
    ·
      refine ⟨42315877504631949428007497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112842340012351865141353325 42315877504631949428007497)
      ·
        refine ⟨31736908128473962071005623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42315877504631949428007497 31736908128473962071005623)
        ·
          refine ⟨47605362192710943106508435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31736908128473962071005623 47605362192710943106508435)
          ·
            refine ⟨71408043289066414659762653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47605362192710943106508435 71408043289066414659762653)
            ·
              refine ⟨26778016233399905497410995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71408043289066414659762653 26778016233399905497410995)
              ·
                refine ⟨40167024350099858246116493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26778016233399905497410995 40167024350099858246116493)
                ·
                  refine ⟨15062634131287446842293685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40167024350099858246116493 15062634131287446842293685)
                  ·
                    refine ⟨1412121949808198141465033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15062634131287446842293685 1412121949808198141465033)
                    ·
                      rfl

theorem cell23_8250293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_8250293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250293 prefixEnd_8250293 := by exact prefixLift 8250293
  have htrace : WordTrace (prefixWord ++ tailWord_8250293) baseStart_8250293 baseEnd_8250293 := by
    simpa [prefixWord, tailWord_8250293, baseEnd_8250293] using wordTrace_append hprefix tailTrace_8250293
  have hstable : (prefixWord ++ tailWord_8250293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250293).length < 2 ^ (prefixWord ++ tailWord_8250293).sum := by decide
  have hdescent : baseEnd_8250293 < baseStart_8250293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250324 : List Nat := [2, 4, 1, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_8250324 : Nat := 118140960795 + 8250324 * 2 ^ 59
def prefixEnd_8250324 : Nat := 4983230072969 + 3 ^ 40 * 8250324 * 2
def baseEnd_8250324 : Nat := 4236381767324883803107457

theorem tailTrace_8250324 : CollatzResearch.WordTrace tailWord_8250324 prefixEnd_8250324 4236381767324883803107457 := by
  unfold tailWord_8250324
  simp only [CollatzResearch.WordTrace]
  refine ⟨150457018681246333002327013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200609358241661777336436017 150457018681246333002327013)
  ·
    refine ⟨28210691002733687437936315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150457018681246333002327013 28210691002733687437936315)
    ·
      refine ⟨42316036504100531156904473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28210691002733687437936315 42316036504100531156904473)
      ·
        refine ⟨31737027378075398367678355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42316036504100531156904473 31737027378075398367678355)
        ·
          refine ⟨47605541067113097551517533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31737027378075398367678355 47605541067113097551517533)
          ·
            refine ⟨17852077900167411581819075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47605541067113097551517533 17852077900167411581819075)
            ·
              refine ⟨26778116850251117372728613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17852077900167411581819075 26778116850251117372728613)
              ·
                refine ⟨5020896909422084507386615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26778116850251117372728613 5020896909422084507386615)
                ·
                  refine ⟨7531345364133126761079923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020896909422084507386615 7531345364133126761079923)
                  ·
                    refine ⟨11297018046199690141619885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7531345364133126761079923 11297018046199690141619885)
                    ·
                      refine ⟨4236381767324883803107457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11297018046199690141619885 4236381767324883803107457)
                      ·
                        rfl

theorem cell23_8250324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_8250324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250324 prefixEnd_8250324 := by exact prefixLift 8250324
  have htrace : WordTrace (prefixWord ++ tailWord_8250324) baseStart_8250324 baseEnd_8250324 := by
    simpa [prefixWord, tailWord_8250324, baseEnd_8250324] using wordTrace_append hprefix tailTrace_8250324
  have hstable : (prefixWord ++ tailWord_8250324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250324).length < 2 ^ (prefixWord ++ tailWord_8250324).sum := by decide
  have hdescent : baseEnd_8250324 < baseStart_8250324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250364 : List Nat := [2, 2, 2, 1, 2, 3, 1, 5, 1, 2, 2]
def baseStart_8250364 : Nat := 118140960795 + 8250364 * 2 ^ 59
def prefixEnd_8250364 : Nat := 4983230072969 + 3 ^ 40 * 8250364 * 2
def baseEnd_8250364 : Nat := 4236402306551063646607273

theorem tailTrace_8250364 : CollatzResearch.WordTrace tailWord_8250364 prefixEnd_8250364 4236402306551063646607273 := by
  unfold tailWord_8250364
  simp only [CollatzResearch.WordTrace]
  refine ⟨150457748141173876418055073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200610330854898501890740097 150457748141173876418055073)
  ·
    refine ⟨112843311105880407313541305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150457748141173876418055073 112843311105880407313541305)
    ·
      refine ⟨84632483329410305485155979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112843311105880407313541305 84632483329410305485155979)
      ·
        refine ⟨126948724994115458227733969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84632483329410305485155979 126948724994115458227733969)
        ·
          refine ⟨95211543745586593670800477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126948724994115458227733969 95211543745586593670800477)
          ·
            refine ⟨35704328904594972626550179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95211543745586593670800477 35704328904594972626550179)
            ·
              refine ⟨53556493356892458939825269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35704328904594972626550179 53556493356892458939825269)
              ·
                refine ⟨5020921252208668025608619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53556493356892458939825269 5020921252208668025608619)
                ·
                  refine ⟨7531381878313002038412929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5020921252208668025608619 7531381878313002038412929)
                  ·
                    refine ⟨5648536408734751528809697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7531381878313002038412929 5648536408734751528809697)
                    ·
                      refine ⟨4236402306551063646607273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648536408734751528809697 4236402306551063646607273)
                      ·
                        rfl

theorem cell23_8250364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_8250364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250364 prefixEnd_8250364 := by exact prefixLift 8250364
  have htrace : WordTrace (prefixWord ++ tailWord_8250364) baseStart_8250364 baseEnd_8250364 := by
    simpa [prefixWord, tailWord_8250364, baseEnd_8250364] using wordTrace_append hprefix tailTrace_8250364
  have hstable : (prefixWord ++ tailWord_8250364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250364).length < 2 ^ (prefixWord ++ tailWord_8250364).sum := by decide
  have hdescent : baseEnd_8250364 < baseStart_8250364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250423 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_8250423 : Nat := 118140960795 + 8250423 * 2 ^ 59
def prefixEnd_8250423 : Nat := 4983230072969 + 3 ^ 40 * 8250423 * 2
def baseEnd_8250423 : Nat := 4236432601909678915769501

theorem tailTrace_8250423 : CollatzResearch.WordTrace tailWord_8250423 prefixEnd_8250423 4236432601909678915769501 := by
  unfold tailWord_8250423
  simp only [CollatzResearch.WordTrace]
  refine ⟨300917648189134005912507923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200611765459422670608338615 300917648189134005912507923)
  ·
    refine ⟨451376472283701008868761885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300917648189134005912507923 451376472283701008868761885)
    ·
      refine ⟨169266177106387878325785707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451376472283701008868761885 169266177106387878325785707)
      ·
        refine ⟨253899265659581817488678561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169266177106387878325785707 253899265659581817488678561)
        ·
          refine ⟨190424449244686363116508921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253899265659581817488678561 190424449244686363116508921)
          ·
            refine ⟨142818336933514772337381691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190424449244686363116508921 142818336933514772337381691)
            ·
              refine ⟨214227505400272158506072537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142818336933514772337381691 214227505400272158506072537)
              ·
                refine ⟨160670629050204118879554403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214227505400272158506072537 160670629050204118879554403)
                ·
                  refine ⟨241005943575306178319331605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160670629050204118879554403 241005943575306178319331605)
                  ·
                    refine ⟨11297153605092477108718669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 241005943575306178319331605 11297153605092477108718669)
                    ·
                      refine ⟨4236432601909678915769501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11297153605092477108718669 4236432601909678915769501)
                      ·
                        rfl

theorem cell23_8250423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_8250423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250423 prefixEnd_8250423 := by exact prefixLift 8250423
  have htrace : WordTrace (prefixWord ++ tailWord_8250423) baseStart_8250423 baseEnd_8250423 := by
    simpa [prefixWord, tailWord_8250423, baseEnd_8250423] using wordTrace_append hprefix tailTrace_8250423
  have hstable : (prefixWord ++ tailWord_8250423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250423).length < 2 ^ (prefixWord ++ tailWord_8250423).sum := by decide
  have hdescent : baseEnd_8250423 < baseStart_8250423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250437 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 4, 2, 2]
def baseStart_8250437 : Nat := 118140960795 + 8250437 * 2 ^ 59
def prefixEnd_8250437 : Nat := 4983230072969 + 3 ^ 40 * 8250437 * 2
def baseEnd_8250437 : Nat := 4236439790638841860994437

theorem tailTrace_8250437 : CollatzResearch.WordTrace tailWord_8250437 prefixEnd_8250437 4236439790638841860994437 := by
  unfold tailWord_8250437
  simp only [CollatzResearch.WordTrace]
  refine ⟨300918158811083286303517565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200612105874055524202345043 300918158811083286303517565)
  ·
    refine ⟨112844309554156232363819087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300918158811083286303517565 112844309554156232363819087)
    ·
      refine ⟨169266464331234348545728631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112844309554156232363819087 169266464331234348545728631)
      ·
        refine ⟨253899696496851522818592947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169266464331234348545728631 253899696496851522818592947)
        ·
          refine ⟨380849544745277284227889421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253899696496851522818592947 380849544745277284227889421)
          ·
            refine ⟨142818579279478981585458533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380849544745277284227889421 142818579279478981585458533)
            ·
              refine ⟨26778483614902309047273475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142818579279478981585458533 26778483614902309047273475)
              ·
                refine ⟨40167725422353463570910213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26778483614902309047273475 40167725422353463570910213)
                ·
                  refine ⟨7531448516691274419545665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40167725422353463570910213 7531448516691274419545665)
                  ·
                    refine ⟨5648586387518455814659249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7531448516691274419545665 5648586387518455814659249)
                    ·
                      refine ⟨4236439790638841860994437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648586387518455814659249 4236439790638841860994437)
                      ·
                        rfl

theorem cell23_8250437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_8250437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250437 prefixEnd_8250437 := by exact prefixLift 8250437
  have htrace : WordTrace (prefixWord ++ tailWord_8250437) baseStart_8250437 baseEnd_8250437 := by
    simpa [prefixWord, tailWord_8250437, baseEnd_8250437] using wordTrace_append hprefix tailTrace_8250437
  have hstable : (prefixWord ++ tailWord_8250437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250437).length < 2 ^ (prefixWord ++ tailWord_8250437).sum := by decide
  have hdescent : baseEnd_8250437 < baseStart_8250437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250497 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_8250497 : Nat := 118140960795 + 8250497 * 2 ^ 59
def prefixEnd_8250497 : Nat := 4983230072969 + 3 ^ 40 * 8250497 * 2
def baseEnd_8250497 : Nat := 4236470599478111626244161

theorem tailTrace_8250497 : CollatzResearch.WordTrace tailWord_8250497 prefixEnd_8250497 4236470599478111626244161 := by
  unfold tailWord_8250497
  simp only [CollatzResearch.WordTrace]
  refine ⟨300920347190865916550701745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200613564793910611033801163 300920347190865916550701745)
  ·
    refine ⟨225690260393149437413026309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300920347190865916550701745 225690260393149437413026309)
    ·
      refine ⟨42316923823715519514942433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225690260393149437413026309 42316923823715519514942433)
      ·
        refine ⟨31737692867786639636206825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42316923823715519514942433 31737692867786639636206825)
        ·
          refine ⟨23803269650839979727155119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31737692867786639636206825 23803269650839979727155119)
          ·
            refine ⟨35704904476259969590732679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23803269650839979727155119 35704904476259969590732679)
            ·
              refine ⟨53557356714389954386099019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35704904476259969590732679 53557356714389954386099019)
              ·
                refine ⟨80336035071584931579148529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53557356714389954386099019 80336035071584931579148529)
                ·
                  refine ⟨60252026303688698684361397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80336035071584931579148529 60252026303688698684361397)
                  ·
                    refine ⟨5648627465970815501658881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60252026303688698684361397 5648627465970815501658881)
                    ·
                      refine ⟨4236470599478111626244161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648627465970815501658881 4236470599478111626244161)
                      ·
                        rfl

theorem cell23_8250497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_8250497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250497 prefixEnd_8250497 := by exact prefixLift 8250497
  have htrace : WordTrace (prefixWord ++ tailWord_8250497) baseStart_8250497 baseEnd_8250497 := by
    simpa [prefixWord, tailWord_8250497, baseEnd_8250497] using wordTrace_append hprefix tailTrace_8250497
  have hstable : (prefixWord ++ tailWord_8250497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250497).length < 2 ^ (prefixWord ++ tailWord_8250497).sum := by decide
  have hdescent : baseEnd_8250497 < baseStart_8250497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250500 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_8250500 : Nat := 118140960795 + 8250500 * 2 ^ 59
def prefixEnd_8250500 : Nat := 4983230072969 + 3 ^ 40 * 8250500 * 2
def baseEnd_8250500 : Nat := 4236472139920075114506647

theorem tailTrace_8250500 : CollatzResearch.WordTrace tailWord_8250500 prefixEnd_8250500 4236472139920075114506647 := by
  unfold tailWord_8250500
  simp only [CollatzResearch.WordTrace]
  refine ⟨150460228304927524031530477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200613637739903365375373969 150460228304927524031530477)
  ·
    refine ⟨56422585614347821511823929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150460228304927524031530477 56422585614347821511823929)
    ·
      refine ⟨42316939210760866133867947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56422585614347821511823929 42316939210760866133867947)
      ·
        refine ⟨63475408816141299200801921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42316939210760866133867947 63475408816141299200801921)
        ·
          refine ⟨47606556612105974400601441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63475408816141299200801921 47606556612105974400601441)
          ·
            refine ⟨35704917459079480800451081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47606556612105974400601441 35704917459079480800451081)
            ·
              refine ⟨26778688094309610600338311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35704917459079480800451081 26778688094309610600338311)
              ·
                refine ⟨40168032141464415900507467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26778688094309610600338311 40168032141464415900507467)
                ·
                  refine ⟨60252048212196623850761201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40168032141464415900507467 60252048212196623850761201)
                  ·
                    refine ⟨45189036159147467888070901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60252048212196623850761201 45189036159147467888070901)
                    ·
                      refine ⟨4236472139920075114506647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45189036159147467888070901 4236472139920075114506647)
                      ·
                        rfl

theorem cell23_8250500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_8250500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250500 prefixEnd_8250500 := by exact prefixLift 8250500
  have htrace : WordTrace (prefixWord ++ tailWord_8250500) baseStart_8250500 baseEnd_8250500 := by
    simpa [prefixWord, tailWord_8250500, baseEnd_8250500] using wordTrace_append hprefix tailTrace_8250500
  have hstable : (prefixWord ++ tailWord_8250500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250500).length < 2 ^ (prefixWord ++ tailWord_8250500).sum := by decide
  have hdescent : baseEnd_8250500 < baseStart_8250500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250503 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 2, 8]
def baseStart_8250503 : Nat := 118140960795 + 8250503 * 2 ^ 59
def prefixEnd_8250503 : Nat := 4983230072969 + 3 ^ 40 * 8250503 * 2
def baseEnd_8250503 : Nat := 1412157893454012867589711

theorem tailTrace_8250503 : CollatzResearch.WordTrace tailWord_8250503 prefixEnd_8250503 1412157893454012867589711 := by
  unfold tailWord_8250503
  simp only [CollatzResearch.WordTrace]
  refine ⟨300920566028844179575420163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200613710685896119716946775 300920566028844179575420163)
  ·
    refine ⟨451380849043266269363130245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300920566028844179575420163 451380849043266269363130245)
    ·
      refine ⟨84633909195612425505586921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 451380849043266269363130245 84633909195612425505586921)
      ·
        refine ⟨63475431896709319129190191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84633909195612425505586921 63475431896709319129190191)
        ·
          refine ⟨95213147845063978693785287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63475431896709319129190191 95213147845063978693785287)
          ·
            refine ⟨142819721767595968040677931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95213147845063978693785287 142819721767595968040677931)
            ·
              refine ⟨214229582651393952061016897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142819721767595968040677931 214229582651393952061016897)
              ·
                refine ⟨160672186988545464045762673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214229582651393952061016897 160672186988545464045762673)
                ·
                  refine ⟨120504140241409098034322005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160672186988545464045762673 120504140241409098034322005)
                  ·
                    refine ⟨1412157893454012867589711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120504140241409098034322005 1412157893454012867589711)
                    ·
                      rfl

theorem cell23_8250503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_8250503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250503 prefixEnd_8250503 := by exact prefixLift 8250503
  have htrace : WordTrace (prefixWord ++ tailWord_8250503) baseStart_8250503 baseEnd_8250503 := by
    simpa [prefixWord, tailWord_8250503, baseEnd_8250503] using wordTrace_append hprefix tailTrace_8250503
  have hstable : (prefixWord ++ tailWord_8250503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250503).length < 2 ^ (prefixWord ++ tailWord_8250503).sum := by decide
  have hdescent : baseEnd_8250503 < baseStart_8250503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250527 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 4]
def baseStart_8250527 : Nat := 118140960795 + 8250527 * 2 ^ 59
def prefixEnd_8250527 : Nat := 4983230072969 + 3 ^ 40 * 8250527 * 2
def baseEnd_8250527 : Nat := 4236486003897746508869023

theorem tailTrace_8250527 : CollatzResearch.WordTrace tailWord_8250527 prefixEnd_8250527 4236486003897746508869023 := by
  unfold tailWord_8250527
  simp only [CollatzResearch.WordTrace]
  refine ⟨300921441380757231674293835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200614294253838154449529223 300921441380757231674293835)
  ·
    refine ⟨451382162071135847511440753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300921441380757231674293835 451382162071135847511440753)
    ·
      refine ⟨338536621553351885633580565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451382162071135847511440753 338536621553351885633580565)
      ·
        refine ⟨15868904135313369639074089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 338536621553351885633580565 15868904135313369639074089)
        ·
          refine ⟨11901678101485027229305567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15868904135313369639074089 11901678101485027229305567)
          ·
            refine ⟨17852517152227540843958351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901678101485027229305567 17852517152227540843958351)
            ·
              refine ⟨26778775728341311265937527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17852517152227540843958351 26778775728341311265937527)
              ·
                refine ⟨40168163592511966898906291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26778775728341311265937527 40168163592511966898906291)
                ·
                  refine ⟨60252245388767950348359437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40168163592511966898906291 60252245388767950348359437)
                  ·
                    refine ⟨22594592020787981380634789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60252245388767950348359437 22594592020787981380634789)
                    ·
                      refine ⟨4236486003897746508869023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22594592020787981380634789 4236486003897746508869023)
                      ·
                        rfl

theorem cell23_8250527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_8250527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250527 prefixEnd_8250527 := by exact prefixLift 8250527
  have htrace : WordTrace (prefixWord ++ tailWord_8250527) baseStart_8250527 baseEnd_8250527 := by
    simpa [prefixWord, tailWord_8250527, baseEnd_8250527] using wordTrace_append hprefix tailTrace_8250527
  have hstable : (prefixWord ++ tailWord_8250527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250527).length < 2 ^ (prefixWord ++ tailWord_8250527).sum := by decide
  have hdescent : baseEnd_8250527 < baseStart_8250527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250563 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 2, 9]
def baseStart_8250563 : Nat := 118140960795 + 8250563 * 2 ^ 59
def prefixEnd_8250563 : Nat := 4983230072969 + 3 ^ 40 * 8250563 * 2
def baseEnd_8250563 : Nat := 1412168163067102789339619

theorem tailTrace_8250563 : CollatzResearch.WordTrace tailWord_8250563 prefixEnd_8250563 1412168163067102789339619 := by
  unfold tailWord_8250563
  simp only [CollatzResearch.WordTrace]
  refine ⟨300922754408626809822604343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200615169605751206548402895 300922754408626809822604343)
  ·
    refine ⟨451384131612940214733906515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300922754408626809822604343 451384131612940214733906515)
    ·
      refine ⟨677076197419410322100859773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451384131612940214733906515 677076197419410322100859773)
      ·
        refine ⟨253903574032278870787822415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677076197419410322100859773 253903574032278870787822415)
        ·
          refine ⟨380855361048418306181733623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253903574032278870787822415 380855361048418306181733623)
          ·
            refine ⟨571283041572627459272600435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380855361048418306181733623 571283041572627459272600435)
            ·
              refine ⟨856924562358941188908900653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571283041572627459272600435 856924562358941188908900653)
              ·
                refine ⟨321346710884602945840837745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856924562358941188908900653 321346710884602945840837745)
                ·
                  refine ⟨241010033163452209380628309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321346710884602945840837745 241010033163452209380628309)
                  ·
                    refine ⟨1412168163067102789339619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 241010033163452209380628309 1412168163067102789339619)
                    ·
                      rfl

theorem cell23_8250563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 9].length) (baseStart_8250563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250563 prefixEnd_8250563 := by exact prefixLift 8250563
  have htrace : WordTrace (prefixWord ++ tailWord_8250563) baseStart_8250563 baseEnd_8250563 := by
    simpa [prefixWord, tailWord_8250563, baseEnd_8250563] using wordTrace_append hprefix tailTrace_8250563
  have hstable : (prefixWord ++ tailWord_8250563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250563).length < 2 ^ (prefixWord ++ tailWord_8250563).sum := by decide
  have hdescent : baseEnd_8250563 < baseStart_8250563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250604 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 2, 3, 2]
def baseStart_8250604 : Nat := 118140960795 + 8250604 * 2 ^ 59
def prefixEnd_8250604 : Nat := 4983230072969 + 3 ^ 40 * 8250604 * 2
def baseEnd_8250604 : Nat := 4236525541908142707606169

theorem tailTrace_8250604 : CollatzResearch.WordTrace tailWord_8250604 prefixEnd_8250604 4236525541908142707606169 := by
  unfold tailWord_8250604
  simp only [CollatzResearch.WordTrace]
  refine ⟨150462124900739136912423433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200616166534318849216564577 150462124900739136912423433)
  ·
    refine ⟨112846593675554352684317575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150462124900739136912423433 112846593675554352684317575)
    ·
      refine ⟨169269890513331529026476363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112846593675554352684317575 169269890513331529026476363)
      ·
        refine ⟨253904835769997293539714545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169269890513331529026476363 253904835769997293539714545)
        ·
          refine ⟨190428626827497970154785909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253904835769997293539714545 190428626827497970154785909)
          ·
            refine ⟨17852683765077934702011179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190428626827497970154785909 17852683765077934702011179)
            ·
              refine ⟨26779025647616902053016769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17852683765077934702011179 26779025647616902053016769)
              ·
                refine ⟨20084269235712676539762577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26779025647616902053016769 20084269235712676539762577)
                ·
                  refine ⟨15063201926784507404821933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20084269235712676539762577 15063201926784507404821933)
                  ·
                    refine ⟨5648700722544190276808225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15063201926784507404821933 5648700722544190276808225)
                    ·
                      refine ⟨4236525541908142707606169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648700722544190276808225 4236525541908142707606169)
                      ·
                        rfl

theorem cell23_8250604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_8250604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250604 prefixEnd_8250604 := by exact prefixLift 8250604
  have htrace : WordTrace (prefixWord ++ tailWord_8250604) baseStart_8250604 baseEnd_8250604 := by
    simpa [prefixWord, tailWord_8250604, baseEnd_8250604] using wordTrace_append hprefix tailTrace_8250604
  have hstable : (prefixWord ++ tailWord_8250604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250604).length < 2 ^ (prefixWord ++ tailWord_8250604).sum := by decide
  have hdescent : baseEnd_8250604 < baseStart_8250604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250634 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_8250634 : Nat := 118140960795 + 8250634 * 2 ^ 59
def prefixEnd_8250634 : Nat := 4983230072969 + 3 ^ 40 * 8250634 * 2
def baseEnd_8250634 : Nat := 4236540946327777590231031

theorem tailTrace_8250634 : CollatzResearch.WordTrace tailWord_8250634 prefixEnd_8250634 4236540946327777590231031 := by
  unfold tailWord_8250634
  simp only [CollatzResearch.WordTrace]
  refine ⟨75231335997842397237109739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200616895994246392632292637 75231335997842397237109739)
  ·
    refine ⟨112847003996763595855664609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75231335997842397237109739 112847003996763595855664609)
    ·
      refine ⟨84635252997572696891748457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112847003996763595855664609 84635252997572696891748457)
      ·
        refine ⟨63476439748179522668811343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84635252997572696891748457 63476439748179522668811343)
        ·
          refine ⟨95214659622269284003217015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63476439748179522668811343 95214659622269284003217015)
          ·
            refine ⟨142821989433403926004825523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95214659622269284003217015 142821989433403926004825523)
            ·
              refine ⟨214232984150105889007238285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142821989433403926004825523 214232984150105889007238285)
              ·
                refine ⟨80337369056289708377714357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214232984150105889007238285 80337369056289708377714357)
                ·
                  refine ⟨7531628349027160160410721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80337369056289708377714357 7531628349027160160410721)
                  ·
                    refine ⟨5648721261770370120308041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7531628349027160160410721 5648721261770370120308041)
                    ·
                      refine ⟨4236540946327777590231031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5648721261770370120308041 4236540946327777590231031)
                      ·
                        rfl

theorem cell23_8250634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_8250634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250634 prefixEnd_8250634 := by exact prefixLift 8250634
  have htrace : WordTrace (prefixWord ++ tailWord_8250634) baseStart_8250634 baseEnd_8250634 := by
    simpa [prefixWord, tailWord_8250634, baseEnd_8250634] using wordTrace_append hprefix tailTrace_8250634
  have hstable : (prefixWord ++ tailWord_8250634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250634).length < 2 ^ (prefixWord ++ tailWord_8250634).sum := by decide
  have hdescent : baseEnd_8250634 < baseStart_8250634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8250647 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_8250647 : Nat := 118140960795 + 8250647 * 2 ^ 59
def prefixEnd_8250647 : Nat := 4983230072969 + 3 ^ 40 * 8250647 * 2
def baseEnd_8250647 : Nat := 4236547621576286039368471

theorem tailTrace_8250647 : CollatzResearch.WordTrace tailWord_8250647 prefixEnd_8250647 4236547621576286039368471 := by
  unfold tailWord_8250647
  simp only [CollatzResearch.WordTrace]
  refine ⟨300925818140322492168662195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200617212093548328112441463 300925818140322492168662195)
  ·
    refine ⟨451388727210483738252993293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300925818140322492168662195 451388727210483738252993293)
    ·
      refine ⟨169270772703931401844872485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 451388727210483738252993293 169270772703931401844872485)
      ·
        refine ⟨31738269881987137845913591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169270772703931401844872485 31738269881987137845913591)
        ·
          refine ⟨47607404822980706768870387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31738269881987137845913591 47607404822980706768870387)
          ·
            refine ⟨71411107234471060153305581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47607404822980706768870387 71411107234471060153305581)
            ·
              refine ⟨26779165212926647557489593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71411107234471060153305581 26779165212926647557489593)
              ·
                refine ⟨20084373909694985668117195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26779165212926647557489593 20084373909694985668117195)
                ·
                  refine ⟨30126560864542478502175793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20084373909694985668117195 30126560864542478502175793)
                  ·
                    refine ⟨22594920648406858876631845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30126560864542478502175793 22594920648406858876631845)
                    ·
                      refine ⟨4236547621576286039368471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22594920648406858876631845 4236547621576286039368471)
                      ·
                        rfl

theorem cell23_8250647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_8250647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8250647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8250647 prefixEnd_8250647 := by exact prefixLift 8250647
  have htrace : WordTrace (prefixWord ++ tailWord_8250647) baseStart_8250647 baseEnd_8250647 := by
    simpa [prefixWord, tailWord_8250647, baseEnd_8250647] using wordTrace_append hprefix tailTrace_8250647
  have hstable : (prefixWord ++ tailWord_8250647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8250647).length < 2 ^ (prefixWord ++ tailWord_8250647).sum := by decide
  have hdescent : baseEnd_8250647 < baseStart_8250647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8250647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
