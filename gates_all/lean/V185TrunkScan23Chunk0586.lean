import V185TrunkScan23Chunk0585

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3465304 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 4, 1, 3]
def baseStart_3465304 : Nat := 118140960795 + 3465304 * 2 ^ 59
def prefixEnd_3465304 : Nat := 4983230072969 + 3 ^ 40 * 3465304 * 2
def baseEnd_3465304 : Nat := 1779366565948015215863363

theorem tailTrace_3465304 : CollatzResearch.WordTrace tailWord_3465304 prefixEnd_3465304 1779366565948015215863363 := by
  unfold tailWord_3465304
  simp only [CollatzResearch.WordTrace]
  refine ⟨63195010118901454825285483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84260013491868606433713977 63195010118901454825285483)
  ·
    refine ⟨94792515178352182237928225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63195010118901454825285483 94792515178352182237928225)
    ·
      refine ⟨71094386383764136678446169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94792515178352182237928225 71094386383764136678446169)
      ·
        refine ⟨53320789787823102508834627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71094386383764136678446169 53320789787823102508834627)
        ·
          refine ⟨79981184681734653763251941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53320789787823102508834627 79981184681734653763251941)
          ·
            refine ⟨14996472127825247580609739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79981184681734653763251941 14996472127825247580609739)
            ·
              refine ⟨22494708191737871370914609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14996472127825247580609739 22494708191737871370914609)
              ·
                refine ⟨16871031143803403528185957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22494708191737871370914609 16871031143803403528185957)
                ·
                  refine ⟨3163318339463138161534867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16871031143803403528185957 3163318339463138161534867)
                  ·
                    refine ⟨4744977509194707242302301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3163318339463138161534867 4744977509194707242302301)
                    ·
                      refine ⟨1779366565948015215863363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4744977509194707242302301 1779366565948015215863363)
                      ·
                        rfl

theorem cell23_3465304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_3465304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465304 prefixEnd_3465304 := by exact prefixLift 3465304
  have htrace : WordTrace (prefixWord ++ tailWord_3465304) baseStart_3465304 baseEnd_3465304 := by
    simpa [prefixWord, tailWord_3465304, baseEnd_3465304] using wordTrace_append hprefix tailTrace_3465304
  have hstable : (prefixWord ++ tailWord_3465304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465304).length < 2 ^ (prefixWord ++ tailWord_3465304).sum := by decide
  have hdescent : baseEnd_3465304 < baseStart_3465304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465322 : List Nat := [3, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_3465322 : Nat := 118140960795 + 3465322 * 2 ^ 59
def prefixEnd_3465322 : Nat := 4983230072969 + 3 ^ 40 * 3465322 * 2
def baseEnd_3465322 : Nat := 1779375808599796145438281

theorem tailTrace_3465322 : CollatzResearch.WordTrace tailWord_3465322 prefixEnd_3465322 1779375808599796145438281 := by
  unfold tailWord_3465322
  simp only [CollatzResearch.WordTrace]
  refine ⟨31597669187934424681181555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84260451167825132483150813 31597669187934424681181555)
  ·
    refine ⟨47396503781901637021772333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31597669187934424681181555 47396503781901637021772333)
    ·
      refine ⟨17773688918213113883164625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47396503781901637021772333 17773688918213113883164625)
      ·
        refine ⟨13330266688659835412373469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17773688918213113883164625 13330266688659835412373469)
        ·
          refine ⟨4998850008247438279640051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13330266688659835412373469 4998850008247438279640051)
          ·
            refine ⟨7498275012371157419460077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4998850008247438279640051 7498275012371157419460077)
            ·
              refine ⟨2811853129639184032297529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7498275012371157419460077 2811853129639184032297529)
              ·
                refine ⟨2108889847229388024223147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2811853129639184032297529 2108889847229388024223147)
                ·
                  refine ⟨3163334770844082036334721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108889847229388024223147 3163334770844082036334721)
                  ·
                    refine ⟨2372501078133061527251041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3163334770844082036334721 2372501078133061527251041)
                    ·
                      refine ⟨1779375808599796145438281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372501078133061527251041 1779375808599796145438281)
                      ·
                        rfl

theorem cell23_3465322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_3465322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465322 prefixEnd_3465322 := by exact prefixLift 3465322
  have htrace : WordTrace (prefixWord ++ tailWord_3465322) baseStart_3465322 baseEnd_3465322 := by
    simpa [prefixWord, tailWord_3465322, baseEnd_3465322] using wordTrace_append hprefix tailTrace_3465322
  have hstable : (prefixWord ++ tailWord_3465322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465322).length < 2 ^ (prefixWord ++ tailWord_3465322).sum := by decide
  have hdescent : baseEnd_3465322 < baseStart_3465322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465344 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 1, 4, 2]
def baseStart_3465344 : Nat := 118140960795 + 3465344 * 2 ^ 59
def prefixEnd_3465344 : Nat := 4983230072969 + 3 ^ 40 * 3465344 * 2
def baseEnd_3465344 : Nat := 1779387105174195059363179

theorem tailTrace_3465344 : CollatzResearch.WordTrace tailWord_3465344 prefixEnd_3465344 1779387105174195059363179 := by
  unfold tailWord_3465344
  simp only [CollatzResearch.WordTrace]
  refine ⟨63195739578828998241013543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84260986105105330988018057 63195739578828998241013543)
  ·
    refine ⟨94793609368243497361520315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63195739578828998241013543 94793609368243497361520315)
    ·
      refine ⟨142190414052365246042280473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94793609368243497361520315 142190414052365246042280473)
      ·
        refine ⟨106642810539273934531710355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142190414052365246042280473 106642810539273934531710355)
        ·
          refine ⟨159964215808910901797565533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106642810539273934531710355 159964215808910901797565533)
          ·
            refine ⟨59986580928341588174087075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159964215808910901797565533 59986580928341588174087075)
            ·
              refine ⟨89979871392512382261130613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59986580928341588174087075 89979871392512382261130613)
              ·
                refine ⟨8435612943048035836980995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89979871392512382261130613 8435612943048035836980995)
                ·
                  refine ⟨12653419414572053755471493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8435612943048035836980995 12653419414572053755471493)
                  ·
                    refine ⟨2372516140232260079150905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12653419414572053755471493 2372516140232260079150905)
                    ·
                      refine ⟨1779387105174195059363179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372516140232260079150905 1779387105174195059363179)
                      ·
                        rfl

theorem cell23_3465344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_3465344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465344 prefixEnd_3465344 := by exact prefixLift 3465344
  have htrace : WordTrace (prefixWord ++ tailWord_3465344) baseStart_3465344 baseEnd_3465344 := by
    simpa [prefixWord, tailWord_3465344, baseEnd_3465344] using wordTrace_append hprefix tailTrace_3465344
  have hstable : (prefixWord ++ tailWord_3465344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465344).length < 2 ^ (prefixWord ++ tailWord_3465344).sum := by decide
  have hdescent : baseEnd_3465344 < baseStart_3465344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465347 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 5]
def baseStart_3465347 : Nat := 118140960795 + 3465347 * 2 ^ 59
def prefixEnd_3465347 : Nat := 4983230072969 + 3 ^ 40 * 3465347 * 2
def baseEnd_3465347 : Nat := 1779388645616158547625665

theorem tailTrace_3465347 : CollatzResearch.WordTrace tailWord_3465347 prefixEnd_3465347 1779388645616158547625665 := by
  unfold tailWord_3465347
  simp only [CollatzResearch.WordTrace]
  refine ⟨126391588576647127994386295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84261059051098085329590863 126391588576647127994386295)
  ·
    refine ⟨189587382864970691991579443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126391588576647127994386295 189587382864970691991579443)
    ·
      refine ⟨284381074297456037987369165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189587382864970691991579443 284381074297456037987369165)
      ·
        refine ⟨106642902861546014245263437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284381074297456037987369165 106642902861546014245263437)
        ·
          refine ⟨39991088573079755341973789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106642902861546014245263437 39991088573079755341973789)
          ·
            refine ⟨14996658214904908253240171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39991088573079755341973789 14996658214904908253240171)
            ·
              refine ⟨22494987322357362379860257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14996658214904908253240171 22494987322357362379860257)
              ·
                refine ⟨16871240491768021784895193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22494987322357362379860257 16871240491768021784895193)
                ·
                  refine ⟨12653430368826016338671395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16871240491768021784895193 12653430368826016338671395)
                  ·
                    refine ⟨18980145553239024508007093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12653430368826016338671395 18980145553239024508007093)
                    ·
                      refine ⟨1779388645616158547625665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18980145553239024508007093 1779388645616158547625665)
                      ·
                        rfl

theorem cell23_3465347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_3465347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465347 prefixEnd_3465347 := by exact prefixLift 3465347
  have htrace : WordTrace (prefixWord ++ tailWord_3465347) baseStart_3465347 baseEnd_3465347 := by
    simpa [prefixWord, tailWord_3465347, baseEnd_3465347] using wordTrace_append hprefix tailTrace_3465347
  have hstable : (prefixWord ++ tailWord_3465347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465347).length < 2 ^ (prefixWord ++ tailWord_3465347).sum := by decide
  have hdescent : baseEnd_3465347 < baseStart_3465347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465394 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_3465394 : Nat := 118140960795 + 3465394 * 2 ^ 59
def prefixEnd_3465394 : Nat := 4983230072969 + 3 ^ 40 * 3465394 * 2
def baseEnd_3465394 : Nat := 1779412779206919863737949

theorem tailTrace_3465394 : CollatzResearch.WordTrace tailWord_3465394 prefixEnd_3465394 1779412779206919863737949 := by
  unfold tailWord_3465394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31598325701869213755336809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84262201871651236680898157 31598325701869213755336809)
  ·
    refine ⟨23698744276401910316502607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31598325701869213755336809 23698744276401910316502607)
    ·
      refine ⟨35548116414602865474753911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23698744276401910316502607 35548116414602865474753911)
      ·
        refine ⟨53322174621904298212130867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35548116414602865474753911 53322174621904298212130867)
        ·
          refine ⟨79983261932856447318196301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53322174621904298212130867 79983261932856447318196301)
          ·
            refine ⟨29993723224821167744323613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79983261932856447318196301 29993723224821167744323613)
            ·
              refine ⟨11247646209307937904121355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29993723224821167744323613 11247646209307937904121355)
              ·
                refine ⟨16871469313961906856182033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11247646209307937904121355 16871469313961906856182033)
                ·
                  refine ⟨12653601985471430142136525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16871469313961906856182033 12653601985471430142136525)
                  ·
                    refine ⟨4745100744551786303301197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12653601985471430142136525 4745100744551786303301197)
                    ·
                      refine ⟨1779412779206919863737949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4745100744551786303301197 1779412779206919863737949)
                      ·
                        rfl

theorem cell23_3465394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_3465394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465394 prefixEnd_3465394 := by exact prefixLift 3465394
  have htrace : WordTrace (prefixWord ++ tailWord_3465394) baseStart_3465394 baseEnd_3465394 := by
    simpa [prefixWord, tailWord_3465394, baseEnd_3465394] using wordTrace_append hprefix tailTrace_3465394
  have hstable : (prefixWord ++ tailWord_3465394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465394).length < 2 ^ (prefixWord ++ tailWord_3465394).sum := by decide
  have hdescent : baseEnd_3465394 < baseStart_3465394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465434 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_3465434 : Nat := 118140960795 + 3465434 * 2 ^ 59
def prefixEnd_3465434 : Nat := 4983230072969 + 3 ^ 40 * 3465434 * 2
def baseEnd_3465434 : Nat := 1779433318433099707237765

theorem tailTrace_3465434 : CollatzResearch.WordTrace tailWord_3465434 prefixEnd_3465434 1779433318433099707237765 := by
  unfold tailWord_3465434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31598690431832985463200839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84263174484887961235202237 31598690431832985463200839)
  ·
    refine ⟨47398035647749478194801259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31598690431832985463200839 47398035647749478194801259)
    ·
      refine ⟨71097053471624217292201889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47398035647749478194801259 71097053471624217292201889)
      ·
        refine ⟨53322790103718162969151417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71097053471624217292201889 53322790103718162969151417)
        ·
          refine ⟨39992092577788622226863563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53322790103718162969151417 39992092577788622226863563)
          ·
            refine ⟨59988138866682933340295345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39992092577788622226863563 59988138866682933340295345)
            ·
              refine ⟨44991104150012200005221509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59988138866682933340295345 44991104150012200005221509)
              ·
                refine ⟨8435832028127287500979033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44991104150012200005221509 8435832028127287500979033)
                ·
                  refine ⟨6326874021095465625734275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8435832028127287500979033 6326874021095465625734275)
                  ·
                    refine ⟨9490311031643198438601413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6326874021095465625734275 9490311031643198438601413)
                    ·
                      refine ⟨1779433318433099707237765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9490311031643198438601413 1779433318433099707237765)
                      ·
                        rfl

theorem cell23_3465434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_3465434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465434 prefixEnd_3465434 := by exact prefixLift 3465434
  have htrace : WordTrace (prefixWord ++ tailWord_3465434) baseStart_3465434 baseEnd_3465434 := by
    simpa [prefixWord, tailWord_3465434, baseEnd_3465434] using wordTrace_append hprefix tailTrace_3465434
  have hstable : (prefixWord ++ tailWord_3465434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465434).length < 2 ^ (prefixWord ++ tailWord_3465434).sum := by decide
  have hdescent : baseEnd_3465434 < baseStart_3465434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465477 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3465477 : Nat := 118140960795 + 3465477 * 2 ^ 59
def prefixEnd_3465477 : Nat := 4983230072969 + 3 ^ 40 * 3465477 * 2
def baseEnd_3465477 : Nat := 1779455398101243039000067

theorem tailTrace_3465477 : CollatzResearch.WordTrace tailWord_3465477 prefixEnd_3465477 1779455398101243039000067 := by
  unfold tailWord_3465477
  simp only [CollatzResearch.WordTrace]
  refine ⟨126396330066176160196618685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84264220044117440131079123 126396330066176160196618685)
  ·
    refine ⟨47398623774816060073732007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126396330066176160196618685 47398623774816060073732007)
    ·
      refine ⟨71097935662224090110598011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47398623774816060073732007 71097935662224090110598011)
      ·
        refine ⟨106646903493336135165897017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71097935662224090110598011 106646903493336135165897017)
        ·
          refine ⟨79985177620002101374422763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106646903493336135165897017 79985177620002101374422763)
          ·
            refine ⟨119977766430003152061634145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79985177620002101374422763 119977766430003152061634145)
            ·
              refine ⟨89983324822502364046225609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119977766430003152061634145 89983324822502364046225609)
              ·
                refine ⟨67487493616876773034669207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89983324822502364046225609 67487493616876773034669207)
                ·
                  refine ⟨101231240425315159552003811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67487493616876773034669207 101231240425315159552003811)
                  ·
                    refine ⟨151846860637972739328005717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101231240425315159552003811 151846860637972739328005717)
                    ·
                      refine ⟨1779455398101243039000067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 151846860637972739328005717 1779455398101243039000067)
                      ·
                        rfl

theorem cell23_3465477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3465477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465477 prefixEnd_3465477 := by exact prefixLift 3465477
  have htrace : WordTrace (prefixWord ++ tailWord_3465477) baseStart_3465477 baseEnd_3465477 := by
    simpa [prefixWord, tailWord_3465477, baseEnd_3465477] using wordTrace_append hprefix tailTrace_3465477
  have hstable : (prefixWord ++ tailWord_3465477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465477).length < 2 ^ (prefixWord ++ tailWord_3465477).sum := by decide
  have hdescent : baseEnd_3465477 < baseStart_3465477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465495 : List Nat := [1, 1, 3, 4, 1, 3, 3, 2, 1, 4]
def baseStart_3465495 : Nat := 118140960795 + 3465495 * 2 ^ 59
def prefixEnd_3465495 : Nat := 4983230072969 + 3 ^ 40 * 3465495 * 2
def baseEnd_3465495 : Nat := 593154880251007989524995

theorem tailTrace_3465495 : CollatzResearch.WordTrace tailWord_3465495 prefixEnd_3465495 593154880251007989524995 := by
  unfold tailWord_3465495
  simp only [CollatzResearch.WordTrace]
  refine ⟨126396986580110949270773939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84264657720073966180515959 126396986580110949270773939)
  ·
    refine ⟨189595479870166423906160909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126396986580110949270773939 189595479870166423906160909)
    ·
      refine ⟨71098304951312408964810341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189595479870166423906160909 71098304951312408964810341)
      ·
        refine ⟨13330932178371076680901939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71098304951312408964810341 13330932178371076680901939)
        ·
          refine ⟨19996398267556615021352909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13330932178371076680901939 19996398267556615021352909)
          ·
            refine ⟨7498649350333730633007341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19996398267556615021352909 7498649350333730633007341)
            ·
              refine ⟨2811993506375148987377753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7498649350333730633007341 2811993506375148987377753)
              ·
                refine ⟨2108995129781361740533315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2811993506375148987377753 2108995129781361740533315)
                ·
                  refine ⟨3163492694672042610799973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108995129781361740533315 3163492694672042610799973)
                  ·
                    refine ⟨593154880251007989524995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3163492694672042610799973 593154880251007989524995)
                    ·
                      rfl

theorem cell23_3465495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_3465495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465495 prefixEnd_3465495 := by exact prefixLift 3465495
  have htrace : WordTrace (prefixWord ++ tailWord_3465495) baseStart_3465495 baseEnd_3465495 := by
    simpa [prefixWord, tailWord_3465495, baseEnd_3465495] using wordTrace_append hprefix tailTrace_3465495
  have hstable : (prefixWord ++ tailWord_3465495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465495).length < 2 ^ (prefixWord ++ tailWord_3465495).sum := by decide
  have hdescent : baseEnd_3465495 < baseStart_3465495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465508 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 6]
def baseStart_3465508 : Nat := 118140960795 + 3465508 * 2 ^ 59
def prefixEnd_3465508 : Nat := 4983230072969 + 3 ^ 40 * 3465508 * 2
def baseEnd_3465508 : Nat := 197719035111281379745825

theorem tailTrace_3465508 : CollatzResearch.WordTrace tailWord_3465508 prefixEnd_3465508 197719035111281379745825 := by
  unfold tailWord_3465508
  simp only [CollatzResearch.WordTrace]
  refine ⟨63198730364531926245498589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84264973819375901660664785 63198730364531926245498589)
  ·
    refine ⟨23699523886699472342061971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63198730364531926245498589 23699523886699472342061971)
    ·
      refine ⟨35549285830049208513092957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23699523886699472342061971 35549285830049208513092957)
      ·
        refine ⟨13330982186268453192409859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35549285830049208513092957 13330982186268453192409859)
        ·
          refine ⟨19996473279402679788614789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13330982186268453192409859 19996473279402679788614789)
          ·
            refine ⟨3749338739888002460365273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19996473279402679788614789 3749338739888002460365273)
            ·
              refine ⟨2812004054916001845273955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749338739888002460365273 2812004054916001845273955)
              ·
                refine ⟨4218006082374002767910933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812004054916001845273955 4218006082374002767910933)
                ·
                  refine ⟨197719035111281379745825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4218006082374002767910933 197719035111281379745825)
                  ·
                    rfl

theorem cell23_3465508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_3465508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465508 prefixEnd_3465508 := by exact prefixLift 3465508
  have htrace : WordTrace (prefixWord ++ tailWord_3465508) baseStart_3465508 baseEnd_3465508 := by
    simpa [prefixWord, tailWord_3465508, baseEnd_3465508] using wordTrace_append hprefix tailTrace_3465508
  have hstable : (prefixWord ++ tailWord_3465508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465508).length < 2 ^ (prefixWord ++ tailWord_3465508).sum := by decide
  have hdescent : baseEnd_3465508 < baseStart_3465508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465521 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 3, 5]
def baseStart_3465521 : Nat := 118140960795 + 3465521 * 2 ^ 59
def prefixEnd_3465521 : Nat := 4983230072969 + 3 ^ 40 * 3465521 * 2
def baseEnd_3465521 : Nat := 593159330416680288949955

theorem tailTrace_3465521 : CollatzResearch.WordTrace tailWord_3465521 prefixEnd_3465521 593159330416680288949955 := by
  unfold tailWord_3465521
  simp only [CollatzResearch.WordTrace]
  refine ⟨126397934878016755711220417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84265289918677837140813611 126397934878016755711220417)
  ·
    refine ⟨94798451158512566783415313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126397934878016755711220417 94798451158512566783415313)
    ·
      refine ⟨71098838368884425087561485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94798451158512566783415313 71098838368884425087561485)
      ·
        refine ⟨26662064388331659407835557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71098838368884425087561485 26662064388331659407835557)
        ·
          refine ⟨4999137072812186138969167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26662064388331659407835557 4999137072812186138969167)
          ·
            refine ⟨7498705609218279208453751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4999137072812186138969167 7498705609218279208453751)
            ·
              refine ⟨11248058413827418812680627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498705609218279208453751 11248058413827418812680627)
              ·
                refine ⟨16872087620741128219020941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11248058413827418812680627 16872087620741128219020941)
                ·
                  refine ⟨6327032857777923082132853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16872087620741128219020941 6327032857777923082132853)
                  ·
                    refine ⟨593159330416680288949955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6327032857777923082132853 593159330416680288949955)
                    ·
                      rfl

theorem cell23_3465521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_3465521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465521 prefixEnd_3465521 := by exact prefixLift 3465521
  have htrace : WordTrace (prefixWord ++ tailWord_3465521) baseStart_3465521 baseEnd_3465521 := by
    simpa [prefixWord, tailWord_3465521, baseEnd_3465521] using wordTrace_append hprefix tailTrace_3465521
  have hstable : (prefixWord ++ tailWord_3465521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465521).length < 2 ^ (prefixWord ++ tailWord_3465521).sum := by decide
  have hdescent : baseEnd_3465521 < baseStart_3465521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465552 : List Nat := [2, 1, 1, 1, 1, 8, 2, 2, 1, 1, 3]
def baseStart_3465552 : Nat := 118140960795 + 3465552 * 2 ^ 59
def prefixEnd_3465552 : Nat := 4983230072969 + 3 ^ 40 * 3465552 * 2
def baseEnd_3465552 : Nat := 1779493909150330245562223

theorem tailTrace_3465552 : CollatzResearch.WordTrace tailWord_3465552 prefixEnd_3465552 1779493909150330245562223 := by
  unfold tailWord_3465552
  simp only [CollatzResearch.WordTrace]
  refine ⟨63199532770452224002799455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84266043693936298670399273 63199532770452224002799455)
  ·
    refine ⟨94799299155678336004199183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63199532770452224002799455 94799299155678336004199183)
    ·
      refine ⟨142198948733517504006298775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94799299155678336004199183 142198948733517504006298775)
      ·
        refine ⟨213298423100276256009448163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142198948733517504006298775 213298423100276256009448163)
        ·
          refine ⟨319947634650414384014172245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213298423100276256009448163 319947634650414384014172245)
          ·
            refine ⟨3749386343559543562666081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 319947634650414384014172245 3749386343559543562666081)
            ·
              refine ⟨2812039757669657671999561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749386343559543562666081 2812039757669657671999561)
              ·
                refine ⟨2109029818252243253999671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812039757669657671999561 2109029818252243253999671)
                ·
                  refine ⟨3163544727378364880999507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109029818252243253999671 3163544727378364880999507)
                  ·
                    refine ⟨4745317091067547321499261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3163544727378364880999507 4745317091067547321499261)
                    ·
                      refine ⟨1779493909150330245562223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4745317091067547321499261 1779493909150330245562223)
                      ·
                        rfl

theorem cell23_3465552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 1, 3].length) (baseStart_3465552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465552 prefixEnd_3465552 := by exact prefixLift 3465552
  have htrace : WordTrace (prefixWord ++ tailWord_3465552) baseStart_3465552 baseEnd_3465552 := by
    simpa [prefixWord, tailWord_3465552, baseEnd_3465552] using wordTrace_append hprefix tailTrace_3465552
  have hstable : (prefixWord ++ tailWord_3465552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465552).length < 2 ^ (prefixWord ++ tailWord_3465552).sum := by decide
  have hdescent : baseEnd_3465552 < baseStart_3465552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465554 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3465554 : Nat := 118140960795 + 3465554 * 2 ^ 59
def prefixEnd_3465554 : Nat := 4983230072969 + 3 ^ 40 * 3465554 * 2
def baseEnd_3465554 : Nat := 1779494936111639237737213

theorem tailTrace_3465554 : CollatzResearch.WordTrace tailWord_3465554 prefixEnd_3465554 1779494936111639237737213 := by
  unfold tailWord_3465554
  simp only [CollatzResearch.WordTrace]
  refine ⟨31599784621724300586792929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84266092324598134898114477 31599784621724300586792929)
  ·
    refine ⟨23699838466293225440094697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31599784621724300586792929 23699838466293225440094697)
    ·
      refine ⟨17774878849719919080071023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23699838466293225440094697 17774878849719919080071023)
      ·
        refine ⟨26662318274579878620106535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17774878849719919080071023 26662318274579878620106535)
        ·
          refine ⟨39993477411869817930159803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26662318274579878620106535 39993477411869817930159803)
          ·
            refine ⟨59990216117804726895239705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39993477411869817930159803 59990216117804726895239705)
            ·
              refine ⟨44992662088353545171429779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59990216117804726895239705 44992662088353545171429779)
              ·
                refine ⟨67488993132530317757144669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44992662088353545171429779 67488993132530317757144669)
                ·
                  refine ⟨25308372424698869158929251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67488993132530317757144669 25308372424698869158929251)
                  ·
                    refine ⟨37962558637048303738393877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25308372424698869158929251 37962558637048303738393877)
                    ·
                      refine ⟨1779494936111639237737213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37962558637048303738393877 1779494936111639237737213)
                      ·
                        rfl

theorem cell23_3465554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3465554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465554 prefixEnd_3465554 := by exact prefixLift 3465554
  have htrace : WordTrace (prefixWord ++ tailWord_3465554) baseStart_3465554 baseEnd_3465554 := by
    simpa [prefixWord, tailWord_3465554, baseEnd_3465554] using wordTrace_append hprefix tailTrace_3465554
  have hstable : (prefixWord ++ tailWord_3465554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465554).length < 2 ^ (prefixWord ++ tailWord_3465554).sum := by decide
  have hdescent : baseEnd_3465554 < baseStart_3465554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465571 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 4]
def baseStart_3465571 : Nat := 118140960795 + 3465571 * 2 ^ 59
def prefixEnd_3465571 : Nat := 4983230072969 + 3 ^ 40 * 3465571 * 2
def baseEnd_3465571 : Nat := 1779503665282765671224635

theorem tailTrace_3465571 : CollatzResearch.WordTrace tailWord_3465571 prefixEnd_3465571 1779503665282765671224635 := by
  unfold tailWord_3465571
  simp only [CollatzResearch.WordTrace]
  refine ⟨126399758527835614250540567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84266505685223742833693711 126399758527835614250540567)
  ·
    refine ⟨189599637791753421375810851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126399758527835614250540567 189599637791753421375810851)
    ·
      refine ⟨284399456687630132063716277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189599637791753421375810851 284399456687630132063716277)
      ·
        refine ⟨26662449064465324880973401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284399456687630132063716277 26662449064465324880973401)
        ·
          refine ⟨19996836798348993660730051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26662449064465324880973401 19996836798348993660730051)
          ·
            refine ⟨29995255197523490491095077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19996836798348993660730051 29995255197523490491095077)
            ·
              refine ⟨5624110349535654467080327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29995255197523490491095077 5624110349535654467080327)
              ·
                refine ⟨8436165524303481700620491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5624110349535654467080327 8436165524303481700620491)
                ·
                  refine ⟨12654248286455222550930737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8436165524303481700620491 12654248286455222550930737)
                  ·
                    refine ⟨9490686214841416913198053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12654248286455222550930737 9490686214841416913198053)
                    ·
                      refine ⟨1779503665282765671224635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9490686214841416913198053 1779503665282765671224635)
                      ·
                        rfl

theorem cell23_3465571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_3465571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465571 prefixEnd_3465571 := by exact prefixLift 3465571
  have htrace : WordTrace (prefixWord ++ tailWord_3465571) baseStart_3465571 baseEnd_3465571 := by
    simpa [prefixWord, tailWord_3465571, baseEnd_3465571] using wordTrace_append hprefix tailTrace_3465571
  have hstable : (prefixWord ++ tailWord_3465571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465571).length < 2 ^ (prefixWord ++ tailWord_3465571).sum := by decide
  have hdescent : baseEnd_3465571 < baseStart_3465571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465575 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_3465575 : Nat := 118140960795 + 3465575 * 2 ^ 59
def prefixEnd_3465575 : Nat := 4983230072969 + 3 ^ 40 * 3465575 * 2
def baseEnd_3465575 : Nat := 1779505719205383655574617

theorem tailTrace_3465575 : CollatzResearch.WordTrace tailWord_3465575 prefixEnd_3465575 1779505719205383655574617 := by
  unfold tailWord_3465575
  simp only [CollatzResearch.WordTrace]
  refine ⟨126399904419821122933686179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84266602946547415289124119 126399904419821122933686179)
  ·
    refine ⟨189599856629731684400529269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126399904419821122933686179 189599856629731684400529269)
    ·
      refine ⟨17774986559037345412549619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189599856629731684400529269 17774986559037345412549619)
      ·
        refine ⟨26662479838556018118824429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17774986559037345412549619 26662479838556018118824429)
        ·
          refine ⟨9998429939458506794559161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26662479838556018118824429 9998429939458506794559161)
          ·
            refine ⟨7498822454593880095919371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9998429939458506794559161 7498822454593880095919371)
            ·
              refine ⟨11248233681890820143879057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498822454593880095919371 11248233681890820143879057)
              ·
                refine ⟨8436175261418115107909293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11248233681890820143879057 8436175261418115107909293)
                ·
                  refine ⟨3163565723031793165465985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8436175261418115107909293 3163565723031793165465985)
                  ·
                    refine ⟨2372674292273844874099489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3163565723031793165465985 2372674292273844874099489)
                    ·
                      refine ⟨1779505719205383655574617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372674292273844874099489 1779505719205383655574617)
                      ·
                        rfl

theorem cell23_3465575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_3465575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465575 prefixEnd_3465575 := by exact prefixLift 3465575
  have htrace : WordTrace (prefixWord ++ tailWord_3465575) baseStart_3465575 baseEnd_3465575 := by
    simpa [prefixWord, tailWord_3465575, baseEnd_3465575] using wordTrace_append hprefix tailTrace_3465575
  have hstable : (prefixWord ++ tailWord_3465575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465575).length < 2 ^ (prefixWord ++ tailWord_3465575).sum := by decide
  have hdescent : baseEnd_3465575 < baseStart_3465575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465578 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3465578 : Nat := 118140960795 + 3465578 * 2 ^ 59
def prefixEnd_3465578 : Nat := 4983230072969 + 3 ^ 40 * 3465578 * 2
def baseEnd_3465578 : Nat := 1779507259647347143837103

theorem tailTrace_3465578 : CollatzResearch.WordTrace tailWord_3465578 prefixEnd_3465578 1779507259647347143837103 := by
  unfold tailWord_3465578
  simp only [CollatzResearch.WordTrace]
  refine ⟨31600003459702563611511347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84266675892540169630696925 31600003459702563611511347)
  ·
    refine ⟨47400005189553845417267021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31600003459702563611511347 47400005189553845417267021)
    ·
      refine ⟨17775001946082692031475133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47400005189553845417267021 17775001946082692031475133)
      ·
        refine ⟨6665625729781009511803175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17775001946082692031475133 6665625729781009511803175)
        ·
          refine ⟨9998438594671514267704763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6665625729781009511803175 9998438594671514267704763)
          ·
            refine ⟨14997657892007271401557145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9998438594671514267704763 14997657892007271401557145)
            ·
              refine ⟨11248243419005453551167859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14997657892007271401557145 11248243419005453551167859)
              ·
                refine ⟨16872365128508180326751789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11248243419005453551167859 16872365128508180326751789)
                ·
                  refine ⟨6327136923190567622531921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16872365128508180326751789 6327136923190567622531921)
                  ·
                    refine ⟨4745352692392925716898941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6327136923190567622531921 4745352692392925716898941)
                    ·
                      refine ⟨1779507259647347143837103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4745352692392925716898941 1779507259647347143837103)
                      ·
                        rfl

theorem cell23_3465578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3465578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465578 prefixEnd_3465578 := by exact prefixLift 3465578
  have htrace : WordTrace (prefixWord ++ tailWord_3465578) baseStart_3465578 baseEnd_3465578 := by
    simpa [prefixWord, tailWord_3465578, baseEnd_3465578] using wordTrace_append hprefix tailTrace_3465578
  have hstable : (prefixWord ++ tailWord_3465578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465578).length < 2 ^ (prefixWord ++ tailWord_3465578).sum := by decide
  have hdescent : baseEnd_3465578 < baseStart_3465578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465581 : List Nat := [1, 5, 1, 1, 1, 2, 5, 7]
def baseStart_3465581 : Nat := 118140960795 + 3465581 * 2 ^ 59
def prefixEnd_3465581 : Nat := 4983230072969 + 3 ^ 40 * 3465581 * 2
def baseEnd_3465581 : Nat := 65907733336641134522207

theorem tailTrace_3465581 : CollatzResearch.WordTrace tailWord_3465581 prefixEnd_3465581 65907733336641134522207 := by
  unfold tailWord_3465581
  simp only [CollatzResearch.WordTrace]
  refine ⟨126400123257799385958404597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84266748838532923972269731 126400123257799385958404597)
  ·
    refine ⟨11850011555418692433600431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126400123257799385958404597 11850011555418692433600431)
    ·
      refine ⟨17775017333128038650400647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11850011555418692433600431 17775017333128038650400647)
      ·
        refine ⟨26662525999692057975600971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17775017333128038650400647 26662525999692057975600971)
        ·
          refine ⟨39993788999538086963401457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26662525999692057975600971 39993788999538086963401457)
          ·
            refine ⟨29995341749653565222551093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39993788999538086963401457 29995341749653565222551093)
            ·
              refine ⟨2812063289030021739614165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29995341749653565222551093 2812063289030021739614165)
              ·
                refine ⟨65907733336641134522207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2812063289030021739614165 65907733336641134522207)
                ·
                  rfl

theorem cell23_3465581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 7].length) (baseStart_3465581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465581 prefixEnd_3465581 := by exact prefixLift 3465581
  have htrace : WordTrace (prefixWord ++ tailWord_3465581) baseStart_3465581 baseEnd_3465581 := by
    simpa [prefixWord, tailWord_3465581, baseEnd_3465581] using wordTrace_append hprefix tailTrace_3465581
  have hstable : (prefixWord ++ tailWord_3465581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465581).length < 2 ^ (prefixWord ++ tailWord_3465581).sum := by decide
  have hdescent : baseEnd_3465581 < baseStart_3465581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465595 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 1, 2, 3]
def baseStart_3465595 : Nat := 118140960795 + 3465595 * 2 ^ 59
def prefixEnd_3465595 : Nat := 4983230072969 + 3 ^ 40 * 3465595 * 2
def baseEnd_3465595 : Nat := 1779515988818473577324525

theorem tailTrace_3465595 : CollatzResearch.WordTrace tailWord_3465595 prefixEnd_3465595 1779515988818473577324525 := by
  unfold tailWord_3465595
  simp only [CollatzResearch.WordTrace]
  refine ⟨126400633879748666349414239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84267089253165777566276159 126400633879748666349414239)
  ·
    refine ⟨189600950819622999524121359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126400633879748666349414239 189600950819622999524121359)
    ·
      refine ⟨284401426229434499286182039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189600950819622999524121359 284401426229434499286182039)
      ·
        refine ⟨426602139344151748929273059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284401426229434499286182039 426602139344151748929273059)
        ·
          refine ⟨639903209016227623393909589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426602139344151748929273059 639903209016227623393909589)
          ·
            refine ⟨3749432865329458730823689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 639903209016227623393909589 3749432865329458730823689)
            ·
              refine ⟨2812074648997094048117767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749432865329458730823689 2812074648997094048117767)
              ·
                refine ⟨4218111973495641072176651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812074648997094048117767 4218111973495641072176651)
                ·
                  refine ⟨6327167960243461608264977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218111973495641072176651 6327167960243461608264977)
                  ·
                    refine ⟨4745375970182596206198733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6327167960243461608264977 4745375970182596206198733)
                    ·
                      refine ⟨1779515988818473577324525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4745375970182596206198733 1779515988818473577324525)
                      ·
                        rfl

theorem cell23_3465595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 2, 3].length) (baseStart_3465595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465595 prefixEnd_3465595 := by exact prefixLift 3465595
  have htrace : WordTrace (prefixWord ++ tailWord_3465595) baseStart_3465595 baseEnd_3465595 := by
    simpa [prefixWord, tailWord_3465595, baseEnd_3465595] using wordTrace_append hprefix tailTrace_3465595
  have hstable : (prefixWord ++ tailWord_3465595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465595).length < 2 ^ (prefixWord ++ tailWord_3465595).sum := by decide
  have hdescent : baseEnd_3465595 < baseStart_3465595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465608 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3465608 : Nat := 118140960795 + 3465608 * 2 ^ 59
def prefixEnd_3465608 : Nat := 4983230072969 + 3 ^ 40 * 3465608 * 2
def baseEnd_3465608 : Nat := 1779522664066982026461965

theorem tailTrace_3465608 : CollatzResearch.WordTrace tailWord_3465608 prefixEnd_3465608 1779522664066982026461965 := by
  unfold tailWord_3465608
  simp only [CollatzResearch.WordTrace]
  refine ⟨63200554014350784784818739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84267405352467713046424985 63200554014350784784818739)
  ·
    refine ⟨94800831021526177177228109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63200554014350784784818739 94800831021526177177228109)
    ·
      refine ⟨35550311633072316441460541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94800831021526177177228109 35550311633072316441460541)
      ·
        refine ⟨13331366862402118665547703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35550311633072316441460541 13331366862402118665547703)
        ·
          refine ⟨19997050293603177998321555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13331366862402118665547703 19997050293603177998321555)
          ·
            refine ⟨29995575440404766997482333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19997050293603177998321555 29995575440404766997482333)
            ·
              refine ⟨11248340790151787624055875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29995575440404766997482333 11248340790151787624055875)
              ·
                refine ⟨16872511185227681436083813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11248340790151787624055875 16872511185227681436083813)
                ·
                  refine ⟨3163595847230190269265715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16872511185227681436083813 3163595847230190269265715)
                  ·
                    refine ⟨4745393770845285403898573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3163595847230190269265715 4745393770845285403898573)
                    ·
                      refine ⟨1779522664066982026461965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4745393770845285403898573 1779522664066982026461965)
                      ·
                        rfl

theorem cell23_3465608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3465608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465608 prefixEnd_3465608 := by exact prefixLift 3465608
  have htrace : WordTrace (prefixWord ++ tailWord_3465608) baseStart_3465608 baseEnd_3465608 := by
    simpa [prefixWord, tailWord_3465608, baseEnd_3465608] using wordTrace_append hprefix tailTrace_3465608
  have hstable : (prefixWord ++ tailWord_3465608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465608).length < 2 ^ (prefixWord ++ tailWord_3465608).sum := by decide
  have hdescent : baseEnd_3465608 < baseStart_3465608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465622 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3465622 : Nat := 118140960795 + 3465622 * 2 ^ 59
def prefixEnd_3465622 : Nat := 4983230072969 + 3 ^ 40 * 3465622 * 2
def baseEnd_3465622 : Nat := 1779529852796144971686901

theorem tailTrace_3465622 : CollatzResearch.WordTrace tailWord_3465622 prefixEnd_3465622 1779529852796144971686901 := by
  unfold tailWord_3465622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7900101165665678122540445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84267745767100566640431413 7900101165665678122540445)
  ·
    refine ⟨2962537937124629295952667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7900101165665678122540445 2962537937124629295952667)
    ·
      refine ⟨4443806905686943943929001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962537937124629295952667 4443806905686943943929001)
      ·
        refine ⟨3332855179265207957946751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4443806905686943943929001 3332855179265207957946751)
        ·
          refine ⟨4999282768897811936920127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3332855179265207957946751 4999282768897811936920127)
          ·
            refine ⟨7498924153346717905380191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4999282768897811936920127 7498924153346717905380191)
            ·
              refine ⟨11248386230020076858070287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498924153346717905380191 11248386230020076858070287)
              ·
                refine ⟨16872579345030115287105431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11248386230020076858070287 16872579345030115287105431)
                ·
                  refine ⟨25308869017545172930658147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16872579345030115287105431 25308869017545172930658147)
                  ·
                    refine ⟨37963303526317759395987221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25308869017545172930658147 37963303526317759395987221)
                    ·
                      refine ⟨1779529852796144971686901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37963303526317759395987221 1779529852796144971686901)
                      ·
                        rfl

theorem cell23_3465622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3465622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465622 prefixEnd_3465622 := by exact prefixLift 3465622
  have htrace : WordTrace (prefixWord ++ tailWord_3465622) baseStart_3465622 baseEnd_3465622 := by
    simpa [prefixWord, tailWord_3465622, baseEnd_3465622] using wordTrace_append hprefix tailTrace_3465622
  have hstable : (prefixWord ++ tailWord_3465622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465622).length < 2 ^ (prefixWord ++ tailWord_3465622).sum := by decide
  have hdescent : baseEnd_3465622 < baseStart_3465622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465625 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 2, 1, 3]
def baseStart_3465625 : Nat := 118140960795 + 3465625 * 2 ^ 59
def prefixEnd_3465625 : Nat := 4983230072969 + 3 ^ 40 * 3465625 * 2
def baseEnd_3465625 : Nat := 1779531393238108459949387

theorem tailTrace_3465625 : CollatzResearch.WordTrace tailWord_3465625 prefixEnd_3465625 1779531393238108459949387 := by
  unfold tailWord_3465625
  simp only [CollatzResearch.WordTrace]
  refine ⟨126401728069639981473006329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84267818713093320982004219 126401728069639981473006329)
  ·
    refine ⟨94801296052229986104754747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126401728069639981473006329 94801296052229986104754747)
    ·
      refine ⟨142201944078344979157132121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94801296052229986104754747 142201944078344979157132121)
      ·
        refine ⟨106651458058758734367849091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142201944078344979157132121 106651458058758734367849091)
        ·
          refine ⟨159977187088138101551773637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106651458058758734367849091 159977187088138101551773637)
          ·
            refine ⟨29995722579025894040957557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159977187088138101551773637 29995722579025894040957557)
            ·
              refine ⟨2812098991783677566339771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29995722579025894040957557 2812098991783677566339771)
              ·
                refine ⟨4218148487675516349509657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812098991783677566339771 4218148487675516349509657)
                ·
                  refine ⟨3163611365756637262132243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4218148487675516349509657 3163611365756637262132243)
                  ·
                    refine ⟨4745417048634955893198365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3163611365756637262132243 4745417048634955893198365)
                    ·
                      refine ⟨1779531393238108459949387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4745417048634955893198365 1779531393238108459949387)
                      ·
                        rfl

theorem cell23_3465625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_3465625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465625 prefixEnd_3465625 := by exact prefixLift 3465625
  have htrace : WordTrace (prefixWord ++ tailWord_3465625) baseStart_3465625 baseEnd_3465625 := by
    simpa [prefixWord, tailWord_3465625, baseEnd_3465625] using wordTrace_append hprefix tailTrace_3465625
  have hstable : (prefixWord ++ tailWord_3465625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465625).length < 2 ^ (prefixWord ++ tailWord_3465625).sum := by decide
  have hdescent : baseEnd_3465625 < baseStart_3465625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465635 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 1, 3, 2]
def baseStart_3465635 : Nat := 118140960795 + 3465635 * 2 ^ 59
def prefixEnd_3465635 : Nat := 4983230072969 + 3 ^ 40 * 3465635 * 2
def baseEnd_3465635 : Nat := 1779536528044653420824341

theorem tailTrace_3465635 : CollatzResearch.WordTrace tailWord_3465635 prefixEnd_3465635 1779536528044653420824341 := by
  unfold tailWord_3465635
  simp only [CollatzResearch.WordTrace]
  refine ⟨126402092799603753180870359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84268061866402502120580239 126402092799603753180870359)
  ·
    refine ⟨189603139199405629771305539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126402092799603753180870359 189603139199405629771305539)
    ·
      refine ⟨284404708799108444656958309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189603139199405629771305539 284404708799108444656958309)
      ·
        refine ⟨53325882899832833373179683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284404708799108444656958309 53325882899832833373179683)
        ·
          refine ⟨79988824349749250059769525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53325882899832833373179683 79988824349749250059769525)
          ·
            refine ⟨7498952282788992193103393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79988824349749250059769525 7498952282788992193103393)
            ·
              refine ⟨5624214212091744144827545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7498952282788992193103393 5624214212091744144827545)
              ·
                refine ⟨4218160659068808108620659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5624214212091744144827545 4218160659068808108620659)
                ·
                  refine ⟨6327240988603212162930989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218160659068808108620659 6327240988603212162930989)
                  ·
                    refine ⟨2372715370726204561099121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6327240988603212162930989 2372715370726204561099121)
                    ·
                      refine ⟨1779536528044653420824341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372715370726204561099121 1779536528044653420824341)
                      ·
                        rfl

theorem cell23_3465635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_3465635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465635 prefixEnd_3465635 := by exact prefixLift 3465635
  have htrace : WordTrace (prefixWord ++ tailWord_3465635) baseStart_3465635 baseEnd_3465635 := by
    simpa [prefixWord, tailWord_3465635, baseEnd_3465635] using wordTrace_append hprefix tailTrace_3465635
  have hstable : (prefixWord ++ tailWord_3465635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465635).length < 2 ^ (prefixWord ++ tailWord_3465635).sum := by decide
  have hdescent : baseEnd_3465635 < baseStart_3465635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465664 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_3465664 : Nat := 118140960795 + 3465664 * 2 ^ 59
def prefixEnd_3465664 : Nat := 4983230072969 + 3 ^ 40 * 3465664 * 2
def baseEnd_3465664 : Nat := 1779551418983633807361707

theorem tailTrace_3465664 : CollatzResearch.WordTrace tailWord_3465664 prefixEnd_3465664 1779551418983633807361707 := by
  unfold tailWord_3465664
  simp only [CollatzResearch.WordTrace]
  refine ⟨63201575258249345566838023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84268767010999127422450697 63201575258249345566838023)
  ·
    refine ⟨94802362887374018350257035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63201575258249345566838023 94802362887374018350257035)
    ·
      refine ⟨142203544331061027525385553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94802362887374018350257035 142203544331061027525385553)
      ·
        refine ⟨106652658248295770644039165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142203544331061027525385553 106652658248295770644039165)
        ·
          refine ⟨39994746843110913991514687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106652658248295770644039165 39994746843110913991514687)
          ·
            refine ⟨59992120264666370987272031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39994746843110913991514687 59992120264666370987272031)
            ·
              refine ⟨89988180396999556480908047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59992120264666370987272031 89988180396999556480908047)
              ·
                refine ⟨134982270595499334721362071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89988180396999556480908047 134982270595499334721362071)
                ·
                  refine ⟨202473405893249002082043107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134982270595499334721362071 202473405893249002082043107)
                  ·
                    refine ⟨303710108839873503123064661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202473405893249002082043107 303710108839873503123064661)
                    ·
                      refine ⟨1779551418983633807361707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 303710108839873503123064661 1779551418983633807361707)
                      ·
                        rfl

theorem cell23_3465664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_3465664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465664 prefixEnd_3465664 := by exact prefixLift 3465664
  have htrace : WordTrace (prefixWord ++ tailWord_3465664) baseStart_3465664 baseEnd_3465664 := by
    simpa [prefixWord, tailWord_3465664, baseEnd_3465664] using wordTrace_append hprefix tailTrace_3465664
  have hstable : (prefixWord ++ tailWord_3465664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465664).length < 2 ^ (prefixWord ++ tailWord_3465664).sum := by decide
  have hdescent : baseEnd_3465664 < baseStart_3465664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465671 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 7]
def baseStart_3465671 : Nat := 118140960795 + 3465671 * 2 ^ 59
def prefixEnd_3465671 : Nat := 4983230072969 + 3 ^ 40 * 3465671 * 2
def baseEnd_3465671 : Nat := 197728334816468364441575

theorem tailTrace_3465671 : CollatzResearch.WordTrace tailWord_3465671 prefixEnd_3465671 197728334816468364441575 := by
  unfold tailWord_3465671
  simp only [CollatzResearch.WordTrace]
  refine ⟨126403405827473331329180867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84268937218315554219453911 126403405827473331329180867)
  ·
    refine ⟨189605108741209996993771301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126403405827473331329180867 189605108741209996993771301)
    ·
      refine ⟨35550957888976874436332119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189605108741209996993771301 35550957888976874436332119)
      ·
        refine ⟨53326436833465311654498179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35550957888976874436332119 53326436833465311654498179)
        ·
          refine ⟨79989655250197967481747269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53326436833465311654498179 79989655250197967481747269)
          ·
            refine ⟨14998060359412118902827613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79989655250197967481747269 14998060359412118902827613)
            ·
              refine ⟨5624272634779544588560355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14998060359412118902827613 5624272634779544588560355)
              ·
                refine ⟨8436408952169316882840533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5624272634779544588560355 8436408952169316882840533)
                ·
                  refine ⟨197728334816468364441575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8436408952169316882840533 197728334816468364441575)
                  ·
                    rfl

theorem cell23_3465671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 7].length) (baseStart_3465671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465671 prefixEnd_3465671 := by exact prefixLift 3465671
  have htrace : WordTrace (prefixWord ++ tailWord_3465671) baseStart_3465671 baseEnd_3465671 := by
    simpa [prefixWord, tailWord_3465671, baseEnd_3465671] using wordTrace_append hprefix tailTrace_3465671
  have hstable : (prefixWord ++ tailWord_3465671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465671).length < 2 ^ (prefixWord ++ tailWord_3465671).sum := by decide
  have hdescent : baseEnd_3465671 < baseStart_3465671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465681 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_3465681 : Nat := 118140960795 + 3465681 * 2 ^ 59
def prefixEnd_3465681 : Nat := 4983230072969 + 3 ^ 40 * 3465681 * 2
def baseEnd_3465681 : Nat := 1779560148154760240849129

theorem tailTrace_3465681 : CollatzResearch.WordTrace tailWord_3465681 prefixEnd_3465681 1779560148154760240849129 := by
  unfold tailWord_3465681
  simp only [CollatzResearch.WordTrace]
  refine ⟨126403770557437103037044897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84269180371624735358029931 126403770557437103037044897)
  ·
    refine ⟨94802827918077827277783673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126403770557437103037044897 94802827918077827277783673)
    ·
      refine ⟨71102120938558370458337755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94802827918077827277783673 71102120938558370458337755)
      ·
        refine ⟨106653181407837555687506633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71102120938558370458337755 106653181407837555687506633)
        ·
          refine ⟨79989886055878166765629975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106653181407837555687506633 79989886055878166765629975)
          ·
            refine ⟨119984829083817250148444963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79989886055878166765629975 119984829083817250148444963)
            ·
              refine ⟨179977243625725875222667445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119984829083817250148444963 179977243625725875222667445)
              ·
                refine ⟨16872866589911800802125073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179977243625725875222667445 16872866589911800802125073)
                ·
                  refine ⟨12654649942433850601593805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16872866589911800802125073 12654649942433850601593805)
                  ·
                    refine ⟨4745493728412693975597677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12654649942433850601593805 4745493728412693975597677)
                    ·
                      refine ⟨1779560148154760240849129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4745493728412693975597677 1779560148154760240849129)
                      ·
                        rfl

theorem cell23_3465681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_3465681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465681 prefixEnd_3465681 := by exact prefixLift 3465681
  have htrace : WordTrace (prefixWord ++ tailWord_3465681) baseStart_3465681 baseEnd_3465681 := by
    simpa [prefixWord, tailWord_3465681, baseEnd_3465681] using wordTrace_append hprefix tailTrace_3465681
  have hstable : (prefixWord ++ tailWord_3465681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465681).length < 2 ^ (prefixWord ++ tailWord_3465681).sum := by decide
  have hdescent : baseEnd_3465681 < baseStart_3465681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465718 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_3465718 : Nat := 118140960795 + 3465718 * 2 ^ 59
def prefixEnd_3465718 : Nat := 4983230072969 + 3 ^ 40 * 3465718 * 2
def baseEnd_3465718 : Nat := 593193048979658865362153

theorem tailTrace_3465718 : CollatzResearch.WordTrace tailWord_3465718 prefixEnd_3465718 593193048979658865362153 := by
  unfold tailWord_3465718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7900320003643941147258863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84270080038868705570761205 7900320003643941147258863)
  ·
    refine ⟨11850480005465911720888295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7900320003643941147258863 11850480005465911720888295)
    ·
      refine ⟨17775720008198867581332443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11850480005465911720888295 17775720008198867581332443)
      ·
        refine ⟨26663580012298301371998665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17775720008198867581332443 26663580012298301371998665)
        ·
          refine ⟨19997685009223726028998999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26663580012298301371998665 19997685009223726028998999)
          ·
            refine ⟨29996527513835589043498499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19997685009223726028998999 29996527513835589043498499)
            ·
              refine ⟨44994791270753383565247749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29996527513835589043498499 44994791270753383565247749)
              ·
                refine ⟨8436523363266259418483953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44994791270753383565247749 8436523363266259418483953)
                ·
                  refine ⟨6327392522449694563862965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8436523363266259418483953 6327392522449694563862965)
                  ·
                    refine ⟨593193048979658865362153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6327392522449694563862965 593193048979658865362153)
                    ·
                      rfl

theorem cell23_3465718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_3465718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465718 prefixEnd_3465718 := by exact prefixLift 3465718
  have htrace : WordTrace (prefixWord ++ tailWord_3465718) baseStart_3465718 baseEnd_3465718 := by
    simpa [prefixWord, tailWord_3465718, baseEnd_3465718] using wordTrace_append hprefix tailTrace_3465718
  have hstable : (prefixWord ++ tailWord_3465718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465718).length < 2 ^ (prefixWord ++ tailWord_3465718).sum := by decide
  have hdescent : baseEnd_3465718 < baseStart_3465718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465761 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 8]
def baseStart_3465761 : Nat := 118140960795 + 3465761 * 2 ^ 59
def prefixEnd_3465761 : Nat := 4983230072969 + 3 ^ 40 * 3465761 * 2
def baseEnd_3465761 : Nat := 197733469623013325316529

theorem tailTrace_3465761 : CollatzResearch.WordTrace tailWord_3465761 prefixEnd_3465761 197733469623013325316529 := by
  unfold tailWord_3465761
  simp only [CollatzResearch.WordTrace]
  refine ⟨126406688397147276699957137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84271125598098184466638091 126406688397147276699957137)
  ·
    refine ⟨94805016297860457524967853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126406688397147276699957137 94805016297860457524967853)
    ·
      refine ⟨35551881111697671571862945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94805016297860457524967853 35551881111697671571862945)
      ·
        refine ⟨26663910833773253678897209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35551881111697671571862945 26663910833773253678897209)
        ·
          refine ⟨19997933125329940259172907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26663910833773253678897209 19997933125329940259172907)
          ·
            refine ⟨29996899687994910388759361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19997933125329940259172907 29996899687994910388759361)
            ·
              refine ⟨22497674765996182791569521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29996899687994910388759361 22497674765996182791569521)
              ·
                refine ⟨16873256074497137093677141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22497674765996182791569521 16873256074497137093677141)
                ·
                  refine ⟨197733469623013325316529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16873256074497137093677141 197733469623013325316529)
                  ·
                    rfl

theorem cell23_3465761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 8].length) (baseStart_3465761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465761 prefixEnd_3465761 := by exact prefixLift 3465761
  have htrace : WordTrace (prefixWord ++ tailWord_3465761) baseStart_3465761 baseEnd_3465761 := by
    simpa [prefixWord, tailWord_3465761, baseEnd_3465761] using wordTrace_append hprefix tailTrace_3465761
  have hstable : (prefixWord ++ tailWord_3465761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465761).length < 2 ^ (prefixWord ++ tailWord_3465761).sum := by decide
  have hdescent : baseEnd_3465761 < baseStart_3465761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465765 : List Nat := [1, 3, 1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_3465765 : Nat := 118140960795 + 3465765 * 2 ^ 59
def prefixEnd_3465765 : Nat := 4983230072969 + 3 ^ 40 * 3465765 * 2
def baseEnd_3465765 : Nat := 593201093509912637399581

theorem tailTrace_3465765 : CollatzResearch.WordTrace tailWord_3465765 prefixEnd_3465765 593201093509912637399581 := by
  unfold tailWord_3465765
  simp only [CollatzResearch.WordTrace]
  refine ⟨126406834289132785383102749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84271222859421856922068499 126406834289132785383102749)
  ·
    refine ⟨47402562858424794518663531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126406834289132785383102749 47402562858424794518663531)
    ·
      refine ⟨71103844287637191777995297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47402562858424794518663531 71103844287637191777995297)
      ·
        refine ⟨53327883215727893833496473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71103844287637191777995297 53327883215727893833496473)
        ·
          refine ⟨39995912411795920375122355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53327883215727893833496473 39995912411795920375122355)
          ·
            refine ⟨59993868617693880562683533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39995912411795920375122355 59993868617693880562683533)
            ·
              refine ⟨22497700731635205211006325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59993868617693880562683533 22497700731635205211006325)
              ·
                refine ⟨2109159443590800488531843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22497700731635205211006325 2109159443590800488531843)
                ·
                  refine ⟨3163739165386200732797765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109159443590800488531843 3163739165386200732797765)
                  ·
                    refine ⟨593201093509912637399581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3163739165386200732797765 593201093509912637399581)
                    ·
                      rfl

theorem cell23_3465765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_3465765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465765 prefixEnd_3465765 := by exact prefixLift 3465765
  have htrace : WordTrace (prefixWord ++ tailWord_3465765) baseStart_3465765 baseEnd_3465765 := by
    simpa [prefixWord, tailWord_3465765, baseEnd_3465765] using wordTrace_append hprefix tailTrace_3465765
  have hstable : (prefixWord ++ tailWord_3465765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465765).length < 2 ^ (prefixWord ++ tailWord_3465765).sum := by decide
  have hdescent : baseEnd_3465765 < baseStart_3465765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465768 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3465768 : Nat := 118140960795 + 3465768 * 2 ^ 59
def prefixEnd_3465768 : Nat := 4983230072969 + 3 ^ 40 * 3465768 * 2
def baseEnd_3465768 : Nat := 1779604820971701400461229

theorem tailTrace_3465768 : CollatzResearch.WordTrace tailWord_3465768 prefixEnd_3465768 1779604820971701400461229 := by
  unfold tailWord_3465768
  simp only [CollatzResearch.WordTrace]
  refine ⟨63203471854060958447730979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84271295805414611263641305 63203471854060958447730979)
  ·
    refine ⟨94805207781091437671596469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63203471854060958447730979 94805207781091437671596469)
    ·
      refine ⟨8887988229477322281712169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94805207781091437671596469 8887988229477322281712169)
      ·
        refine ⟨6665991172107991711284127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8887988229477322281712169 6665991172107991711284127)
        ·
          refine ⟨9998986758161987566926191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6665991172107991711284127 9998986758161987566926191)
          ·
            refine ⟨14998480137242981350389287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9998986758161987566926191 14998480137242981350389287)
            ·
              refine ⟨22497720205864472025583931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14998480137242981350389287 22497720205864472025583931)
              ·
                refine ⟨33746580308796708038375897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22497720205864472025583931 33746580308796708038375897)
                ·
                  refine ⟨25309935231597531028781923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33746580308796708038375897 25309935231597531028781923)
                  ·
                    refine ⟨37964902847396296543172885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25309935231597531028781923 37964902847396296543172885)
                    ·
                      refine ⟨1779604820971701400461229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37964902847396296543172885 1779604820971701400461229)
                      ·
                        rfl

theorem cell23_3465768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3465768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465768 prefixEnd_3465768 := by exact prefixLift 3465768
  have htrace : WordTrace (prefixWord ++ tailWord_3465768) baseStart_3465768 baseEnd_3465768 := by
    simpa [prefixWord, tailWord_3465768, baseEnd_3465768] using wordTrace_append hprefix tailTrace_3465768
  have hstable : (prefixWord ++ tailWord_3465768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465768).length < 2 ^ (prefixWord ++ tailWord_3465768).sum := by decide
  have hdescent : baseEnd_3465768 < baseStart_3465768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465771 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 3]
def baseStart_3465771 : Nat := 118140960795 + 3465771 * 2 ^ 59
def prefixEnd_3465771 : Nat := 4983230072969 + 3 ^ 40 * 3465771 * 2
def baseEnd_3465771 : Nat := 1779606361413664888723715

theorem tailTrace_3465771 : CollatzResearch.WordTrace tailWord_3465771 prefixEnd_3465771 1779606361413664888723715 := by
  unfold tailWord_3465771
  simp only [CollatzResearch.WordTrace]
  refine ⟨126407053127111048407821167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84271368751407365605214111 126407053127111048407821167)
  ·
    refine ⟨189610579690666572611731751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126407053127111048407821167 189610579690666572611731751)
    ·
      refine ⟨284415869535999858917597627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189610579690666572611731751 284415869535999858917597627)
      ·
        refine ⟨426623804303999788376396441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284415869535999858917597627 426623804303999788376396441)
        ·
          refine ⟨319967853227999841282297331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426623804303999788376396441 319967853227999841282297331)
          ·
            refine ⟨479951779841999761923445997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319967853227999841282297331 479951779841999761923445997)
            ·
              refine ⟨179981917440749910721292249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479951779841999761923445997 179981917440749910721292249)
              ·
                refine ⟨134986438080562433040969187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179981917440749910721292249 134986438080562433040969187)
                ·
                  refine ⟨202479657120843649561453781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134986438080562433040969187 202479657120843649561453781)
                  ·
                    refine ⟨4745616963769773036596573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202479657120843649561453781 4745616963769773036596573)
                    ·
                      refine ⟨1779606361413664888723715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4745616963769773036596573 1779606361413664888723715)
                      ·
                        rfl

theorem cell23_3465771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 3].length) (baseStart_3465771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465771 prefixEnd_3465771 := by exact prefixLift 3465771
  have htrace : WordTrace (prefixWord ++ tailWord_3465771) baseStart_3465771 baseEnd_3465771 := by
    simpa [prefixWord, tailWord_3465771, baseEnd_3465771] using wordTrace_append hprefix tailTrace_3465771
  have hstable : (prefixWord ++ tailWord_3465771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465771).length < 2 ^ (prefixWord ++ tailWord_3465771).sum := by decide
  have hdescent : baseEnd_3465771 < baseStart_3465771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465778 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 6]
def baseStart_3465778 : Nat := 118140960795 + 3465778 * 2 ^ 59
def prefixEnd_3465778 : Nat := 4983230072969 + 3 ^ 40 * 3465778 * 2
def baseEnd_3465778 : Nat := 197734439530916262370687

theorem tailTrace_3465778 : CollatzResearch.WordTrace tailWord_3465778 prefixEnd_3465778 197734439530916262370687 := by
  unfold tailWord_3465778
  simp only [CollatzResearch.WordTrace]
  refine ⟨31601827109521422150831497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84271538958723792402217325 31601827109521422150831497)
  ·
    refine ⟨23701370332141066613123623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31601827109521422150831497 23701370332141066613123623)
    ·
      refine ⟨35552055498211599919685435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23701370332141066613123623 35552055498211599919685435)
      ·
        refine ⟨53328083247317399879528153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35552055498211599919685435 53328083247317399879528153)
        ·
          refine ⟨39996062435488049909646115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53328083247317399879528153 39996062435488049909646115)
          ·
            refine ⟨59994093653232074864469173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39996062435488049909646115 59994093653232074864469173)
            ·
              refine ⟨5624446279990507018543985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59994093653232074864469173 5624446279990507018543985)
              ·
                refine ⟨4218334709992880263907989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5624446279990507018543985 4218334709992880263907989)
                ·
                  refine ⟨197734439530916262370687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4218334709992880263907989 197734439530916262370687)
                  ·
                    rfl

theorem cell23_3465778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_3465778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465778 prefixEnd_3465778 := by exact prefixLift 3465778
  have htrace : WordTrace (prefixWord ++ tailWord_3465778) baseStart_3465778 baseEnd_3465778 := by
    simpa [prefixWord, tailWord_3465778, baseEnd_3465778] using wordTrace_append hprefix tailTrace_3465778
  have hstable : (prefixWord ++ tailWord_3465778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465778).length < 2 ^ (prefixWord ++ tailWord_3465778).sum := by decide
  have hdescent : baseEnd_3465778 < baseStart_3465778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465781 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3465781 : Nat := 118140960795 + 3465781 * 2 ^ 59
def prefixEnd_3465781 : Nat := 4983230072969 + 3 ^ 40 * 3465781 * 2
def baseEnd_3465781 : Nat := 1779611496220209849598669

theorem tailTrace_3465781 : CollatzResearch.WordTrace tailWord_3465781 prefixEnd_3465781 1779611496220209849598669 := by
  unfold tailWord_3465781
  simp only [CollatzResearch.WordTrace]
  refine ⟨126407417857074820115685197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84271611904716546743790131 126407417857074820115685197)
  ·
    refine ⟨47402781696403057543381949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126407417857074820115685197 47402781696403057543381949)
    ·
      refine ⟨17776043136151146578768231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47402781696403057543381949 17776043136151146578768231)
      ·
        refine ⟨26664064704226719868152347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17776043136151146578768231 26664064704226719868152347)
        ·
          refine ⟨39996097056340079802228521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26664064704226719868152347 39996097056340079802228521)
          ·
            refine ⟨29997072792255059851671391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39996097056340079802228521 29997072792255059851671391)
            ·
              refine ⟨44995609188382589777507087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29997072792255059851671391 44995609188382589777507087)
              ·
                refine ⟨67493413782573884666260631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44995609188382589777507087 67493413782573884666260631)
                ·
                  refine ⟨101240120673860826999390947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67493413782573884666260631 101240120673860826999390947)
                  ·
                    refine ⟨151860181010791240499086421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101240120673860826999390947 151860181010791240499086421)
                    ·
                      refine ⟨1779611496220209849598669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 151860181010791240499086421 1779611496220209849598669)
                      ·
                        rfl

theorem cell23_3465781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3465781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465781 prefixEnd_3465781 := by exact prefixLift 3465781
  have htrace : WordTrace (prefixWord ++ tailWord_3465781) baseStart_3465781 baseEnd_3465781 := by
    simpa [prefixWord, tailWord_3465781, baseEnd_3465781] using wordTrace_append hprefix tailTrace_3465781
  have hstable : (prefixWord ++ tailWord_3465781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465781).length < 2 ^ (prefixWord ++ tailWord_3465781).sum := by decide
  have hdescent : baseEnd_3465781 < baseStart_3465781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465782 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3465782 : Nat := 118140960795 + 3465782 * 2 ^ 59
def prefixEnd_3465782 : Nat := 4983230072969 + 3 ^ 40 * 3465782 * 2
def baseEnd_3465782 : Nat := 593204003233621448562055

theorem tailTrace_3465782 : CollatzResearch.WordTrace tailWord_3465782 prefixEnd_3465782 593204003233621448562055 := by
  unfold tailWord_3465782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7900465895629449830404475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84271636220047464857647733 7900465895629449830404475)
  ·
    refine ⟨11850698843444174745606713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7900465895629449830404475 11850698843444174745606713)
    ·
      refine ⟨8888024132583131059205035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11850698843444174745606713 8888024132583131059205035)
      ·
        refine ⟨13332036198874696588807553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8888024132583131059205035 13332036198874696588807553)
        ·
          refine ⟨9999027149156022441605665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13332036198874696588807553 9999027149156022441605665)
          ·
            refine ⟨7499270361867016831204249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9999027149156022441605665 7499270361867016831204249)
            ·
              refine ⟨5624452771400262623403187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7499270361867016831204249 5624452771400262623403187)
              ·
                refine ⟨8436679157100393935104781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5624452771400262623403187 8436679157100393935104781)
                ·
                  refine ⟨3163754683912647725664293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8436679157100393935104781 3163754683912647725664293)
                  ·
                    refine ⟨593204003233621448562055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3163754683912647725664293 593204003233621448562055)
                    ·
                      rfl

theorem cell23_3465782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3465782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465782 prefixEnd_3465782 := by exact prefixLift 3465782
  have htrace : WordTrace (prefixWord ++ tailWord_3465782) baseStart_3465782 baseEnd_3465782 := by
    simpa [prefixWord, tailWord_3465782, baseEnd_3465782] using wordTrace_append hprefix tailTrace_3465782
  have hstable : (prefixWord ++ tailWord_3465782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465782).length < 2 ^ (prefixWord ++ tailWord_3465782).sum := by decide
  have hdescent : baseEnd_3465782 < baseStart_3465782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465815 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 2, 3, 2]
def baseStart_3465815 : Nat := 118140960795 + 3465815 * 2 ^ 59
def prefixEnd_3465815 : Nat := 4983230072969 + 3 ^ 40 * 3465815 * 2
def baseEnd_3465815 : Nat := 1779628954562462716573513

theorem tailTrace_3465815 : CollatzResearch.WordTrace tailWord_3465815 prefixEnd_3465815 1779628954562462716573513 := by
  unfold tailWord_3465815
  simp only [CollatzResearch.WordTrace]
  refine ⟨126408657938951643922422899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84272438625967762614948599 126408657938951643922422899)
  ·
    refine ⟨189612986908427465883634349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126408657938951643922422899 189612986908427465883634349)
    ·
      refine ⟨71104870090660299706362881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189612986908427465883634349 71104870090660299706362881)
      ·
        refine ⟨53328652567995224779772161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71104870090660299706362881 53328652567995224779772161)
        ·
          refine ⟨39996489425996418584829121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53328652567995224779772161 39996489425996418584829121)
          ·
            refine ⟨29997367069497313938621841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39996489425996418584829121 29997367069497313938621841)
            ·
              refine ⟨22498025302122985453966381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29997367069497313938621841 22498025302122985453966381)
              ·
                refine ⟨8436759488296119545237393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22498025302122985453966381 8436759488296119545237393)
                ·
                  refine ⟨6327569616222089658928045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8436759488296119545237393 6327569616222089658928045)
                  ·
                    refine ⟨2372838606083283622098017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6327569616222089658928045 2372838606083283622098017)
                    ·
                      refine ⟨1779628954562462716573513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372838606083283622098017 1779628954562462716573513)
                      ·
                        rfl

theorem cell23_3465815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_3465815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465815 prefixEnd_3465815 := by exact prefixLift 3465815
  have htrace : WordTrace (prefixWord ++ tailWord_3465815) baseStart_3465815 baseEnd_3465815 := by
    simpa [prefixWord, tailWord_3465815, baseEnd_3465815] using wordTrace_append hprefix tailTrace_3465815
  have hstable : (prefixWord ++ tailWord_3465815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465815).length < 2 ^ (prefixWord ++ tailWord_3465815).sum := by decide
  have hdescent : baseEnd_3465815 < baseStart_3465815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465848 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_3465848 : Nat := 118140960795 + 3465848 * 2 ^ 59
def prefixEnd_3465848 : Nat := 4983230072969 + 3 ^ 40 * 3465848 * 2
def baseEnd_3465848 : Nat := 1779645899424061087460861

theorem tailTrace_3465848 : CollatzResearch.WordTrace tailWord_3465848 prefixEnd_3465848 1779645899424061087460861 := by
  unfold tailWord_3465848
  simp only [CollatzResearch.WordTrace]
  refine ⟨63204930773916045279187099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84273241031888060372249465 63204930773916045279187099)
  ·
    refine ⟨94807396160874067918780649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63204930773916045279187099 94807396160874067918780649)
    ·
      refine ⟨71105547120655550939085487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94807396160874067918780649 71105547120655550939085487)
      ·
        refine ⟨106658320680983326408628231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71105547120655550939085487 106658320680983326408628231)
        ·
          refine ⟨159987481021474989612942347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106658320680983326408628231 159987481021474989612942347)
          ·
            refine ⟨239981221532212484419413521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159987481021474989612942347 239981221532212484419413521)
            ·
              refine ⟨179985916149159363314560141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239981221532212484419413521 179985916149159363314560141)
              ·
                refine ⟨67494718555934761242960053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179985916149159363314560141 67494718555934761242960053)
                ·
                  refine ⟨6327629864618883866527505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67494718555934761242960053 6327629864618883866527505)
                  ·
                    refine ⟨4745722398464162899895629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6327629864618883866527505 4745722398464162899895629)
                    ·
                      refine ⟨1779645899424061087460861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4745722398464162899895629 1779645899424061087460861)
                      ·
                        rfl

theorem cell23_3465848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_3465848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465848 prefixEnd_3465848 := by exact prefixLift 3465848
  have htrace : WordTrace (prefixWord ++ tailWord_3465848) baseStart_3465848 baseEnd_3465848 := by
    simpa [prefixWord, tailWord_3465848, baseEnd_3465848] using wordTrace_append hprefix tailTrace_3465848
  have hstable : (prefixWord ++ tailWord_3465848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465848).length < 2 ^ (prefixWord ++ tailWord_3465848).sum := by decide
  have hdescent : baseEnd_3465848 < baseStart_3465848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465871 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_3465871 : Nat := 118140960795 + 3465871 * 2 ^ 59
def prefixEnd_3465871 : Nat := 4983230072969 + 3 ^ 40 * 3465871 * 2
def baseEnd_3465871 : Nat := 1779657709479114497473255

theorem tailTrace_3465871 : CollatzResearch.WordTrace tailWord_3465871 prefixEnd_3465871 1779657709479114497473255 := by
  unfold tailWord_3465871
  simp only [CollatzResearch.WordTrace]
  refine ⟨126410700426748765486461467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84273800284499176990974311 126410700426748765486461467)
  ·
    refine ⟨189616050640123148229692201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126410700426748765486461467 189616050640123148229692201)
    ·
      refine ⟨142212037980092361172269151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189616050640123148229692201 142212037980092361172269151)
      ·
        refine ⟨213318056970138541758403727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142212037980092361172269151 213318056970138541758403727)
        ·
          refine ⟨319977085455207812637605591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213318056970138541758403727 319977085455207812637605591)
          ·
            refine ⟨479965628182811718956408387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319977085455207812637605591 479965628182811718956408387)
            ·
              refine ⟨719948442274217578434612581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479965628182811718956408387 719948442274217578434612581)
              ·
                refine ⟨134990332926415795956489859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719948442274217578434612581 134990332926415795956489859)
                ·
                  refine ⟨202485499389623693934734789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134990332926415795956489859 202485499389623693934734789)
                  ·
                    refine ⟨37966031135554442612762773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202485499389623693934734789 37966031135554442612762773)
                    ·
                      refine ⟨1779657709479114497473255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37966031135554442612762773 1779657709479114497473255)
                      ·
                        rfl

theorem cell23_3465871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_3465871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465871 prefixEnd_3465871 := by exact prefixLift 3465871
  have htrace : WordTrace (prefixWord ++ tailWord_3465871) baseStart_3465871 baseEnd_3465871 := by
    simpa [prefixWord, tailWord_3465871, baseEnd_3465871] using wordTrace_append hprefix tailTrace_3465871
  have hstable : (prefixWord ++ tailWord_3465871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465871).length < 2 ^ (prefixWord ++ tailWord_3465871).sum := by decide
  have hdescent : baseEnd_3465871 < baseStart_3465871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465879 : List Nat := [1, 1, 3, 3, 2, 1, 2, 5, 1, 2, 2]
def baseStart_3465879 : Nat := 118140960795 + 3465879 * 2 ^ 59
def prefixEnd_3465879 : Nat := 4983230072969 + 3 ^ 40 * 3465879 * 2
def baseEnd_3465879 : Nat := 1779661817324350466173219

theorem tailTrace_3465879 : CollatzResearch.WordTrace tailWord_3465879 prefixEnd_3465879 1779661817324350466173219 := by
  unfold tailWord_3465879
  simp only [CollatzResearch.WordTrace]
  refine ⟨126410992210719782852752691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84273994807146521901835127 126410992210719782852752691)
  ·
    refine ⟨189616488316079674279129037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126410992210719782852752691 189616488316079674279129037)
    ·
      refine ⟨71106183118529877854673389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189616488316079674279129037 71106183118529877854673389)
      ·
        refine ⟨26664818669448704195502521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71106183118529877854673389 26664818669448704195502521)
        ·
          refine ⟨19998614002086528146626891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26664818669448704195502521 19998614002086528146626891)
          ·
            refine ⟨29997921003129792219940337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19998614002086528146626891 29997921003129792219940337)
            ·
              refine ⟨22498440752347344164955253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29997921003129792219940337 22498440752347344164955253)
              ·
                refine ⟨2109228820532563515464555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22498440752347344164955253 2109228820532563515464555)
                ·
                  refine ⟨3163843230798845273196833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109228820532563515464555 3163843230798845273196833)
                  ·
                    refine ⟨2372882423099133954897625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3163843230798845273196833 2372882423099133954897625)
                    ·
                      refine ⟨1779661817324350466173219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372882423099133954897625 1779661817324350466173219)
                      ·
                        rfl

theorem cell23_3465879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_3465879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465879 prefixEnd_3465879 := by exact prefixLift 3465879
  have htrace : WordTrace (prefixWord ++ tailWord_3465879) baseStart_3465879 baseEnd_3465879 := by
    simpa [prefixWord, tailWord_3465879, baseEnd_3465879] using wordTrace_append hprefix tailTrace_3465879
  have hstable : (prefixWord ++ tailWord_3465879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465879).length < 2 ^ (prefixWord ++ tailWord_3465879).sum := by decide
  have hdescent : baseEnd_3465879 < baseStart_3465879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465902 : List Nat := [4, 1, 4, 1, 1, 3, 1, 8]
def baseStart_3465902 : Nat := 118140960795 + 3465902 * 2 ^ 59
def prefixEnd_3465902 : Nat := 4983230072969 + 3 ^ 40 * 3465902 * 2
def baseEnd_3465902 : Nat := 65913838051089032451319

theorem tailTrace_3465902 : CollatzResearch.WordTrace tailWord_3465902 prefixEnd_3465902 65913838051089032451319 := by
  unfold tailWord_3465902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15801478886204557222604995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84274554059757638520559973 15801478886204557222604995)
  ·
    refine ⟨23702218329306835833907493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15801478886204557222604995 23702218329306835833907493)
    ·
      refine ⟨4444165936745031718857655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23702218329306835833907493 4444165936745031718857655)
      ·
        refine ⟨6666248905117547578286483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444165936745031718857655 6666248905117547578286483)
        ·
          refine ⟨9999373357676321367429725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6666248905117547578286483 9999373357676321367429725)
          ·
            refine ⟨3749765009128620512786147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9999373357676321367429725 3749765009128620512786147)
            ·
              refine ⟨5624647513692930769179221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3749765009128620512786147 5624647513692930769179221)
              ·
                refine ⟨65913838051089032451319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5624647513692930769179221 65913838051089032451319)
                ·
                  rfl

theorem cell23_3465902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_3465902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465902 prefixEnd_3465902 := by exact prefixLift 3465902
  have htrace : WordTrace (prefixWord ++ tailWord_3465902) baseStart_3465902 baseEnd_3465902 := by
    simpa [prefixWord, tailWord_3465902, baseEnd_3465902] using wordTrace_append hprefix tailTrace_3465902
  have hstable : (prefixWord ++ tailWord_3465902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465902).length < 2 ^ (prefixWord ++ tailWord_3465902).sum := by decide
  have hdescent : baseEnd_3465902 < baseStart_3465902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465933 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_3465933 : Nat := 118140960795 + 3465933 * 2 ^ 59
def prefixEnd_3465933 : Nat := 4983230072969 + 3 ^ 40 * 3465933 * 2
def baseEnd_3465933 : Nat := 1779689545279693254897971

theorem tailTrace_3465933 : CollatzResearch.WordTrace tailWord_3465933 prefixEnd_3465933 1779689545279693254897971 := by
  unfold tailWord_3465933
  simp only [CollatzResearch.WordTrace]
  refine ⟨126412961752524150075218453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84275307835016100050145635 126412961752524150075218453)
  ·
    refine ⟨5925607582149569534775865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126412961752524150075218453 5925607582149569534775865)
    ·
      refine ⟨4444205686612177151081899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5925607582149569534775865 4444205686612177151081899)
      ·
        refine ⟨6666308529918265726622849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444205686612177151081899 6666308529918265726622849)
        ·
          refine ⟨4999731397438699294967137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6666308529918265726622849 4999731397438699294967137)
          ·
            refine ⟨3749798548079024471225353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4999731397438699294967137 3749798548079024471225353)
            ·
              refine ⟨2812348911059268353419015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749798548079024471225353 2812348911059268353419015)
              ·
                refine ⟨4218523366588902530128523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812348911059268353419015 4218523366588902530128523)
                ·
                  refine ⟨6327785049883353795192785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218523366588902530128523 6327785049883353795192785)
                  ·
                    refine ⟨4745838787412515346394589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6327785049883353795192785 4745838787412515346394589)
                    ·
                      refine ⟨1779689545279693254897971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4745838787412515346394589 1779689545279693254897971)
                      ·
                        rfl

theorem cell23_3465933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_3465933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465933 prefixEnd_3465933 := by exact prefixLift 3465933
  have htrace : WordTrace (prefixWord ++ tailWord_3465933) baseStart_3465933 baseEnd_3465933 := by
    simpa [prefixWord, tailWord_3465933, baseEnd_3465933] using wordTrace_append hprefix tailTrace_3465933
  have hstable : (prefixWord ++ tailWord_3465933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465933).length < 2 ^ (prefixWord ++ tailWord_3465933).sum := by decide
  have hdescent : baseEnd_3465933 < baseStart_3465933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465965 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3465965 : Nat := 118140960795 + 3465965 * 2 ^ 59
def prefixEnd_3465965 : Nat := 4983230072969 + 3 ^ 40 * 3465965 * 2
def baseEnd_3465965 : Nat := 1779705976660637129697823

theorem tailTrace_3465965 : CollatzResearch.WordTrace tailWord_3465965 prefixEnd_3465965 1779705976660637129697823 := by
  unfold tailWord_3465965
  simp only [CollatzResearch.WordTrace]
  refine ⟨126414128888408219540383349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84276085925605479693588899 126414128888408219540383349)
  ·
    refine ⟨11851324583288270581910939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126414128888408219540383349 11851324583288270581910939)
    ·
      refine ⟨17776986874932405872866409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11851324583288270581910939 17776986874932405872866409)
      ·
        refine ⟨13332740156199304404649807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17776986874932405872866409 13332740156199304404649807)
        ·
          refine ⟨19999110234298956606974711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13332740156199304404649807 19999110234298956606974711)
          ·
            refine ⟨29998665351448434910462067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19999110234298956606974711 29998665351448434910462067)
            ·
              refine ⟨44997998027172652365693101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29998665351448434910462067 44997998027172652365693101)
              ·
                refine ⟨16874249260189744637134913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44997998027172652365693101 16874249260189744637134913)
                ·
                  refine ⟨12655686945142308477851185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16874249260189744637134913 12655686945142308477851185)
                  ·
                    refine ⟨9491765208856731358388389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12655686945142308477851185 9491765208856731358388389)
                    ·
                      refine ⟨1779705976660637129697823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9491765208856731358388389 1779705976660637129697823)
                      ·
                        rfl

theorem cell23_3465965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3465965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465965 prefixEnd_3465965 := by exact prefixLift 3465965
  have htrace : WordTrace (prefixWord ++ tailWord_3465965) baseStart_3465965 baseEnd_3465965 := by
    simpa [prefixWord, tailWord_3465965, baseEnd_3465965] using wordTrace_append hprefix tailTrace_3465965
  have hstable : (prefixWord ++ tailWord_3465965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465965).length < 2 ^ (prefixWord ++ tailWord_3465965).sum := by decide
  have hdescent : baseEnd_3465965 < baseStart_3465965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465992 : List Nat := [2, 1, 3, 2, 2, 2, 3, 3, 5]
def baseStart_3465992 : Nat := 118140960795 + 3465992 * 2 ^ 59
def prefixEnd_3465992 : Nat := 4983230072969 + 3 ^ 40 * 3465992 * 2
def baseEnd_3465992 : Nat := 197746648959812058228911

theorem tailTrace_3465992 : CollatzResearch.WordTrace tailWord_3465992 prefixEnd_3465992 197746648959812058228911 := by
  unfold tailWord_3465992
  simp only [CollatzResearch.WordTrace]
  refine ⟨63207556829655201575808115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84276742439540268767744153 63207556829655201575808115)
  ·
    refine ⟨94811335244482802363712173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63207556829655201575808115 94811335244482802363712173)
    ·
      refine ⟨35554250716681050886392065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94811335244482802363712173 35554250716681050886392065)
      ·
        refine ⟨26665688037510788164794049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35554250716681050886392065 26665688037510788164794049)
        ·
          refine ⟨19999266028133091123595537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26665688037510788164794049 19999266028133091123595537)
          ·
            refine ⟨14999449521099818342696653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19999266028133091123595537 14999449521099818342696653)
            ·
              refine ⟨5624793570412431878511245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14999449521099818342696653 5624793570412431878511245)
              ·
                refine ⟨2109297588904661954441717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5624793570412431878511245 2109297588904661954441717)
                ·
                  refine ⟨197746648959812058228911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2109297588904661954441717 197746648959812058228911)
                  ·
                    rfl

theorem cell23_3465992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 5].length) (baseStart_3465992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465992 prefixEnd_3465992 := by exact prefixLift 3465992
  have htrace : WordTrace (prefixWord ++ tailWord_3465992) baseStart_3465992 baseEnd_3465992 := by
    simpa [prefixWord, tailWord_3465992, baseEnd_3465992] using wordTrace_append hprefix tailTrace_3465992
  have hstable : (prefixWord ++ tailWord_3465992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465992).length < 2 ^ (prefixWord ++ tailWord_3465992).sum := by decide
  have hdescent : baseEnd_3465992 < baseStart_3465992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3465995 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 1, 7, 2]
def baseStart_3465995 : Nat := 118140960795 + 3465995 * 2 ^ 59
def prefixEnd_3465995 : Nat := 4983230072969 + 3 ^ 40 * 3465995 * 2
def baseEnd_3465995 : Nat := 1779721381080272012322685

theorem tailTrace_3465995 : CollatzResearch.WordTrace tailWord_3465995 prefixEnd_3465995 1779721381080272012322685 := by
  unfold tailWord_3465995
  simp only [CollatzResearch.WordTrace]
  refine ⟨126415223078299534663975439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84276815385533023109316959 126415223078299534663975439)
  ·
    refine ⟨189622834617449301995963159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126415223078299534663975439 189622834617449301995963159)
    ·
      refine ⟨284434251926173952993944739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189622834617449301995963159 284434251926173952993944739)
      ·
        refine ⟨426651377889260929490917109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284434251926173952993944739 426651377889260929490917109)
        ·
          refine ⟨39998566677118212139773479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426651377889260929490917109 39998566677118212139773479)
          ·
            refine ⟨59997850015677318209660219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39998566677118212139773479 59997850015677318209660219)
            ·
              refine ⟨89996775023515977314490329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59997850015677318209660219 89996775023515977314490329)
              ·
                refine ⟨67497581267636982985867747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89996775023515977314490329 67497581267636982985867747)
                ·
                  refine ⟨101246371901455474478801621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67497581267636982985867747 101246371901455474478801621)
                  ·
                    refine ⟨2372961841440362683096913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 101246371901455474478801621 2372961841440362683096913)
                    ·
                      refine ⟨1779721381080272012322685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372961841440362683096913 1779721381080272012322685)
                      ·
                        rfl

theorem cell23_3465995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 7, 2].length) (baseStart_3465995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3465995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3465995 prefixEnd_3465995 := by exact prefixLift 3465995
  have htrace : WordTrace (prefixWord ++ tailWord_3465995) baseStart_3465995 baseEnd_3465995 := by
    simpa [prefixWord, tailWord_3465995, baseEnd_3465995] using wordTrace_append hprefix tailTrace_3465995
  have hstable : (prefixWord ++ tailWord_3465995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3465995).length < 2 ^ (prefixWord ++ tailWord_3465995).sum := by decide
  have hdescent : baseEnd_3465995 < baseStart_3465995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3465995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466005 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_3466005 : Nat := 118140960795 + 3466005 * 2 ^ 59
def prefixEnd_3466005 : Nat := 4983230072969 + 3 ^ 40 * 3466005 * 2
def baseEnd_3466005 : Nat := 593242171962272324399213

theorem tailTrace_3466005 : CollatzResearch.WordTrace tailWord_3466005 prefixEnd_3466005 593242171962272324399213 := by
  unfold tailWord_3466005
  simp only [CollatzResearch.WordTrace]
  refine ⟨126415587808263306371839469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84277058538842204247892979 126415587808263306371839469)
  ·
    refine ⟨47405845428098739889439801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126415587808263306371839469 47405845428098739889439801)
    ·
      refine ⟨35554384071074054917079851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47405845428098739889439801 35554384071074054917079851)
      ·
        refine ⟨53331576106611082375619777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35554384071074054917079851 53331576106611082375619777)
        ·
          refine ⟨39998682079958311781714833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53331576106611082375619777 39998682079958311781714833)
          ·
            refine ⟨29999011559968733836286125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39998682079958311781714833 29999011559968733836286125)
            ·
              refine ⟨11249629334988275188607297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29999011559968733836286125 11249629334988275188607297)
              ·
                refine ⟨8437222001241206391455473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11249629334988275188607297 8437222001241206391455473)
                ·
                  refine ⟨6327916500930904793591605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8437222001241206391455473 6327916500930904793591605)
                  ·
                    refine ⟨593242171962272324399213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6327916500930904793591605 593242171962272324399213)
                    ·
                      rfl

theorem cell23_3466005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_3466005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466005 prefixEnd_3466005 := by exact prefixLift 3466005
  have htrace : WordTrace (prefixWord ++ tailWord_3466005) baseStart_3466005 baseEnd_3466005 := by
    simpa [prefixWord, tailWord_3466005, baseEnd_3466005] using wordTrace_append hprefix tailTrace_3466005
  have hstable : (prefixWord ++ tailWord_3466005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466005).length < 2 ^ (prefixWord ++ tailWord_3466005).sum := by decide
  have hdescent : baseEnd_3466005 < baseStart_3466005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466015 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_3466015 : Nat := 118140960795 + 3466015 * 2 ^ 59
def prefixEnd_3466015 : Nat := 4983230072969 + 3 ^ 40 * 3466015 * 2
def baseEnd_3466015 : Nat := 1779731650693361934072593

theorem tailTrace_3466015 : CollatzResearch.WordTrace tailWord_3466015 prefixEnd_3466015 1779731650693361934072593 := by
  unfold tailWord_3466015
  simp only [CollatzResearch.WordTrace]
  refine ⟨126415952538227078079703499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84277301692151385386468999 126415952538227078079703499)
  ·
    refine ⟨189623928807340617119555249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126415952538227078079703499 189623928807340617119555249)
    ·
      refine ⟨142217946605505462839666437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189623928807340617119555249 142217946605505462839666437)
      ·
        refine ⟨26665864988532274282437457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142217946605505462839666437 26665864988532274282437457)
        ·
          refine ⟨19999398741399205711828093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26665864988532274282437457 19999398741399205711828093)
          ·
            refine ⟨7499774528024702141935535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19999398741399205711828093 7499774528024702141935535)
            ·
              refine ⟨11249661792037053212903303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7499774528024702141935535 11249661792037053212903303)
              ·
                refine ⟨16874492688055579819354955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11249661792037053212903303 16874492688055579819354955)
                ·
                  refine ⟨25311739032083369729032433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16874492688055579819354955 25311739032083369729032433)
                  ·
                    refine ⟨18983804274062527296774325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25311739032083369729032433 18983804274062527296774325)
                    ·
                      refine ⟨1779731650693361934072593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18983804274062527296774325 1779731650693361934072593)
                      ·
                        rfl

theorem cell23_3466015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_3466015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466015 prefixEnd_3466015 := by exact prefixLift 3466015
  have htrace : WordTrace (prefixWord ++ tailWord_3466015) baseStart_3466015 baseEnd_3466015 := by
    simpa [prefixWord, tailWord_3466015, baseEnd_3466015] using wordTrace_append hprefix tailTrace_3466015
  have hstable : (prefixWord ++ tailWord_3466015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466015).length < 2 ^ (prefixWord ++ tailWord_3466015).sum := by decide
  have hdescent : baseEnd_3466015 < baseStart_3466015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466020 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_3466020 : Nat := 118140960795 + 3466020 * 2 ^ 59
def prefixEnd_3466020 : Nat := 4983230072969 + 3 ^ 40 * 3466020 * 2
def baseEnd_3466020 : Nat := 1779734218096634414510071

theorem tailTrace_3466020 : CollatzResearch.WordTrace tailWord_3466020 prefixEnd_3466020 1779734218096634414510071 := by
  unfold tailWord_3466020
  simp only [CollatzResearch.WordTrace]
  refine ⟨63208067451604481966817757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84277423268805975955757009 63208067451604481966817757)
  ·
    refine ⟨23703025294351680737556659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63208067451604481966817757 23703025294351680737556659)
    ·
      refine ⟨35554537941527521106334989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23703025294351680737556659 35554537941527521106334989)
      ·
        refine ⟨13332951728072820414875621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35554537941527521106334989 13332951728072820414875621)
        ·
          refine ⟨2499928449013653827789179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13332951728072820414875621 2499928449013653827789179)
          ·
            refine ⟨3749892673520480741683769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499928449013653827789179 3749892673520480741683769)
            ·
              refine ⟨2812419505140360556262827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749892673520480741683769 2812419505140360556262827)
              ·
                refine ⟨4218629257710540834394241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812419505140360556262827 4218629257710540834394241)
                ·
                  refine ⟨3163971943282905625795681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4218629257710540834394241 3163971943282905625795681)
                  ·
                    refine ⟨2372978957462179219346761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3163971943282905625795681 2372978957462179219346761)
                    ·
                      refine ⟨1779734218096634414510071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2372978957462179219346761 1779734218096634414510071)
                      ·
                        rfl

theorem cell23_3466020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_3466020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466020 prefixEnd_3466020 := by exact prefixLift 3466020
  have htrace : WordTrace (prefixWord ++ tailWord_3466020) baseStart_3466020 baseEnd_3466020 := by
    simpa [prefixWord, tailWord_3466020, baseEnd_3466020] using wordTrace_append hprefix tailTrace_3466020
  have hstable : (prefixWord ++ tailWord_3466020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466020).length < 2 ^ (prefixWord ++ tailWord_3466020).sum := by decide
  have hdescent : baseEnd_3466020 < baseStart_3466020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466048 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 10]
def baseStart_3466048 : Nat := 118140960795 + 3466048 * 2 ^ 59
def prefixEnd_3466048 : Nat := 4983230072969 + 3 ^ 40 * 3466048 * 2
def baseEnd_3466048 : Nat := 197749843950551144995549

theorem tailTrace_3466048 : CollatzResearch.WordTrace tailWord_3466048 prefixEnd_3466048 197749843950551144995549 := by
  unfold tailWord_3466048
  simp only [CollatzResearch.WordTrace]
  refine ⟨63208578073553762357827399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84278104098071683143769865 63208578073553762357827399)
  ·
    refine ⟨94812867110330643536741099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63208578073553762357827399 94812867110330643536741099)
    ·
      refine ⟨142219300665495965305111649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94812867110330643536741099 142219300665495965305111649)
      ·
        refine ⟨106664475499121973978833737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142219300665495965305111649 106664475499121973978833737)
        ·
          refine ⟨79998356624341480484125303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106664475499121973978833737 79998356624341480484125303)
          ·
            refine ⟨119997534936512220726187955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79998356624341480484125303 119997534936512220726187955)
            ·
              refine ⟨179996302404768331089281933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119997534936512220726187955 179996302404768331089281933)
              ·
                refine ⟨67498613401788124158480725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179996302404768331089281933 67498613401788124158480725)
                ·
                  refine ⟨197749843950551144995549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67498613401788124158480725 197749843950551144995549)
                  ·
                    rfl

theorem cell23_3466048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 10].length) (baseStart_3466048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466048 prefixEnd_3466048 := by exact prefixLift 3466048
  have htrace : WordTrace (prefixWord ++ tailWord_3466048) baseStart_3466048 baseEnd_3466048 := by
    simpa [prefixWord, tailWord_3466048, baseEnd_3466048] using wordTrace_append hprefix tailTrace_3466048
  have hstable : (prefixWord ++ tailWord_3466048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466048).length < 2 ^ (prefixWord ++ tailWord_3466048).sum := by decide
  have hdescent : baseEnd_3466048 < baseStart_3466048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466069 : List Nat := [1, 3, 2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_3466069 : Nat := 118140960795 + 3466069 * 2 ^ 59
def prefixEnd_3466069 : Nat := 4983230072969 + 3 ^ 40 * 3466069 * 2
def baseEnd_3466069 : Nat := 593253126216234907599115

theorem tailTrace_3466069 : CollatzResearch.WordTrace tailWord_3466069 prefixEnd_3466069 593253126216234907599115 := by
  unfold tailWord_3466069
  simp only [CollatzResearch.WordTrace]
  refine ⟨126417922080031445302169261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84278614720020963534779507 126417922080031445302169261)
  ·
    refine ⟨47406720780011791988313473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126417922080031445302169261 47406720780011791988313473)
    ·
      refine ⟨35555040585008843991235105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47406720780011791988313473 35555040585008843991235105)
      ·
        refine ⟨26666280438756632993426329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35555040585008843991235105 26666280438756632993426329)
        ·
          refine ⟨19999710329067474745069747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26666280438756632993426329 19999710329067474745069747)
          ·
            refine ⟨29999565493601212117604621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19999710329067474745069747 29999565493601212117604621)
            ·
              refine ⟨11249837060100454544101733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29999565493601212117604621 11249837060100454544101733)
              ·
                refine ⟨2109344448768835227019075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11249837060100454544101733 2109344448768835227019075)
                ·
                  refine ⟨3164016673153252840528613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109344448768835227019075 3164016673153252840528613)
                  ·
                    refine ⟨593253126216234907599115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3164016673153252840528613 593253126216234907599115)
                    ·
                      rfl

theorem cell23_3466069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_3466069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466069 prefixEnd_3466069 := by exact prefixLift 3466069
  have htrace : WordTrace (prefixWord ++ tailWord_3466069) baseStart_3466069 baseEnd_3466069 := by
    simpa [prefixWord, tailWord_3466069, baseEnd_3466069] using wordTrace_append hprefix tailTrace_3466069
  have hstable : (prefixWord ++ tailWord_3466069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466069).length < 2 ^ (prefixWord ++ tailWord_3466069).sum := by decide
  have hdescent : baseEnd_3466069 < baseStart_3466069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466169 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3466169 : Nat := 118140960795 + 3466169 * 2 ^ 59
def prefixEnd_3466169 : Nat := 4983230072969 + 3 ^ 40 * 3466169 * 2
def baseEnd_3466169 : Nat := 1779810726714154331546885

theorem tailTrace_3466169 : CollatzResearch.WordTrace tailWord_3466169 prefixEnd_3466169 1779810726714154331546885 := by
  unfold tailWord_3466169
  simp only [CollatzResearch.WordTrace]
  refine ⟨126421569379669162380809561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84281046253112774920539707 126421569379669162380809561)
  ·
    refine ⟨94816177034751871785607171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126421569379669162380809561 94816177034751871785607171)
    ·
      refine ⟨142224265552127807678410757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94816177034751871785607171 142224265552127807678410757)
      ·
        refine ⟨26667049791023963939702017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142224265552127807678410757 26667049791023963939702017)
        ·
          refine ⟨20000287343267972954776513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26667049791023963939702017 20000287343267972954776513)
          ·
            refine ⟨15000215507450979716082385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20000287343267972954776513 15000215507450979716082385)
            ·
              refine ⟨11250161630588234787061789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15000215507450979716082385 11250161630588234787061789)
              ·
                refine ⟨4218810611470588045148171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11250161630588234787061789 4218810611470588045148171)
                ·
                  refine ⟨6328215917205882067722257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4218810611470588045148171 6328215917205882067722257)
                  ·
                    refine ⟨4746161937904411550791693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6328215917205882067722257 4746161937904411550791693)
                    ·
                      refine ⟨1779810726714154331546885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4746161937904411550791693 1779810726714154331546885)
                      ·
                        rfl

theorem cell23_3466169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3466169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466169 prefixEnd_3466169 := by exact prefixLift 3466169
  have htrace : WordTrace (prefixWord ++ tailWord_3466169) baseStart_3466169 baseEnd_3466169 := by
    simpa [prefixWord, tailWord_3466169, baseEnd_3466169] using wordTrace_append hprefix tailTrace_3466169
  have hstable : (prefixWord ++ tailWord_3466169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466169).length < 2 ^ (prefixWord ++ tailWord_3466169).sum := by decide
  have hdescent : baseEnd_3466169 < baseStart_3466169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466192 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 2, 7, 2]
def baseStart_3466192 : Nat := 118140960795 + 3466192 * 2 ^ 59
def prefixEnd_3466192 : Nat := 4983230072969 + 3 ^ 40 * 3466192 * 2
def baseEnd_3466192 : Nat := 1779822536769207741559279

theorem tailTrace_3466192 : CollatzResearch.WordTrace tailWord_3466192 prefixEnd_3466192 1779822536769207741559279 := by
  unfold tailWord_3466192
  simp only [CollatzResearch.WordTrace]
  refine ⟨63211204129292918654448415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84281605505723891539264553 63211204129292918654448415)
  ·
    refine ⟨94816806193939377981672623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63211204129292918654448415 94816806193939377981672623)
    ·
      refine ⟨142225209290909066972508935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94816806193939377981672623 142225209290909066972508935)
      ·
        refine ⟨213337813936363600458763403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142225209290909066972508935 213337813936363600458763403)
        ·
          refine ⟨320006720904545400688145105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213337813936363600458763403 320006720904545400688145105)
          ·
            refine ⟨240005040678409050516108829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320006720904545400688145105 240005040678409050516108829)
            ·
              refine ⟨90001890254403393943540811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240005040678409050516108829 90001890254403393943540811)
              ·
                refine ⟨135002835381605090915311217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90001890254403393943540811 135002835381605090915311217)
                ·
                  refine ⟨101252126536203818186483413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135002835381605090915311217 101252126536203818186483413)
                  ·
                    refine ⟨2373096715692276988745705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 101252126536203818186483413 2373096715692276988745705)
                    ·
                      refine ⟨1779822536769207741559279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373096715692276988745705 1779822536769207741559279)
                      ·
                        rfl

theorem cell23_3466192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 7, 2].length) (baseStart_3466192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466192 prefixEnd_3466192 := by exact prefixLift 3466192
  have htrace : WordTrace (prefixWord ++ tailWord_3466192) baseStart_3466192 baseEnd_3466192 := by
    simpa [prefixWord, tailWord_3466192, baseEnd_3466192] using wordTrace_append hprefix tailTrace_3466192
  have hstable : (prefixWord ++ tailWord_3466192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466192).length < 2 ^ (prefixWord ++ tailWord_3466192).sum := by decide
  have hdescent : baseEnd_3466192 < baseStart_3466192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466228 : List Nat := [2, 6, 2, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3466228 : Nat := 118140960795 + 3466228 * 2 ^ 59
def prefixEnd_3466228 : Nat := 4983230072969 + 3 ^ 40 * 3466228 * 2
def baseEnd_3466228 : Nat := 1779841022072769600709115

theorem tailTrace_3466228 : CollatzResearch.WordTrace tailWord_3466228 prefixEnd_3466228 1779841022072769600709115 := by
  unfold tailWord_3466228
  simp only [CollatzResearch.WordTrace]
  refine ⟨63211860643227707728603669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84282480857636943638138225 63211860643227707728603669)
  ·
    refine ⟨2963055967651298799778297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63211860643227707728603669 2963055967651298799778297)
    ·
      refine ⟨2222291975738474099833723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2963055967651298799778297 2222291975738474099833723)
      ·
        refine ⟨3333437963607711149750585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2222291975738474099833723 3333437963607711149750585)
        ·
          refine ⟨2500078472705783362312939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3333437963607711149750585 2500078472705783362312939)
          ·
            refine ⟨3750117709058675043469409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500078472705783362312939 3750117709058675043469409)
            ·
              refine ⟨2812588281794006282602057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3750117709058675043469409 2812588281794006282602057)
              ·
                refine ⟨2109441211345504711951543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812588281794006282602057 2109441211345504711951543)
                ·
                  refine ⟨3164161817018257067927315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109441211345504711951543 3164161817018257067927315)
                  ·
                    refine ⟨4746242725527385601890973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3164161817018257067927315 4746242725527385601890973)
                    ·
                      refine ⟨1779841022072769600709115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4746242725527385601890973 1779841022072769600709115)
                      ·
                        rfl

theorem cell23_3466228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3466228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466228 prefixEnd_3466228 := by exact prefixLift 3466228
  have htrace : WordTrace (prefixWord ++ tailWord_3466228) baseStart_3466228 baseEnd_3466228 := by
    simpa [prefixWord, tailWord_3466228, baseEnd_3466228] using wordTrace_append hprefix tailTrace_3466228
  have hstable : (prefixWord ++ tailWord_3466228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466228).length < 2 ^ (prefixWord ++ tailWord_3466228).sum := by decide
  have hdescent : baseEnd_3466228 < baseStart_3466228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466235 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 6]
def baseStart_3466235 : Nat := 118140960795 + 3466235 * 2 ^ 59
def prefixEnd_3466235 : Nat := 4983230072969 + 3 ^ 40 * 3466235 * 2
def baseEnd_3466235 : Nat := 1779844616437351073321581

theorem tailTrace_3466235 : CollatzResearch.WordTrace tailWord_3466235 prefixEnd_3466235 1779844616437351073321581 := by
  unfold tailWord_3466235
  simp only [CollatzResearch.WordTrace]
  refine ⟨126423976597430055652712159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84282651064953370435141439 126423976597430055652712159)
  ·
    refine ⟨189635964896145083479068239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126423976597430055652712159 189635964896145083479068239)
    ·
      refine ⟨284453947344217625218602359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189635964896145083479068239 284453947344217625218602359)
      ·
        refine ⟨426680921016326437827903539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284453947344217625218602359 426680921016326437827903539)
        ·
          refine ⟨640021381524489656741855309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426680921016326437827903539 640021381524489656741855309)
          ·
            refine ⟨240008018071683621278195741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 640021381524489656741855309 240008018071683621278195741)
            ·
              refine ⟨90003006776881357979323403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240008018071683621278195741 90003006776881357979323403)
              ·
                refine ⟨135004510165322036968985105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90003006776881357979323403 135004510165322036968985105)
                ·
                  refine ⟨101253382623991527726738829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135004510165322036968985105 101253382623991527726738829)
                  ·
                    refine ⟨37970018483996822897527061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101253382623991527726738829 37970018483996822897527061)
                    ·
                      refine ⟨1779844616437351073321581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37970018483996822897527061 1779844616437351073321581)
                      ·
                        rfl

theorem cell23_3466235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_3466235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466235 prefixEnd_3466235 := by exact prefixLift 3466235
  have htrace : WordTrace (prefixWord ++ tailWord_3466235) baseStart_3466235 baseEnd_3466235 := by
    simpa [prefixWord, tailWord_3466235, baseEnd_3466235] using wordTrace_append hprefix tailTrace_3466235
  have hstable : (prefixWord ++ tailWord_3466235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466235).length < 2 ^ (prefixWord ++ tailWord_3466235).sum := by decide
  have hdescent : baseEnd_3466235 < baseStart_3466235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466252 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3466252 : Nat := 118140960795 + 3466252 * 2 ^ 59
def prefixEnd_3466252 : Nat := 4983230072969 + 3 ^ 40 * 3466252 * 2
def baseEnd_3466252 : Nat := 1779853345608477506809003

theorem tailTrace_3466252 : CollatzResearch.WordTrace tailWord_3466252 prefixEnd_3466252 1779853345608477506809003 := by
  unfold tailWord_3466252
  simp only [CollatzResearch.WordTrace]
  refine ⟨63212298319184233778040505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84283064425578978370720673 63212298319184233778040505)
  ·
    refine ⟨47409223739388175333530379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63212298319184233778040505 47409223739388175333530379)
    ·
      refine ⟨71113835609082263000295569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47409223739388175333530379 71113835609082263000295569)
      ·
        refine ⟨53335376706811697250221677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71113835609082263000295569 53335376706811697250221677)
        ·
          refine ⟨20000766265054386468833129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53335376706811697250221677 20000766265054386468833129)
          ·
            refine ⟨15000574698790789851624847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20000766265054386468833129 15000574698790789851624847)
            ·
              refine ⟨22500862048186184777437271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15000574698790789851624847 22500862048186184777437271)
              ·
                refine ⟨33751293072279277166155907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22500862048186184777437271 33751293072279277166155907)
                ·
                  refine ⟨50626939608418915749233861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33751293072279277166155907 50626939608418915749233861)
                  ·
                    refine ⟨9492551176578546702981349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50626939608418915749233861 9492551176578546702981349)
                    ·
                      refine ⟨1779853345608477506809003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9492551176578546702981349 1779853345608477506809003)
                      ·
                        rfl

theorem cell23_3466252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3466252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466252 prefixEnd_3466252 := by exact prefixLift 3466252
  have htrace : WordTrace (prefixWord ++ tailWord_3466252) baseStart_3466252 baseEnd_3466252 := by
    simpa [prefixWord, tailWord_3466252, baseEnd_3466252] using wordTrace_append hprefix tailTrace_3466252
  have hstable : (prefixWord ++ tailWord_3466252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466252).length < 2 ^ (prefixWord ++ tailWord_3466252).sum := by decide
  have hdescent : baseEnd_3466252 < baseStart_3466252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466255 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_3466255 : Nat := 118140960795 + 3466255 * 2 ^ 59
def prefixEnd_3466255 : Nat := 4983230072969 + 3 ^ 40 * 3466255 * 2
def baseEnd_3466255 : Nat := 1779854886050440995071489

theorem tailTrace_3466255 : CollatzResearch.WordTrace tailWord_3466255 prefixEnd_3466255 1779854886050440995071489 := by
  unfold tailWord_3466255
  simp only [CollatzResearch.WordTrace]
  refine ⟨126424706057357599068440219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84283137371571732712293479 126424706057357599068440219)
  ·
    refine ⟨189637059086036398602660329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126424706057357599068440219 189637059086036398602660329)
    ·
      refine ⟨142227794314527298951995247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189637059086036398602660329 142227794314527298951995247)
      ·
        refine ⟨213341691471790948427992871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142227794314527298951995247 213341691471790948427992871)
        ·
          refine ⟨320012537207686422641989307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213341691471790948427992871 320012537207686422641989307)
          ·
            refine ⟨480018805811529633962983961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320012537207686422641989307 480018805811529633962983961)
            ·
              refine ⟨360014104358647225472237971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480018805811529633962983961 360014104358647225472237971)
              ·
                refine ⟨540021156537970838208356957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360014104358647225472237971 540021156537970838208356957)
                ·
                  refine ⟨202507933701739064328133859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540021156537970838208356957 202507933701739064328133859)
                  ·
                    refine ⟨303761900552608596492200789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202507933701739064328133859 303761900552608596492200789)
                    ·
                      refine ⟨1779854886050440995071489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 303761900552608596492200789 1779854886050440995071489)
                      ·
                        rfl

theorem cell23_3466255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_3466255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466255 prefixEnd_3466255 := by exact prefixLift 3466255
  have htrace : WordTrace (prefixWord ++ tailWord_3466255) baseStart_3466255 baseEnd_3466255 := by
    simpa [prefixWord, tailWord_3466255, baseEnd_3466255] using wordTrace_append hprefix tailTrace_3466255
  have hstable : (prefixWord ++ tailWord_3466255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466255).length < 2 ^ (prefixWord ++ tailWord_3466255).sum := by decide
  have hdescent : baseEnd_3466255 < baseStart_3466255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466312 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3466312 : Nat := 118140960795 + 3466312 * 2 ^ 59
def prefixEnd_3466312 : Nat := 4983230072969 + 3 ^ 40 * 3466312 * 2
def baseEnd_3466312 : Nat := 1779884154447747272058727

theorem tailTrace_3466312 : CollatzResearch.WordTrace tailWord_3466312 prefixEnd_3466312 1779884154447747272058727 := by
  unfold tailWord_3466312
  simp only [CollatzResearch.WordTrace]
  refine ⟨63213392509075548901632595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84284523345434065202176793 63213392509075548901632595)
  ·
    refine ⟨94820088763613323352448893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63213392509075548901632595 94820088763613323352448893)
    ·
      refine ⟨35557533286354996257168335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94820088763613323352448893 35557533286354996257168335)
      ·
        refine ⟨53336299929532494385752503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35557533286354996257168335 53336299929532494385752503)
        ·
          refine ⟨80004449894298741578628755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53336299929532494385752503 80004449894298741578628755)
          ·
            refine ⟨120006674841448112367943133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80004449894298741578628755 120006674841448112367943133)
            ·
              refine ⟨45002503065543042137978675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120006674841448112367943133 45002503065543042137978675)
              ·
                refine ⟨67503754598314563206968013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45002503065543042137978675 67503754598314563206968013)
                ·
                  refine ⟨25313907974367961202613005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67503754598314563206968013 25313907974367961202613005)
                  ·
                    refine ⟨9492715490387985450979877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25313907974367961202613005 9492715490387985450979877)
                    ·
                      refine ⟨1779884154447747272058727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9492715490387985450979877 1779884154447747272058727)
                      ·
                        rfl

theorem cell23_3466312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3466312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466312 prefixEnd_3466312 := by exact prefixLift 3466312
  have htrace : WordTrace (prefixWord ++ tailWord_3466312) baseStart_3466312 baseEnd_3466312 := by
    simpa [prefixWord, tailWord_3466312, baseEnd_3466312] using wordTrace_append hprefix tailTrace_3466312
  have hstable : (prefixWord ++ tailWord_3466312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466312).length < 2 ^ (prefixWord ++ tailWord_3466312).sum := by decide
  have hdescent : baseEnd_3466312 < baseStart_3466312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466329 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 4, 4, 2]
def baseStart_3466329 : Nat := 118140960795 + 3466329 * 2 ^ 59
def prefixEnd_3466329 : Nat := 4983230072969 + 3 ^ 40 * 3466329 * 2
def baseEnd_3466329 : Nat := 1779892883618873705546149

theorem tailTrace_3466329 : CollatzResearch.WordTrace tailWord_3466329 prefixEnd_3466329 1779892883618873705546149 := by
  unfold tailWord_3466329
  simp only [CollatzResearch.WordTrace]
  refine ⟨126427405059089509706634041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84284936706059673137756027 126427405059089509706634041)
  ·
    refine ⟨94820553794317132279975531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126427405059089509706634041 94820553794317132279975531)
    ·
      refine ⟨142230830691475698419963297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94820553794317132279975531 142230830691475698419963297)
      ·
        refine ⟨106673123018606773814972473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142230830691475698419963297 106673123018606773814972473)
        ·
          refine ⟨80004842263955080361229355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106673123018606773814972473 80004842263955080361229355)
          ·
            refine ⟨120007263395932620541844033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80004842263955080361229355 120007263395932620541844033)
            ·
              refine ⟨90005447546949465406383025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120007263395932620541844033 90005447546949465406383025)
              ·
                refine ⟨67504085660212099054787269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90005447546949465406383025 67504085660212099054787269)
                ·
                  refine ⟨12657016061289768572772613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67504085660212099054787269 12657016061289768572772613)
                  ·
                    refine ⟨2373190511491831607394865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12657016061289768572772613 2373190511491831607394865)
                    ·
                      refine ⟨1779892883618873705546149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373190511491831607394865 1779892883618873705546149)
                      ·
                        rfl

theorem cell23_3466329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_3466329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466329 prefixEnd_3466329 := by exact prefixLift 3466329
  have htrace : WordTrace (prefixWord ++ tailWord_3466329) baseStart_3466329 baseEnd_3466329 := by
    simpa [prefixWord, tailWord_3466329, baseEnd_3466329] using wordTrace_append hprefix tailTrace_3466329
  have hstable : (prefixWord ++ tailWord_3466329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466329).length < 2 ^ (prefixWord ++ tailWord_3466329).sum := by decide
  have hdescent : baseEnd_3466329 < baseStart_3466329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466346 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3466346 : Nat := 118140960795 + 3466346 * 2 ^ 59
def prefixEnd_3466346 : Nat := 4983230072969 + 3 ^ 40 * 3466346 * 2
def baseEnd_3466346 : Nat := 1779901612790000139033571

theorem tailTrace_3466346 : CollatzResearch.WordTrace tailWord_3466346 prefixEnd_3466346 1779901612790000139033571 := by
  unfold tailWord_3466346
  simp only [CollatzResearch.WordTrace]
  refine ⟨31607006275006980402500723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84285350066685281073335261 31607006275006980402500723)
  ·
    refine ⟨47410509412510470603751085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31607006275006980402500723 47410509412510470603751085)
    ·
      refine ⟨17778941029691426476406657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47410509412510470603751085 17778941029691426476406657)
      ·
        refine ⟨13334205772268569857304993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17778941029691426476406657 13334205772268569857304993)
        ·
          refine ⟨10000654329201427392978745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13334205772268569857304993 10000654329201427392978745)
          ·
            refine ⟨7500490746901070544734059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10000654329201427392978745 7500490746901070544734059)
            ·
              refine ⟨11250736120351605817101089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7500490746901070544734059 11250736120351605817101089)
              ·
                refine ⟨8438052090263704362825817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11250736120351605817101089 8438052090263704362825817)
                ·
                  refine ⟨6328539067697778272119363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8438052090263704362825817 6328539067697778272119363)
                  ·
                    refine ⟨9492808601546667408179045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6328539067697778272119363 9492808601546667408179045)
                    ·
                      refine ⟨1779901612790000139033571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9492808601546667408179045 1779901612790000139033571)
                      ·
                        rfl

theorem cell23_3466346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3466346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466346 prefixEnd_3466346 := by exact prefixLift 3466346
  have htrace : WordTrace (prefixWord ++ tailWord_3466346) baseStart_3466346 baseEnd_3466346 := by
    simpa [prefixWord, tailWord_3466346, baseEnd_3466346] using wordTrace_append hprefix tailTrace_3466346
  have hstable : (prefixWord ++ tailWord_3466346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466346).length < 2 ^ (prefixWord ++ tailWord_3466346).sum := by decide
  have hdescent : baseEnd_3466346 < baseStart_3466346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466352 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 8]
def baseStart_3466352 : Nat := 118140960795 + 3466352 * 2 ^ 59
def prefixEnd_3466352 : Nat := 4983230072969 + 3 ^ 40 * 3466352 * 2
def baseEnd_3466352 : Nat := 197767188185991901728727

theorem tailTrace_3466352 : CollatzResearch.WordTrace tailWord_3466352 prefixEnd_3466352 197767188185991901728727 := by
  unfold tailWord_3466352
  simp only [CollatzResearch.WordTrace]
  refine ⟨63214121969003092317360655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84285495958670789756480873 63214121969003092317360655)
  ·
    refine ⟨94821182953504638476040983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63214121969003092317360655 94821182953504638476040983)
    ·
      refine ⟨142231774430256957714061475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94821182953504638476040983 142231774430256957714061475)
      ·
        refine ⟨213347661645385436571092213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142231774430256957714061475 213347661645385436571092213)
        ·
          refine ⟨20001343279254884678539895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213347661645385436571092213 20001343279254884678539895)
          ·
            refine ⟨30002014918882327017809843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20001343279254884678539895 30002014918882327017809843)
            ·
              refine ⟨45003022378323490526714765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30002014918882327017809843 45003022378323490526714765)
              ·
                refine ⟨16876133391871308947518037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45003022378323490526714765 16876133391871308947518037)
                ·
                  refine ⟨197767188185991901728727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16876133391871308947518037 197767188185991901728727)
                  ·
                    rfl

theorem cell23_3466352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 8].length) (baseStart_3466352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466352 prefixEnd_3466352 := by exact prefixLift 3466352
  have htrace : WordTrace (prefixWord ++ tailWord_3466352) baseStart_3466352 baseEnd_3466352 := by
    simpa [prefixWord, tailWord_3466352, baseEnd_3466352] using wordTrace_append hprefix tailTrace_3466352
  have hstable : (prefixWord ++ tailWord_3466352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466352).length < 2 ^ (prefixWord ++ tailWord_3466352).sum := by decide
  have hdescent : baseEnd_3466352 < baseStart_3466352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466407 : List Nat := [1, 1, 6, 2, 1, 3, 2, 2, 1, 4]
def baseStart_3466407 : Nat := 118140960795 + 3466407 * 2 ^ 59
def prefixEnd_3466407 : Nat := 4983230072969 + 3 ^ 40 * 3466407 * 2
def baseEnd_3466407 : Nat := 593310978369974800123597

theorem tailTrace_3466407 : CollatzResearch.WordTrace tailWord_3466407 prefixEnd_3466407 593310978369974800123597 := by
  unfold tailWord_3466407
  simp only [CollatzResearch.WordTrace]
  refine ⟨126430249952806929027973475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84286833301871286018648983 126430249952806929027973475)
  ·
    refine ⟨189645374929210393541960213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126430249952806929027973475 189645374929210393541960213)
    ·
      refine ⟨8889626949806737197279385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 189645374929210393541960213 8889626949806737197279385)
      ·
        refine ⟨6667220212355052897959539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8889626949806737197279385 6667220212355052897959539)
        ·
          refine ⟨10000830318532579346939309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667220212355052897959539 10000830318532579346939309)
          ·
            refine ⟨3750311369449717255102241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10000830318532579346939309 3750311369449717255102241)
            ·
              refine ⟨2812733527087287941326681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3750311369449717255102241 2812733527087287941326681)
              ·
                refine ⟨2109550145315465955995011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812733527087287941326681 2109550145315465955995011)
                ·
                  refine ⟨3164325217973198933992517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109550145315465955995011 3164325217973198933992517)
                  ·
                    refine ⟨593310978369974800123597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3164325217973198933992517 593310978369974800123597)
                    ·
                      rfl

theorem cell23_3466407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_3466407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466407 prefixEnd_3466407 := by exact prefixLift 3466407
  have htrace : WordTrace (prefixWord ++ tailWord_3466407) baseStart_3466407 baseEnd_3466407 := by
    simpa [prefixWord, tailWord_3466407, baseEnd_3466407] using wordTrace_append hprefix tailTrace_3466407
  have hstable : (prefixWord ++ tailWord_3466407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466407).length < 2 ^ (prefixWord ++ tailWord_3466407).sum := by decide
  have hdescent : baseEnd_3466407 < baseStart_3466407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466419 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 4]
def baseStart_3466419 : Nat := 118140960795 + 3466419 * 2 ^ 59
def prefixEnd_3466419 : Nat := 4983230072969 + 3 ^ 40 * 3466419 * 2
def baseEnd_3466419 : Nat := 1779939096877778353420735

theorem tailTrace_3466419 : CollatzResearch.WordTrace tailWord_3466419 prefixEnd_3466419 1779939096877778353420735 := by
  unfold tailWord_3466419
  simp only [CollatzResearch.WordTrace]
  refine ⟨126430687628763455077410311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84287125085842303384940207 126430687628763455077410311)
  ·
    refine ⟨189646031443145182616115467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126430687628763455077410311 189646031443145182616115467)
    ·
      refine ⟨284469047164717773924173201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189646031443145182616115467 284469047164717773924173201)
      ·
        refine ⟨213351785373538330443129901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284469047164717773924173201 213351785373538330443129901)
        ·
          refine ⟨80006919515076873916173713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213351785373538330443129901 80006919515076873916173713)
          ·
            refine ⟨60005189636307655437130285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80006919515076873916173713 60005189636307655437130285)
            ·
              refine ⟨22501946113615370788923857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60005189636307655437130285 22501946113615370788923857)
              ·
                refine ⟨16876459585211528091692893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22501946113615370788923857 16876459585211528091692893)
                ·
                  refine ⟨6328672344454323034384835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16876459585211528091692893 6328672344454323034384835)
                  ·
                    refine ⟨9493008516681484551577253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6328672344454323034384835 9493008516681484551577253)
                    ·
                      refine ⟨1779939096877778353420735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9493008516681484551577253 1779939096877778353420735)
                      ·
                        rfl

theorem cell23_3466419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_3466419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466419 prefixEnd_3466419 := by exact prefixLift 3466419
  have htrace : WordTrace (prefixWord ++ tailWord_3466419) baseStart_3466419 baseEnd_3466419 := by
    simpa [prefixWord, tailWord_3466419, baseEnd_3466419] using wordTrace_append hprefix tailTrace_3466419
  have hstable : (prefixWord ++ tailWord_3466419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466419).length < 2 ^ (prefixWord ++ tailWord_3466419).sum := by decide
  have hdescent : baseEnd_3466419 < baseStart_3466419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466429 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_3466429 : Nat := 118140960795 + 3466429 * 2 ^ 59
def prefixEnd_3466429 : Nat := 4983230072969 + 3 ^ 40 * 3466429 * 2
def baseEnd_3466429 : Nat := 593314743894774438098563

theorem tailTrace_3466429 : CollatzResearch.WordTrace tailWord_3466429 prefixEnd_3466429 593314743894774438098563 := by
  unfold tailWord_3466429
  simp only [CollatzResearch.WordTrace]
  refine ⟨126431052358727226785274341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84287368239151484523516227 126431052358727226785274341)
  ·
    refine ⟨23705822317261355022238939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126431052358727226785274341 23705822317261355022238939)
    ·
      refine ⟨35558733475892032533358409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23705822317261355022238939 35558733475892032533358409)
      ·
        refine ⟨26669050106919024400018807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35558733475892032533358409 26669050106919024400018807)
        ·
          refine ⟨40003575160378536600028211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26669050106919024400018807 40003575160378536600028211)
          ·
            refine ⟨60005362740567804900042317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40003575160378536600028211 60005362740567804900042317)
            ·
              refine ⟨22502011027712926837515869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60005362740567804900042317 22502011027712926837515869)
              ·
                refine ⟨8438254135392347564068451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22502011027712926837515869 8438254135392347564068451)
                ·
                  refine ⟨12657381203088521346102677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8438254135392347564068451 12657381203088521346102677)
                  ·
                    refine ⟨593314743894774438098563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12657381203088521346102677 593314743894774438098563)
                    ·
                      rfl

theorem cell23_3466429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_3466429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466429 prefixEnd_3466429 := by exact prefixLift 3466429
  have htrace : WordTrace (prefixWord ++ tailWord_3466429) baseStart_3466429 baseEnd_3466429 := by
    simpa [prefixWord, tailWord_3466429, baseEnd_3466429] using wordTrace_append hprefix tailTrace_3466429
  have hstable : (prefixWord ++ tailWord_3466429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466429).length < 2 ^ (prefixWord ++ tailWord_3466429).sum := by decide
  have hdescent : baseEnd_3466429 < baseStart_3466429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466434 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_3466434 : Nat := 118140960795 + 3466434 * 2 ^ 59
def prefixEnd_3466434 : Nat := 4983230072969 + 3 ^ 40 * 3466434 * 2
def baseEnd_3466434 : Nat := 1779946799087595794733167

theorem tailTrace_3466434 : CollatzResearch.WordTrace tailWord_3466434 prefixEnd_3466434 1779946799087595794733167 := by
  unfold tailWord_3466434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31607808680927278159801589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84287489815806075092804237 31607808680927278159801589)
  ·
    refine ⟨2963232063836932327481399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31607808680927278159801589 2963232063836932327481399)
    ·
      refine ⟨4444848095755398491222099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2963232063836932327481399 4444848095755398491222099)
      ·
        refine ⟨6667272143633097736833149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444848095755398491222099 6667272143633097736833149)
        ·
          refine ⟨2500227053862411651312431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6667272143633097736833149 2500227053862411651312431)
          ·
            refine ⟨3750340580793617476968647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500227053862411651312431 3750340580793617476968647)
            ·
              refine ⟨5625510871190426215452971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3750340580793617476968647 5625510871190426215452971)
              ·
                refine ⟨8438266306785639323179457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5625510871190426215452971 8438266306785639323179457)
                ·
                  refine ⟨6328699730089229492384593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8438266306785639323179457 6328699730089229492384593)
                  ·
                    refine ⟨4746524797566922119288445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6328699730089229492384593 4746524797566922119288445)
                    ·
                      refine ⟨1779946799087595794733167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4746524797566922119288445 1779946799087595794733167)
                      ·
                        rfl

theorem cell23_3466434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_3466434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466434 prefixEnd_3466434 := by exact prefixLift 3466434
  have htrace : WordTrace (prefixWord ++ tailWord_3466434) baseStart_3466434 baseEnd_3466434 := by
    simpa [prefixWord, tailWord_3466434, baseEnd_3466434] using wordTrace_append hprefix tailTrace_3466434
  have hstable : (prefixWord ++ tailWord_3466434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466434).length < 2 ^ (prefixWord ++ tailWord_3466434).sum := by decide
  have hdescent : baseEnd_3466434 < baseStart_3466434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466453 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3466453 : Nat := 118140960795 + 3466453 * 2 ^ 59
def prefixEnd_3466453 : Nat := 4983230072969 + 3 ^ 40 * 3466453 * 2
def baseEnd_3466453 : Nat := 1779956555220031220395579

theorem tailTrace_3466453 : CollatzResearch.WordTrace tailWord_3466453 prefixEnd_3466453 1779956555220031220395579 := by
  unfold tailWord_3466453
  simp only [CollatzResearch.WordTrace]
  refine ⟨126431927710640278884148013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84287951807093519256098675 126431927710640278884148013)
  ·
    refine ⟨47411972891490104581555505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126431927710640278884148013 47411972891490104581555505)
    ·
      refine ⟨35558979668617578436166629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47411972891490104581555505 35558979668617578436166629)
      ·
        refine ⟨6667308687865795956781243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35558979668617578436166629 6667308687865795956781243)
        ·
          refine ⟨10000963031798693935171865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667308687865795956781243 10000963031798693935171865)
          ·
            refine ⟨7500722273849020451378899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10000963031798693935171865 7500722273849020451378899)
            ·
              refine ⟨11251083410773530677068349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7500722273849020451378899 11251083410773530677068349)
              ·
                refine ⟨4219156279040074003900631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11251083410773530677068349 4219156279040074003900631)
                ·
                  refine ⟨6328734418560111005850947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219156279040074003900631 6328734418560111005850947)
                  ·
                    refine ⟨9493101627840166508776421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6328734418560111005850947 9493101627840166508776421)
                    ·
                      refine ⟨1779956555220031220395579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9493101627840166508776421 1779956555220031220395579)
                      ·
                        rfl

theorem cell23_3466453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3466453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466453 prefixEnd_3466453 := by exact prefixLift 3466453
  have htrace : WordTrace (prefixWord ++ tailWord_3466453) baseStart_3466453 baseEnd_3466453 := by
    simpa [prefixWord, tailWord_3466453, baseEnd_3466453] using wordTrace_append hprefix tailTrace_3466453
  have hstable : (prefixWord ++ tailWord_3466453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466453).length < 2 ^ (prefixWord ++ tailWord_3466453).sum := by decide
  have hdescent : baseEnd_3466453 < baseStart_3466453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466499 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 5]
def baseStart_3466499 : Nat := 118140960795 + 3466499 * 2 ^ 59
def prefixEnd_3466499 : Nat := 4983230072969 + 3 ^ 40 * 3466499 * 2
def baseEnd_3466499 : Nat := 1779980175330138040420367

theorem tailTrace_3466499 : CollatzResearch.WordTrace tailWord_3466499 prefixEnd_3466499 1779980175330138040420367 := by
  unfold tailWord_3466499
  simp only [CollatzResearch.WordTrace]
  refine ⟨126433605468473628740322551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84289070312315752493548367 126433605468473628740322551)
  ·
    refine ⟨189650408202710443110483827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126433605468473628740322551 189650408202710443110483827)
    ·
      refine ⟨284475612304065664665725741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189650408202710443110483827 284475612304065664665725741)
      ·
        refine ⟨106678354614024624249647153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284475612304065664665725741 106678354614024624249647153)
        ·
          refine ⟨80008765960518468187235365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106678354614024624249647153 80008765960518468187235365)
          ·
            refine ⟨15001643617597212785106631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80008765960518468187235365 15001643617597212785106631)
            ·
              refine ⟨22502465426395819177659947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15001643617597212785106631 22502465426395819177659947)
              ·
                refine ⟨33753698139593728766489921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22502465426395819177659947 33753698139593728766489921)
                ·
                  refine ⟨25315273604695296574867441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33753698139593728766489921 25315273604695296574867441)
                  ·
                    refine ⟨18986455203521472431150581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25315273604695296574867441 18986455203521472431150581)
                    ·
                      refine ⟨1779980175330138040420367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18986455203521472431150581 1779980175330138040420367)
                      ·
                        rfl

theorem cell23_3466499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_3466499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466499 prefixEnd_3466499 := by exact prefixLift 3466499
  have htrace : WordTrace (prefixWord ++ tailWord_3466499) baseStart_3466499 baseEnd_3466499 := by
    simpa [prefixWord, tailWord_3466499, baseEnd_3466499] using wordTrace_append hprefix tailTrace_3466499
  have hstable : (prefixWord ++ tailWord_3466499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466499).length < 2 ^ (prefixWord ++ tailWord_3466499).sum := by decide
  have hdescent : baseEnd_3466499 < baseStart_3466499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466504 : List Nat := [2, 1, 3, 2, 4, 2, 1, 3, 1, 2, 2]
def baseStart_3466504 : Nat := 118140960795 + 3466504 * 2 ^ 59
def prefixEnd_3466504 : Nat := 4983230072969 + 3 ^ 40 * 3466504 * 2
def baseEnd_3466504 : Nat := 1779982742733410520857845

theorem tailTrace_3466504 : CollatzResearch.WordTrace tailWord_3466504 prefixEnd_3466504 1779982742733410520857845 := by
  unfold tailWord_3466504
  simp only [CollatzResearch.WordTrace]
  refine ⟨63216893916727757297127283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84289191888970343062836377 63216893916727757297127283)
  ·
    refine ⟨94825340875091635945690925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63216893916727757297127283 94825340875091635945690925)
    ·
      refine ⟨35559502828159363479634097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94825340875091635945690925 35559502828159363479634097)
      ·
        refine ⟨26669627121119522609725573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35559502828159363479634097 26669627121119522609725573)
        ·
          refine ⟨5000555085209910489323545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26669627121119522609725573 5000555085209910489323545)
          ·
            refine ⟨3750416313907432866992659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5000555085209910489323545 3750416313907432866992659)
            ·
              refine ⟨5625624470861149300488989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3750416313907432866992659 5625624470861149300488989)
              ·
                refine ⟨2109609176572930987683371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5625624470861149300488989 2109609176572930987683371)
                ·
                  refine ⟨3164413764859396481525057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109609176572930987683371 3164413764859396481525057)
                  ·
                    refine ⟨2373310323644547361143793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3164413764859396481525057 2373310323644547361143793)
                    ·
                      refine ⟨1779982742733410520857845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373310323644547361143793 1779982742733410520857845)
                      ·
                        rfl

theorem cell23_3466504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_3466504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466504 prefixEnd_3466504 := by exact prefixLift 3466504
  have htrace : WordTrace (prefixWord ++ tailWord_3466504) baseStart_3466504 baseEnd_3466504 := by
    simpa [prefixWord, tailWord_3466504, baseEnd_3466504] using wordTrace_append hprefix tailTrace_3466504
  have hstable : (prefixWord ++ tailWord_3466504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466504).length < 2 ^ (prefixWord ++ tailWord_3466504).sum := by decide
  have hdescent : baseEnd_3466504 < baseStart_3466504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466513 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 1, 3, 2]
def baseStart_3466513 : Nat := 118140960795 + 3466513 * 2 ^ 59
def prefixEnd_3466513 : Nat := 4983230072969 + 3 ^ 40 * 3466513 * 2
def baseEnd_3466513 : Nat := 1779987364059300985645303

theorem tailTrace_3466513 : CollatzResearch.WordTrace tailWord_3466513 prefixEnd_3466513 1779987364059300985645303 := by
  unfold tailWord_3466513
  simp only [CollatzResearch.WordTrace]
  refine ⟨126434116090422909131332193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84289410726948606087554795 126434116090422909131332193)
  ·
    refine ⟨94825587067817181848499145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126434116090422909131332193 94825587067817181848499145)
    ·
      refine ⟨71119190300862886386374359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94825587067817181848499145 71119190300862886386374359)
      ·
        refine ⟨106678785451294329579561539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71119190300862886386374359 106678785451294329579561539)
        ·
          refine ⟨160018178176941494369342309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106678785451294329579561539 160018178176941494369342309)
          ·
            refine ⟨30003408408176530194251683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160018178176941494369342309 30003408408176530194251683)
            ·
              refine ⟨45005112612264795291377525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30003408408176530194251683 45005112612264795291377525)
              ·
                refine ⟨4219229307399824558566643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45005112612264795291377525 4219229307399824558566643)
                ·
                  refine ⟨6328843961099736837849965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219229307399824558566643 6328843961099736837849965)
                  ·
                    refine ⟨2373316485412401314193737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6328843961099736837849965 2373316485412401314193737)
                    ·
                      refine ⟨1779987364059300985645303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373316485412401314193737 1779987364059300985645303)
                      ·
                        rfl

theorem cell23_3466513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_3466513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466513 prefixEnd_3466513 := by exact prefixLift 3466513
  have htrace : WordTrace (prefixWord ++ tailWord_3466513) baseStart_3466513 baseEnd_3466513 := by
    simpa [prefixWord, tailWord_3466513, baseEnd_3466513] using wordTrace_append hprefix tailTrace_3466513
  have hstable : (prefixWord ++ tailWord_3466513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466513).length < 2 ^ (prefixWord ++ tailWord_3466513).sum := by decide
  have hdescent : baseEnd_3466513 < baseStart_3466513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466529 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3466529 : Nat := 118140960795 + 3466529 * 2 ^ 59
def prefixEnd_3466529 : Nat := 4983230072969 + 3 ^ 40 * 3466529 * 2
def baseEnd_3466529 : Nat := 1779995579749772923045229

theorem tailTrace_3466529 : CollatzResearch.WordTrace tailWord_3466529 prefixEnd_3466529 1779995579749772923045229 := by
  unfold tailWord_3466529
  simp only [CollatzResearch.WordTrace]
  refine ⟨126434699658364943863914641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84289799772243295909276427 126434699658364943863914641)
  ·
    refine ⟨94826024743773707897935981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126434699658364943863914641 94826024743773707897935981)
    ·
      refine ⟨35559759278915140461725993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94826024743773707897935981 35559759278915140461725993)
      ·
        refine ⟨26669819459186355346294495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35559759278915140461725993 26669819459186355346294495)
        ·
          refine ⟨40004729188779533019441743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26669819459186355346294495 40004729188779533019441743)
          ·
            refine ⟨60007093783169299529162615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40004729188779533019441743 60007093783169299529162615)
            ·
              refine ⟨90010640674753949293743923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60007093783169299529162615 90010640674753949293743923)
              ·
                refine ⟨135015961012130923940615885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90010640674753949293743923 135015961012130923940615885)
                ·
                  refine ⟨50630985379549096477730957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135015961012130923940615885 50630985379549096477730957)
                  ·
                    refine ⟨18986619517330911179149109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50630985379549096477730957 18986619517330911179149109)
                    ·
                      refine ⟨1779995579749772923045229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18986619517330911179149109 1779995579749772923045229)
                      ·
                        rfl

theorem cell23_3466529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3466529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466529 prefixEnd_3466529 := by exact prefixLift 3466529
  have htrace : WordTrace (prefixWord ++ tailWord_3466529) baseStart_3466529 baseEnd_3466529 := by
    simpa [prefixWord, tailWord_3466529, baseEnd_3466529] using wordTrace_append hprefix tailTrace_3466529
  have hstable : (prefixWord ++ tailWord_3466529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466529).length < 2 ^ (prefixWord ++ tailWord_3466529).sum := by decide
  have hdescent : baseEnd_3466529 < baseStart_3466529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466546 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_3466546 : Nat := 118140960795 + 3466546 * 2 ^ 59
def prefixEnd_3466546 : Nat := 4983230072969 + 3 ^ 40 * 3466546 * 2
def baseEnd_3466546 : Nat := 1780004308920899356532651

theorem tailTrace_3466546 : CollatzResearch.WordTrace tailWord_3466546 prefixEnd_3466546 1780004308920899356532651 := by
  unfold tailWord_3466546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31608829924825838941820873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84290213132868903844855661 31608829924825838941820873)
  ·
    refine ⟨23706622443619379206365655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31608829924825838941820873 23706622443619379206365655)
    ·
      refine ⟨35559933665429068809548483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23706622443619379206365655 35559933665429068809548483)
      ·
        refine ⟨53339900498143603214322725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35559933665429068809548483 53339900498143603214322725)
        ·
          refine ⟨10001231343401925602685511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53339900498143603214322725 10001231343401925602685511)
          ·
            refine ⟨15001847015102888404028267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10001231343401925602685511 15001847015102888404028267)
            ·
              refine ⟨22502770522654332606042401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15001847015102888404028267 22502770522654332606042401)
              ·
                refine ⟨16877077891990749454531801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22502770522654332606042401 16877077891990749454531801)
                ·
                  refine ⟨12657808418993062090898851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16877077891990749454531801 12657808418993062090898851)
                  ·
                    refine ⟨18986712628489593136348277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12657808418993062090898851 18986712628489593136348277)
                    ·
                      refine ⟨1780004308920899356532651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18986712628489593136348277 1780004308920899356532651)
                      ·
                        rfl

theorem cell23_3466546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_3466546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466546 prefixEnd_3466546 := by exact prefixLift 3466546
  have htrace : WordTrace (prefixWord ++ tailWord_3466546) baseStart_3466546 baseEnd_3466546 := by
    simpa [prefixWord, tailWord_3466546, baseEnd_3466546] using wordTrace_append hprefix tailTrace_3466546
  have hstable : (prefixWord ++ tailWord_3466546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466546).length < 2 ^ (prefixWord ++ tailWord_3466546).sum := by decide
  have hdescent : baseEnd_3466546 < baseStart_3466546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466564 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_3466564 : Nat := 118140960795 + 3466564 * 2 ^ 59
def prefixEnd_3466564 : Nat := 4983230072969 + 3 ^ 40 * 3466564 * 2
def baseEnd_3466564 : Nat := 1780013551572680286107569

theorem tailTrace_3466564 : CollatzResearch.WordTrace tailWord_3466564 prefixEnd_3466564 1780013551572680286107569 := by
  unfold tailWord_3466564
  simp only [CollatzResearch.WordTrace]
  refine ⟨63217988106619072420719373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84290650808825429894292497 63217988106619072420719373)
  ·
    refine ⟨23706745539982152157769765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63217988106619072420719373 23706745539982152157769765)
    ·
      refine ⟨4445014788746653529581831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23706745539982152157769765 4445014788746653529581831)
      ·
        refine ⟨6667522183119980294372747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4445014788746653529581831 6667522183119980294372747)
        ·
          refine ⟨10001283274679970441559121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667522183119980294372747 10001283274679970441559121)
          ·
            refine ⟨7500962456009977831169341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10001283274679970441559121 7500962456009977831169341)
            ·
              refine ⟨2812860921003741686688503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7500962456009977831169341 2812860921003741686688503)
              ·
                refine ⟨4219291381505612530032755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812860921003741686688503 4219291381505612530032755)
                ·
                  refine ⟨6328937072258418795049133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219291381505612530032755 6328937072258418795049133)
                  ·
                    refine ⟨2373351402096907048143425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6328937072258418795049133 2373351402096907048143425)
                    ·
                      refine ⟨1780013551572680286107569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373351402096907048143425 1780013551572680286107569)
                      ·
                        rfl

theorem cell23_3466564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_3466564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466564 prefixEnd_3466564 := by exact prefixLift 3466564
  have htrace : WordTrace (prefixWord ++ tailWord_3466564) baseStart_3466564 baseEnd_3466564 := by
    simpa [prefixWord, tailWord_3466564, baseEnd_3466564] using wordTrace_append hprefix tailTrace_3466564
  have hstable : (prefixWord ++ tailWord_3466564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466564).length < 2 ^ (prefixWord ++ tailWord_3466564).sum := by decide
  have hdescent : baseEnd_3466564 < baseStart_3466564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466576 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 3]
def baseStart_3466576 : Nat := 118140960795 + 3466576 * 2 ^ 59
def prefixEnd_3466576 : Nat := 4983230072969 + 3 ^ 40 * 3466576 * 2
def baseEnd_3466576 : Nat := 1780019713340534239157513

theorem tailTrace_3466576 : CollatzResearch.WordTrace tailWord_3466576 prefixEnd_3466576 1780019713340534239157513 := by
  unfold tailWord_3466576
  simp only [CollatzResearch.WordTrace]
  refine ⟨63218206944597335445437791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84290942592796447260583721 63218206944597335445437791)
  ·
    refine ⟨94827310416896003168156687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63218206944597335445437791 94827310416896003168156687)
    ·
      refine ⟨142240965625344004752235031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94827310416896003168156687 142240965625344004752235031)
      ·
        refine ⟨213361448438016007128352547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142240965625344004752235031 213361448438016007128352547)
        ·
          refine ⟨320042172657024010692528821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213361448438016007128352547 320042172657024010692528821)
          ·
            refine ⟨30003953686596001002424577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320042172657024010692528821 30003953686596001002424577)
            ·
              refine ⟨22502965264947000751818433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30003953686596001002424577 22502965264947000751818433)
              ·
                refine ⟨16877223948710250563863825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22502965264947000751818433 16877223948710250563863825)
                ·
                  refine ⟨12657917961532687922897869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16877223948710250563863825 12657917961532687922897869)
                  ·
                    refine ⟨4746719235574757971086701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12657917961532687922897869 4746719235574757971086701)
                    ·
                      refine ⟨1780019713340534239157513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4746719235574757971086701 1780019713340534239157513)
                      ·
                        rfl

theorem cell23_3466576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_3466576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466576 prefixEnd_3466576 := by exact prefixLift 3466576
  have htrace : WordTrace (prefixWord ++ tailWord_3466576) baseStart_3466576 baseEnd_3466576 := by
    simpa [prefixWord, tailWord_3466576, baseEnd_3466576] using wordTrace_append hprefix tailTrace_3466576
  have hstable : (prefixWord ++ tailWord_3466576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466576).length < 2 ^ (prefixWord ++ tailWord_3466576).sum := by decide
  have hdescent : baseEnd_3466576 < baseStart_3466576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466583 : List Nat := [1, 1, 3, 2, 3, 3, 1, 4, 5]
def baseStart_3466583 : Nat := 118140960795 + 3466583 * 2 ^ 59
def prefixEnd_3466583 : Nat := 4983230072969 + 3 ^ 40 * 3466583 * 2
def baseEnd_3466583 : Nat := 197780367522790634641109

theorem tailTrace_3466583 : CollatzResearch.WordTrace tailWord_3466583 prefixEnd_3466583 197780367522790634641109 := by
  unfold tailWord_3466583
  simp only [CollatzResearch.WordTrace]
  refine ⟨126436669200169311086380403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84291112800112874057586935 126436669200169311086380403)
  ·
    refine ⟨189655003800253966629570605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126436669200169311086380403 189655003800253966629570605)
    ·
      refine ⟨71120626425095237486088977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189655003800253966629570605 71120626425095237486088977)
      ·
        refine ⟨53340469818821428114566733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71120626425095237486088977 53340469818821428114566733)
        ·
          refine ⟨20002676182058035542962525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53340469818821428114566733 20002676182058035542962525)
          ·
            refine ⟨7501003568271763328610947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20002676182058035542962525 7501003568271763328610947)
            ·
              refine ⟨11251505352407644992916421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7501003568271763328610947 11251505352407644992916421)
              ·
                refine ⟨2109657253576433436171829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11251505352407644992916421 2109657253576433436171829)
                ·
                  refine ⟨197780367522790634641109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2109657253576433436171829 197780367522790634641109)
                  ·
                    rfl

theorem cell23_3466583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 5].length) (baseStart_3466583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466583 prefixEnd_3466583 := by exact prefixLift 3466583
  have htrace : WordTrace (prefixWord ++ tailWord_3466583) baseStart_3466583 baseEnd_3466583 := by
    simpa [prefixWord, tailWord_3466583, baseEnd_3466583] using wordTrace_append hprefix tailTrace_3466583
  have hstable : (prefixWord ++ tailWord_3466583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466583).length < 2 ^ (prefixWord ++ tailWord_3466583).sum := by decide
  have hdescent : baseEnd_3466583 < baseStart_3466583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466613 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3466613 : Nat := 118140960795 + 3466613 * 2 ^ 59
def prefixEnd_3466613 : Nat := 4983230072969 + 3 ^ 40 * 3466613 * 2
def baseEnd_3466613 : Nat := 593346237374916864798281

theorem tailTrace_3466613 : CollatzResearch.WordTrace tailWord_3466613 prefixEnd_3466613 593346237374916864798281 := by
  unfold tailWord_3466613
  simp only [CollatzResearch.WordTrace]
  refine ⟨126437763390060626209972493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84291842260040417473314995 126437763390060626209972493)
  ·
    refine ⟨47414161271272734828739685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126437763390060626209972493 47414161271272734828739685)
    ·
      refine ⟨8890155238363637780388691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47414161271272734828739685 8890155238363637780388691)
      ·
        refine ⟨13335232857545456670583037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8890155238363637780388691 13335232857545456670583037)
        ·
          refine ⟨5000712321579546251468639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13335232857545456670583037 5000712321579546251468639)
          ·
            refine ⟨7501068482369319377202959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000712321579546251468639 7501068482369319377202959)
            ·
              refine ⟨11251602723553979065804439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7501068482369319377202959 11251602723553979065804439)
              ·
                refine ⟨16877404085330968598706659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11251602723553979065804439 16877404085330968598706659)
                ·
                  refine ⟨25316106127996452898059989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16877404085330968598706659 25316106127996452898059989)
                  ·
                    refine ⟨593346237374916864798281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25316106127996452898059989 593346237374916864798281)
                    ·
                      rfl

theorem cell23_3466613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3466613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466613 prefixEnd_3466613 := by exact prefixLift 3466613
  have htrace : WordTrace (prefixWord ++ tailWord_3466613) baseStart_3466613 baseEnd_3466613 := by
    simpa [prefixWord, tailWord_3466613, baseEnd_3466613] using wordTrace_append hprefix tailTrace_3466613
  have hstable : (prefixWord ++ tailWord_3466613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466613).length < 2 ^ (prefixWord ++ tailWord_3466613).sum := by decide
  have hdescent : baseEnd_3466613 < baseStart_3466613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466653 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_3466653 : Nat := 118140960795 + 3466653 * 2 ^ 59
def prefixEnd_3466653 : Nat := 4983230072969 + 3 ^ 40 * 3466653 * 2
def baseEnd_3466653 : Nat := 1780059251350930437894659

theorem tailTrace_3466653 : CollatzResearch.WordTrace tailWord_3466653 prefixEnd_3466653 1780059251350930437894659 := by
  unfold tailWord_3466653
  simp only [CollatzResearch.WordTrace]
  refine ⟨126439222309915713041428613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84292814873277142027619075 126439222309915713041428613)
  ·
    refine ⟨23707354183109196195267865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126439222309915713041428613 23707354183109196195267865)
    ·
      refine ⟨17780515637331897146450899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23707354183109196195267865 17780515637331897146450899)
      ·
        refine ⟨26670773455997845719676349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17780515637331897146450899 26670773455997845719676349)
        ·
          refine ⟨10001540045999192144878631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26670773455997845719676349 10001540045999192144878631)
          ·
            refine ⟨15002310068998788217317947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10001540045999192144878631 15002310068998788217317947)
            ·
              refine ⟨22503465103498182325976921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15002310068998788217317947 22503465103498182325976921)
              ·
                refine ⟨16877598827623636744482691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22503465103498182325976921 16877598827623636744482691)
                ·
                  refine ⟨25316398241435455116724037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16877598827623636744482691 25316398241435455116724037)
                  ·
                    refine ⟨4746824670269147834385757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25316398241435455116724037 4746824670269147834385757)
                    ·
                      refine ⟨1780059251350930437894659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4746824670269147834385757 1780059251350930437894659)
                      ·
                        rfl

theorem cell23_3466653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_3466653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466653 prefixEnd_3466653 := by exact prefixLift 3466653
  have htrace : WordTrace (prefixWord ++ tailWord_3466653) baseStart_3466653 baseEnd_3466653 := by
    simpa [prefixWord, tailWord_3466653, baseEnd_3466653] using wordTrace_append hprefix tailTrace_3466653
  have hstable : (prefixWord ++ tailWord_3466653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466653).length < 2 ^ (prefixWord ++ tailWord_3466653).sum := by decide
  have hdescent : baseEnd_3466653 < baseStart_3466653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466677 : List Nat := [1, 3, 3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3466677 : Nat := 118140960795 + 3466677 * 2 ^ 59
def prefixEnd_3466677 : Nat := 4983230072969 + 3 ^ 40 * 3466677 * 2
def baseEnd_3466677 : Nat := 593357191628879447998183

theorem tailTrace_3466677 : CollatzResearch.WordTrace tailWord_3466677 prefixEnd_3466677 593357191628879447998183 := by
  unfold tailWord_3466677
  simp only [CollatzResearch.WordTrace]
  refine ⟨126440097661828765140302285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84293398441219176760201523 126440097661828765140302285)
  ·
    refine ⟨47415036623185786927613357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126440097661828765140302285 47415036623185786927613357)
    ·
      refine ⟨17780638733694670097855009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47415036623185786927613357 17780638733694670097855009)
      ·
        refine ⟨13335479050271002573391257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17780638733694670097855009 13335479050271002573391257)
        ·
          refine ⟨10001609287703251930043443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13335479050271002573391257 10001609287703251930043443)
          ·
            refine ⟨15002413931554877895065165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10001609287703251930043443 15002413931554877895065165)
            ·
              refine ⟨5625905224333079210649437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15002413931554877895065165 5625905224333079210649437)
              ·
                refine ⟨2109714459124904703993539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5625905224333079210649437 2109714459124904703993539)
                ·
                  refine ⟨3164571688687357055990309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109714459124904703993539 3164571688687357055990309)
                  ·
                    refine ⟨593357191628879447998183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3164571688687357055990309 593357191628879447998183)
                    ·
                      rfl

theorem cell23_3466677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3466677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466677 prefixEnd_3466677 := by exact prefixLift 3466677
  have htrace : WordTrace (prefixWord ++ tailWord_3466677) baseStart_3466677 baseEnd_3466677 := by
    simpa [prefixWord, tailWord_3466677, baseEnd_3466677] using wordTrace_append hprefix tailTrace_3466677
  have hstable : (prefixWord ++ tailWord_3466677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466677).length < 2 ^ (prefixWord ++ tailWord_3466677).sum := by decide
  have hdescent : baseEnd_3466677 < baseStart_3466677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466727 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_3466727 : Nat := 118140960795 + 3466727 * 2 ^ 59
def prefixEnd_3466727 : Nat := 4983230072969 + 3 ^ 40 * 3466727 * 2
def baseEnd_3466727 : Nat := 1780097248919363148369319

theorem tailTrace_3466727 : CollatzResearch.WordTrace tailWord_3466727 prefixEnd_3466727 1780097248919363148369319 := by
  unfold tailWord_3466727
  simp only [CollatzResearch.WordTrace]
  refine ⟨126441921311647623679622435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84294614207765082453081623 126441921311647623679622435)
  ·
    refine ⟨189662881967471435519433653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126441921311647623679622435 189662881967471435519433653)
    ·
      refine ⟨17780895184450447079946905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189662881967471435519433653 17780895184450447079946905)
      ·
        refine ⟨13335671388337835309960179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17780895184450447079946905 13335671388337835309960179)
        ·
          refine ⟨20003507082506752964940269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13335671388337835309960179 20003507082506752964940269)
          ·
            refine ⟨7501315155940032361852601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20003507082506752964940269 7501315155940032361852601)
            ·
              refine ⟨5625986366955024271389451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7501315155940032361852601 5625986366955024271389451)
              ·
                refine ⟨8438979550432536407084177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5625986366955024271389451 8438979550432536407084177)
                ·
                  refine ⟨6329234662824402305313133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8438979550432536407084177 6329234662824402305313133)
                  ·
                    refine ⟨2373462998559150864492425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6329234662824402305313133 2373462998559150864492425)
                    ·
                      refine ⟨1780097248919363148369319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373462998559150864492425 1780097248919363148369319)
                      ·
                        rfl

theorem cell23_3466727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_3466727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466727 prefixEnd_3466727 := by exact prefixLift 3466727
  have htrace : WordTrace (prefixWord ++ tailWord_3466727) baseStart_3466727 baseEnd_3466727 := by
    simpa [prefixWord, tailWord_3466727, baseEnd_3466727] using wordTrace_append hprefix tailTrace_3466727
  have hstable : (prefixWord ++ tailWord_3466727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466727).length < 2 ^ (prefixWord ++ tailWord_3466727).sum := by decide
  have hdescent : baseEnd_3466727 < baseStart_3466727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466807 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 3]
def baseStart_3466807 : Nat := 118140960795 + 3466807 * 2 ^ 59
def prefixEnd_3466807 : Nat := 4983230072969 + 3 ^ 40 * 3466807 * 2
def baseEnd_3466807 : Nat := 1780138327371722835368951

theorem tailTrace_3466807 : CollatzResearch.WordTrace tailWord_3466807 prefixEnd_3466807 1780138327371722835368951 := by
  unfold tailWord_3466807
  simp only [CollatzResearch.WordTrace]
  refine ⟨126444839151357797342534675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84296559434238531561689783 126444839151357797342534675)
  ·
    refine ⟨189667258727036696013802013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126444839151357797342534675 189667258727036696013802013)
    ·
      refine ⟨71125222022638761005175755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189667258727036696013802013 71125222022638761005175755)
      ·
        refine ⟨106687833033958141507763633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71125222022638761005175755 106687833033958141507763633)
        ·
          refine ⟨80015874775468606130822725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106687833033958141507763633 80015874775468606130822725)
          ·
            refine ⟨15002976520400363649529261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80015874775468606130822725 15002976520400363649529261)
            ·
              refine ⟨5626116195150136368573473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15002976520400363649529261 5626116195150136368573473)
              ·
                refine ⟨4219587146362602276430105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5626116195150136368573473 4219587146362602276430105)
                ·
                  refine ⟨3164690359771951707322579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4219587146362602276430105 3164690359771951707322579)
                  ·
                    refine ⟨4747035539657927560983869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3164690359771951707322579 4747035539657927560983869)
                    ·
                      refine ⟨1780138327371722835368951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4747035539657927560983869 1780138327371722835368951)
                      ·
                        rfl

theorem cell23_3466807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_3466807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466807 prefixEnd_3466807 := by exact prefixLift 3466807
  have htrace : WordTrace (prefixWord ++ tailWord_3466807) baseStart_3466807 baseEnd_3466807 := by
    simpa [prefixWord, tailWord_3466807, baseEnd_3466807] using wordTrace_append hprefix tailTrace_3466807
  have hstable : (prefixWord ++ tailWord_3466807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466807).length < 2 ^ (prefixWord ++ tailWord_3466807).sum := by decide
  have hdescent : baseEnd_3466807 < baseStart_3466807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466833 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_3466833 : Nat := 118140960795 + 3466833 * 2 ^ 59
def prefixEnd_3466833 : Nat := 4983230072969 + 3 ^ 40 * 3466833 * 2
def baseEnd_3466833 : Nat := 1780151677868739733643831

theorem tailTrace_3466833 : CollatzResearch.WordTrace tailWord_3466833 prefixEnd_3466833 1780151677868739733643831 := by
  unfold tailWord_3466833
  simp only [CollatzResearch.WordTrace]
  refine ⟨126445787449263603782981153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84297191632842402521987435 126445787449263603782981153)
  ·
    refine ⟨94834340586947702837235865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126445787449263603782981153 94834340586947702837235865)
    ·
      refine ⟨71125755440210777127926899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94834340586947702837235865 71125755440210777127926899)
      ·
        refine ⟨106688633160316165691890349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71125755440210777127926899 106688633160316165691890349)
        ·
          refine ⟨40008237435118562134458881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106688633160316165691890349 40008237435118562134458881)
          ·
            refine ⟨30006178076338921600844161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40008237435118562134458881 30006178076338921600844161)
            ·
              refine ⟨22504633557254191200633121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30006178076338921600844161 22504633557254191200633121)
              ·
                refine ⟨16878475167940643400474841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22504633557254191200633121 16878475167940643400474841)
                ·
                  refine ⟨12658856375955482550356131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16878475167940643400474841 12658856375955482550356131)
                  ·
                    refine ⟨18988284563933223825534197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12658856375955482550356131 18988284563933223825534197)
                    ·
                      refine ⟨1780151677868739733643831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18988284563933223825534197 1780151677868739733643831)
                      ·
                        rfl

theorem cell23_3466833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_3466833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466833 prefixEnd_3466833 := by exact prefixLift 3466833
  have htrace : WordTrace (prefixWord ++ tailWord_3466833) baseStart_3466833 baseEnd_3466833 := by
    simpa [prefixWord, tailWord_3466833, baseEnd_3466833] using wordTrace_append hprefix tailTrace_3466833
  have hstable : (prefixWord ++ tailWord_3466833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466833).length < 2 ^ (prefixWord ++ tailWord_3466833).sum := by decide
  have hdescent : baseEnd_3466833 < baseStart_3466833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466834 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_3466834 : Nat := 118140960795 + 3466834 * 2 ^ 59
def prefixEnd_3466834 : Nat := 4983230072969 + 3 ^ 40 * 3466834 * 2
def baseEnd_3466834 : Nat := 1780152191349394229731327

theorem tailTrace_3466834 : CollatzResearch.WordTrace tailWord_3466834 prefixEnd_3466834 1780152191349394229731327 := by
  unfold tailWord_3466834
  simp only [CollatzResearch.WordTrace]
  refine ⟨31611455980564995238441889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84297215948173320635845037 31611455980564995238441889)
  ·
    refine ⟨23708591985423746428831417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31611455980564995238441889 23708591985423746428831417)
    ·
      refine ⟨17781443989067809821623563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23708591985423746428831417 17781443989067809821623563)
      ·
        refine ⟨26672165983601714732435345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17781443989067809821623563 26672165983601714732435345)
        ·
          refine ⟨20004124487701286049326509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26672165983601714732435345 20004124487701286049326509)
          ·
            refine ⟨7501546682887982268497441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20004124487701286049326509 7501546682887982268497441)
            ·
              refine ⟨5626160012165986701373081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7501546682887982268497441 5626160012165986701373081)
              ·
                refine ⟨4219620009124490026029811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5626160012165986701373081 4219620009124490026029811)
                ·
                  refine ⟨6329430013686735039044717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219620009124490026029811 6329430013686735039044717)
                  ·
                    refine ⟨2373536255132525639641769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6329430013686735039044717 2373536255132525639641769)
                    ·
                      refine ⟨1780152191349394229731327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373536255132525639641769 1780152191349394229731327)
                      ·
                        rfl

theorem cell23_3466834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_3466834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466834 prefixEnd_3466834 := by exact prefixLift 3466834
  have htrace : WordTrace (prefixWord ++ tailWord_3466834) baseStart_3466834 baseEnd_3466834 := by
    simpa [prefixWord, tailWord_3466834, baseEnd_3466834] using wordTrace_append hprefix tailTrace_3466834
  have hstable : (prefixWord ++ tailWord_3466834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466834).length < 2 ^ (prefixWord ++ tailWord_3466834).sum := by decide
  have hdescent : baseEnd_3466834 < baseStart_3466834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466881 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_3466881 : Nat := 118140960795 + 3466881 * 2 ^ 59
def prefixEnd_3466881 : Nat := 4983230072969 + 3 ^ 40 * 3466881 * 2
def baseEnd_3466881 : Nat := 1780176324940155545843611

theorem tailTrace_3466881 : CollatzResearch.WordTrace tailWord_3466881 prefixEnd_3466881 1780176324940155545843611 := by
  unfold tailWord_3466881
  simp only [CollatzResearch.WordTrace]
  refine ⟨126447538153089707980728497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84298358768726471987152331 126447538153089707980728497)
  ·
    refine ⟨94835653614817280985546373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126447538153089707980728497 94835653614817280985546373)
    ·
      refine ⟨17781685052778240184789945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94835653614817280985546373 17781685052778240184789945)
      ·
        refine ⟨13336263789583680138592459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17781685052778240184789945 13336263789583680138592459)
        ·
          refine ⟨20004395684375520207888689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13336263789583680138592459 20004395684375520207888689)
          ·
            refine ⟨15003296763281640155916517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20004395684375520207888689 15003296763281640155916517)
            ·
              refine ⟨2813118143115307529234347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15003296763281640155916517 2813118143115307529234347)
              ·
                refine ⟨4219677214672961293851521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2813118143115307529234347 4219677214672961293851521)
                ·
                  refine ⟨3164757911004720970388641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4219677214672961293851521 3164757911004720970388641)
                  ·
                    refine ⟨2373568433253540727791481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3164757911004720970388641 2373568433253540727791481)
                    ·
                      refine ⟨1780176324940155545843611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373568433253540727791481 1780176324940155545843611)
                      ·
                        rfl

theorem cell23_3466881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_3466881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466881 prefixEnd_3466881 := by exact prefixLift 3466881
  have htrace : WordTrace (prefixWord ++ tailWord_3466881) baseStart_3466881 baseEnd_3466881 := by
    simpa [prefixWord, tailWord_3466881, baseEnd_3466881] using wordTrace_append hprefix tailTrace_3466881
  have hstable : (prefixWord ++ tailWord_3466881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466881).length < 2 ^ (prefixWord ++ tailWord_3466881).sum := by decide
  have hdescent : baseEnd_3466881 < baseStart_3466881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466883 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 6, 5]
def baseStart_3466883 : Nat := 118140960795 + 3466883 * 2 ^ 59
def prefixEnd_3466883 : Nat := 4983230072969 + 3 ^ 40 * 3466883 * 2
def baseEnd_3466883 : Nat := 593392450633821512672867

theorem tailTrace_3466883 : CollatzResearch.WordTrace tailWord_3466883 prefixEnd_3466883 593392450633821512672867 := by
  unfold tailWord_3466883
  simp only [CollatzResearch.WordTrace]
  refine ⟨126447611099082462322301303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84298407399388308214867535 126447611099082462322301303)
  ·
    refine ⟨189671416648623693483451955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126447611099082462322301303 189671416648623693483451955)
    ·
      refine ⟨284507124972935540225177933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189671416648623693483451955 284507124972935540225177933)
      ·
        refine ⟨106690171864850827584441725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284507124972935540225177933 106690171864850827584441725)
        ·
          refine ⟨40008814449319060344165647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106690171864850827584441725 40008814449319060344165647)
          ·
            refine ⟨60013221673978590516248471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40008814449319060344165647 60013221673978590516248471)
            ·
              refine ⟨90019832510967885774372707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60013221673978590516248471 90019832510967885774372707)
              ·
                refine ⟨135029748766451828661559061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90019832510967885774372707 135029748766451828661559061)
                ·
                  refine ⟨6329519473427429468510581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135029748766451828661559061 6329519473427429468510581)
                  ·
                    refine ⟨593392450633821512672867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6329519473427429468510581 593392450633821512672867)
                    ·
                      rfl

theorem cell23_3466883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 5].length) (baseStart_3466883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466883 prefixEnd_3466883 := by exact prefixLift 3466883
  have htrace : WordTrace (prefixWord ++ tailWord_3466883) baseStart_3466883 baseEnd_3466883 := by
    simpa [prefixWord, tailWord_3466883, baseEnd_3466883] using wordTrace_append hprefix tailTrace_3466883
  have hstable : (prefixWord ++ tailWord_3466883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466883).length < 2 ^ (prefixWord ++ tailWord_3466883).sum := by decide
  have hdescent : baseEnd_3466883 < baseStart_3466883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466954 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_3466954 : Nat := 118140960795 + 3466954 * 2 ^ 59
def prefixEnd_3466954 : Nat := 4983230072969 + 3 ^ 40 * 3466954 * 2
def baseEnd_3466954 : Nat := 1780213809027933760230775

theorem tailTrace_3466954 : CollatzResearch.WordTrace tailWord_3466954 prefixEnd_3466954 1780213809027933760230775 := by
  unfold tailWord_3466954
  simp only [CollatzResearch.WordTrace]
  refine ⟨31612550170456310362033979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84300133787883494298757277 31612550170456310362033979)
  ·
    refine ⟨47418825255684465543050969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31612550170456310362033979 47418825255684465543050969)
    ·
      refine ⟨35564118941763349157288227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47418825255684465543050969 35564118941763349157288227)
      ·
        refine ⟨53346178412645023735932341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35564118941763349157288227 53346178412645023735932341)
        ·
          refine ⟨5001204226185470975243657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53346178412645023735932341 5001204226185470975243657)
          ·
            refine ⟨3750903169639103231432743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5001204226185470975243657 3750903169639103231432743)
            ·
              refine ⟨5626354754458654847149115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3750903169639103231432743 5626354754458654847149115)
              ·
                refine ⟨8439532131687982270723673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626354754458654847149115 8439532131687982270723673)
                ·
                  refine ⟨6329649098765986703042755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8439532131687982270723673 6329649098765986703042755)
                  ·
                    refine ⟨9494473648148980054564133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6329649098765986703042755 9494473648148980054564133)
                    ·
                      refine ⟨1780213809027933760230775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9494473648148980054564133 1780213809027933760230775)
                      ·
                        rfl

theorem cell23_3466954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_3466954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466954 prefixEnd_3466954 := by exact prefixLift 3466954
  have htrace : WordTrace (prefixWord ++ tailWord_3466954) baseStart_3466954 baseEnd_3466954 := by
    simpa [prefixWord, tailWord_3466954, baseEnd_3466954] using wordTrace_append hprefix tailTrace_3466954
  have hstable : (prefixWord ++ tailWord_3466954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466954).length < 2 ^ (prefixWord ++ tailWord_3466954).sum := by decide
  have hdescent : baseEnd_3466954 < baseStart_3466954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3466987 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 3]
def baseStart_3466987 : Nat := 118140960795 + 3466987 * 2 ^ 59
def prefixEnd_3466987 : Nat := 4983230072969 + 3 ^ 40 * 3466987 * 2
def baseEnd_3466987 : Nat := 1780230753889532131118123

theorem tailTrace_3466987 : CollatzResearch.WordTrace tailWord_3466987 prefixEnd_3466987 1780230753889532131118123 := by
  unfold tailWord_3466987
  simp only [CollatzResearch.WordTrace]
  refine ⟨126451404290705688084087215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84300936193803792056058143 126451404290705688084087215)
  ·
    refine ⟨189677106436058532126130823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126451404290705688084087215 189677106436058532126130823)
    ·
      refine ⟨284515659654087798189196235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189677106436058532126130823 284515659654087798189196235)
      ·
        refine ⟨426773489481131697283794353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284515659654087798189196235 426773489481131697283794353)
        ·
          refine ⟨320080117110848772962845765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426773489481131697283794353 320080117110848772962845765)
          ·
            refine ⟨60015021958284144930533581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320080117110848772962845765 60015021958284144930533581)
            ·
              refine ⟨22505633234356554348950093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60015021958284144930533581 22505633234356554348950093)
              ·
                refine ⟨8439612462883707880856285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22505633234356554348950093 8439612462883707880856285)
                ·
                  refine ⟨3164854673581390455321107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8439612462883707880856285 3164854673581390455321107)
                  ·
                    refine ⟨4747282010372085682981661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3164854673581390455321107 4747282010372085682981661)
                    ·
                      refine ⟨1780230753889532131118123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4747282010372085682981661 1780230753889532131118123)
                      ·
                        rfl

theorem cell23_3466987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 3].length) (baseStart_3466987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3466987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3466987 prefixEnd_3466987 := by exact prefixLift 3466987
  have htrace : WordTrace (prefixWord ++ tailWord_3466987) baseStart_3466987 baseEnd_3466987 := by
    simpa [prefixWord, tailWord_3466987, baseEnd_3466987] using wordTrace_append hprefix tailTrace_3466987
  have hstable : (prefixWord ++ tailWord_3466987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3466987).length < 2 ^ (prefixWord ++ tailWord_3466987).sum := by decide
  have hdescent : baseEnd_3466987 < baseStart_3466987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3466987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467020 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_3467020 : Nat := 118140960795 + 3467020 * 2 ^ 59
def prefixEnd_3467020 : Nat := 4983230072969 + 3 ^ 40 * 3467020 * 2
def baseEnd_3467020 : Nat := 593415899583710167335157

theorem tailTrace_3467020 : CollatzResearch.WordTrace tailWord_3467020 prefixEnd_3467020 593415899583710167335157 := by
  unfold tailWord_3467020
  simp only [CollatzResearch.WordTrace]
  refine ⟨63226303949793067360019257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84301738599724089813359009 63226303949793067360019257)
  ·
    refine ⟨47419727962344800520014443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63226303949793067360019257 47419727962344800520014443)
    ·
      refine ⟨71129591943517200780021665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47419727962344800520014443 71129591943517200780021665)
      ·
        refine ⟨53347193957637900585016249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71129591943517200780021665 53347193957637900585016249)
        ·
          refine ⟨40010395468228425438762187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53347193957637900585016249 40010395468228425438762187)
          ·
            refine ⟨60015593202342638158143281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40010395468228425438762187 60015593202342638158143281)
            ·
              refine ⟨45011694901756978618607461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60015593202342638158143281 45011694901756978618607461)
              ·
                refine ⟨8439692794079433490988899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45011694901756978618607461 8439692794079433490988899)
                ·
                  refine ⟨12659539191119150236483349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8439692794079433490988899 12659539191119150236483349)
                  ·
                    refine ⟨593415899583710167335157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12659539191119150236483349 593415899583710167335157)
                    ·
                      rfl

theorem cell23_3467020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_3467020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467020 prefixEnd_3467020 := by exact prefixLift 3467020
  have htrace : WordTrace (prefixWord ++ tailWord_3467020) baseStart_3467020 baseEnd_3467020 := by
    simpa [prefixWord, tailWord_3467020, baseEnd_3467020] using wordTrace_append hprefix tailTrace_3467020
  have hstable : (prefixWord ++ tailWord_3467020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467020).length < 2 ^ (prefixWord ++ tailWord_3467020).sum := by decide
  have hdescent : baseEnd_3467020 < baseStart_3467020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467040 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3467040 : Nat := 118140960795 + 3467040 * 2 ^ 59
def prefixEnd_3467040 : Nat := 4983230072969 + 3 ^ 40 * 3467040 * 2
def baseEnd_3467040 : Nat := 1780257968364220423755379

theorem tailTrace_3467040 : CollatzResearch.WordTrace tailWord_3467040 prefixEnd_3467040 1780257968364220423755379 := by
  unfold tailWord_3467040
  simp only [CollatzResearch.WordTrace]
  refine ⟨63226668679756839067883287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84302224906342452090511049 63226668679756839067883287)
  ·
    refine ⟨94840003019635258601824931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63226668679756839067883287 94840003019635258601824931)
    ·
      refine ⟨142260004529452887902737397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94840003019635258601824931 142260004529452887902737397)
      ·
        refine ⟨13336875424636208240881631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142260004529452887902737397 13336875424636208240881631)
        ·
          refine ⟨20005313136954312361322447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13336875424636208240881631 20005313136954312361322447)
          ·
            refine ⟨30007969705431468541983671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20005313136954312361322447 30007969705431468541983671)
            ·
              refine ⟨45011954558147202812975507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30007969705431468541983671 45011954558147202812975507)
              ·
                refine ⟨67517931837220804219463261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45011954558147202812975507 67517931837220804219463261)
                ·
                  refine ⟨25319224438957801582298723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67517931837220804219463261 25319224438957801582298723)
                  ·
                    refine ⟨37978836658436702373448085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25319224438957801582298723 37978836658436702373448085)
                    ·
                      refine ⟨1780257968364220423755379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37978836658436702373448085 1780257968364220423755379)
                      ·
                        rfl

theorem cell23_3467040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3467040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467040 prefixEnd_3467040 := by exact prefixLift 3467040
  have htrace : WordTrace (prefixWord ++ tailWord_3467040) baseStart_3467040 baseEnd_3467040 := by
    simpa [prefixWord, tailWord_3467040, baseEnd_3467040] using wordTrace_append hprefix tailTrace_3467040
  have hstable : (prefixWord ++ tailWord_3467040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467040).length < 2 ^ (prefixWord ++ tailWord_3467040).sum := by decide
  have hdescent : baseEnd_3467040 < baseStart_3467040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467061 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_3467061 : Nat := 118140960795 + 3467061 * 2 ^ 59
def prefixEnd_3467061 : Nat := 4983230072969 + 3 ^ 40 * 3467061 * 2
def baseEnd_3467061 : Nat := 1780268751457964841592783

theorem tailTrace_3467061 : CollatzResearch.WordTrace tailWord_3467061 prefixEnd_3467061 1780268751457964841592783 := by
  unfold tailWord_3467061
  simp only [CollatzResearch.WordTrace]
  refine ⟨126454103292437598722281037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84302735528291732481520691 126454103292437598722281037)
  ·
    refine ⟨47420288734664099520855389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126454103292437598722281037 47420288734664099520855389)
    ·
      refine ⟨17782608275499037320320771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47420288734664099520855389 17782608275499037320320771)
      ·
        refine ⟨26673912413248555980481157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17782608275499037320320771 26673912413248555980481157)
        ·
          refine ⟨5001358577484104246340217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26673912413248555980481157 5001358577484104246340217)
          ·
            refine ⟨3751018933113078184755163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5001358577484104246340217 3751018933113078184755163)
            ·
              refine ⟨5626528399669617277132745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751018933113078184755163 5626528399669617277132745)
              ·
                refine ⟨4219896299752212957849559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5626528399669617277132745 4219896299752212957849559)
                ·
                  refine ⟨6329844449628319436774339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219896299752212957849559 6329844449628319436774339)
                  ·
                    refine ⟨9494766674442479155161509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6329844449628319436774339 9494766674442479155161509)
                    ·
                      refine ⟨1780268751457964841592783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9494766674442479155161509 1780268751457964841592783)
                      ·
                        rfl

theorem cell23_3467061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_3467061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467061 prefixEnd_3467061 := by exact prefixLift 3467061
  have htrace : WordTrace (prefixWord ++ tailWord_3467061) baseStart_3467061 baseEnd_3467061 := by
    simpa [prefixWord, tailWord_3467061, baseEnd_3467061] using wordTrace_append hprefix tailTrace_3467061
  have hstable : (prefixWord ++ tailWord_3467061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467061).length < 2 ^ (prefixWord ++ tailWord_3467061).sum := by decide
  have hdescent : baseEnd_3467061 < baseStart_3467061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467064 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 1, 2, 3]
def baseStart_3467064 : Nat := 118140960795 + 3467064 * 2 ^ 59
def prefixEnd_3467064 : Nat := 4983230072969 + 3 ^ 40 * 3467064 * 2
def baseEnd_3467064 : Nat := 1780270291899928329855269

theorem tailTrace_3467064 : CollatzResearch.WordTrace tailWord_3467064 prefixEnd_3467064 1780270291899928329855269 := by
  unfold tailWord_3467064
  simp only [CollatzResearch.WordTrace]
  refine ⟨63227106355713365117320123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84302808474284486823093497 63227106355713365117320123)
  ·
    refine ⟨94840659533570047675980185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63227106355713365117320123 94840659533570047675980185)
    ·
      refine ⟨71130494650177535756985139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94840659533570047675980185 71130494650177535756985139)
      ·
        refine ⟨106695741975266303635477709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71130494650177535756985139 106695741975266303635477709)
        ·
          refine ⟨40010903240724863863304141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106695741975266303635477709 40010903240724863863304141)
          ·
            refine ⟨15004088715271823948739053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40010903240724863863304141 15004088715271823948739053)
            ·
              refine ⟨5626533268226933980777145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15004088715271823948739053 5626533268226933980777145)
              ·
                refine ⟨4219899951170200485582859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5626533268226933980777145 4219899951170200485582859)
                ·
                  refine ⟨6329849926755300728374289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4219899951170200485582859 6329849926755300728374289)
                  ·
                    refine ⟨4747387445066475546280717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6329849926755300728374289 4747387445066475546280717)
                    ·
                      refine ⟨1780270291899928329855269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4747387445066475546280717 1780270291899928329855269)
                      ·
                        rfl

theorem cell23_3467064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_3467064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467064 prefixEnd_3467064 := by exact prefixLift 3467064
  have htrace : WordTrace (prefixWord ++ tailWord_3467064) baseStart_3467064 baseEnd_3467064 := by
    simpa [prefixWord, tailWord_3467064, baseEnd_3467064] using wordTrace_append hprefix tailTrace_3467064
  have hstable : (prefixWord ++ tailWord_3467064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467064).length < 2 ^ (prefixWord ++ tailWord_3467064).sum := by decide
  have hdescent : baseEnd_3467064 < baseStart_3467064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467077 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_3467077 : Nat := 118140960795 + 3467077 * 2 ^ 59
def prefixEnd_3467077 : Nat := 4983230072969 + 3 ^ 40 * 3467077 * 2
def baseEnd_3467077 : Nat := 1780276967148436778992709

theorem tailTrace_3467077 : CollatzResearch.WordTrace tailWord_3467077 prefixEnd_3467077 1780276967148436778992709 := by
  unfold tailWord_3467077
  simp only [CollatzResearch.WordTrace]
  refine ⟨126454686860379633454863485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84303124573586422303242323 126454686860379633454863485)
  ·
    refine ⟨47420507572642362545573807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126454686860379633454863485 47420507572642362545573807)
    ·
      refine ⟨71130761358963543818360711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47420507572642362545573807 71130761358963543818360711)
      ·
        refine ⟨106696142038445315727541067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71130761358963543818360711 106696142038445315727541067)
        ·
          refine ⟨160044213057667973591311601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106696142038445315727541067 160044213057667973591311601)
          ·
            refine ⟨120033159793250980193483701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160044213057667973591311601 120033159793250980193483701)
            ·
              refine ⟨11253108730617279393139097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120033159793250980193483701 11253108730617279393139097)
              ·
                refine ⟨8439831547962959544854323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11253108730617279393139097 8439831547962959544854323)
                ·
                  refine ⟨12659747321944439317281485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8439831547962959544854323 12659747321944439317281485)
                  ·
                    refine ⟨4747405245729164743980557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12659747321944439317281485 4747405245729164743980557)
                    ·
                      refine ⟨1780276967148436778992709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4747405245729164743980557 1780276967148436778992709)
                      ·
                        rfl

theorem cell23_3467077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_3467077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467077 prefixEnd_3467077 := by exact prefixLift 3467077
  have htrace : WordTrace (prefixWord ++ tailWord_3467077) baseStart_3467077 baseEnd_3467077 := by
    simpa [prefixWord, tailWord_3467077, baseEnd_3467077] using wordTrace_append hprefix tailTrace_3467077
  have hstable : (prefixWord ++ tailWord_3467077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467077).length < 2 ^ (prefixWord ++ tailWord_3467077).sum := by decide
  have hdescent : baseEnd_3467077 < baseStart_3467077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467104 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 3, 3, 2]
def baseStart_3467104 : Nat := 118140960795 + 3467104 * 2 ^ 59
def prefixEnd_3467104 : Nat := 4983230072969 + 3 ^ 40 * 3467104 * 2
def baseEnd_3467104 : Nat := 1780290831126108173355085

theorem tailTrace_3467104 : CollatzResearch.WordTrace tailWord_3467104 prefixEnd_3467104 1780290831126108173355085 := by
  unfold tailWord_3467104
  simp only [CollatzResearch.WordTrace]
  refine ⟨63227835815640908533048183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84303781087521211377397577 63227835815640908533048183)
  ·
    refine ⟨94841753723461362799572275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63227835815640908533048183 94841753723461362799572275)
    ·
      refine ⟨142262630585192044199358413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94841753723461362799572275 142262630585192044199358413)
      ·
        refine ⟨53348486469447016574759405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142262630585192044199358413 53348486469447016574759405)
        ·
          refine ⟨20005682426042631215534777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53348486469447016574759405 20005682426042631215534777)
          ·
            refine ⟨15004261819531973411651083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20005682426042631215534777 15004261819531973411651083)
            ·
              refine ⟨22506392729297960117476625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15004261819531973411651083 22506392729297960117476625)
              ·
                refine ⟨16879794546973470088107469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22506392729297960117476625 16879794546973470088107469)
                ·
                  refine ⟨6329922955115051283040301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16879794546973470088107469 6329922955115051283040301)
                  ·
                    refine ⟨2373721108168144231140113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6329922955115051283040301 2373721108168144231140113)
                    ·
                      refine ⟨1780290831126108173355085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373721108168144231140113 1780290831126108173355085)
                      ·
                        rfl

theorem cell23_3467104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_3467104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467104 prefixEnd_3467104 := by exact prefixLift 3467104
  have htrace : WordTrace (prefixWord ++ tailWord_3467104) baseStart_3467104 baseEnd_3467104 := by
    simpa [prefixWord, tailWord_3467104, baseEnd_3467104] using wordTrace_append hprefix tailTrace_3467104
  have hstable : (prefixWord ++ tailWord_3467104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467104).length < 2 ^ (prefixWord ++ tailWord_3467104).sum := by decide
  have hdescent : baseEnd_3467104 < baseStart_3467104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467157 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 7]
def baseStart_3467157 : Nat := 118140960795 + 3467157 * 2 ^ 59
def prefixEnd_3467157 : Nat := 4983230072969 + 3 ^ 40 * 3467157 * 2
def baseEnd_3467157 : Nat := 197813116177866273999149

theorem tailTrace_3467157 : CollatzResearch.WordTrace tailWord_3467157 prefixEnd_3467157 197813116177866273999149 := by
  unfold tailWord_3467157
  simp only [CollatzResearch.WordTrace]
  refine ⟨126457604700089807117775725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84305069800059871411850483 126457604700089807117775725)
  ·
    refine ⟨47421601762533677669165897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126457604700089807117775725 47421601762533677669165897)
    ·
      refine ⟨35566201321900258251874423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47421601762533677669165897 35566201321900258251874423)
      ·
        refine ⟨53349301982850387377811635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35566201321900258251874423 53349301982850387377811635)
        ·
          refine ⟨80023952974275581066717453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53349301982850387377811635 80023952974275581066717453)
          ·
            refine ⟨30008982365353342900019045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80023952974275581066717453 30008982365353342900019045)
            ·
              refine ⟨5626684193503751793753571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30008982365353342900019045 5626684193503751793753571)
              ·
                refine ⟨8440026290255627690630357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5626684193503751793753571 8440026290255627690630357)
                ·
                  refine ⟨197813116177866273999149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8440026290255627690630357 197813116177866273999149)
                  ·
                    rfl

theorem cell23_3467157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_3467157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467157 prefixEnd_3467157 := by exact prefixLift 3467157
  have htrace : WordTrace (prefixWord ++ tailWord_3467157) baseStart_3467157 baseEnd_3467157 := by
    simpa [prefixWord, tailWord_3467157, baseEnd_3467157] using wordTrace_append hprefix tailTrace_3467157
  have hstable : (prefixWord ++ tailWord_3467157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467157).length < 2 ^ (prefixWord ++ tailWord_3467157).sum := by decide
  have hdescent : baseEnd_3467157 < baseStart_3467157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467164 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3467164 : Nat := 118140960795 + 3467164 * 2 ^ 59
def prefixEnd_3467164 : Nat := 4983230072969 + 3 ^ 40 * 3467164 * 2
def baseEnd_3467164 : Nat := 1780321639965377938604809

theorem tailTrace_3467164 : CollatzResearch.WordTrace tailWord_3467164 prefixEnd_3467164 1780321639965377938604809 := by
  unfold tailWord_3467164
  simp only [CollatzResearch.WordTrace]
  refine ⟨63228930005532223656640273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84305240007376298208853697 63228930005532223656640273)
  ·
    refine ⟨47421697504149167742480205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63228930005532223656640273 47421697504149167742480205)
    ·
      refine ⟨17783136564055937903430077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47421697504149167742480205 17783136564055937903430077)
      ·
        refine ⟨6668676211520976713786279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17783136564055937903430077 6668676211520976713786279)
        ·
          refine ⟨10003014317281465070679419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6668676211520976713786279 10003014317281465070679419)
          ·
            refine ⟨15004521475922197606019129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10003014317281465070679419 15004521475922197606019129)
            ·
              refine ⟨11253391106941648204514347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15004521475922197606019129 11253391106941648204514347)
              ·
                refine ⟨16880086660412472306771521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11253391106941648204514347 16880086660412472306771521)
                ·
                  refine ⟨12660064995309354230078641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16880086660412472306771521 12660064995309354230078641)
                  ·
                    refine ⟨9495048746482015672558981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12660064995309354230078641 9495048746482015672558981)
                    ·
                      refine ⟨1780321639965377938604809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9495048746482015672558981 1780321639965377938604809)
                      ·
                        rfl

theorem cell23_3467164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3467164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467164 prefixEnd_3467164 := by exact prefixLift 3467164
  have htrace : WordTrace (prefixWord ++ tailWord_3467164) baseStart_3467164 baseEnd_3467164 := by
    simpa [prefixWord, tailWord_3467164, baseEnd_3467164] using wordTrace_append hprefix tailTrace_3467164
  have hstable : (prefixWord ++ tailWord_3467164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467164).length < 2 ^ (prefixWord ++ tailWord_3467164).sum := by decide
  have hdescent : baseEnd_3467164 < baseStart_3467164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467187 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 2, 5]
def baseStart_3467187 : Nat := 118140960795 + 3467187 * 2 ^ 59
def prefixEnd_3467187 : Nat := 4983230072969 + 3 ^ 40 * 3467187 * 2
def baseEnd_3467187 : Nat := 593444483340143782872401

theorem tailTrace_3467187 : CollatzResearch.WordTrace tailWord_3467187 prefixEnd_3467187 593444483340143782872401 := by
  unfold tailWord_3467187
  simp only [CollatzResearch.WordTrace]
  refine ⟨126458698889981122241367815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84305799259987414827578543 126458698889981122241367815)
  ·
    refine ⟨189688048334971683362051723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126458698889981122241367815 189688048334971683362051723)
    ·
      refine ⟨284532072502457525043077585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189688048334971683362051723 284532072502457525043077585)
      ·
        refine ⟨213399054376843143782308189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284532072502457525043077585 213399054376843143782308189)
        ·
          refine ⟨80024645391316178918365571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213399054376843143782308189 80024645391316178918365571)
          ·
            refine ⟨120036968086974268377548357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80024645391316178918365571 120036968086974268377548357)
            ·
              refine ⟨22506931516307675320790317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120036968086974268377548357 22506931516307675320790317)
              ·
                refine ⟨8440099318615378245296369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22506931516307675320790317 8440099318615378245296369)
                ·
                  refine ⟨6330074488961533683972277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8440099318615378245296369 6330074488961533683972277)
                  ·
                    refine ⟨593444483340143782872401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6330074488961533683972277 593444483340143782872401)
                    ·
                      rfl

theorem cell23_3467187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 5].length) (baseStart_3467187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467187 prefixEnd_3467187 := by exact prefixLift 3467187
  have htrace : WordTrace (prefixWord ++ tailWord_3467187) baseStart_3467187 baseEnd_3467187 := by
    simpa [prefixWord, tailWord_3467187, baseEnd_3467187] using wordTrace_append hprefix tailTrace_3467187
  have hstable : (prefixWord ++ tailWord_3467187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467187).length < 2 ^ (prefixWord ++ tailWord_3467187).sum := by decide
  have hdescent : baseEnd_3467187 < baseStart_3467187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467224 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 1, 6, 2]
def baseStart_3467224 : Nat := 118140960795 + 3467224 * 2 ^ 59
def prefixEnd_3467224 : Nat := 4983230072969 + 3 ^ 40 * 3467224 * 2
def baseEnd_3467224 : Nat := 1780352448804647703854533

theorem tailTrace_3467224 : CollatzResearch.WordTrace tailWord_3467224 prefixEnd_3467224 1780352448804647703854533 := by
  unfold tailWord_3467224
  simp only [CollatzResearch.WordTrace]
  refine ⟨63230024195423538780232363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84306698927231385040309817 63230024195423538780232363)
  ·
    refine ⟨94845036293135308170348545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63230024195423538780232363 94845036293135308170348545)
    ·
      refine ⟨71133777219851481127761409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94845036293135308170348545 71133777219851481127761409)
      ·
        refine ⟨53350332914888610845821057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71133777219851481127761409 53350332914888610845821057)
        ·
          refine ⟨40012749686166458134365793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53350332914888610845821057 40012749686166458134365793)
          ·
            refine ⟨30009562264624843600774345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40012749686166458134365793 30009562264624843600774345)
            ·
              refine ⟨22507171698468632700580759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30009562264624843600774345 22507171698468632700580759)
              ·
                refine ⟨33760757547702949050871139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22507171698468632700580759 33760757547702949050871139)
                ·
                  refine ⟨50641136321554423576306709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33760757547702949050871139 50641136321554423576306709)
                  ·
                    refine ⟨2373803265072863605139377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50641136321554423576306709 2373803265072863605139377)
                    ·
                      refine ⟨1780352448804647703854533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373803265072863605139377 1780352448804647703854533)
                      ·
                        rfl

theorem cell23_3467224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_3467224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467224 prefixEnd_3467224 := by exact prefixLift 3467224
  have htrace : WordTrace (prefixWord ++ tailWord_3467224) baseStart_3467224 baseEnd_3467224 := by
    simpa [prefixWord, tailWord_3467224, baseEnd_3467224] using wordTrace_append hprefix tailTrace_3467224
  have hstable : (prefixWord ++ tailWord_3467224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467224).length < 2 ^ (prefixWord ++ tailWord_3467224).sum := by decide
  have hdescent : baseEnd_3467224 < baseStart_3467224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467301 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 1, 5, 2]
def baseStart_3467301 : Nat := 118140960795 + 3467301 * 2 ^ 59
def prefixEnd_3467301 : Nat := 4983230072969 + 3 ^ 40 * 3467301 * 2
def baseEnd_3467301 : Nat := 1780391986815043902591679

theorem tailTrace_3467301 : CollatzResearch.WordTrace tailWord_3467301 prefixEnd_3467301 1780391986815043902591679 := by
  unfold tailWord_3467301
  simp only [CollatzResearch.WordTrace]
  refine ⟨126462856811568119711017757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84308571207712079807345171 126462856811568119711017757)
  ·
    refine ⟨47423571304338044891631659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126462856811568119711017757 47423571304338044891631659)
    ·
      refine ⟨71135356956507067337447489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47423571304338044891631659 71135356956507067337447489)
      ·
        refine ⟨53351517717380300503085617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71135356956507067337447489 53351517717380300503085617)
        ·
          refine ⟨40013638288035225377314213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53351517717380300503085617 40013638288035225377314213)
          ·
            refine ⟨7502557179006604758246415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40013638288035225377314213 7502557179006604758246415)
            ·
              refine ⟨11253835768509907137369623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502557179006604758246415 11253835768509907137369623)
              ·
                refine ⟨16880753652764860706054435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11253835768509907137369623 16880753652764860706054435)
                ·
                  refine ⟨25321130479147291059081653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16880753652764860706054435 25321130479147291059081653)
                  ·
                    refine ⟨2373855982420058536788905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25321130479147291059081653 2373855982420058536788905)
                    ·
                      refine ⟨1780391986815043902591679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373855982420058536788905 1780391986815043902591679)
                      ·
                        rfl

theorem cell23_3467301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_3467301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467301 prefixEnd_3467301 := by exact prefixLift 3467301
  have htrace : WordTrace (prefixWord ++ tailWord_3467301) baseStart_3467301 baseEnd_3467301 := by
    simpa [prefixWord, tailWord_3467301, baseEnd_3467301] using wordTrace_append hprefix tailTrace_3467301
  have hstable : (prefixWord ++ tailWord_3467301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467301).length < 2 ^ (prefixWord ++ tailWord_3467301).sum := by decide
  have hdescent : baseEnd_3467301 < baseStart_3467301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467307 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 3, 6]
def baseStart_3467307 : Nat := 118140960795 + 3467307 * 2 ^ 59
def prefixEnd_3467307 : Nat := 4983230072969 + 3 ^ 40 * 3467307 * 2
def baseEnd_3467307 : Nat := 593465022566323626372217

theorem tailTrace_3467307 : CollatzResearch.WordTrace tailWord_3467307 prefixEnd_3467307 593465022566323626372217 := by
  unfold tailWord_3467307
  simp only [CollatzResearch.WordTrace]
  refine ⟨126463075649546382735736175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84308717099697588490490783 126463075649546382735736175)
  ·
    refine ⟨189694613474319574103604263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126463075649546382735736175 189694613474319574103604263)
    ·
      refine ⟨284541920211479361155406395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189694613474319574103604263 284541920211479361155406395)
      ·
        refine ⟨426812880317219041733109593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284541920211479361155406395 426812880317219041733109593)
        ·
          refine ⟨320109660237914281299832195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426812880317219041733109593 320109660237914281299832195)
          ·
            refine ⟨480164490356871421949748293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320109660237914281299832195 480164490356871421949748293)
            ·
              refine ⟨90030841941913391615577805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 480164490356871421949748293 90030841941913391615577805)
              ·
                refine ⟨33761565728217521855841677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90030841941913391615577805 33761565728217521855841677)
                ·
                  refine ⟨12660587148081570695940629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33761565728217521855841677 12660587148081570695940629)
                  ·
                    refine ⟨593465022566323626372217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12660587148081570695940629 593465022566323626372217)
                    ·
                      rfl

theorem cell23_3467307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 6].length) (baseStart_3467307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467307 prefixEnd_3467307 := by exact prefixLift 3467307
  have htrace : WordTrace (prefixWord ++ tailWord_3467307) baseStart_3467307 baseEnd_3467307 := by
    simpa [prefixWord, tailWord_3467307, baseEnd_3467307] using wordTrace_append hprefix tailTrace_3467307
  have hstable : (prefixWord ++ tailWord_3467307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467307).length < 2 ^ (prefixWord ++ tailWord_3467307).sum := by decide
  have hdescent : baseEnd_3467307 < baseStart_3467307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467318 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_3467318 : Nat := 118140960795 + 3467318 * 2 ^ 59
def prefixEnd_3467318 : Nat := 4983230072969 + 3 ^ 40 * 3467318 * 2
def baseEnd_3467318 : Nat := 1780400715986170336079101

theorem tailTrace_3467318 : CollatzResearch.WordTrace tailWord_3467318 prefixEnd_3467318 1780400715986170336079101 := by
  unfold tailWord_3467318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7903967303281658225899163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84308984568337687742924405 7903967303281658225899163)
  ·
    refine ⟨11855950954922487338848745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7903967303281658225899163 11855950954922487338848745)
    ·
      refine ⟨8891963216191865504136559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11855950954922487338848745 8891963216191865504136559)
      ·
        refine ⟨13337944824287798256204839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8891963216191865504136559 13337944824287798256204839)
        ·
          refine ⟨20006917236431697384307259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13337944824287798256204839 20006917236431697384307259)
          ·
            refine ⟨30010375854647546076460889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20006917236431697384307259 30010375854647546076460889)
            ·
              refine ⟨22507781890985659557345667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30010375854647546076460889 22507781890985659557345667)
              ·
                refine ⟨33761672836478489336018501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22507781890985659557345667 33761672836478489336018501)
                ·
                  refine ⟨6330313656839716750503469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33761672836478489336018501 6330313656839716750503469)
                  ·
                    refine ⟨2373867621314893781438801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6330313656839716750503469 2373867621314893781438801)
                    ·
                      refine ⟨1780400715986170336079101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373867621314893781438801 1780400715986170336079101)
                      ·
                        rfl

theorem cell23_3467318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_3467318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467318 prefixEnd_3467318 := by exact prefixLift 3467318
  have htrace : WordTrace (prefixWord ++ tailWord_3467318) baseStart_3467318 baseEnd_3467318 := by
    simpa [prefixWord, tailWord_3467318, baseEnd_3467318] using wordTrace_append hprefix tailTrace_3467318
  have hstable : (prefixWord ++ tailWord_3467318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467318).length < 2 ^ (prefixWord ++ tailWord_3467318).sum := by decide
  have hdescent : baseEnd_3467318 < baseStart_3467318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467337 : List Nat := [1, 2, 1, 1, 2, 2, 4, 10]
def baseStart_3467337 : Nat := 118140960795 + 3467337 * 2 ^ 59
def prefixEnd_3467337 : Nat := 4983230072969 + 3 ^ 40 * 3467337 * 2
def baseEnd_3467337 : Nat := 65941128596985398583019

theorem tailTrace_3467337 : CollatzResearch.WordTrace tailWord_3467337 prefixEnd_3467337 65941128596985398583019 := by
  unfold tailWord_3467337
  simp only [CollatzResearch.WordTrace]
  refine ⟨126464169839437697859328265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84309446559625131906218843 126464169839437697859328265)
  ·
    refine ⟨94848127379578273394496199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126464169839437697859328265 94848127379578273394496199)
    ·
      refine ⟨142272191069367410091744299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94848127379578273394496199 142272191069367410091744299)
      ·
        refine ⟨213408286604051115137616449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142272191069367410091744299 213408286604051115137616449)
        ·
          refine ⟨160056214953038336353212337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213408286604051115137616449 160056214953038336353212337)
          ·
            refine ⟨120042161214778752264909253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160056214953038336353212337 120042161214778752264909253)
            ·
              refine ⟨22507905227771016049670485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120042161214778752264909253 22507905227771016049670485)
              ·
                refine ⟨65941128596985398583019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22507905227771016049670485 65941128596985398583019)
                ·
                  rfl

theorem cell23_3467337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 10].length) (baseStart_3467337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467337 prefixEnd_3467337 := by exact prefixLift 3467337
  have htrace : WordTrace (prefixWord ++ tailWord_3467337) baseStart_3467337 baseEnd_3467337 := by
    simpa [prefixWord, tailWord_3467337, baseEnd_3467337] using wordTrace_append hprefix tailTrace_3467337
  have hstable : (prefixWord ++ tailWord_3467337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467337).length < 2 ^ (prefixWord ++ tailWord_3467337).sum := by decide
  have hdescent : baseEnd_3467337 < baseStart_3467337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467351 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 3]
def baseStart_3467351 : Nat := 118140960795 + 3467351 * 2 ^ 59
def prefixEnd_3467351 : Nat := 4983230072969 + 3 ^ 40 * 3467351 * 2
def baseEnd_3467351 : Nat := 1780417660847768706966449

theorem tailTrace_3467351 : CollatzResearch.WordTrace tailWord_3467351 prefixEnd_3467351 1780417660847768706966449 := by
  unfold tailWord_3467351
  simp only [CollatzResearch.WordTrace]
  refine ⟨126464680461386978250337907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84309786974257985500225271 126464680461386978250337907)
  ·
    refine ⟨189697020692080467375506861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126464680461386978250337907 189697020692080467375506861)
    ·
      refine ⟨71136382759530175265815073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189697020692080467375506861 71136382759530175265815073)
      ·
        refine ⟨53352287069647631449361305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71136382759530175265815073 53352287069647631449361305)
        ·
          refine ⟨40014215302235723587020979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53352287069647631449361305 40014215302235723587020979)
          ·
            refine ⟨60021322953353585380531469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40014215302235723587020979 60021322953353585380531469)
            ·
              refine ⟨22507996107507594517699301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60021322953353585380531469 22507996107507594517699301)
              ·
                refine ⟨4220249270157673972068619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22507996107507594517699301 4220249270157673972068619)
                ·
                  refine ⟨6330373905236510958102929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4220249270157673972068619 6330373905236510958102929)
                  ·
                    refine ⟨4747780428927383218577197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6330373905236510958102929 4747780428927383218577197)
                    ·
                      refine ⟨1780417660847768706966449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4747780428927383218577197 1780417660847768706966449)
                      ·
                        rfl

theorem cell23_3467351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_3467351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467351 prefixEnd_3467351 := by exact prefixLift 3467351
  have htrace : WordTrace (prefixWord ++ tailWord_3467351) baseStart_3467351 baseEnd_3467351 := by
    simpa [prefixWord, tailWord_3467351, baseEnd_3467351] using wordTrace_append hprefix tailTrace_3467351
  have hstable : (prefixWord ++ tailWord_3467351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467351).length < 2 ^ (prefixWord ++ tailWord_3467351).sum := by decide
  have hdescent : baseEnd_3467351 < baseStart_3467351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467382 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_3467382 : Nat := 118140960795 + 3467382 * 2 ^ 59
def prefixEnd_3467382 : Nat := 4983230072969 + 3 ^ 40 * 3467382 * 2
def baseEnd_3467382 : Nat := 1780433578748058085678807

theorem tailTrace_3467382 : CollatzResearch.WordTrace tailWord_3467382 prefixEnd_3467382 1780433578748058085678807 := by
  unfold tailWord_3467382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7904113195267166909044775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84310540749516447029810933 7904113195267166909044775)
  ·
    refine ⟨11856169792900750363567163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7904113195267166909044775 11856169792900750363567163)
    ·
      refine ⟨17784254689351125545350745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11856169792900750363567163 17784254689351125545350745)
      ·
        refine ⟨13338191017013344159013059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17784254689351125545350745 13338191017013344159013059)
        ·
          refine ⟨20007286525520016238519589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13338191017013344159013059 20007286525520016238519589)
          ·
            refine ⟨3751366223535003044722423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20007286525520016238519589 3751366223535003044722423)
            ·
              refine ⟨5627049335302504567083635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751366223535003044722423 5627049335302504567083635)
              ·
                refine ⟨8440574002953756850625453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5627049335302504567083635 8440574002953756850625453)
                ·
                  refine ⟨3165215251107658818984545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8440574002953756850625453 3165215251107658818984545)
                  ·
                    refine ⟨2373911438330744114238409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3165215251107658818984545 2373911438330744114238409)
                    ·
                      refine ⟨1780433578748058085678807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2373911438330744114238409 1780433578748058085678807)
                      ·
                        rfl

theorem cell23_3467382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_3467382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467382 prefixEnd_3467382 := by exact prefixLift 3467382
  have htrace : WordTrace (prefixWord ++ tailWord_3467382) baseStart_3467382 baseEnd_3467382 := by
    simpa [prefixWord, tailWord_3467382, baseEnd_3467382] using wordTrace_append hprefix tailTrace_3467382
  have hstable : (prefixWord ++ tailWord_3467382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467382).length < 2 ^ (prefixWord ++ tailWord_3467382).sum := by decide
  have hdescent : baseEnd_3467382 < baseStart_3467382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467531 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 3]
def baseStart_3467531 : Nat := 118140960795 + 3467531 * 2 ^ 59
def prefixEnd_3467531 : Nat := 4983230072969 + 3 ^ 40 * 3467531 * 2
def baseEnd_3467531 : Nat := 1780510087365578002715621

theorem tailTrace_3467531 : CollatzResearch.WordTrace tailWord_3467531 prefixEnd_3467531 1780510087365578002715621 := by
  unfold tailWord_3467531
  simp only [CollatzResearch.WordTrace]
  refine ⟨126471245600734868991890447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84314163733823245994593631 126471245600734868991890447)
  ·
    refine ⟨189706868401102303487835671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126471245600734868991890447 189706868401102303487835671)
    ·
      refine ⟨284560302601653455231753507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189706868401102303487835671 284560302601653455231753507)
      ·
        refine ⟨426840453902480182847630261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284560302601653455231753507 426840453902480182847630261)
        ·
          refine ⟨40016292553357517141965337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426840453902480182847630261 40016292553357517141965337)
          ·
            refine ⟨30012219415018137856474003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40016292553357517141965337 30012219415018137856474003)
            ·
              refine ⟨45018329122527206784711005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30012219415018137856474003 45018329122527206784711005)
              ·
                refine ⟨16881873420947702544266627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45018329122527206784711005 16881873420947702544266627)
                ·
                  refine ⟨25322810131421553816399941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16881873420947702544266627 25322810131421553816399941)
                  ·
                    refine ⟨4748026899641541340574989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25322810131421553816399941 4748026899641541340574989)
                    ·
                      refine ⟨1780510087365578002715621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4748026899641541340574989 1780510087365578002715621)
                      ·
                        rfl

theorem cell23_3467531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 3].length) (baseStart_3467531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467531 prefixEnd_3467531 := by exact prefixLift 3467531
  have htrace : WordTrace (prefixWord ++ tailWord_3467531) baseStart_3467531 baseEnd_3467531 := by
    simpa [prefixWord, tailWord_3467531, baseEnd_3467531] using wordTrace_append hprefix tailTrace_3467531
  have hstable : (prefixWord ++ tailWord_3467531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467531).length < 2 ^ (prefixWord ++ tailWord_3467531).sum := by decide
  have hdescent : baseEnd_3467531 < baseStart_3467531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467551 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 8]
def baseStart_3467551 : Nat := 118140960795 + 3467551 * 2 ^ 59
def prefixEnd_3467551 : Nat := 4983230072969 + 3 ^ 40 * 3467551 * 2
def baseEnd_3467551 : Nat := 197835595219851991607281

theorem tailTrace_3467551 : CollatzResearch.WordTrace tailWord_3467551 prefixEnd_3467551 197835595219851991607281 := by
  unfold tailWord_3467551
  simp only [CollatzResearch.WordTrace]
  refine ⟨126471975060662412407618507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84314650040441608271745671 126471975060662412407618507)
  ·
    refine ⟨189707962590993618611427761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126471975060662412407618507 189707962590993618611427761)
    ·
      refine ⟨142280971943245213958570821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189707962590993618611427761 142280971943245213958570821)
      ·
        refine ⟨26677682239358477617232029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142280971943245213958570821 26677682239358477617232029)
        ·
          refine ⟨10004130839759429106462011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26677682239358477617232029 10004130839759429106462011)
          ·
            refine ⟨15006196259639143659693017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10004130839759429106462011 15006196259639143659693017)
            ·
              refine ⟨11254647194729357744769763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15006196259639143659693017 11254647194729357744769763)
              ·
                refine ⟨16881970792094036617154645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11254647194729357744769763 16881970792094036617154645)
                ·
                  refine ⟨197835595219851991607281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16881970792094036617154645 197835595219851991607281)
                  ·
                    rfl

theorem cell23_3467551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 8].length) (baseStart_3467551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467551 prefixEnd_3467551 := by exact prefixLift 3467551
  have htrace : WordTrace (prefixWord ++ tailWord_3467551) baseStart_3467551 baseEnd_3467551 := by
    simpa [prefixWord, tailWord_3467551, baseEnd_3467551] using wordTrace_append hprefix tailTrace_3467551
  have hstable : (prefixWord ++ tailWord_3467551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467551).length < 2 ^ (prefixWord ++ tailWord_3467551).sum := by decide
  have hdescent : baseEnd_3467551 < baseStart_3467551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467635 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 3, 2, 2]
def baseStart_3467635 : Nat := 118140960795 + 3467635 * 2 ^ 59
def prefixEnd_3467635 : Nat := 4983230072969 + 3 ^ 40 * 3467635 * 2
def baseEnd_3467635 : Nat := 1780563489353645595815143

theorem tailTrace_3467635 : CollatzResearch.WordTrace tailWord_3467635 prefixEnd_3467635 1780563489353645595815143 := by
  unfold tailWord_3467635
  simp only [CollatzResearch.WordTrace]
  refine ⟨126475038792358094753676359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84316692528238729835784239 126475038792358094753676359)
  ·
    refine ⟨189712558188537142130514539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126475038792358094753676359 189712558188537142130514539)
    ·
      refine ⟨284568837282805713195771809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189712558188537142130514539 284568837282805713195771809)
      ·
        refine ⟨213426627962104284896828857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284568837282805713195771809 213426627962104284896828857)
        ·
          refine ⟨160069970971578213672621643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213426627962104284896828857 160069970971578213672621643)
          ·
            refine ⟨240104956457367320508932465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160069970971578213672621643 240104956457367320508932465)
            ·
              refine ⟨180078717343025490381699349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240104956457367320508932465 180078717343025490381699349)
              ·
                refine ⟨8441189875454319861642157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180078717343025490381699349 8441189875454319861642157)
                ·
                  refine ⟨3165446203295369948115809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8441189875454319861642157 3165446203295369948115809)
                  ·
                    refine ⟨2374084652471527461086857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3165446203295369948115809 2374084652471527461086857)
                    ·
                      refine ⟨1780563489353645595815143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2374084652471527461086857 1780563489353645595815143)
                      ·
                        rfl

theorem cell23_3467635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 2, 2].length) (baseStart_3467635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467635 prefixEnd_3467635 := by exact prefixLift 3467635
  have htrace : WordTrace (prefixWord ++ tailWord_3467635) baseStart_3467635 baseEnd_3467635 := by
    simpa [prefixWord, tailWord_3467635, baseEnd_3467635] using wordTrace_append hprefix tailTrace_3467635
  have hstable : (prefixWord ++ tailWord_3467635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467635).length < 2 ^ (prefixWord ++ tailWord_3467635).sum := by decide
  have hdescent : baseEnd_3467635 < baseStart_3467635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467655 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_3467655 : Nat := 118140960795 + 3467655 * 2 ^ 59
def prefixEnd_3467655 : Nat := 4983230072969 + 3 ^ 40 * 3467655 * 2
def baseEnd_3467655 : Nat := 1780573758966735517565051

theorem tailTrace_3467655 : CollatzResearch.WordTrace tailWord_3467655 prefixEnd_3467655 1780573758966735517565051 := by
  unfold tailWord_3467655
  simp only [CollatzResearch.WordTrace]
  refine ⟨126475768252285638169404419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84317178834857092112936279 126475768252285638169404419)
  ·
    refine ⟨189713652378428457254106629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126475768252285638169404419 189713652378428457254106629)
    ·
      refine ⟨35571309820955335735144993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189713652378428457254106629 35571309820955335735144993)
      ·
        refine ⟨26678482365716501801358745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35571309820955335735144993 26678482365716501801358745)
        ·
          refine ⟨20008861774287376351019059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26678482365716501801358745 20008861774287376351019059)
          ·
            refine ⟨30013292661431064526528589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20008861774287376351019059 30013292661431064526528589)
            ·
              refine ⟨11254984748036649197448221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30013292661431064526528589 11254984748036649197448221)
              ·
                refine ⟨4220619280513743449043083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11254984748036649197448221 4220619280513743449043083)
                ·
                  refine ⟨6330928920770615173564625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4220619280513743449043083 6330928920770615173564625)
                  ·
                    refine ⟨4748196690577961380173469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6330928920770615173564625 4748196690577961380173469)
                    ·
                      refine ⟨1780573758966735517565051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4748196690577961380173469 1780573758966735517565051)
                      ·
                        rfl

theorem cell23_3467655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_3467655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467655 prefixEnd_3467655 := by exact prefixLift 3467655
  have htrace : WordTrace (prefixWord ++ tailWord_3467655) baseStart_3467655 baseEnd_3467655 := by
    simpa [prefixWord, tailWord_3467655, baseEnd_3467655] using wordTrace_append hprefix tailTrace_3467655
  have hstable : (prefixWord ++ tailWord_3467655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467655).length < 2 ^ (prefixWord ++ tailWord_3467655).sum := by decide
  have hdescent : baseEnd_3467655 < baseStart_3467655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467662 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_3467662 : Nat := 118140960795 + 3467662 * 2 ^ 59
def prefixEnd_3467662 : Nat := 4983230072969 + 3 ^ 40 * 3467662 * 2
def baseEnd_3467662 : Nat := 593525784443772330059173

theorem tailTrace_3467662 : CollatzResearch.WordTrace tailWord_3467662 prefixEnd_3467662 593525784443772330059173 := by
  unfold tailWord_3467662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15809502945407534795613655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84317349042173518909939493 15809502945407534795613655)
  ·
    refine ⟨23714254418111302193420483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15809502945407534795613655 23714254418111302193420483)
    ·
      refine ⟨35571381627166953290130725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23714254418111302193420483 35571381627166953290130725)
      ·
        refine ⟨6669634055093803741899511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35571381627166953290130725 6669634055093803741899511)
        ·
          refine ⟨10004451082640705612849267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6669634055093803741899511 10004451082640705612849267)
          ·
            refine ⟨15006676623961058419273901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10004451082640705612849267 15006676623961058419273901)
            ·
              refine ⟨5627503733985396907227713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15006676623961058419273901 5627503733985396907227713)
              ·
                refine ⟨4220627800489047680420785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627503733985396907227713 4220627800489047680420785)
                ·
                  refine ⟨3165470850366785760315589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4220627800489047680420785 3165470850366785760315589)
                  ·
                    refine ⟨593525784443772330059173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165470850366785760315589 593525784443772330059173)
                    ·
                      rfl

theorem cell23_3467662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_3467662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467662 prefixEnd_3467662 := by exact prefixLift 3467662
  have htrace : WordTrace (prefixWord ++ tailWord_3467662) baseStart_3467662 baseEnd_3467662 := by
    simpa [prefixWord, tailWord_3467662, baseEnd_3467662] using wordTrace_append hprefix tailTrace_3467662
  have hstable : (prefixWord ++ tailWord_3467662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467662).length < 2 ^ (prefixWord ++ tailWord_3467662).sum := by decide
  have hdescent : baseEnd_3467662 < baseStart_3467662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467671 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 1, 9]
def baseStart_3467671 : Nat := 118140960795 + 3467671 * 2 ^ 59
def prefixEnd_3467671 : Nat := 4983230072969 + 3 ^ 40 * 3467671 * 2
def baseEnd_3467671 : Nat := 593527324885735818321659

theorem tailTrace_3467671 : CollatzResearch.WordTrace tailWord_3467671 prefixEnd_3467671 593527324885735818321659 := by
  unfold tailWord_3467671
  simp only [CollatzResearch.WordTrace]
  refine ⟨126476351820227672901986867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84317567880151781934657911 126476351820227672901986867)
  ·
    refine ⟨189714527730341509352980301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126476351820227672901986867 189714527730341509352980301)
    ·
      refine ⟨71142947898878066007367613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189714527730341509352980301 71142947898878066007367613)
      ·
        refine ⟨26678605462079274752762855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71142947898878066007367613 26678605462079274752762855)
        ·
          refine ⟨40017908193118912129144283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26678605462079274752762855 40017908193118912129144283)
          ·
            refine ⟨60026862289678368193716425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40017908193118912129144283 60026862289678368193716425)
            ·
              refine ⟨45020146717258776145287319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60026862289678368193716425 45020146717258776145287319)
              ·
                refine ⟨67530220075888164217930979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45020146717258776145287319 67530220075888164217930979)
                ·
                  refine ⟨101295330113832246326896469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67530220075888164217930979 101295330113832246326896469)
                  ·
                    refine ⟨593527324885735818321659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 101295330113832246326896469 593527324885735818321659)
                    ·
                      rfl

theorem cell23_3467671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_3467671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467671 prefixEnd_3467671 := by exact prefixLift 3467671
  have htrace : WordTrace (prefixWord ++ tailWord_3467671) baseStart_3467671 baseEnd_3467671 := by
    simpa [prefixWord, tailWord_3467671, baseEnd_3467671] using wordTrace_append hprefix tailTrace_3467671
  have hstable : (prefixWord ++ tailWord_3467671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467671).length < 2 ^ (prefixWord ++ tailWord_3467671).sum := by decide
  have hdescent : baseEnd_3467671 < baseStart_3467671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467738 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_3467738 : Nat := 118140960795 + 3467738 * 2 ^ 59
def prefixEnd_3467738 : Nat := 4983230072969 + 3 ^ 40 * 3467738 * 2
def baseEnd_3467738 : Nat := 1780616377861058692827169

theorem tailTrace_3467738 : CollatzResearch.WordTrace tailWord_3467738 prefixEnd_3467738 1780616377861058692827169 := by
  unfold tailWord_3467738
  simp only [CollatzResearch.WordTrace]
  refine ⟨31619698877746235836168967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84319197007323295563117245 31619698877746235836168967)
  ·
    refine ⟨47429548316619353754253451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31619698877746235836168967 47429548316619353754253451)
    ·
      refine ⟨71144322474929030631380177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47429548316619353754253451 71144322474929030631380177)
      ·
        refine ⟨53358241856196772973535133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71144322474929030631380177 53358241856196772973535133)
        ·
          refine ⟨20009340696073789865075675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53358241856196772973535133 20009340696073789865075675)
          ·
            refine ⟨30014011044110684797613513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20009340696073789865075675 30014011044110684797613513)
            ·
              refine ⟨22510508283083013598210135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30014011044110684797613513 22510508283083013598210135)
              ·
                refine ⟨33765762424624520397315203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22510508283083013598210135 33765762424624520397315203)
                ·
                  refine ⟨50648643636936780595972805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33765762424624520397315203 50648643636936780595972805)
                  ·
                    refine ⟨9496620681925646361744901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50648643636936780595972805 9496620681925646361744901)
                    ·
                      refine ⟨1780616377861058692827169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9496620681925646361744901 1780616377861058692827169)
                      ·
                        rfl

theorem cell23_3467738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_3467738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467738 prefixEnd_3467738 := by exact prefixLift 3467738
  have htrace : WordTrace (prefixWord ++ tailWord_3467738) baseStart_3467738 baseEnd_3467738 := by
    simpa [prefixWord, tailWord_3467738, baseEnd_3467738] using wordTrace_append hprefix tailTrace_3467738
  have hstable : (prefixWord ++ tailWord_3467738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467738).length < 2 ^ (prefixWord ++ tailWord_3467738).sum := by decide
  have hdescent : baseEnd_3467738 < baseStart_3467738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467746 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3467746 : Nat := 118140960795 + 3467746 * 2 ^ 59
def prefixEnd_3467746 : Nat := 4983230072969 + 3 ^ 40 * 3467746 * 2
def baseEnd_3467746 : Nat := 1780620485706294661527133

theorem tailTrace_3467746 : CollatzResearch.WordTrace tailWord_3467746 prefixEnd_3467746 1780620485706294661527133 := by
  unfold tailWord_3467746
  simp only [CollatzResearch.WordTrace]
  refine ⟨31619771823738990177741773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84319391529970640473978061 31619771823738990177741773)
  ·
    refine ⟨11857414433902121316653165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31619771823738990177741773 11857414433902121316653165)
    ·
      refine ⟨4446530412713295493744937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11857414433902121316653165 4446530412713295493744937)
      ·
        refine ⟨3334897809534971620308703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4446530412713295493744937 3334897809534971620308703)
        ·
          refine ⟨5002346714302457430463055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334897809534971620308703 5002346714302457430463055)
          ·
            refine ⟨7503520071453686145694583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5002346714302457430463055 7503520071453686145694583)
            ·
              refine ⟨11255280107180529218541875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7503520071453686145694583 11255280107180529218541875)
              ·
                refine ⟨16882920160770793827812813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11255280107180529218541875 16882920160770793827812813)
                ·
                  refine ⟨6331095060289047685429805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16882920160770793827812813 6331095060289047685429805)
                  ·
                    refine ⟨2374160647608392882036177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6331095060289047685429805 2374160647608392882036177)
                    ·
                      refine ⟨1780620485706294661527133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2374160647608392882036177 1780620485706294661527133)
                      ·
                        rfl

theorem cell23_3467746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3467746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467746 prefixEnd_3467746 := by exact prefixLift 3467746
  have htrace : WordTrace (prefixWord ++ tailWord_3467746) baseStart_3467746 baseEnd_3467746 := by
    simpa [prefixWord, tailWord_3467746, baseEnd_3467746] using wordTrace_append hprefix tailTrace_3467746
  have hstable : (prefixWord ++ tailWord_3467746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467746).length < 2 ^ (prefixWord ++ tailWord_3467746).sum := by decide
  have hdescent : baseEnd_3467746 < baseStart_3467746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467789 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3467789 : Nat := 118140960795 + 3467789 * 2 ^ 59
def prefixEnd_3467789 : Nat := 4983230072969 + 3 ^ 40 * 3467789 * 2
def baseEnd_3467789 : Nat := 1780642565374437993289435

theorem tailTrace_3467789 : CollatzResearch.WordTrace tailWord_3467789 prefixEnd_3467789 1780642565374437993289435 := by
  unfold tailWord_3467789
  simp only [CollatzResearch.WordTrace]
  refine ⟨126480655633800179054782421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84320437089200119369854947 126480655633800179054782421)
  ·
    refine ⟨2964390366417191696596463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 126480655633800179054782421 2964390366417191696596463)
    ·
      refine ⟨4446585549625787544894695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2964390366417191696596463 4446585549625787544894695)
      ·
        refine ⟨6669878324438681317342043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4446585549625787544894695 6669878324438681317342043)
        ·
          refine ⟨10004817486658021976013065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6669878324438681317342043 10004817486658021976013065)
          ·
            refine ⟨7503613114993516482009799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10004817486658021976013065 7503613114993516482009799)
            ·
              refine ⟨11255419672490274723014699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7503613114993516482009799 11255419672490274723014699)
              ·
                refine ⟨16883129508735412084522049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11255419672490274723014699 16883129508735412084522049)
                ·
                  refine ⟨12662347131551559063391537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16883129508735412084522049 12662347131551559063391537)
                  ·
                    refine ⟨9496760348663669297543653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12662347131551559063391537 9496760348663669297543653)
                    ·
                      refine ⟨1780642565374437993289435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9496760348663669297543653 1780642565374437993289435)
                      ·
                        rfl

theorem cell23_3467789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3467789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467789 prefixEnd_3467789 := by exact prefixLift 3467789
  have htrace : WordTrace (prefixWord ++ tailWord_3467789) baseStart_3467789 baseEnd_3467789 := by
    simpa [prefixWord, tailWord_3467789, baseEnd_3467789] using wordTrace_append hprefix tailTrace_3467789
  have hstable : (prefixWord ++ tailWord_3467789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467789).length < 2 ^ (prefixWord ++ tailWord_3467789).sum := by decide
  have hdescent : baseEnd_3467789 < baseStart_3467789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467812 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_3467812 : Nat := 118140960795 + 3467812 * 2 ^ 59
def prefixEnd_3467812 : Nat := 4983230072969 + 3 ^ 40 * 3467812 * 2
def baseEnd_3467812 : Nat := 593551458476497134433943

theorem tailTrace_3467812 : CollatzResearch.WordTrace tailWord_3467812 prefixEnd_3467812 593551458476497134433943 := by
  unfold tailWord_3467812
  simp only [CollatzResearch.WordTrace]
  refine ⟨63240747256358426991434845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84320996341811235988579793 63240747256358426991434845)
  ·
    refine ⟨23715280221134410121788067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63240747256358426991434845 23715280221134410121788067)
    ·
      refine ⟨35572920331701615182682101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23715280221134410121788067 35572920331701615182682101)
      ·
        refine ⟨3334961281097026423376447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35572920331701615182682101 3334961281097026423376447)
        ·
          refine ⟨5002441921645539635064671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334961281097026423376447 5002441921645539635064671)
          ·
            refine ⟨7503662882468309452597007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5002441921645539635064671 7503662882468309452597007)
            ·
              refine ⟨11255494323702464178895511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7503662882468309452597007 11255494323702464178895511)
              ·
                refine ⟨16883241485553696268343267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11255494323702464178895511 16883241485553696268343267)
                ·
                  refine ⟨25324862228330544402514901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16883241485553696268343267 25324862228330544402514901)
                  ·
                    refine ⟨593551458476497134433943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25324862228330544402514901 593551458476497134433943)
                    ·
                      rfl

theorem cell23_3467812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_3467812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467812 prefixEnd_3467812 := by exact prefixLift 3467812
  have htrace : WordTrace (prefixWord ++ tailWord_3467812) baseStart_3467812 baseEnd_3467812 := by
    simpa [prefixWord, tailWord_3467812, baseEnd_3467812] using wordTrace_append hprefix tailTrace_3467812
  have hstable : (prefixWord ++ tailWord_3467812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467812).length < 2 ^ (prefixWord ++ tailWord_3467812).sum := by decide
  have hdescent : baseEnd_3467812 < baseStart_3467812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467893 : List Nat := [1, 3, 4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3467893 : Nat := 118140960795 + 3467893 * 2 ^ 59
def prefixEnd_3467893 : Nat := 4983230072969 + 3 ^ 40 * 3467893 * 2
def baseEnd_3467893 : Nat := 593565322454168528796319

theorem tailTrace_3467893 : CollatzResearch.WordTrace tailWord_3467893 prefixEnd_3467893 593565322454168528796319 := by
  unfold tailWord_3467893
  simp only [CollatzResearch.WordTrace]
  refine ⟨126484448825423404816568333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84322965883615603211045555 126484448825423404816568333)
  ·
    refine ⟨47431668309533776806213125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126484448825423404816568333 47431668309533776806213125)
    ·
      refine ⟨8893437808037583151164961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47431668309533776806213125 8893437808037583151164961)
      ·
        refine ⟨6670078356028187363373721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8893437808037583151164961 6670078356028187363373721)
        ·
          refine ⟨5002558767021140522530291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6670078356028187363373721 5002558767021140522530291)
          ·
            refine ⟨7503838150531710783795437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5002558767021140522530291 7503838150531710783795437)
            ·
              refine ⟨2813939306449391543923289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7503838150531710783795437 2813939306449391543923289)
              ·
                refine ⟨2110454479837043657942467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2813939306449391543923289 2110454479837043657942467)
                ·
                  refine ⟨3165681719755565486913701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110454479837043657942467 3165681719755565486913701)
                  ·
                    refine ⟨593565322454168528796319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165681719755565486913701 593565322454168528796319)
                    ·
                      rfl

theorem cell23_3467893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3467893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467893 prefixEnd_3467893 := by exact prefixLift 3467893
  have htrace : WordTrace (prefixWord ++ tailWord_3467893) baseStart_3467893 baseEnd_3467893 := by
    simpa [prefixWord, tailWord_3467893, baseEnd_3467893] using wordTrace_append hprefix tailTrace_3467893
  have hstable : (prefixWord ++ tailWord_3467893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467893).length < 2 ^ (prefixWord ++ tailWord_3467893).sum := by decide
  have hdescent : baseEnd_3467893 < baseStart_3467893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467915 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 6, 4]
def baseStart_3467915 : Nat := 118140960795 + 3467915 * 2 ^ 59
def prefixEnd_3467915 : Nat := 4983230072969 + 3 ^ 40 * 3467915 * 2
def baseEnd_3467915 : Nat := 593569087978968166771285

theorem tailTrace_3467915 : CollatzResearch.WordTrace tailWord_3467915 prefixEnd_3467915 593569087978968166771285 := by
  unfold tailWord_3467915
  simp only [CollatzResearch.WordTrace]
  refine ⟨126485251231343702573869199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84323500820895801715912799 126485251231343702573869199)
  ·
    refine ⟨189727876847015553860803799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126485251231343702573869199 189727876847015553860803799)
    ·
      refine ⟨284591815270523330791205699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189727876847015553860803799 284591815270523330791205699)
      ·
        refine ⟨426887722905784996186808549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284591815270523330791205699 426887722905784996186808549)
        ·
          refine ⟨80041448044834686785026603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426887722905784996186808549 80041448044834686785026603)
          ·
            refine ⟨120062172067252030177539905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80041448044834686785026603 120062172067252030177539905)
            ·
              refine ⟨90046629050439022633154929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120062172067252030177539905 90046629050439022633154929)
              ·
                refine ⟨67534971787829266974866197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90046629050439022633154929 67534971787829266974866197)
                ·
                  refine ⟨3165701802554496889446853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67534971787829266974866197 3165701802554496889446853)
                  ·
                    refine ⟨593569087978968166771285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165701802554496889446853 593569087978968166771285)
                    ·
                      rfl

theorem cell23_3467915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 4].length) (baseStart_3467915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467915 prefixEnd_3467915 := by exact prefixLift 3467915
  have htrace : WordTrace (prefixWord ++ tailWord_3467915) baseStart_3467915 baseEnd_3467915 := by
    simpa [prefixWord, tailWord_3467915, baseEnd_3467915] using wordTrace_append hprefix tailTrace_3467915
  have hstable : (prefixWord ++ tailWord_3467915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467915).length < 2 ^ (prefixWord ++ tailWord_3467915).sum := by decide
  have hdescent : baseEnd_3467915 < baseStart_3467915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467932 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_3467932 : Nat := 118140960795 + 3467932 * 2 ^ 59
def prefixEnd_3467932 : Nat := 4983230072969 + 3 ^ 40 * 3467932 * 2
def baseEnd_3467932 : Nat := 593571997702676977933759

theorem tailTrace_3467932 : CollatzResearch.WordTrace tailWord_3467932 prefixEnd_3467932 593571997702676977933759 := by
  unfold tailWord_3467932
  simp only [CollatzResearch.WordTrace]
  refine ⟨63242935636141057238619025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84323914181521409651492033 63242935636141057238619025)
  ·
    refine ⟨47432201727105792928964269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63242935636141057238619025 47432201727105792928964269)
    ·
      refine ⟨17787075647664672348361601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47432201727105792928964269 17787075647664672348361601)
      ·
        refine ⟨13340306735748504261271201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17787075647664672348361601 13340306735748504261271201)
        ·
          refine ⟨10005230051811378195953401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13340306735748504261271201 10005230051811378195953401)
          ·
            refine ⟨7503922538858533646965051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10005230051811378195953401 7503922538858533646965051)
            ·
              refine ⟨11255883808287800470447577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7503922538858533646965051 11255883808287800470447577)
              ·
                refine ⟨8441912856215850352835683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11255883808287800470447577 8441912856215850352835683)
                ·
                  refine ⟨12662869284323775529253525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8441912856215850352835683 12662869284323775529253525)
                  ·
                    refine ⟨593571997702676977933759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12662869284323775529253525 593571997702676977933759)
                    ·
                      rfl

theorem cell23_3467932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_3467932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467932 prefixEnd_3467932 := by exact prefixLift 3467932
  have htrace : WordTrace (prefixWord ++ tailWord_3467932) baseStart_3467932 baseEnd_3467932 := by
    simpa [prefixWord, tailWord_3467932, baseEnd_3467932] using wordTrace_append hprefix tailTrace_3467932
  have hstable : (prefixWord ++ tailWord_3467932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467932).length < 2 ^ (prefixWord ++ tailWord_3467932).sum := by decide
  have hdescent : baseEnd_3467932 < baseStart_3467932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467949 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3467949 : Nat := 118140960795 + 3467949 * 2 ^ 59
def prefixEnd_3467949 : Nat := 4983230072969 + 3 ^ 40 * 3467949 * 2
def baseEnd_3467949 : Nat := 593574907426385789096233

theorem tailTrace_3467949 : CollatzResearch.WordTrace tailWord_3467949 prefixEnd_3467949 593574907426385789096233 := by
  unfold tailWord_3467949
  simp only [CollatzResearch.WordTrace]
  refine ⟨126486491313220526380606901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84324327542147017587071267 126486491313220526380606901)
  ·
    refine ⟨11858108560614424348181897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126486491313220526380606901 11858108560614424348181897)
    ·
      refine ⟨8893581420460818261136423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11858108560614424348181897 8893581420460818261136423)
      ·
        refine ⟨13340372130691227391704635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8893581420460818261136423 13340372130691227391704635)
        ·
          refine ⟨20010558196036841087556953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13340372130691227391704635 20010558196036841087556953)
          ·
            refine ⟨15007918647027630815667715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20010558196036841087556953 15007918647027630815667715)
            ·
              refine ⟨22511877970541446223501573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15007918647027630815667715 22511877970541446223501573)
              ·
                refine ⟨4220977119476521166906545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22511877970541446223501573 4220977119476521166906545)
                ·
                  refine ⟨3165732839607390875179909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4220977119476521166906545 3165732839607390875179909)
                  ·
                    refine ⟨593574907426385789096233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165732839607390875179909 593574907426385789096233)
                    ·
                      rfl

theorem cell23_3467949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3467949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467949 prefixEnd_3467949 := by exact prefixLift 3467949
  have htrace : WordTrace (prefixWord ++ tailWord_3467949) baseStart_3467949 baseEnd_3467949 := by
    simpa [prefixWord, tailWord_3467949, baseEnd_3467949] using wordTrace_append hprefix tailTrace_3467949
  have hstable : (prefixWord ++ tailWord_3467949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467949).length < 2 ^ (prefixWord ++ tailWord_3467949).sum := by decide
  have hdescent : baseEnd_3467949 < baseStart_3467949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467950 : List Nat := [4, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_3467950 : Nat := 118140960795 + 3467950 * 2 ^ 59
def prefixEnd_3467950 : Nat := 4983230072969 + 3 ^ 40 * 3467950 * 2
def baseEnd_3467950 : Nat := 1780725235759811863376195

theorem tailTrace_3467950 : CollatzResearch.WordTrace tailWord_3467950 prefixEnd_3467950 1780725235759811863376195 := by
  unfold tailWord_3467950
  simp only [CollatzResearch.WordTrace]
  refine ⟨15810815973277112943924163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84324351857477935700928869 15810815973277112943924163)
  ·
    refine ⟨23716223959915669415886245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15810815973277112943924163 23716223959915669415886245)
    ·
      refine ⟨4446791992484188015478671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23716223959915669415886245 4446791992484188015478671)
      ·
        refine ⟨6670187988726282023218007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4446791992484188015478671 6670187988726282023218007)
        ·
          refine ⟨10005281983089423034827011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6670187988726282023218007 10005281983089423034827011)
          ·
            refine ⟨15007922974634134552240517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10005281983089423034827011 15007922974634134552240517)
            ·
              refine ⟨2813985557743900228545097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15007922974634134552240517 2813985557743900228545097)
              ·
                refine ⟨2110489168307925171408823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2813985557743900228545097 2110489168307925171408823)
                ·
                  refine ⟨3165733752461887757113235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110489168307925171408823 3165733752461887757113235)
                  ·
                    refine ⟨4748600628692831635669853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3165733752461887757113235 4748600628692831635669853)
                    ·
                      refine ⟨1780725235759811863376195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4748600628692831635669853 1780725235759811863376195)
                      ·
                        rfl

theorem cell23_3467950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_3467950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467950 prefixEnd_3467950 := by exact prefixLift 3467950
  have htrace : WordTrace (prefixWord ++ tailWord_3467950) baseStart_3467950 baseEnd_3467950 := by
    simpa [prefixWord, tailWord_3467950, baseEnd_3467950] using wordTrace_append hprefix tailTrace_3467950
  have hstable : (prefixWord ++ tailWord_3467950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467950).length < 2 ^ (prefixWord ++ tailWord_3467950).sum := by decide
  have hdescent : baseEnd_3467950 < baseStart_3467950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3467985 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_3467985 : Nat := 118140960795 + 3467985 * 2 ^ 59
def prefixEnd_3467985 : Nat := 4983230072969 + 3 ^ 40 * 3467985 * 2
def baseEnd_3467985 : Nat := 1780743207582719226438533

theorem tailTrace_3467985 : CollatzResearch.WordTrace tailWord_3467985 prefixEnd_3467985 1780743207582719226438533 := by
  unfold tailWord_3467985
  simp only [CollatzResearch.WordTrace]
  refine ⟨126487804341090104528917409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84325202894060069685944939 126487804341090104528917409)
  ·
    refine ⟨94865853255817578396688057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126487804341090104528917409 94865853255817578396688057)
    ·
      refine ⟨71149389941863183797516043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94865853255817578396688057 71149389941863183797516043)
      ·
        refine ⟨106724084912794775696274065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71149389941863183797516043 106724084912794775696274065)
        ·
          refine ⟨80043063684596081772205549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106724084912794775696274065 80043063684596081772205549)
          ·
            refine ⟨30016148881723530664577081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80043063684596081772205549 30016148881723530664577081)
            ·
              refine ⟨22512111661292647998432811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30016148881723530664577081 22512111661292647998432811)
              ·
                refine ⟨33768167491938971997649217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22512111661292647998432811 33768167491938971997649217)
                ·
                  refine ⟨25326125618954228998236913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33768167491938971997649217 25326125618954228998236913)
                  ·
                    refine ⟨18994594214215671748677685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25326125618954228998236913 18994594214215671748677685)
                    ·
                      refine ⟨1780743207582719226438533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18994594214215671748677685 1780743207582719226438533)
                      ·
                        rfl

theorem cell23_3467985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_3467985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3467985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3467985 prefixEnd_3467985 := by exact prefixLift 3467985
  have htrace : WordTrace (prefixWord ++ tailWord_3467985) baseStart_3467985 baseEnd_3467985 := by
    simpa [prefixWord, tailWord_3467985, baseEnd_3467985] using wordTrace_append hprefix tailTrace_3467985
  have hstable : (prefixWord ++ tailWord_3467985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3467985).length < 2 ^ (prefixWord ++ tailWord_3467985).sum := by decide
  have hdescent : baseEnd_3467985 < baseStart_3467985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3467985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468020 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3468020 : Nat := 118140960795 + 3468020 * 2 ^ 59
def prefixEnd_3468020 : Nat := 4983230072969 + 3 ^ 40 * 3468020 * 2
def baseEnd_3468020 : Nat := 1780761179405626589500873

theorem tailTrace_3468020 : CollatzResearch.WordTrace tailWord_3468020 prefixEnd_3468020 1780761179405626589500873 := by
  unfold tailWord_3468020
  simp only [CollatzResearch.WordTrace]
  refine ⟨63244540447981652753220757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84326053930642203670961009 63244540447981652753220757)
  ·
    refine ⟨2964587833499139972807223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63244540447981652753220757 2964587833499139972807223)
    ·
      refine ⟨4446881750248709959210835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2964587833499139972807223 4446881750248709959210835)
      ·
        refine ⟨6670322625373064938816253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4446881750248709959210835 6670322625373064938816253)
        ·
          refine ⟨2501370984514899352056095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6670322625373064938816253 2501370984514899352056095)
          ·
            refine ⟨3752056476772349028084143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501370984514899352056095 3752056476772349028084143)
            ·
              refine ⟨5628084715158523542126215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752056476772349028084143 5628084715158523542126215)
              ·
                refine ⟨8442127072737785313189323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628084715158523542126215 8442127072737785313189323)
                ·
                  refine ⟨12663190609106677969783985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8442127072737785313189323 12663190609106677969783985)
                  ·
                    refine ⟨9497392956830008477337989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12663190609106677969783985 9497392956830008477337989)
                    ·
                      refine ⟨1780761179405626589500873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9497392956830008477337989 1780761179405626589500873)
                      ·
                        rfl

theorem cell23_3468020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3468020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468020 prefixEnd_3468020 := by exact prefixLift 3468020
  have htrace : WordTrace (prefixWord ++ tailWord_3468020) baseStart_3468020 baseEnd_3468020 := by
    simpa [prefixWord, tailWord_3468020, baseEnd_3468020] using wordTrace_append hprefix tailTrace_3468020
  have hstable : (prefixWord ++ tailWord_3468020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468020).length < 2 ^ (prefixWord ++ tailWord_3468020).sum := by decide
  have hdescent : baseEnd_3468020 < baseStart_3468020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468022 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3468022 : Nat := 118140960795 + 3468022 * 2 ^ 59
def prefixEnd_3468022 : Nat := 4983230072969 + 3 ^ 40 * 3468022 * 2
def baseEnd_3468022 : Nat := 593587402122311860558621

theorem tailTrace_3468022 : CollatzResearch.WordTrace tailWord_3468022 prefixEnd_3468022 593587402122311860558621 := by
  unfold tailWord_3468022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7905572115122253740500895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84326102561304039898676213 7905572115122253740500895)
  ·
    refine ⟨11858358172683380610751343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7905572115122253740500895 11858358172683380610751343)
    ·
      refine ⟨17787537259025070916127015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11858358172683380610751343 17787537259025070916127015)
      ·
        refine ⟨26681305888537606374190523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17787537259025070916127015 26681305888537606374190523)
        ·
          refine ⟨40021958832806409561285785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26681305888537606374190523 40021958832806409561285785)
          ·
            refine ⟨30016469124604807170964339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40021958832806409561285785 30016469124604807170964339)
            ·
              refine ⟨45024703686907210756446509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30016469124604807170964339 45024703686907210756446509)
              ·
                refine ⟨16884263882590204033667441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45024703686907210756446509 16884263882590204033667441)
                ·
                  refine ⟨12663197911942653025250581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16884263882590204033667441 12663197911942653025250581)
                  ·
                    refine ⟨593587402122311860558621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12663197911942653025250581 593587402122311860558621)
                    ·
                      rfl

theorem cell23_3468022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3468022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468022 prefixEnd_3468022 := by exact prefixLift 3468022
  have htrace : WordTrace (prefixWord ++ tailWord_3468022) baseStart_3468022 baseEnd_3468022 := by
    simpa [prefixWord, tailWord_3468022, baseEnd_3468022] using wordTrace_append hprefix tailTrace_3468022
  have hstable : (prefixWord ++ tailWord_3468022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468022).length < 2 ^ (prefixWord ++ tailWord_3468022).sum := by decide
  have hdescent : baseEnd_3468022 < baseStart_3468022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468075 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 7]
def baseStart_3468075 : Nat := 118140960795 + 3468075 * 2 ^ 59
def prefixEnd_3468075 : Nat := 4983230072969 + 3 ^ 40 * 3468075 * 2
def baseEnd_3468075 : Nat := 1780789420841623874313119

theorem tailTrace_3468075 : CollatzResearch.WordTrace tailWord_3468075 prefixEnd_3468075 1780789420841623874313119 := by
  unfold tailWord_3468075
  simp only [CollatzResearch.WordTrace]
  refine ⟨126491086910764049899693679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84327391273842699933129119 126491086910764049899693679)
  ·
    refine ⟨189736630366146074849540519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126491086910764049899693679 189736630366146074849540519)
    ·
      refine ⟨284604945549219112274310779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189736630366146074849540519 284604945549219112274310779)
      ·
        refine ⟨426907418323828668411466169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284604945549219112274310779 426907418323828668411466169)
        ·
          refine ⟨320180563742871501308599627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426907418323828668411466169 320180563742871501308599627)
          ·
            refine ⟨480270845614307251962899441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320180563742871501308599627 480270845614307251962899441)
            ·
              refine ⟨360203134210730438972174581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480270845614307251962899441 360203134210730438972174581)
              ·
                refine ⟨33769043832255978653641367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 360203134210730438972174581 33769043832255978653641367)
                ·
                  refine ⟨50653565748383967980462051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33769043832255978653641367 50653565748383967980462051)
                  ·
                    refine ⟨75980348622575951970693077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50653565748383967980462051 75980348622575951970693077)
                    ·
                      refine ⟨1780789420841623874313119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75980348622575951970693077 1780789420841623874313119)
                      ·
                        rfl

theorem cell23_3468075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_3468075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468075 prefixEnd_3468075 := by exact prefixLift 3468075
  have htrace : WordTrace (prefixWord ++ tailWord_3468075) baseStart_3468075 baseEnd_3468075 := by
    simpa [prefixWord, tailWord_3468075, baseEnd_3468075] using wordTrace_append hprefix tailTrace_3468075
  have hstable : (prefixWord ++ tailWord_3468075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468075).length < 2 ^ (prefixWord ++ tailWord_3468075).sum := by decide
  have hdescent : baseEnd_3468075 < baseStart_3468075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468082 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_3468082 : Nat := 118140960795 + 3468082 * 2 ^ 59
def prefixEnd_3468082 : Nat := 4983230072969 + 3 ^ 40 * 3468082 * 2
def baseEnd_3468082 : Nat := 593597671735401782308529

theorem tailTrace_3468082 : CollatzResearch.WordTrace tailWord_3468082 prefixEnd_3468082 593597671735401782308529 := by
  unfold tailWord_3468082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31622835555434672523799625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84327561481159126730132333 31622835555434672523799625)
  ·
    refine ⟨23717126666576004392849719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31622835555434672523799625 23717126666576004392849719)
    ·
      refine ⟨35575689999864006589274579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23717126666576004392849719 35575689999864006589274579)
      ·
        refine ⟨53363534999796009883911869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35575689999864006589274579 53363534999796009883911869)
        ·
          refine ⟨20011325624923503706466951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53363534999796009883911869 20011325624923503706466951)
          ·
            refine ⟨30016988437385255559700427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20011325624923503706466951 30016988437385255559700427)
            ·
              refine ⟨45025482656077883339550641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30016988437385255559700427 45025482656077883339550641)
              ·
                refine ⟨33769111992058412504662981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45025482656077883339550641 33769111992058412504662981)
                ·
                  refine ⟨6331708498510952344624309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33769111992058412504662981 6331708498510952344624309)
                  ·
                    refine ⟨593597671735401782308529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6331708498510952344624309 593597671735401782308529)
                    ·
                      rfl

theorem cell23_3468082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_3468082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468082 prefixEnd_3468082 := by exact prefixLift 3468082
  have htrace : WordTrace (prefixWord ++ tailWord_3468082) baseStart_3468082 baseEnd_3468082 := by
    simpa [prefixWord, tailWord_3468082, baseEnd_3468082] using wordTrace_append hprefix tailTrace_3468082
  have hstable : (prefixWord ++ tailWord_3468082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468082).length < 2 ^ (prefixWord ++ tailWord_3468082).sum := by decide
  have hdescent : baseEnd_3468082 < baseStart_3468082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468119 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_3468119 : Nat := 118140960795 + 3468119 * 2 ^ 59
def prefixEnd_3468119 : Nat := 4983230072969 + 3 ^ 40 * 3468119 * 2
def baseEnd_3468119 : Nat := 1780812013990421702162917

theorem tailTrace_3468119 : CollatzResearch.WordTrace tailWord_3468119 prefixEnd_3468119 1780812013990421702162917 := by
  unfold tailWord_3468119
  simp only [CollatzResearch.WordTrace]
  refine ⟨126492691722604645414295411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84328461148403096942863607 126492691722604645414295411)
  ·
    refine ⟨189739037583906968121443117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126492691722604645414295411 189739037583906968121443117)
    ·
      refine ⟨71152139093965113045541169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189739037583906968121443117 71152139093965113045541169)
      ·
        refine ⟨53364104320473834784155877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71152139093965113045541169 53364104320473834784155877)
        ·
          refine ⟨10005769560088844022029227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53364104320473834784155877 10005769560088844022029227)
          ·
            refine ⟨15008654340133266033043841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10005769560088844022029227 15008654340133266033043841)
            ·
              refine ⟨11256490755099949524782881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15008654340133266033043841 11256490755099949524782881)
              ·
                refine ⟨8442368066324962143587161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11256490755099949524782881 8442368066324962143587161)
                ·
                  refine ⟨6331776049743721607690371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8442368066324962143587161 6331776049743721607690371)
                  ·
                    refine ⟨9497664074615582411535557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6331776049743721607690371 9497664074615582411535557)
                    ·
                      refine ⟨1780812013990421702162917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9497664074615582411535557 1780812013990421702162917)
                      ·
                        rfl

theorem cell23_3468119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_3468119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468119 prefixEnd_3468119 := by exact prefixLift 3468119
  have htrace : WordTrace (prefixWord ++ tailWord_3468119) baseStart_3468119 baseEnd_3468119 := by
    simpa [prefixWord, tailWord_3468119, baseEnd_3468119] using wordTrace_append hprefix tailTrace_3468119
  have hstable : (prefixWord ++ tailWord_3468119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468119).length < 2 ^ (prefixWord ++ tailWord_3468119).sum := by decide
  have hdescent : baseEnd_3468119 < baseStart_3468119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468136 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_3468136 : Nat := 118140960795 + 3468136 * 2 ^ 59
def prefixEnd_3468136 : Nat := 4983230072969 + 3 ^ 40 * 3468136 * 2
def baseEnd_3468136 : Nat := 1780820743161548135650339

theorem tailTrace_3468136 : CollatzResearch.WordTrace tailWord_3468136 prefixEnd_3468136 1780820743161548135650339 := by
  unfold tailWord_3468136
  simp only [CollatzResearch.WordTrace]
  refine ⟨63246655881771528658832131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84328874509028704878442841 63246655881771528658832131)
  ·
    refine ⟨94869983822657292988248197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63246655881771528658832131 94869983822657292988248197)
    ·
      refine ⟨17788121966748242435296537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94869983822657292988248197 17788121966748242435296537)
      ·
        refine ⟨13341091475061181826472403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17788121966748242435296537 13341091475061181826472403)
        ·
          refine ⟨20011637212591772739708605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13341091475061181826472403 20011637212591772739708605)
          ·
            refine ⟨7504363954721914777390727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20011637212591772739708605 7504363954721914777390727)
            ·
              refine ⟨11256545932082872166086091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504363954721914777390727 11256545932082872166086091)
              ·
                refine ⟨16884818898124308249129137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11256545932082872166086091 16884818898124308249129137)
                ·
                  refine ⟨12663614173593231186846853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16884818898124308249129137 12663614173593231186846853)
                  ·
                    refine ⟨2374427657548730847533785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12663614173593231186846853 2374427657548730847533785)
                    ·
                      refine ⟨1780820743161548135650339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2374427657548730847533785 1780820743161548135650339)
                      ·
                        rfl

theorem cell23_3468136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_3468136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468136 prefixEnd_3468136 := by exact prefixLift 3468136
  have htrace : WordTrace (prefixWord ++ tailWord_3468136) baseStart_3468136 baseEnd_3468136 := by
    simpa [prefixWord, tailWord_3468136, baseEnd_3468136] using wordTrace_append hprefix tailTrace_3468136
  have hstable : (prefixWord ++ tailWord_3468136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468136).length < 2 ^ (prefixWord ++ tailWord_3468136).sum := by decide
  have hdescent : baseEnd_3468136 < baseStart_3468136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468152 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_3468152 : Nat := 118140960795 + 3468152 * 2 ^ 59
def prefixEnd_3468152 : Nat := 4983230072969 + 3 ^ 40 * 3468152 * 2
def baseEnd_3468152 : Nat := 1780828958852020073050265

theorem tailTrace_3468152 : CollatzResearch.WordTrace tailWord_3468152 prefixEnd_3468152 1780828958852020073050265 := by
  unfold tailWord_3468152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63246947665742546025123355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84329263554323394700164473 63246947665742546025123355)
  ·
    refine ⟨94870421498613819037685033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63246947665742546025123355 94870421498613819037685033)
    ·
      refine ⟨71152816123960364278263775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94870421498613819037685033 71152816123960364278263775)
      ·
        refine ⟨106729224185940546417395663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71152816123960364278263775 106729224185940546417395663)
        ·
          refine ⟨160093836278910819626093495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106729224185940546417395663 160093836278910819626093495)
          ·
            refine ⟨240140754418366229439140243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160093836278910819626093495 240140754418366229439140243)
            ·
              refine ⟨360211131627549344158710365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240140754418366229439140243 360211131627549344158710365)
              ·
                refine ⟨135079174360331004059516387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360211131627549344158710365 135079174360331004059516387)
                ·
                  refine ⟨202618761540496506089274581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135079174360331004059516387 202618761540496506089274581)
                  ·
                    refine ⟨4748877223605386861467373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202618761540496506089274581 4748877223605386861467373)
                    ·
                      refine ⟨1780828958852020073050265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4748877223605386861467373 1780828958852020073050265)
                      ·
                        rfl

theorem cell23_3468152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_3468152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468152 prefixEnd_3468152 := by exact prefixLift 3468152
  have htrace : WordTrace (prefixWord ++ tailWord_3468152) baseStart_3468152 baseEnd_3468152 := by
    simpa [prefixWord, tailWord_3468152, baseEnd_3468152] using wordTrace_append hprefix tailTrace_3468152
  have hstable : (prefixWord ++ tailWord_3468152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468152).length < 2 ^ (prefixWord ++ tailWord_3468152).sum := by decide
  have hdescent : baseEnd_3468152 < baseStart_3468152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468236 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_3468236 : Nat := 118140960795 + 3468236 * 2 ^ 59
def prefixEnd_3468236 : Nat := 4983230072969 + 3 ^ 40 * 3468236 * 2
def baseEnd_3468236 : Nat := 593624030408999248133293

theorem tailTrace_3468236 : CollatzResearch.WordTrace tailWord_3468236 prefixEnd_3468236 593624030408999248133293 := by
  unfold tailWord_3468236
  simp only [CollatzResearch.WordTrace]
  refine ⟨63248479531590387198152281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84331306042120516264203041 63248479531590387198152281)
  ·
    refine ⟨47436359648692790398614211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63248479531590387198152281 47436359648692790398614211)
    ·
      refine ⟨71154539473039185597921317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47436359648692790398614211 71154539473039185597921317)
      ·
        refine ⟨13341476151194847299610247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71154539473039185597921317 13341476151194847299610247)
        ·
          refine ⟨20012214226792270949415371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13341476151194847299610247 20012214226792270949415371)
          ·
            refine ⟨30018321340188406424123057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20012214226792270949415371 30018321340188406424123057)
            ·
              refine ⟨22513741005141304818092293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30018321340188406424123057 22513741005141304818092293)
              ·
                refine ⟨4221326438463994653392305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22513741005141304818092293 4221326438463994653392305)
                ·
                  refine ⟨3165994828847995990044229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221326438463994653392305 3165994828847995990044229)
                  ·
                    refine ⟨593624030408999248133293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3165994828847995990044229 593624030408999248133293)
                    ·
                      rfl

theorem cell23_3468236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_3468236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468236 prefixEnd_3468236 := by exact prefixLift 3468236
  have htrace : WordTrace (prefixWord ++ tailWord_3468236) baseStart_3468236 baseEnd_3468236 := by
    simpa [prefixWord, tailWord_3468236, baseEnd_3468236] using wordTrace_append hprefix tailTrace_3468236
  have hstable : (prefixWord ++ tailWord_3468236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468236).length < 2 ^ (prefixWord ++ tailWord_3468236).sum := by decide
  have hdescent : baseEnd_3468236 < baseStart_3468236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468249 : List Nat := [1, 2, 1, 2, 5, 2, 2, 8]
def baseStart_3468249 : Nat := 118140960795 + 3468249 * 2 ^ 59
def prefixEnd_3468249 : Nat := 4983230072969 + 3 ^ 40 * 3468249 * 2
def baseEnd_3468249 : Nat := 65958472832426155316197

theorem tailTrace_3468249 : CollatzResearch.WordTrace tailWord_3468249 prefixEnd_3468249 65958472832426155316197 := by
  unfold tailWord_3468249
  simp only [CollatzResearch.WordTrace]
  refine ⟨126497433212133677616527801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84331622141422451744351867 126497433212133677616527801)
  ·
    refine ⟨94873074909100258212395851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126497433212133677616527801 94873074909100258212395851)
    ·
      refine ⟨142309612363650387318593777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94873074909100258212395851 142309612363650387318593777)
      ·
        refine ⟨106732209272737790488945333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142309612363650387318593777 106732209272737790488945333)
        ·
          refine ⟨10006144619319167858338625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106732209272737790488945333 10006144619319167858338625)
          ·
            refine ⟨7504608464489375893753969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10006144619319167858338625 7504608464489375893753969)
            ·
              refine ⟨5628456348367031920315477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7504608464489375893753969 5628456348367031920315477)
              ·
                refine ⟨65958472832426155316197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5628456348367031920315477 65958472832426155316197)
                ·
                  rfl

theorem cell23_3468249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 8].length) (baseStart_3468249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468249 prefixEnd_3468249 := by exact prefixLift 3468249
  have htrace : WordTrace (prefixWord ++ tailWord_3468249) baseStart_3468249 baseEnd_3468249 := by
    simpa [prefixWord, tailWord_3468249, baseEnd_3468249] using wordTrace_append hprefix tailTrace_3468249
  have hstable : (prefixWord ++ tailWord_3468249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468249).length < 2 ^ (prefixWord ++ tailWord_3468249).sum := by decide
  have hdescent : baseEnd_3468249 < baseStart_3468249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468253 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_3468253 : Nat := 118140960795 + 3468253 * 2 ^ 59
def prefixEnd_3468253 : Nat := 4983230072969 + 3 ^ 40 * 3468253 * 2
def baseEnd_3468253 : Nat := 593626940132708059295767

theorem tailTrace_3468253 : CollatzResearch.WordTrace tailWord_3468253 prefixEnd_3468253 593626940132708059295767 := by
  unfold tailWord_3468253
  simp only [CollatzResearch.WordTrace]
  refine ⟨126497579104119186299673413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84331719402746124199782275 126497579104119186299673413)
  ·
    refine ⟨23718296082022347431188765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126497579104119186299673413 23718296082022347431188765)
    ·
      refine ⟨8894361030758380286695787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23718296082022347431188765 8894361030758380286695787)
      ·
        refine ⟨13341541546137570430043681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8894361030758380286695787 13341541546137570430043681)
        ·
          refine ⟨10006156159603177822532761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13341541546137570430043681 10006156159603177822532761)
          ·
            refine ⟨7504617119702383366899571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10006156159603177822532761 7504617119702383366899571)
            ·
              refine ⟨11256925679553575050349357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7504617119702383366899571 11256925679553575050349357)
              ·
                refine ⟨4221347129832590643881009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11256925679553575050349357 4221347129832590643881009)
                ·
                  refine ⟨3166010347374442982910757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221347129832590643881009 3166010347374442982910757)
                  ·
                    refine ⟨593626940132708059295767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3166010347374442982910757 593626940132708059295767)
                    ·
                      rfl

theorem cell23_3468253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_3468253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468253 prefixEnd_3468253 := by exact prefixLift 3468253
  have htrace : WordTrace (prefixWord ++ tailWord_3468253) baseStart_3468253 baseEnd_3468253 := by
    simpa [prefixWord, tailWord_3468253, baseEnd_3468253] using wordTrace_append hprefix tailTrace_3468253
  have hstable : (prefixWord ++ tailWord_3468253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468253).length < 2 ^ (prefixWord ++ tailWord_3468253).sum := by decide
  have hdescent : baseEnd_3468253 < baseStart_3468253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468263 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3468263 : Nat := 118140960795 + 3468263 * 2 ^ 59
def prefixEnd_3468263 : Nat := 4983230072969 + 3 ^ 40 * 3468263 * 2
def baseEnd_3468263 : Nat := 1780885955204669138762255

theorem tailTrace_3468263 : CollatzResearch.WordTrace tailWord_3468263 prefixEnd_3468263 1780885955204669138762255 := by
  unfold tailWord_3468263
  simp only [CollatzResearch.WordTrace]
  refine ⟨126497943834082958007537443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84331962556055305338358295 126497943834082958007537443)
  ·
    refine ⟨189746915751124437011306165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126497943834082958007537443 189746915751124437011306165)
    ·
      refine ⟨17788773351667915969809953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189746915751124437011306165 17788773351667915969809953)
      ·
        refine ⟨13341580013750936977357465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17788773351667915969809953 13341580013750936977357465)
        ·
          refine ⟨10006185010313202733018099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13341580013750936977357465 10006185010313202733018099)
          ·
            refine ⟨15009277515469804099527149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10006185010313202733018099 15009277515469804099527149)
            ·
              refine ⟨5628479068301176537322681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15009277515469804099527149 5628479068301176537322681)
              ·
                refine ⟨4221359301225882402992011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5628479068301176537322681 4221359301225882402992011)
                ·
                  refine ⟨6332038951838823604488017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221359301225882402992011 6332038951838823604488017)
                  ·
                    refine ⟨4749029213879117703366013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6332038951838823604488017 4749029213879117703366013)
                    ·
                      refine ⟨1780885955204669138762255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4749029213879117703366013 1780885955204669138762255)
                      ·
                        rfl

theorem cell23_3468263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3468263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468263 prefixEnd_3468263 := by exact prefixLift 3468263
  have htrace : WordTrace (prefixWord ++ tailWord_3468263) baseStart_3468263 baseEnd_3468263 := by
    simpa [prefixWord, tailWord_3468263, baseEnd_3468263] using wordTrace_append hprefix tailTrace_3468263
  have hstable : (prefixWord ++ tailWord_3468263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468263).length < 2 ^ (prefixWord ++ tailWord_3468263).sum := by decide
  have hdescent : baseEnd_3468263 < baseStart_3468263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468277 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3468277 : Nat := 118140960795 + 3468277 * 2 ^ 59
def prefixEnd_3468277 : Nat := 4983230072969 + 3 ^ 40 * 3468277 * 2
def baseEnd_3468277 : Nat := 1780893143933832083987191

theorem tailTrace_3468277 : CollatzResearch.WordTrace tailWord_3468277 prefixEnd_3468277 1780893143933832083987191 := by
  unfold tailWord_3468277
  simp only [CollatzResearch.WordTrace]
  refine ⟨126498454456032238398547085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84332302970688158932364723 126498454456032238398547085)
  ·
    refine ⟨47436920421012089399455157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126498454456032238398547085 47436920421012089399455157)
    ·
      refine ⟨4447211289469883381198921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47436920421012089399455157 4447211289469883381198921)
      ·
        refine ⟨3335408467102412535899191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4447211289469883381198921 3335408467102412535899191)
        ·
          refine ⟨5003112700653618803848787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335408467102412535899191 5003112700653618803848787)
          ·
            refine ⟨7504669050980428205773181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003112700653618803848787 7504669050980428205773181)
            ·
              refine ⟨2814250894117660577164943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7504669050980428205773181 2814250894117660577164943)
              ·
                refine ⟨4221376341176490865747415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814250894117660577164943 4221376341176490865747415)
                ·
                  refine ⟨6332064511764736298621123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221376341176490865747415 6332064511764736298621123)
                  ·
                    refine ⟨9498096767647104447931685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6332064511764736298621123 9498096767647104447931685)
                    ·
                      refine ⟨1780893143933832083987191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9498096767647104447931685 1780893143933832083987191)
                      ·
                        rfl

theorem cell23_3468277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3468277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468277 prefixEnd_3468277 := by exact prefixLift 3468277
  have htrace : WordTrace (prefixWord ++ tailWord_3468277) baseStart_3468277 baseEnd_3468277 := by
    simpa [prefixWord, tailWord_3468277, baseEnd_3468277] using wordTrace_append hprefix tailTrace_3468277
  have hstable : (prefixWord ++ tailWord_3468277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468277).length < 2 ^ (prefixWord ++ tailWord_3468277).sum := by decide
  have hdescent : baseEnd_3468277 < baseStart_3468277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468293 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 3]
def baseStart_3468293 : Nat := 118140960795 + 3468293 * 2 ^ 59
def prefixEnd_3468293 : Nat := 4983230072969 + 3 ^ 40 * 3468293 * 2
def baseEnd_3468293 : Nat := 1780901359624304021387117

theorem tailTrace_3468293 : CollatzResearch.WordTrace tailWord_3468293 prefixEnd_3468293 1780901359624304021387117 := by
  unfold tailWord_3468293
  simp only [CollatzResearch.WordTrace]
  refine ⟨126499038023974273131129533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84332692015982848754086355 126499038023974273131129533)
  ·
    refine ⟨47437139258990352424173575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126499038023974273131129533 47437139258990352424173575)
    ·
      refine ⟨71155708888485528636260363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47437139258990352424173575 71155708888485528636260363)
      ·
        refine ⟨106733563332728292954390545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71155708888485528636260363 106733563332728292954390545)
        ·
          refine ⟨80050172499546219715792909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106733563332728292954390545 80050172499546219715792909)
          ·
            refine ⟨30018814687329832393422341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80050172499546219715792909 30018814687329832393422341)
            ·
              refine ⟨5628527753874343573766689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30018814687329832393422341 5628527753874343573766689)
              ·
                refine ⟨4221395815405757680325017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5628527753874343573766689 4221395815405757680325017)
                ·
                  refine ⟨3166046861554318260243763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221395815405757680325017 3166046861554318260243763)
                  ·
                    refine ⟨4749070292331477390365645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166046861554318260243763 4749070292331477390365645)
                    ·
                      refine ⟨1780901359624304021387117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4749070292331477390365645 1780901359624304021387117)
                      ·
                        rfl

theorem cell23_3468293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_3468293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468293 prefixEnd_3468293 := by exact prefixLift 3468293
  have htrace : WordTrace (prefixWord ++ tailWord_3468293) baseStart_3468293 baseEnd_3468293 := by
    simpa [prefixWord, tailWord_3468293, baseEnd_3468293] using wordTrace_append hprefix tailTrace_3468293
  have hstable : (prefixWord ++ tailWord_3468293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468293).length < 2 ^ (prefixWord ++ tailWord_3468293).sum := by decide
  have hdescent : baseEnd_3468293 < baseStart_3468293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468299 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 4]
def baseStart_3468299 : Nat := 118140960795 + 3468299 * 2 ^ 59
def prefixEnd_3468299 : Nat := 4983230072969 + 3 ^ 40 * 3468299 * 2
def baseEnd_3468299 : Nat := 1780904440508230997912089

theorem tailTrace_3468299 : CollatzResearch.WordTrace tailWord_3468299 prefixEnd_3468299 1780904440508230997912089 := by
  unfold tailWord_3468299
  simp only [CollatzResearch.WordTrace]
  refine ⟨126499256861952536155847951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84332837907968357437231967 126499256861952536155847951)
  ·
    refine ⟨189748885292928804233771927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126499256861952536155847951 189748885292928804233771927)
    ·
      refine ⟨284623327939393206350657891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189748885292928804233771927 284623327939393206350657891)
      ·
        refine ⟨426934991909089809525986837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284623327939393206350657891 426934991909089809525986837)
        ·
          refine ⟨20012577745738584821530633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 426934991909089809525986837 20012577745738584821530633)
          ·
            refine ⟨15009433309303938616147975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20012577745738584821530633 15009433309303938616147975)
            ·
              refine ⟨22514149963955907924221963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15009433309303938616147975 22514149963955907924221963)
              ·
                refine ⟨33771224945933861886332945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22514149963955907924221963 33771224945933861886332945)
                ·
                  refine ⟨25328418709450396414749709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33771224945933861886332945 25328418709450396414749709)
                  ·
                    refine ⟨9498157016043898655531141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25328418709450396414749709 9498157016043898655531141)
                    ·
                      refine ⟨1780904440508230997912089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9498157016043898655531141 1780904440508230997912089)
                      ·
                        rfl

theorem cell23_3468299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 4].length) (baseStart_3468299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468299 prefixEnd_3468299 := by exact prefixLift 3468299
  have htrace : WordTrace (prefixWord ++ tailWord_3468299) baseStart_3468299 baseEnd_3468299 := by
    simpa [prefixWord, tailWord_3468299, baseEnd_3468299] using wordTrace_append hprefix tailTrace_3468299
  have hstable : (prefixWord ++ tailWord_3468299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468299).length < 2 ^ (prefixWord ++ tailWord_3468299).sum := by decide
  have hdescent : baseEnd_3468299 < baseStart_3468299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468309 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_3468309 : Nat := 118140960795 + 3468309 * 2 ^ 59
def prefixEnd_3468309 : Nat := 4983230072969 + 3 ^ 40 * 3468309 * 2
def baseEnd_3468309 : Nat := 593636525104925319595681

theorem tailTrace_3468309 : CollatzResearch.WordTrace tailWord_3468309 prefixEnd_3468309 593636525104925319595681 := by
  unfold tailWord_3468309
  simp only [CollatzResearch.WordTrace]
  refine ⟨126499621591916307863711981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84333081061277538575807987 126499621591916307863711981)
  ·
    refine ⟨47437358096968615448891993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126499621591916307863711981 47437358096968615448891993)
    ·
      refine ⟨35578018572726461586668995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47437358096968615448891993 35578018572726461586668995)
      ·
        refine ⟨53367027859089692380003493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35578018572726461586668995 53367027859089692380003493)
        ·
          refine ⟨10006317723579317321250655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53367027859089692380003493 10006317723579317321250655)
          ·
            refine ⟨15009476585368975981875983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10006317723579317321250655 15009476585368975981875983)
            ·
              refine ⟨22514214878053463972813975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15009476585368975981875983 22514214878053463972813975)
              ·
                refine ⟨33771322317080195959220963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22514214878053463972813975 33771322317080195959220963)
                ·
                  refine ⟨50656983475620293938831445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33771322317080195959220963 50656983475620293938831445)
                  ·
                    refine ⟨593636525104925319595681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50656983475620293938831445 593636525104925319595681)
                    ·
                      rfl

theorem cell23_3468309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_3468309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468309 prefixEnd_3468309 := by exact prefixLift 3468309
  have htrace : WordTrace (prefixWord ++ tailWord_3468309) baseStart_3468309 baseEnd_3468309 := by
    simpa [prefixWord, tailWord_3468309, baseEnd_3468309] using wordTrace_append hprefix tailTrace_3468309
  have hstable : (prefixWord ++ tailWord_3468309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468309).length < 2 ^ (prefixWord ++ tailWord_3468309).sum := by decide
  have hdescent : baseEnd_3468309 < baseStart_3468309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468366 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_3468366 : Nat := 118140960795 + 3468366 * 2 ^ 59
def prefixEnd_3468366 : Nat := 4983230072969 + 3 ^ 40 * 3468366 * 2
def baseEnd_3468366 : Nat := 1780938843712082235774281

theorem tailTrace_3468366 : CollatzResearch.WordTrace tailWord_3468366 prefixEnd_3468366 1780938843712082235774281 := by
  unfold tailWord_3468366
  simp only [CollatzResearch.WordTrace]
  refine ⟨15812712569088725824817119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84334467035139871065691301 15812712569088725824817119)
  ·
    refine ⟨23719068853633088737225679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15812712569088725824817119 23719068853633088737225679)
    ·
      refine ⟨35578603280449633105838519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23719068853633088737225679 35578603280449633105838519)
      ·
        refine ⟨53367904920674449658757779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35578603280449633105838519 53367904920674449658757779)
        ·
          refine ⟨80051857381011674488136669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53367904920674449658757779 80051857381011674488136669)
          ·
            refine ⟨30019446517879377933051251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80051857381011674488136669 30019446517879377933051251)
            ·
              refine ⟨45029169776819066899576877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30019446517879377933051251 45029169776819066899576877)
              ·
                refine ⟨16885938666307150087341329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45029169776819066899576877 16885938666307150087341329)
                ·
                  refine ⟨12664453999730362565505997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16885938666307150087341329 12664453999730362565505997)
                  ·
                    refine ⟨4749170249898885962064749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12664453999730362565505997 4749170249898885962064749)
                    ·
                      refine ⟨1780938843712082235774281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4749170249898885962064749 1780938843712082235774281)
                      ·
                        rfl

theorem cell23_3468366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_3468366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468366 prefixEnd_3468366 := by exact prefixLift 3468366
  have htrace : WordTrace (prefixWord ++ tailWord_3468366) baseStart_3468366 baseEnd_3468366 := by
    simpa [prefixWord, tailWord_3468366, baseEnd_3468366] using wordTrace_append hprefix tailTrace_3468366
  have hstable : (prefixWord ++ tailWord_3468366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468366).length < 2 ^ (prefixWord ++ tailWord_3468366).sum := by decide
  have hdescent : baseEnd_3468366 < baseStart_3468366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468369 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 1, 7]
def baseStart_3468369 : Nat := 118140960795 + 3468369 * 2 ^ 59
def prefixEnd_3468369 : Nat := 4983230072969 + 3 ^ 40 * 3468369 * 2
def baseEnd_3468369 : Nat := 593646794718015241345589

theorem tailTrace_3468369 : CollatzResearch.WordTrace tailWord_3468369 prefixEnd_3468369 593646794718015241345589 := by
  unfold tailWord_3468369
  simp only [CollatzResearch.WordTrace]
  refine ⟨126501809971698938110896161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84334539981132625407264107 126501809971698938110896161)
  ·
    refine ⟨94876357478774203583172121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126501809971698938110896161 94876357478774203583172121)
    ·
      refine ⟨71157268109080652687379091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94876357478774203583172121 71157268109080652687379091)
      ·
        refine ⟨106735902163620979031068637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71157268109080652687379091 106735902163620979031068637)
        ·
          refine ⟨40025963311357867136650739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106735902163620979031068637 40025963311357867136650739)
          ·
            refine ⟨60038944967036800704976109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40025963311357867136650739 60038944967036800704976109)
            ·
              refine ⟨22514604362638800264366041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60038944967036800704976109 22514604362638800264366041)
              ·
                refine ⟨16885953271979100198274531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22514604362638800264366041 16885953271979100198274531)
                ·
                  refine ⟨25328929907968650297411797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16885953271979100198274531 25328929907968650297411797)
                  ·
                    refine ⟨593646794718015241345589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25328929907968650297411797 593646794718015241345589)
                    ·
                      rfl

theorem cell23_3468369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_3468369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468369 prefixEnd_3468369 := by exact prefixLift 3468369
  have htrace : WordTrace (prefixWord ++ tailWord_3468369) baseStart_3468369 baseEnd_3468369 := by
    simpa [prefixWord, tailWord_3468369, baseEnd_3468369] using wordTrace_append hprefix tailTrace_3468369
  have hstable : (prefixWord ++ tailWord_3468369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468369).length < 2 ^ (prefixWord ++ tailWord_3468369).sum := by decide
  have hdescent : baseEnd_3468369 < baseStart_3468369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468490 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_3468490 : Nat := 118140960795 + 3468490 * 2 ^ 59
def prefixEnd_3468490 : Nat := 4983230072969 + 3 ^ 40 * 3468490 * 2
def baseEnd_3468490 : Nat := 1781002515313239750623711

theorem tailTrace_3468490 : CollatzResearch.WordTrace tailWord_3468490 prefixEnd_3468490 1781002515313239750623711 := by
  unfold tailWord_3468490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31626555801065143944012731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84337482136173717184033949 31626555801065143944012731)
  ·
    refine ⟨47439833701597715916019097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31626555801065143944012731 47439833701597715916019097)
    ·
      refine ⟨35579875276198286937014323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47439833701597715916019097 35579875276198286937014323)
      ·
        refine ⟨53369812914297430405521485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35579875276198286937014323 53369812914297430405521485)
        ·
          refine ⟨20013679842861536402070557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53369812914297430405521485 20013679842861536402070557)
          ·
            refine ⟨7505129941073076150776459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20013679842861536402070557 7505129941073076150776459)
            ·
              refine ⟨11257694911609614226164689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7505129941073076150776459 11257694911609614226164689)
              ·
                refine ⟨8443271183707210669623517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11257694911609614226164689 8443271183707210669623517)
                ·
                  refine ⟨3166226693890204001108819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8443271183707210669623517 3166226693890204001108819)
                  ·
                    refine ⟨4749340040835306001663229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166226693890204001108819 4749340040835306001663229)
                    ·
                      refine ⟨1781002515313239750623711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4749340040835306001663229 1781002515313239750623711)
                      ·
                        rfl

theorem cell23_3468490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_3468490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468490 prefixEnd_3468490 := by exact prefixLift 3468490
  have htrace : WordTrace (prefixWord ++ tailWord_3468490) baseStart_3468490 baseEnd_3468490 := by
    simpa [prefixWord, tailWord_3468490, baseEnd_3468490] using wordTrace_append hprefix tailTrace_3468490
  have hstable : (prefixWord ++ tailWord_3468490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468490).length < 2 ^ (prefixWord ++ tailWord_3468490).sum := by decide
  have hdescent : baseEnd_3468490 < baseStart_3468490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468523 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 4, 4]
def baseStart_3468523 : Nat := 118140960795 + 3468523 * 2 ^ 59
def prefixEnd_3468523 : Nat := 4983230072969 + 3 ^ 40 * 3468523 * 2
def baseEnd_3468523 : Nat := 593673153391612707170353

theorem tailTrace_3468523 : CollatzResearch.WordTrace tailWord_3468523 prefixEnd_3468523 593673153391612707170353 := by
  unfold tailWord_3468523
  simp only [CollatzResearch.WordTrace]
  refine ⟨126507426813141022412002223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84338284542094014941334815 126507426813141022412002223)
  ·
    refine ⟨189761140219711533618003335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126507426813141022412002223 189761140219711533618003335)
    ·
      refine ⟨284641710329567300427005003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189761140219711533618003335 284641710329567300427005003)
      ·
        refine ⟨426962565494350950640507505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284641710329567300427005003 426962565494350950640507505)
        ·
          refine ⟨320221924120763212980380629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426962565494350950640507505 320221924120763212980380629)
          ·
            refine ⟨7505201346580387804227671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 320221924120763212980380629 7505201346580387804227671)
            ·
              refine ⟨11257802019870581706341507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7505201346580387804227671 11257802019870581706341507)
              ·
                refine ⟨16886703029805872559512261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11257802019870581706341507 16886703029805872559512261)
                ·
                  refine ⟨3166256818088601104908549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16886703029805872559512261 3166256818088601104908549)
                  ·
                    refine ⟨593673153391612707170353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3166256818088601104908549 593673153391612707170353)
                    ·
                      rfl

theorem cell23_3468523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 4].length) (baseStart_3468523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468523 prefixEnd_3468523 := by exact prefixLift 3468523
  have htrace : WordTrace (prefixWord ++ tailWord_3468523) baseStart_3468523 baseEnd_3468523 := by
    simpa [prefixWord, tailWord_3468523, baseEnd_3468523] using wordTrace_append hprefix tailTrace_3468523
  have hstable : (prefixWord ++ tailWord_3468523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468523).length < 2 ^ (prefixWord ++ tailWord_3468523).sum := by decide
  have hdescent : baseEnd_3468523 < baseStart_3468523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468540 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_3468540 : Nat := 118140960795 + 3468540 * 2 ^ 59
def prefixEnd_3468540 : Nat := 4983230072969 + 3 ^ 40 * 3468540 * 2
def baseEnd_3468540 : Nat := 593676063115321518332827

theorem tailTrace_3468540 : CollatzResearch.WordTrace tailWord_3468540 prefixEnd_3468540 593676063115321518332827 := by
  unfold tailWord_3468540
  simp only [CollatzResearch.WordTrace]
  refine ⟨63254023427039717157685537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84338697902719622876914049 63254023427039717157685537)
  ·
    refine ⟨47440517570279787868264153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63254023427039717157685537 47440517570279787868264153)
    ·
      refine ⟨35580388177709840901198115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47440517570279787868264153 35580388177709840901198115)
      ·
        refine ⟨53370582266564761351797173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35580388177709840901198115 53370582266564761351797173)
        ·
          refine ⟨5003492087490446376730985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53370582266564761351797173 5003492087490446376730985)
          ·
            refine ⟨3752619065617834782548239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5003492087490446376730985 3752619065617834782548239)
            ·
              refine ⟨5628928598426752173822359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752619065617834782548239 5628928598426752173822359)
              ·
                refine ⟨8443392897640128260733539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628928598426752173822359 8443392897640128260733539)
                ·
                  refine ⟨12665089346460192391100309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8443392897640128260733539 12665089346460192391100309)
                  ·
                    refine ⟨593676063115321518332827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12665089346460192391100309 593676063115321518332827)
                    ·
                      rfl

theorem cell23_3468540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_3468540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468540 prefixEnd_3468540 := by exact prefixLift 3468540
  have htrace : WordTrace (prefixWord ++ tailWord_3468540) baseStart_3468540 baseEnd_3468540 := by
    simpa [prefixWord, tailWord_3468540, baseEnd_3468540] using wordTrace_append hprefix tailTrace_3468540
  have hstable : (prefixWord ++ tailWord_3468540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468540).length < 2 ^ (prefixWord ++ tailWord_3468540).sum := by decide
  have hdescent : baseEnd_3468540 < baseStart_3468540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468543 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 4]
def baseStart_3468543 : Nat := 118140960795 + 3468543 * 2 ^ 59
def prefixEnd_3468543 : Nat := 4983230072969 + 3 ^ 40 * 3468543 * 2
def baseEnd_3468543 : Nat := 1781029729787928043260967

theorem tailTrace_3468543 : CollatzResearch.WordTrace tailWord_3468543 prefixEnd_3468543 1781029729787928043260967 := by
  unfold tailWord_3468543
  simp only [CollatzResearch.WordTrace]
  refine ⟨126508156273068565827730283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84338770848712377218486855 126508156273068565827730283)
  ·
    refine ⟨189762234409602848741595425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126508156273068565827730283 189762234409602848741595425)
    ·
      refine ⟨142321675807202136556196569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189762234409602848741595425 142321675807202136556196569)
      ·
        refine ⟨106741256855401602417147427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142321675807202136556196569 106741256855401602417147427)
        ·
          refine ⟨160111885283102403625721141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106741256855401602417147427 160111885283102403625721141)
          ·
            refine ⟨15010489245290850339911357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160111885283102403625721141 15010489245290850339911357)
            ·
              refine ⟨5628933466984068877466759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15010489245290850339911357 5628933466984068877466759)
              ·
                refine ⟨8443400200476103316200139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628933466984068877466759 8443400200476103316200139)
                ·
                  refine ⟨12665100300714154974300209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8443400200476103316200139 12665100300714154974300209)
                  ·
                    refine ⟨9498825225535616230725157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12665100300714154974300209 9498825225535616230725157)
                    ·
                      refine ⟨1781029729787928043260967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9498825225535616230725157 1781029729787928043260967)
                      ·
                        rfl

theorem cell23_3468543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_3468543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468543 prefixEnd_3468543 := by exact prefixLift 3468543
  have htrace : WordTrace (prefixWord ++ tailWord_3468543) baseStart_3468543 baseEnd_3468543 := by
    simpa [prefixWord, tailWord_3468543, baseEnd_3468543] using wordTrace_append hprefix tailTrace_3468543
  have hstable : (prefixWord ++ tailWord_3468543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468543).length < 2 ^ (prefixWord ++ tailWord_3468543).sum := by decide
  have hdescent : baseEnd_3468543 < baseStart_3468543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468580 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_3468580 : Nat := 118140960795 + 3468580 * 2 ^ 59
def prefixEnd_3468580 : Nat := 4983230072969 + 3 ^ 40 * 3468580 * 2
def baseEnd_3468580 : Nat := 1781048728572144398498297

theorem tailTrace_3468580 : CollatzResearch.WordTrace tailWord_3468580 prefixEnd_3468580 1781048728572144398498297 := by
  unfold tailWord_3468580
  simp only [CollatzResearch.WordTrace]
  refine ⟨63254752886967260573413597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84339670515956347431218129 63254752886967260573413597)
  ·
    refine ⟨23720532332612722715030099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63254752886967260573413597 23720532332612722715030099)
    ·
      refine ⟨35580798498919084072545149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23720532332612722715030099 35580798498919084072545149)
      ·
        refine ⟨13342799437094656527204431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35580798498919084072545149 13342799437094656527204431)
        ·
          refine ⟨20014199155641984790806647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13342799437094656527204431 20014199155641984790806647)
          ·
            refine ⟨30021298733462977186209971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20014199155641984790806647 30021298733462977186209971)
            ·
              refine ⟨45031948100194465779314957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30021298733462977186209971 45031948100194465779314957)
              ·
                refine ⟨16886980537572924667243109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45031948100194465779314957 16886980537572924667243109)
                ·
                  refine ⟨3166308850794923375108083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16886980537572924667243109 3166308850794923375108083)
                  ·
                    refine ⟨4749463276192385062662125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166308850794923375108083 4749463276192385062662125)
                    ·
                      refine ⟨1781048728572144398498297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4749463276192385062662125 1781048728572144398498297)
                      ·
                        rfl

theorem cell23_3468580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_3468580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468580 prefixEnd_3468580 := by exact prefixLift 3468580
  have htrace : WordTrace (prefixWord ++ tailWord_3468580) baseStart_3468580 baseEnd_3468580 := by
    simpa [prefixWord, tailWord_3468580, baseEnd_3468580] using wordTrace_append hprefix tailTrace_3468580
  have hstable : (prefixWord ++ tailWord_3468580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468580).length < 2 ^ (prefixWord ++ tailWord_3468580).sum := by decide
  have hdescent : baseEnd_3468580 < baseStart_3468580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468581 : List Nat := [1, 3, 1, 2, 4, 2, 3, 2, 1, 2, 2]
def baseStart_3468581 : Nat := 118140960795 + 3468581 * 2 ^ 59
def prefixEnd_3468581 : Nat := 4983230072969 + 3 ^ 40 * 3468581 * 2
def baseEnd_3468581 : Nat := 1781049242052798894585793

theorem tailTrace_3468581 : CollatzResearch.WordTrace tailWord_3468581 prefixEnd_3468581 1781049242052798894585793 := by
  unfold tailWord_3468581
  simp only [CollatzResearch.WordTrace]
  refine ⟨126509542246930898317613597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84339694831287265545075731 126509542246930898317613597)
  ·
    refine ⟨47441078342599086869105099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126509542246930898317613597 47441078342599086869105099)
    ·
      refine ⟨71161617513898630303657649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47441078342599086869105099 71161617513898630303657649)
      ·
        refine ⟨53371213135423972727743237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71161617513898630303657649 53371213135423972727743237)
        ·
          refine ⟨10007102462891994886451857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53371213135423972727743237 10007102462891994886451857)
          ·
            refine ⟨7505326847168996164838893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10007102462891994886451857 7505326847168996164838893)
            ·
              refine ⟨2814497567688373561814585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7505326847168996164838893 2814497567688373561814585)
              ·
                refine ⟨2110873175766280171360939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814497567688373561814585 2110873175766280171360939)
                ·
                  refine ⟨3166309763649420257041409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110873175766280171360939 3166309763649420257041409)
                  ·
                    refine ⟨2374732322737065192781057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3166309763649420257041409 2374732322737065192781057)
                    ·
                      refine ⟨1781049242052798894585793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2374732322737065192781057 1781049242052798894585793)
                      ·
                        rfl

theorem cell23_3468581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_3468581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468581 prefixEnd_3468581 := by exact prefixLift 3468581
  have htrace : WordTrace (prefixWord ++ tailWord_3468581) baseStart_3468581 baseEnd_3468581 := by
    simpa [prefixWord, tailWord_3468581, baseEnd_3468581] using wordTrace_append hprefix tailTrace_3468581
  have hstable : (prefixWord ++ tailWord_3468581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468581).length < 2 ^ (prefixWord ++ tailWord_3468581).sum := by decide
  have hdescent : baseEnd_3468581 < baseStart_3468581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468597 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_3468597 : Nat := 118140960795 + 3468597 * 2 ^ 59
def prefixEnd_3468597 : Nat := 4983230072969 + 3 ^ 40 * 3468597 * 2
def baseEnd_3468597 : Nat := 1781057457743270831985719

theorem tailTrace_3468597 : CollatzResearch.WordTrace tailWord_3468597 prefixEnd_3468597 1781057457743270831985719 := by
  unfold tailWord_3468597
  simp only [CollatzResearch.WordTrace]
  refine ⟨126510125814872933050196045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84340083876581955366797363 126510125814872933050196045)
  ·
    refine ⟨47441297180577349893823517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126510125814872933050196045 47441297180577349893823517)
    ·
      refine ⟨17790486442716506210183819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47441297180577349893823517 17790486442716506210183819)
      ·
        refine ⟨26685729664074759315275729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17790486442716506210183819 26685729664074759315275729)
        ·
          refine ⟨20014297248056069486456797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26685729664074759315275729 20014297248056069486456797)
          ·
            refine ⟨7505361468021026057421299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20014297248056069486456797 7505361468021026057421299)
            ·
              refine ⟨11258042202031539086131949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7505361468021026057421299 11258042202031539086131949)
              ·
                refine ⟨4221765825761827157299481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11258042202031539086131949 4221765825761827157299481)
                ·
                  refine ⟨3166324369321370367974611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221765825761827157299481 3166324369321370367974611)
                  ·
                    refine ⟨4749486553982055551961917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166324369321370367974611 4749486553982055551961917)
                    ·
                      refine ⟨1781057457743270831985719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4749486553982055551961917 1781057457743270831985719)
                      ·
                        rfl

theorem cell23_3468597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_3468597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468597 prefixEnd_3468597 := by exact prefixLift 3468597
  have htrace : WordTrace (prefixWord ++ tailWord_3468597) baseStart_3468597 baseEnd_3468597 := by
    simpa [prefixWord, tailWord_3468597, baseEnd_3468597] using wordTrace_append hprefix tailTrace_3468597
  have hstable : (prefixWord ++ tailWord_3468597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468597).length < 2 ^ (prefixWord ++ tailWord_3468597).sum := by decide
  have hdescent : baseEnd_3468597 < baseStart_3468597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468607 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 1, 3, 2]
def baseStart_3468607 : Nat := 118140960795 + 3468607 * 2 ^ 59
def prefixEnd_3468607 : Nat := 4983230072969 + 3 ^ 40 * 3468607 * 2
def baseEnd_3468607 : Nat := 1781062592549815792860673

theorem tailTrace_3468607 : CollatzResearch.WordTrace tailWord_3468607 prefixEnd_3468607 1781062592549815792860673 := by
  unfold tailWord_3468607
  simp only [CollatzResearch.WordTrace]
  refine ⟨126510490544836704758060075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84340327029891136505373383 126510490544836704758060075)
  ·
    refine ⟨189765735817255057137090113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126510490544836704758060075 189765735817255057137090113)
    ·
      refine ⟨142324301862941292852817585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189765735817255057137090113 142324301862941292852817585)
      ·
        refine ⟨106743226397205969639613189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142324301862941292852817585 106743226397205969639613189)
        ·
          refine ⟨20014354949476119307427473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106743226397205969639613189 20014354949476119307427473)
          ·
            refine ⟨15010766212107089480570605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20014354949476119307427473 15010766212107089480570605)
            ·
              refine ⟨5629037329540158555213977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15010766212107089480570605 5629037329540158555213977)
              ·
                refine ⟨4221777997155118916410483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5629037329540158555213977 4221777997155118916410483)
                ·
                  refine ⟨6332666995732678374615725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221777997155118916410483 6332666995732678374615725)
                  ·
                    refine ⟨2374750123399754390480897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6332666995732678374615725 2374750123399754390480897)
                    ·
                      refine ⟨1781062592549815792860673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2374750123399754390480897 1781062592549815792860673)
                      ·
                        rfl

theorem cell23_3468607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_3468607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468607 prefixEnd_3468607 := by exact prefixLift 3468607
  have htrace : WordTrace (prefixWord ++ tailWord_3468607) baseStart_3468607 baseEnd_3468607 := by
    simpa [prefixWord, tailWord_3468607, baseEnd_3468607] using wordTrace_append hprefix tailTrace_3468607
  have hstable : (prefixWord ++ tailWord_3468607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468607).length < 2 ^ (prefixWord ++ tailWord_3468607).sum := by decide
  have hdescent : baseEnd_3468607 < baseStart_3468607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468620 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 3, 4, 2]
def baseStart_3468620 : Nat := 118140960795 + 3468620 * 2 ^ 59
def prefixEnd_3468620 : Nat := 4983230072969 + 3 ^ 40 * 3468620 * 2
def baseEnd_3468620 : Nat := 1781069267798324241998113

theorem tailTrace_3468620 : CollatzResearch.WordTrace tailWord_3468620 prefixEnd_3468620 1781069267798324241998113 := by
  unfold tailWord_3468620
  simp only [CollatzResearch.WordTrace]
  refine ⟨63255482346894803989141657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84340643129193071985522209 63255482346894803989141657)
  ·
    refine ⟨47441611760171102991856243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63255482346894803989141657 47441611760171102991856243)
    ·
      refine ⟨71162417640256654487784365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47441611760171102991856243 71162417640256654487784365)
      ·
        refine ⟨26685906615096245432919137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71162417640256654487784365 26685906615096245432919137)
        ·
          refine ⟨20014429961322184074689353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26685906615096245432919137 20014429961322184074689353)
          ·
            refine ⟨15010822470991638056017015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20014429961322184074689353 15010822470991638056017015)
            ·
              refine ⟨22516233706487457084025523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15010822470991638056017015 22516233706487457084025523)
              ·
                refine ⟨33774350559731185626038285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22516233706487457084025523 33774350559731185626038285)
                ·
                  refine ⟨12665381459899194609764357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33774350559731185626038285 12665381459899194609764357)
                  ·
                    refine ⟨2374759023731098989330817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12665381459899194609764357 2374759023731098989330817)
                    ·
                      refine ⟨1781069267798324241998113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2374759023731098989330817 1781069267798324241998113)
                      ·
                        rfl

theorem cell23_3468620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_3468620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468620 prefixEnd_3468620 := by exact prefixLift 3468620
  have htrace : WordTrace (prefixWord ++ tailWord_3468620) baseStart_3468620 baseEnd_3468620 := by
    simpa [prefixWord, tailWord_3468620, baseEnd_3468620] using wordTrace_append hprefix tailTrace_3468620
  have hstable : (prefixWord ++ tailWord_3468620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468620).length < 2 ^ (prefixWord ++ tailWord_3468620).sum := by decide
  have hdescent : baseEnd_3468620 < baseStart_3468620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468733 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 10]
def baseStart_3468733 : Nat := 118140960795 + 3468733 * 2 ^ 59
def prefixEnd_3468733 : Nat := 4983230072969 + 3 ^ 40 * 3468733 * 2
def baseEnd_3468733 : Nat := 197903032345809144431677

theorem tailTrace_3468733 : CollatzResearch.WordTrace tailWord_3468733 prefixEnd_3468733 197903032345809144431677 := by
  unfold tailWord_3468733
  simp only [CollatzResearch.WordTrace]
  refine ⟨126515086142380228277146853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84343390761586818851431235 126515086142380228277146853)
  ·
    refine ⟨23721578651696292801965035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126515086142380228277146853 23721578651696292801965035)
    ·
      refine ⟨35582367977544439202947553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23721578651696292801965035 35582367977544439202947553)
      ·
        refine ⟨26686775983158329402210665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35582367977544439202947553 26686775983158329402210665)
        ·
          refine ⟨20015081987368747051657999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26686775983158329402210665 20015081987368747051657999)
          ·
            refine ⟨30022622981053120577486999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20015081987368747051657999 30022622981053120577486999)
            ·
              refine ⟨45033934471579680866230499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30022622981053120577486999 45033934471579680866230499)
              ·
                refine ⟨67550901707369521299345749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45033934471579680866230499 67550901707369521299345749)
                ·
                  refine ⟨197903032345809144431677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67550901707369521299345749 197903032345809144431677)
                  ·
                    rfl

theorem cell23_3468733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_3468733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468733 prefixEnd_3468733 := by exact prefixLift 3468733
  have htrace : WordTrace (prefixWord ++ tailWord_3468733) baseStart_3468733 baseEnd_3468733 := by
    simpa [prefixWord, tailWord_3468733, baseEnd_3468733] using wordTrace_append hprefix tailTrace_3468733
  have hstable : (prefixWord ++ tailWord_3468733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468733).length < 2 ^ (prefixWord ++ tailWord_3468733).sum := by decide
  have hdescent : baseEnd_3468733 < baseStart_3468733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468763 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 9, 5]
def baseStart_3468763 : Nat := 118140960795 + 3468763 * 2 ^ 59
def prefixEnd_3468763 : Nat := 4983230072969 + 3 ^ 40 * 3468763 * 2
def baseEnd_3468763 : Nat := 593714231843972394169985

theorem tailTrace_3468763 : CollatzResearch.WordTrace tailWord_3468763 prefixEnd_3468763 593714231843972394169985 := by
  unfold tailWord_3468763
  simp only [CollatzResearch.WordTrace]
  refine ⟨126516180332271543400738943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84344120221514362267159295 126516180332271543400738943)
  ·
    refine ⟨189774270498407315101108415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126516180332271543400738943 189774270498407315101108415)
    ·
      refine ⟨284661405747610972651662623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189774270498407315101108415 284661405747610972651662623)
      ·
        refine ⟨426992108621416458977493935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284661405747610972651662623 426992108621416458977493935)
        ·
          refine ⟨640488162932124688466240903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426992108621416458977493935 640488162932124688466240903)
          ·
            refine ⟨960732244398187032699361355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640488162932124688466240903 960732244398187032699361355)
            ·
              refine ⟨1441098366597280549049042033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960732244398187032699361355 1441098366597280549049042033)
              ·
                refine ⟨1080823774947960411786781525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441098366597280549049042033 1080823774947960411786781525)
                ·
                  refine ⟨6332951806335705537813173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1080823774947960411786781525 6332951806335705537813173)
                  ·
                    refine ⟨593714231843972394169985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6332951806335705537813173 593714231843972394169985)
                    ·
                      rfl

theorem cell23_3468763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 5].length) (baseStart_3468763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468763 prefixEnd_3468763 := by exact prefixLift 3468763
  have htrace : WordTrace (prefixWord ++ tailWord_3468763) baseStart_3468763 baseEnd_3468763 := by
    simpa [prefixWord, tailWord_3468763, baseEnd_3468763] using wordTrace_append hprefix tailTrace_3468763
  have hstable : (prefixWord ++ tailWord_3468763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468763).length < 2 ^ (prefixWord ++ tailWord_3468763).sum := by decide
  have hdescent : baseEnd_3468763 < baseStart_3468763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468780 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_3468780 : Nat := 118140960795 + 3468780 * 2 ^ 59
def prefixEnd_3468780 : Nat := 4983230072969 + 3 ^ 40 * 3468780 * 2
def baseEnd_3468780 : Nat := 593717141567681205332459

theorem tailTrace_3468780 : CollatzResearch.WordTrace tailWord_3468780 prefixEnd_3468780 593717141567681205332459 := by
  unfold tailWord_3468780
  simp only [CollatzResearch.WordTrace]
  refine ⟨63258400186604977652053897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84344533582139970202738529 63258400186604977652053897)
  ·
    refine ⟨47443800139953733239040423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63258400186604977652053897 47443800139953733239040423)
    ·
      refine ⟨71165700209930599858560635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47443800139953733239040423 71165700209930599858560635)
      ·
        refine ⟨106748550314895899787840953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71165700209930599858560635 106748550314895899787840953)
        ·
          refine ⟨80061412736171924840880715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106748550314895899787840953 80061412736171924840880715)
          ·
            refine ⟨120092119104257887261321073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80061412736171924840880715 120092119104257887261321073)
            ·
              refine ⟨90069089328193415445990805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120092119104257887261321073 90069089328193415445990805)
              ·
                refine ⟨4221988562259066349030819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90069089328193415445990805 4221988562259066349030819)
                ·
                  refine ⟨6332982843388599523546229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221988562259066349030819 6332982843388599523546229)
                  ·
                    refine ⟨593717141567681205332459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6332982843388599523546229 593717141567681205332459)
                    ·
                      rfl

theorem cell23_3468780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_3468780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468780 prefixEnd_3468780 := by exact prefixLift 3468780
  have htrace : WordTrace (prefixWord ++ tailWord_3468780) baseStart_3468780 baseEnd_3468780 := by
    simpa [prefixWord, tailWord_3468780, baseEnd_3468780] using wordTrace_append hprefix tailTrace_3468780
  have hstable : (prefixWord ++ tailWord_3468780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468780).length < 2 ^ (prefixWord ++ tailWord_3468780).sum := by decide
  have hdescent : baseEnd_3468780 < baseStart_3468780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468794 : List Nat := [3, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3]
def baseStart_3468794 : Nat := 118140960795 + 3468794 * 2 ^ 59
def prefixEnd_3468794 : Nat := 4983230072969 + 3 ^ 40 * 3468794 * 2
def baseEnd_3468794 : Nat := 1781158613432206561222313

theorem tailTrace_3468794 : CollatzResearch.WordTrace tailWord_3468794 prefixEnd_3468794 1781158613432206561222313 := by
  unfold tailWord_3468794
  simp only [CollatzResearch.WordTrace]
  refine ⟨31629327748789808923779359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84344873996772823796744957 31629327748789808923779359)
  ·
    refine ⟨47443991623184713385669039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31629327748789808923779359 47443991623184713385669039)
    ·
      refine ⟨71165987434777070078503559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47443991623184713385669039 71165987434777070078503559)
      ·
        refine ⟨106748981152165605117755339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71165987434777070078503559 106748981152165605117755339)
        ·
          refine ⟨160123471728248407676633009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106748981152165605117755339 160123471728248407676633009)
          ·
            refine ⟨120092603796186305757474757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160123471728248407676633009 120092603796186305757474757)
            ·
              refine ⟨22517363211784932329526517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120092603796186305757474757 22517363211784932329526517)
              ·
                refine ⟨2111002801104837405893111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22517363211784932329526517 2111002801104837405893111)
                ·
                  refine ⟨3166504201657256108839667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111002801104837405893111 3166504201657256108839667)
                  ·
                    refine ⟨4749756302485884163259501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166504201657256108839667 4749756302485884163259501)
                    ·
                      refine ⟨1781158613432206561222313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4749756302485884163259501 1781158613432206561222313)
                      ·
                        rfl

theorem cell23_3468794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3].length) (baseStart_3468794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468794 prefixEnd_3468794 := by exact prefixLift 3468794
  have htrace : WordTrace (prefixWord ++ tailWord_3468794) baseStart_3468794 baseEnd_3468794 := by
    simpa [prefixWord, tailWord_3468794, baseEnd_3468794] using wordTrace_append hprefix tailTrace_3468794
  have hstable : (prefixWord ++ tailWord_3468794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468794).length < 2 ^ (prefixWord ++ tailWord_3468794).sum := by decide
  have hdescent : baseEnd_3468794 < baseStart_3468794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468811 : List Nat := [1, 1, 1, 1, 8, 1, 1, 4, 1, 1, 3]
def baseStart_3468811 : Nat := 118140960795 + 3468811 * 2 ^ 59
def prefixEnd_3468811 : Nat := 4983230072969 + 3 ^ 40 * 3468811 * 2
def baseEnd_3468811 : Nat := 1781167342603332994709735

theorem tailTrace_3468811 : CollatzResearch.WordTrace tailWord_3468811 prefixEnd_3468811 1781167342603332994709735 := by
  unfold tailWord_3468811
  simp only [CollatzResearch.WordTrace]
  refine ⟨126517931036097647598486287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84345287357398431732324191 126517931036097647598486287)
  ·
    refine ⟨189776896554146471397729431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126517931036097647598486287 189776896554146471397729431)
    ·
      refine ⟨284665344831219707096594147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189776896554146471397729431 284665344831219707096594147)
      ·
        refine ⟨426998017246829560644891221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284665344831219707096594147 426998017246829560644891221)
        ·
          refine ⟨5003883014611283913807319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 426998017246829560644891221 5003883014611283913807319)
          ·
            refine ⟨7505824521916925870710979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003883014611283913807319 7505824521916925870710979)
            ·
              refine ⟨11258736782875388806066469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7505824521916925870710979 11258736782875388806066469)
              ·
                refine ⟨2111013146789135401137463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11258736782875388806066469 2111013146789135401137463)
                ·
                  refine ⟨3166519720183703101706195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111013146789135401137463 3166519720183703101706195)
                  ·
                    refine ⟨4749779580275554652559293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166519720183703101706195 4749779580275554652559293)
                    ·
                      refine ⟨1781167342603332994709735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4749779580275554652559293 1781167342603332994709735)
                      ·
                        rfl

theorem cell23_3468811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 1, 3].length) (baseStart_3468811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468811 prefixEnd_3468811 := by exact prefixLift 3468811
  have htrace : WordTrace (prefixWord ++ tailWord_3468811) baseStart_3468811 baseEnd_3468811 := by
    simpa [prefixWord, tailWord_3468811, baseEnd_3468811] using wordTrace_append hprefix tailTrace_3468811
  have hstable : (prefixWord ++ tailWord_3468811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468811).length < 2 ^ (prefixWord ++ tailWord_3468811).sum := by decide
  have hdescent : baseEnd_3468811 < baseStart_3468811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468834 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_3468834 : Nat := 118140960795 + 3468834 * 2 ^ 59
def prefixEnd_3468834 : Nat := 4983230072969 + 3 ^ 40 * 3468834 * 2
def baseEnd_3468834 : Nat := 1781179152658386404722129

theorem tailTrace_3468834 : CollatzResearch.WordTrace tailWord_3468834 prefixEnd_3468834 1781179152658386404722129 := by
  unfold tailWord_3468834
  simp only [CollatzResearch.WordTrace]
  refine ⟨31629692478753580631643389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84345846610009548351049037 31629692478753580631643389)
  ·
    refine ⟨11861134679532592736866271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31629692478753580631643389 11861134679532592736866271)
    ·
      refine ⟨17791702019298889105299407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11861134679532592736866271 17791702019298889105299407)
      ·
        refine ⟨26687553028948333657949111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17791702019298889105299407 26687553028948333657949111)
        ·
          refine ⟨40031329543422500486923667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26687553028948333657949111 40031329543422500486923667)
          ·
            refine ⟨60046994315133750730385501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40031329543422500486923667 60046994315133750730385501)
            ·
              refine ⟨22517622868175156523894563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60046994315133750730385501 22517622868175156523894563)
              ·
                refine ⟨33776434302262734785841845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22517622868175156523894563 33776434302262734785841845)
                ·
                  refine ⟨3166540715837131386172673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33776434302262734785841845 3166540715837131386172673)
                  ·
                    refine ⟨2374905536877848539629505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3166540715837131386172673 2374905536877848539629505)
                    ·
                      refine ⟨1781179152658386404722129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2374905536877848539629505 1781179152658386404722129)
                      ·
                        rfl

theorem cell23_3468834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_3468834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468834 prefixEnd_3468834 := by exact prefixLift 3468834
  have htrace : WordTrace (prefixWord ++ tailWord_3468834) baseStart_3468834 baseEnd_3468834 := by
    simpa [prefixWord, tailWord_3468834, baseEnd_3468834] using wordTrace_append hprefix tailTrace_3468834
  have hstable : (prefixWord ++ tailWord_3468834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468834).length < 2 ^ (prefixWord ++ tailWord_3468834).sum := by decide
  have hdescent : baseEnd_3468834 < baseStart_3468834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468837 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 3]
def baseStart_3468837 : Nat := 118140960795 + 3468837 * 2 ^ 59
def prefixEnd_3468837 : Nat := 4983230072969 + 3 ^ 40 * 3468837 * 2
def baseEnd_3468837 : Nat := 1781180693100349892984615

theorem tailTrace_3468837 : CollatzResearch.WordTrace tailWord_3468837 prefixEnd_3468837 1781180693100349892984615 := by
  unfold tailWord_3468837
  simp only [CollatzResearch.WordTrace]
  refine ⟨126518879334003454038932765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84345919556002302692621843 126518879334003454038932765)
  ·
    refine ⟨47444579750251295264599787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126518879334003454038932765 47444579750251295264599787)
    ·
      refine ⟨71166869625376942896899681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47444579750251295264599787 71166869625376942896899681)
      ·
        refine ⟨53375152219032707172674761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71166869625376942896899681 53375152219032707172674761)
        ·
          refine ⟨40031364164274530379506071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53375152219032707172674761 40031364164274530379506071)
          ·
            refine ⟨60047046246411795569259107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40031364164274530379506071 60047046246411795569259107)
            ·
              refine ⟨90070569369617693353888661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60047046246411795569259107 90070569369617693353888661)
              ·
                refine ⟨4222057939200829375963531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90070569369617693353888661 4222057939200829375963531)
                ·
                  refine ⟨6333086908801244063945297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222057939200829375963531 6333086908801244063945297)
                  ·
                    refine ⟨4749815181600933047958973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6333086908801244063945297 4749815181600933047958973)
                    ·
                      refine ⟨1781180693100349892984615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4749815181600933047958973 1781180693100349892984615)
                      ·
                        rfl

theorem cell23_3468837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_3468837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468837 prefixEnd_3468837 := by exact prefixLift 3468837
  have htrace : WordTrace (prefixWord ++ tailWord_3468837) baseStart_3468837 baseEnd_3468837 := by
    simpa [prefixWord, tailWord_3468837, baseEnd_3468837] using wordTrace_append hprefix tailTrace_3468837
  have hstable : (prefixWord ++ tailWord_3468837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468837).length < 2 ^ (prefixWord ++ tailWord_3468837).sum := by decide
  have hdescent : baseEnd_3468837 < baseStart_3468837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468851 : List Nat := [1, 1, 1, 2, 4, 3, 1, 5, 1, 2, 2]
def baseStart_3468851 : Nat := 118140960795 + 3468851 * 2 ^ 59
def prefixEnd_3468851 : Nat := 4983230072969 + 3 ^ 40 * 3468851 * 2
def baseEnd_3468851 : Nat := 1781187881829512838209551

theorem tailTrace_3468851 : CollatzResearch.WordTrace tailWord_3468851 prefixEnd_3468851 1781187881829512838209551 := by
  unfold tailWord_3468851
  simp only [CollatzResearch.WordTrace]
  refine ⟨126519389955952734429942407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84346259970635156286628271 126519389955952734429942407)
  ·
    refine ⟨189779084933929101644913611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126519389955952734429942407 189779084933929101644913611)
    ·
      refine ⟨284668627400893652467370417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189779084933929101644913611 284668627400893652467370417)
      ·
        refine ⟨213501470550670239350527813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284668627400893652467370417 213501470550670239350527813)
        ·
          refine ⟨40031525728250669878223965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213501470550670239350527813 40031525728250669878223965)
          ·
            refine ⟨15011822148094001204333987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40031525728250669878223965 15011822148094001204333987)
            ·
              refine ⟨22517733222141001806500981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15011822148094001204333987 22517733222141001806500981)
              ·
                refine ⟨2111037489575718919359467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22517733222141001806500981 2111037489575718919359467)
                ·
                  refine ⟨3166556234363578379039201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111037489575718919359467 3166556234363578379039201)
                  ·
                    refine ⟨2374917175772683784279401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3166556234363578379039201 2374917175772683784279401)
                    ·
                      refine ⟨1781187881829512838209551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2374917175772683784279401 1781187881829512838209551)
                      ·
                        rfl

theorem cell23_3468851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 2, 2].length) (baseStart_3468851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468851 prefixEnd_3468851 := by exact prefixLift 3468851
  have htrace : WordTrace (prefixWord ++ tailWord_3468851) baseStart_3468851 baseEnd_3468851 := by
    simpa [prefixWord, tailWord_3468851, baseEnd_3468851] using wordTrace_append hprefix tailTrace_3468851
  have hstable : (prefixWord ++ tailWord_3468851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468851).length < 2 ^ (prefixWord ++ tailWord_3468851).sum := by decide
  have hdescent : baseEnd_3468851 < baseStart_3468851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468861 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_3468861 : Nat := 118140960795 + 3468861 * 2 ^ 59
def prefixEnd_3468861 : Nat := 4983230072969 + 3 ^ 40 * 3468861 * 2
def baseEnd_3468861 : Nat := 593731005545352599694835

theorem tailTrace_3468861 : CollatzResearch.WordTrace tailWord_3468861 prefixEnd_3468861 593731005545352599694835 := by
  unfold tailWord_3468861
  simp only [CollatzResearch.WordTrace]
  refine ⟨126519754685916506137806437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84346503123944337425204291 126519754685916506137806437)
  ·
    refine ⟨23722454003609344900838707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126519754685916506137806437 23722454003609344900838707)
    ·
      refine ⟨35583681005414017351258061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23722454003609344900838707 35583681005414017351258061)
      ·
        refine ⟨13343880377030256506721773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35583681005414017351258061 13343880377030256506721773)
        ·
          refine ⟨5003955141386346190020665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13343880377030256506721773 5003955141386346190020665)
          ·
            refine ⟨3752966356039759642515499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5003955141386346190020665 3752966356039759642515499)
            ·
              refine ⟨5629449534059639463773249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752966356039759642515499 5629449534059639463773249)
              ·
                refine ⟨4222087150544729597829937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5629449534059639463773249 4222087150544729597829937)
                ·
                  refine ⟨3166565362908547198372453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4222087150544729597829937 3166565362908547198372453)
                  ·
                    refine ⟨593731005545352599694835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3166565362908547198372453 593731005545352599694835)
                    ·
                      rfl

theorem cell23_3468861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_3468861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468861 prefixEnd_3468861 := by exact prefixLift 3468861
  have htrace : WordTrace (prefixWord ++ tailWord_3468861) baseStart_3468861 baseEnd_3468861 := by
    simpa [prefixWord, tailWord_3468861, baseEnd_3468861] using wordTrace_append hprefix tailTrace_3468861
  have hstable : (prefixWord ++ tailWord_3468861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468861).length < 2 ^ (prefixWord ++ tailWord_3468861).sum := by decide
  have hdescent : baseEnd_3468861 < baseStart_3468861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468890 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_3468890 : Nat := 118140960795 + 3468890 * 2 ^ 59
def prefixEnd_3468890 : Nat := 4983230072969 + 3 ^ 40 * 3468890 * 2
def baseEnd_3468890 : Nat := 1781207907575038185621871

theorem tailTrace_3468890 : CollatzResearch.WordTrace tailWord_3468890 prefixEnd_3468890 1781207907575038185621871 := by
  unfold tailWord_3468890
  simp only [CollatzResearch.WordTrace]
  refine ⟨31630203100702861022653031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84347208268540962727074749 31630203100702861022653031)
  ·
    refine ⟨47445304651054291533979547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31630203100702861022653031 47445304651054291533979547)
    ·
      refine ⟨71167956976581437300969321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47445304651054291533979547 71167956976581437300969321)
      ·
        refine ⟨53375967732436077975726991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71167956976581437300969321 53375967732436077975726991)
        ·
          refine ⟨80063951598654116963590487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53375967732436077975726991 80063951598654116963590487)
          ·
            refine ⟨120095927397981175445385731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80063951598654116963590487 120095927397981175445385731)
            ·
              refine ⟨180143891096971763168078597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120095927397981175445385731 180143891096971763168078597)
              ·
                refine ⟨33776979580682205594014737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180143891096971763168078597 33776979580682205594014737)
                ·
                  refine ⟨25332734685511654195511053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33776979580682205594014737 25332734685511654195511053)
                  ·
                    refine ⟨9499775507066870323316645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25332734685511654195511053 9499775507066870323316645)
                    ·
                      refine ⟨1781207907575038185621871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9499775507066870323316645 1781207907575038185621871)
                      ·
                        rfl

theorem cell23_3468890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_3468890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468890 prefixEnd_3468890 := by exact prefixLift 3468890
  have htrace : WordTrace (prefixWord ++ tailWord_3468890) baseStart_3468890 baseEnd_3468890 := by
    simpa [prefixWord, tailWord_3468890, baseEnd_3468890] using wordTrace_append hprefix tailTrace_3468890
  have hstable : (prefixWord ++ tailWord_3468890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468890).length < 2 ^ (prefixWord ++ tailWord_3468890).sum := by decide
  have hdescent : baseEnd_3468890 < baseStart_3468890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468957 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_3468957 : Nat := 118140960795 + 3468957 * 2 ^ 59
def prefixEnd_3468957 : Nat := 4983230072969 + 3 ^ 40 * 3468957 * 2
def baseEnd_3468957 : Nat := 1781242310778889423484063

theorem tailTrace_3468957 : CollatzResearch.WordTrace tailWord_3468957 prefixEnd_3468957 1781242310778889423484063 := by
  unfold tailWord_3468957
  simp only [CollatzResearch.WordTrace]
  refine ⟨126523256093568714533301125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84348837395712476355534083 126523256093568714533301125)
  ·
    refine ⟨23723110517544133974993961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126523256093568714533301125 23723110517544133974993961)
    ·
      refine ⟨17792332888158100481245471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23723110517544133974993961 17792332888158100481245471)
      ·
        refine ⟨26688499332237150721868207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17792332888158100481245471 26688499332237150721868207)
        ·
          refine ⟨40032748998355726082802311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26688499332237150721868207 40032748998355726082802311)
          ·
            refine ⟨60049123497533589124203467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40032748998355726082802311 60049123497533589124203467)
            ·
              refine ⟨90073685246300383686305201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60049123497533589124203467 90073685246300383686305201)
              ·
                refine ⟨67555263934725287764728901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90073685246300383686305201 67555263934725287764728901)
                ·
                  refine ⟨12666611987760991455886669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67555263934725287764728901 12666611987760991455886669)
                  ·
                    refine ⟨4749979495410371795957501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12666611987760991455886669 4749979495410371795957501)
                    ·
                      refine ⟨1781242310778889423484063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4749979495410371795957501 1781242310778889423484063)
                      ·
                        rfl

theorem cell23_3468957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_3468957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468957 prefixEnd_3468957 := by exact prefixLift 3468957
  have htrace : WordTrace (prefixWord ++ tailWord_3468957) baseStart_3468957 baseEnd_3468957 := by
    simpa [prefixWord, tailWord_3468957, baseEnd_3468957] using wordTrace_append hprefix tailTrace_3468957
  have hstable : (prefixWord ++ tailWord_3468957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468957).length < 2 ^ (prefixWord ++ tailWord_3468957).sum := by decide
  have hdescent : baseEnd_3468957 < baseStart_3468957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468981 : List Nat := [1, 3, 3, 3, 2, 1, 1, 4, 5]
def baseStart_3468981 : Nat := 118140960795 + 3468981 * 2 ^ 59
def prefixEnd_3468981 : Nat := 4983230072969 + 3 ^ 40 * 3468981 * 2
def baseEnd_3468981 : Nat := 197917181590510814398217

theorem tailTrace_3468981 : CollatzResearch.WordTrace tailWord_3468981 prefixEnd_3468981 197917181590510814398217 := by
  unfold tailWord_3468981
  simp only [CollatzResearch.WordTrace]
  refine ⟨126524131445481766632174797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84349420963654511088116531 126524131445481766632174797)
  ·
    refine ⟨47446549292055662487065549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126524131445481766632174797 47446549292055662487065549)
    ·
      refine ⟨17792455984520873432649581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47446549292055662487065549 17792455984520873432649581)
      ·
        refine ⟨6672170994195327537243593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17792455984520873432649581 6672170994195327537243593)
        ·
          refine ⟨5004128245646495652932695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6672170994195327537243593 5004128245646495652932695)
          ·
            refine ⟨7506192368469743479399043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004128245646495652932695 7506192368469743479399043)
            ·
              refine ⟨11259288552704615219098565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7506192368469743479399043 11259288552704615219098565)
              ·
                refine ⟨2111116603632115353580981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11259288552704615219098565 2111116603632115353580981)
                ·
                  refine ⟨197917181590510814398217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2111116603632115353580981 197917181590510814398217)
                  ·
                    rfl

theorem cell23_3468981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_3468981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3468981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3468981 prefixEnd_3468981 := by exact prefixLift 3468981
  have htrace : WordTrace (prefixWord ++ tailWord_3468981) baseStart_3468981 baseEnd_3468981 := by
    simpa [prefixWord, tailWord_3468981, baseEnd_3468981] using wordTrace_append hprefix tailTrace_3468981
  have hstable : (prefixWord ++ tailWord_3468981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468981).length < 2 ^ (prefixWord ++ tailWord_3468981).sum := by decide
  have hdescent : baseEnd_3468981 < baseStart_3468981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469034 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_3469034 : Nat := 118140960795 + 3469034 * 2 ^ 59
def prefixEnd_3469034 : Nat := 4983230072969 + 3 ^ 40 * 3469034 * 2
def baseEnd_3469034 : Nat := 1781281848789285622221209

theorem tailTrace_3469034 : CollatzResearch.WordTrace tailWord_3469034 prefixEnd_3469034 1781281848789285622221209 := by
  unfold tailWord_3469034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31631516128572439170963539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84350709676193171122569437 31631516128572439170963539)
  ·
    refine ⟨47447274192858658756445309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31631516128572439170963539 47447274192858658756445309)
    ·
      refine ⟨17792727822321997033666991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47447274192858658756445309 17792727822321997033666991)
      ·
        refine ⟨26689091733482995550500487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17792727822321997033666991 26689091733482995550500487)
        ·
          refine ⟨40033637600224493325750731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26689091733482995550500487 40033637600224493325750731)
          ·
            refine ⟨60050456400336739988626097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40033637600224493325750731 60050456400336739988626097)
            ·
              refine ⟨45037842300252554991469573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60050456400336739988626097 45037842300252554991469573)
              ·
                refine ⟨8444595431297354060900545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45037842300252554991469573 8444595431297354060900545)
                ·
                  refine ⟨6333446573473015545675409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8444595431297354060900545 6333446573473015545675409)
                  ·
                    refine ⟨4750084930104761659256557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6333446573473015545675409 4750084930104761659256557)
                    ·
                      refine ⟨1781281848789285622221209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4750084930104761659256557 1781281848789285622221209)
                      ·
                        rfl

theorem cell23_3469034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_3469034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469034 prefixEnd_3469034 := by exact prefixLift 3469034
  have htrace : WordTrace (prefixWord ++ tailWord_3469034) baseStart_3469034 baseEnd_3469034 := by
    simpa [prefixWord, tailWord_3469034, baseEnd_3469034] using wordTrace_append hprefix tailTrace_3469034
  have hstable : (prefixWord ++ tailWord_3469034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469034).length < 2 ^ (prefixWord ++ tailWord_3469034).sum := by decide
  have hdescent : baseEnd_3469034 < baseStart_3469034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469041 : List Nat := [1, 2, 2, 2, 2, 3, 2, 4, 1, 4]
def baseStart_3469041 : Nat := 118140960795 + 3469041 * 2 ^ 59
def prefixEnd_3469041 : Nat := 4983230072969 + 3 ^ 40 * 3469041 * 2
def baseEnd_3469041 : Nat := 593761814384622364944559

theorem tailTrace_3469041 : CollatzResearch.WordTrace tailWord_3469041 prefixEnd_3469041 593761814384622364944559 := by
  unfold tailWord_3469041
  simp only [CollatzResearch.WordTrace]
  refine ⟨126526319825264396879358977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84350879883509597919572651 126526319825264396879358977)
  ·
    refine ⟨94894739868948297659519233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126526319825264396879358977 94894739868948297659519233)
    ·
      refine ⟨71171054901711223244639425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94894739868948297659519233 71171054901711223244639425)
      ·
        refine ⟨53378291176283417433479569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71171054901711223244639425 53378291176283417433479569)
        ·
          refine ⟨40033718382212563075109677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53378291176283417433479569 40033718382212563075109677)
          ·
            refine ⟨15012644393329711153166129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40033718382212563075109677 15012644393329711153166129)
            ·
              refine ⟨11259483294997283364874597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15012644393329711153166129 11259483294997283364874597)
              ·
                refine ⟨2111153117811990630913987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11259483294997283364874597 2111153117811990630913987)
                ·
                  refine ⟨3166729676717985946370981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111153117811990630913987 3166729676717985946370981)
                  ·
                    refine ⟨593761814384622364944559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3166729676717985946370981 593761814384622364944559)
                    ·
                      rfl

theorem cell23_3469041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_3469041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469041 prefixEnd_3469041 := by exact prefixLift 3469041
  have htrace : WordTrace (prefixWord ++ tailWord_3469041) baseStart_3469041 baseEnd_3469041 := by
    simpa [prefixWord, tailWord_3469041, baseEnd_3469041] using wordTrace_append hprefix tailTrace_3469041
  have hstable : (prefixWord ++ tailWord_3469041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469041).length < 2 ^ (prefixWord ++ tailWord_3469041).sum := by decide
  have hdescent : baseEnd_3469041 < baseStart_3469041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469067 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 3, 5]
def baseStart_3469067 : Nat := 118140960795 + 3469067 * 2 ^ 59
def prefixEnd_3469067 : Nat := 4983230072969 + 3 ^ 40 * 3469067 * 2
def baseEnd_3469067 : Nat := 593766264550294664369519

theorem tailTrace_3469067 : CollatzResearch.WordTrace tailWord_3469067 prefixEnd_3469067 593766264550294664369519 := by
  unfold tailWord_3469067
  simp only [CollatzResearch.WordTrace]
  refine ⟨126527268123170203319805455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84351512082113468879870303 126527268123170203319805455)
  ·
    refine ⟨189790902184755304979708183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126527268123170203319805455 189790902184755304979708183)
    ·
      refine ⟨284686353277132957469562275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189790902184755304979708183 284686353277132957469562275)
      ·
        refine ⟨427029529915699436204343413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284686353277132957469562275 427029529915699436204343413)
        ·
          refine ⟨40034018429596822144157195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 427029529915699436204343413 40034018429596822144157195)
          ·
            refine ⟨60051027644395233216235793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40034018429596822144157195 60051027644395233216235793)
            ·
              refine ⟨45038270733296424912176845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60051027644395233216235793 45038270733296424912176845)
              ·
                refine ⟨16889351524986159342066317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45038270733296424912176845 16889351524986159342066317)
                ·
                  refine ⟨6333506821869809753274869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16889351524986159342066317 6333506821869809753274869)
                  ·
                    refine ⟨593766264550294664369519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6333506821869809753274869 593766264550294664369519)
                    ·
                      rfl

theorem cell23_3469067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 5].length) (baseStart_3469067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469067 prefixEnd_3469067 := by exact prefixLift 3469067
  have htrace : WordTrace (prefixWord ++ tailWord_3469067) baseStart_3469067 baseEnd_3469067 := by
    simpa [prefixWord, tailWord_3469067, baseEnd_3469067] using wordTrace_append hprefix tailTrace_3469067
  have hstable : (prefixWord ++ tailWord_3469067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469067).length < 2 ^ (prefixWord ++ tailWord_3469067).sum := by decide
  have hdescent : baseEnd_3469067 < baseStart_3469067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469084 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_3469084 : Nat := 118140960795 + 3469084 * 2 ^ 59
def prefixEnd_3469084 : Nat := 4983230072969 + 3 ^ 40 * 3469084 * 2
def baseEnd_3469084 : Nat := 593769174274003475531993

theorem tailTrace_3469084 : CollatzResearch.WordTrace tailWord_3469084 prefixEnd_3469084 593769174274003475531993 := by
  unfold tailWord_3469084
  simp only [CollatzResearch.WordTrace]
  refine ⟨63263944082054307611587153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84351925442739076815449537 63263944082054307611587153)
  ·
    refine ⟨47447958061540730708690365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63263944082054307611587153 47447958061540730708690365)
    ·
      refine ⟨17792984273077774015758887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47447958061540730708690365 17792984273077774015758887)
      ·
        refine ⟨26689476409616661023638331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17792984273077774015758887 26689476409616661023638331)
        ·
          refine ⟨40034214614424991535457497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26689476409616661023638331 40034214614424991535457497)
          ·
            refine ⟨30025660960818743651593123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40034214614424991535457497 30025660960818743651593123)
            ·
              refine ⟨45038491441228115477389685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30025660960818743651593123 45038491441228115477389685)
              ·
                refine ⟨4222358572615135826005283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45038491441228115477389685 4222358572615135826005283)
                ·
                  refine ⟨6333537858922703739007925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222358572615135826005283 6333537858922703739007925)
                  ·
                    refine ⟨593769174274003475531993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6333537858922703739007925 593769174274003475531993)
                    ·
                      rfl

theorem cell23_3469084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_3469084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469084 prefixEnd_3469084 := by exact prefixLift 3469084
  have htrace : WordTrace (prefixWord ++ tailWord_3469084) baseStart_3469084 baseEnd_3469084 := by
    simpa [prefixWord, tailWord_3469084, baseEnd_3469084] using wordTrace_append hprefix tailTrace_3469084
  have hstable : (prefixWord ++ tailWord_3469084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469084).length < 2 ^ (prefixWord ++ tailWord_3469084).sum := by decide
  have hdescent : baseEnd_3469084 < baseStart_3469084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469118 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_3469118 : Nat := 118140960795 + 3469118 * 2 ^ 59
def prefixEnd_3469118 : Nat := 4983230072969 + 3 ^ 40 * 3469118 * 2
def baseEnd_3469118 : Nat := 593774993721421097856941

theorem tailTrace_3469118 : CollatzResearch.WordTrace tailWord_3469118 prefixEnd_3469118 593774993721421097856941 := by
  unfold tailWord_3469118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15816141030748179878739001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84352752163990292686608005 15816141030748179878739001)
  ·
    refine ⟨11862105773061134909054251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15816141030748179878739001 11862105773061134909054251)
    ·
      refine ⟨17793158659591702363581377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11862105773061134909054251 17793158659591702363581377)
      ·
        refine ⟨13344868994693776772686033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17793158659591702363581377 13344868994693776772686033)
        ·
          refine ⟨10008651746020332579514525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13344868994693776772686033 10008651746020332579514525)
          ·
            refine ⟨3753244404757624717317947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10008651746020332579514525 3753244404757624717317947)
            ·
              refine ⟨5629866607136437075976921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753244404757624717317947 5629866607136437075976921)
              ·
                refine ⟨4222399955352327806982691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5629866607136437075976921 4222399955352327806982691)
                ·
                  refine ⟨6333599933028491710474037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222399955352327806982691 6333599933028491710474037)
                  ·
                    refine ⟨593774993721421097856941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6333599933028491710474037 593774993721421097856941)
                    ·
                      rfl

theorem cell23_3469118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_3469118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469118 prefixEnd_3469118 := by exact prefixLift 3469118
  have htrace : WordTrace (prefixWord ++ tailWord_3469118) baseStart_3469118 baseEnd_3469118 := by
    simpa [prefixWord, tailWord_3469118, baseEnd_3469118] using wordTrace_append hprefix tailTrace_3469118
  have hstable : (prefixWord ++ tailWord_3469118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469118).length < 2 ^ (prefixWord ++ tailWord_3469118).sum := by decide
  have hdescent : baseEnd_3469118 < baseStart_3469118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469127 : List Nat := [1, 1, 4, 1, 2, 1, 4, 9]
def baseStart_3469127 : Nat := 118140960795 + 3469127 * 2 ^ 59
def prefixEnd_3469127 : Nat := 4983230072969 + 3 ^ 40 * 3469127 * 2
def baseEnd_3469127 : Nat := 65975170462598287346603

theorem tailTrace_3469127 : CollatzResearch.WordTrace tailWord_3469127 prefixEnd_3469127 65975170462598287346603 := by
  unfold tailWord_3469127
  simp only [CollatzResearch.WordTrace]
  refine ⟨126529456502952833566989635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84352971001968555711326423 126529456502952833566989635)
  ·
    refine ⟨189794184754429250350484453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126529456502952833566989635 189794184754429250350484453)
    ·
      refine ⟨35586409641455484440715835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189794184754429250350484453 35586409641455484440715835)
      ·
        refine ⟨53379614462183226661073753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35586409641455484440715835 53379614462183226661073753)
        ·
          refine ⟨40034710846637419995805315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53379614462183226661073753 40034710846637419995805315)
          ·
            refine ⟨60052066269956129993707973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40034710846637419995805315 60052066269956129993707973)
            ·
              refine ⟨11259762425616774373820245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60052066269956129993707973 11259762425616774373820245)
              ·
                refine ⟨65975170462598287346603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11259762425616774373820245 65975170462598287346603)
                ·
                  rfl

theorem cell23_3469127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 9].length) (baseStart_3469127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469127 prefixEnd_3469127 := by exact prefixLift 3469127
  have htrace : WordTrace (prefixWord ++ tailWord_3469127) baseStart_3469127 baseEnd_3469127 := by
    simpa [prefixWord, tailWord_3469127, baseEnd_3469127] using wordTrace_append hprefix tailTrace_3469127
  have hstable : (prefixWord ++ tailWord_3469127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469127).length < 2 ^ (prefixWord ++ tailWord_3469127).sum := by decide
  have hdescent : baseEnd_3469127 < baseStart_3469127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469138 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_3469138 : Nat := 118140960795 + 3469138 * 2 ^ 59
def prefixEnd_3469138 : Nat := 4983230072969 + 3 ^ 40 * 3469138 * 2
def baseEnd_3469138 : Nat := 1781335250777353215320731

theorem tailTrace_3469138 : CollatzResearch.WordTrace tailWord_3469138 prefixEnd_3469138 1781335250777353215320731 := by
  unfold tailWord_3469138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31632464426478245611410017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84353238470608654963760045 31632464426478245611410017)
  ·
    refine ⟨23724348319858684208557513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31632464426478245611410017 23724348319858684208557513)
    ·
      refine ⟨17793261239894013156418135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23724348319858684208557513 17793261239894013156418135)
      ·
        refine ⟨26689891859841019734627203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17793261239894013156418135 26689891859841019734627203)
        ·
          refine ⟨40034837789761529601940805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26689891859841019734627203 40034837789761529601940805)
          ·
            refine ⟨7506532085580286800363901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40034837789761529601940805 7506532085580286800363901)
            ·
              refine ⟨2814949532092607550136463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7506532085580286800363901 2814949532092607550136463)
              ·
                refine ⟨4222424298138911325204695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814949532092607550136463 4222424298138911325204695)
                ·
                  refine ⟨6333636447208366987807043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222424298138911325204695 6333636447208366987807043)
                  ·
                    refine ⟨9500454670812550481710565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6333636447208366987807043 9500454670812550481710565)
                    ·
                      refine ⟨1781335250777353215320731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9500454670812550481710565 1781335250777353215320731)
                      ·
                        rfl

theorem cell23_3469138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_3469138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469138 prefixEnd_3469138 := by exact prefixLift 3469138
  have htrace : WordTrace (prefixWord ++ tailWord_3469138) baseStart_3469138 baseEnd_3469138 := by
    simpa [prefixWord, tailWord_3469138, baseEnd_3469138] using wordTrace_append hprefix tailTrace_3469138
  have hstable : (prefixWord ++ tailWord_3469138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469138).length < 2 ^ (prefixWord ++ tailWord_3469138).sum := by decide
  have hdescent : baseEnd_3469138 < baseStart_3469138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469141 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_3469141 : Nat := 118140960795 + 3469141 * 2 ^ 59
def prefixEnd_3469141 : Nat := 4983230072969 + 3 ^ 40 * 3469141 * 2
def baseEnd_3469141 : Nat := 1781336791219316703583217

theorem tailTrace_3469141 : CollatzResearch.WordTrace tailWord_3469141 prefixEnd_3469141 1781336791219316703583217 := by
  unfold tailWord_3469141
  simp only [CollatzResearch.WordTrace]
  refine ⟨126529967124902113957999277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84353311416601409305332851 126529967124902113957999277)
  ·
    refine ⟨47448737671838292734249729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126529967124902113957999277 47448737671838292734249729)
    ·
      refine ⟨35586553253878719550687297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47448737671838292734249729 35586553253878719550687297)
      ·
        refine ⟨26689914940409039663015473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35586553253878719550687297 26689914940409039663015473)
        ·
          refine ⟨20017436205306779747261605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26689914940409039663015473 20017436205306779747261605)
          ·
            refine ⟨3753269288495021202611551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20017436205306779747261605 3753269288495021202611551)
            ·
              refine ⟨5629903932742531803917327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753269288495021202611551 5629903932742531803917327)
              ·
                refine ⟨8444855899113797705875991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629903932742531803917327 8444855899113797705875991)
                ·
                  refine ⟨12667283848670696558813987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8444855899113797705875991 12667283848670696558813987)
                  ·
                    refine ⟨19000925773006044838220981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12667283848670696558813987 19000925773006044838220981)
                    ·
                      refine ⟨1781336791219316703583217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19000925773006044838220981 1781336791219316703583217)
                      ·
                        rfl

theorem cell23_3469141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_3469141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469141 prefixEnd_3469141 := by exact prefixLift 3469141
  have htrace : WordTrace (prefixWord ++ tailWord_3469141) baseStart_3469141 baseEnd_3469141 := by
    simpa [prefixWord, tailWord_3469141, baseEnd_3469141] using wordTrace_append hprefix tailTrace_3469141
  have hstable : (prefixWord ++ tailWord_3469141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469141).length < 2 ^ (prefixWord ++ tailWord_3469141).sum := by decide
  have hdescent : baseEnd_3469141 < baseStart_3469141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469167 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_3469167 : Nat := 118140960795 + 3469167 * 2 ^ 59
def prefixEnd_3469167 : Nat := 4983230072969 + 3 ^ 40 * 3469167 * 2
def baseEnd_3469167 : Nat := 1781350141716333601858097

theorem tailTrace_3469167 : CollatzResearch.WordTrace tailWord_3469167 prefixEnd_3469167 1781350141716333601858097 := by
  unfold tailWord_3469167
  simp only [CollatzResearch.WordTrace]
  refine ⟨126530915422807920398445755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84353943615205280265630503 126530915422807920398445755)
  ·
    refine ⟨189796373134211880597668633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126530915422807920398445755 189796373134211880597668633)
    ·
      refine ⟨142347279850658910448251475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189796373134211880597668633 142347279850658910448251475)
      ·
        refine ⟨213520919775988365672377213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142347279850658910448251475 213520919775988365672377213)
        ·
          refine ⟨80070344915995637127141455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213520919775988365672377213 80070344915995637127141455)
          ·
            refine ⟨120105517373993455690712183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80070344915995637127141455 120105517373993455690712183)
            ·
              refine ⟨180158276060990183536068275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120105517373993455690712183 180158276060990183536068275)
              ·
                refine ⟨270237414091485275304102413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180158276060990183536068275 270237414091485275304102413)
                ·
                  refine ⟨101339030284306978239038405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270237414091485275304102413 101339030284306978239038405)
                  ·
                    refine ⟨19001068178307558419819701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101339030284306978239038405 19001068178307558419819701)
                    ·
                      refine ⟨1781350141716333601858097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19001068178307558419819701 1781350141716333601858097)
                      ·
                        rfl

theorem cell23_3469167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_3469167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469167 prefixEnd_3469167 := by exact prefixLift 3469167
  have htrace : WordTrace (prefixWord ++ tailWord_3469167) baseStart_3469167 baseEnd_3469167 := by
    simpa [prefixWord, tailWord_3469167, baseEnd_3469167] using wordTrace_append hprefix tailTrace_3469167
  have hstable : (prefixWord ++ tailWord_3469167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469167).length < 2 ^ (prefixWord ++ tailWord_3469167).sum := by decide
  have hdescent : baseEnd_3469167 < baseStart_3469167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469192 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_3469192 : Nat := 118140960795 + 3469192 * 2 ^ 59
def prefixEnd_3469192 : Nat := 4983230072969 + 3 ^ 40 * 3469192 * 2
def baseEnd_3469192 : Nat := 1781362978732696004045483

theorem tailTrace_3469192 : CollatzResearch.WordTrace tailWord_3469192 prefixEnd_3469192 1781362978732696004045483 := by
  unfold tailWord_3469192
  simp only [CollatzResearch.WordTrace]
  refine ⟨63265913623858674834052915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84354551498478233112070553 63265913623858674834052915)
  ·
    refine ⟨94898870435788012251079373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63265913623858674834052915 94898870435788012251079373)
    ·
      refine ⟨35587076413420504594154765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94898870435788012251079373 35587076413420504594154765)
      ·
        refine ⟨13345153655032689222808037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35587076413420504594154765 13345153655032689222808037)
        ·
          refine ⟨2502216310318629229276507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13345153655032689222808037 2502216310318629229276507)
          ·
            refine ⟨3753324465477943843914761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502216310318629229276507 3753324465477943843914761)
            ·
              refine ⟨2814993349108457882936071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3753324465477943843914761 2814993349108457882936071)
              ·
                refine ⟨4222490023662686824404107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814993349108457882936071 4222490023662686824404107)
                ·
                  refine ⟨6333735035494030236606161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222490023662686824404107 6333735035494030236606161)
                  ·
                    refine ⟨4750301276620522677454621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6333735035494030236606161 4750301276620522677454621)
                    ·
                      refine ⟨1781362978732696004045483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4750301276620522677454621 1781362978732696004045483)
                      ·
                        rfl

theorem cell23_3469192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_3469192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469192 prefixEnd_3469192 := by exact prefixLift 3469192
  have htrace : WordTrace (prefixWord ++ tailWord_3469192) baseStart_3469192 baseEnd_3469192 := by
    simpa [prefixWord, tailWord_3469192, baseEnd_3469192] using wordTrace_append hprefix tailTrace_3469192
  have hstable : (prefixWord ++ tailWord_3469192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469192).length < 2 ^ (prefixWord ++ tailWord_3469192).sum := by decide
  have hdescent : baseEnd_3469192 < baseStart_3469192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469264 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 4, 5]
def baseStart_3469264 : Nat := 118140960795 + 3469264 * 2 ^ 59
def prefixEnd_3469264 : Nat := 4983230072969 + 3 ^ 40 * 3469264 * 2
def baseEnd_3469264 : Nat := 593799983113273240781717

theorem tailTrace_3469264 : CollatzResearch.WordTrace tailWord_3469264 prefixEnd_3469264 593799983113273240781717 := by
  unfold tailWord_3469264
  simp only [CollatzResearch.WordTrace]
  refine ⟨63267226651728252982363423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84356302202304337309817897 63267226651728252982363423)
  ·
    refine ⟨94900839977592379473545135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63267226651728252982363423 94900839977592379473545135)
    ·
      refine ⟨142351259966388569210317703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94900839977592379473545135 142351259966388569210317703)
      ·
        refine ⟨213526889949582853815476555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142351259966388569210317703 213526889949582853815476555)
        ·
          refine ⟨320290334924374280723214833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213526889949582853815476555 320290334924374280723214833)
          ·
            refine ⟨240217751193280710542411125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320290334924374280723214833 240217751193280710542411125)
            ·
              refine ⟨22520414174370066613351043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240217751193280710542411125 22520414174370066613351043)
              ·
                refine ⟨33780621261555099920026565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22520414174370066613351043 33780621261555099920026565)
                ·
                  refine ⟨6333866486541581235004981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33780621261555099920026565 6333866486541581235004981)
                  ·
                    refine ⟨593799983113273240781717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6333866486541581235004981 593799983113273240781717)
                    ·
                      rfl

theorem cell23_3469264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_3469264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469264 prefixEnd_3469264 := by exact prefixLift 3469264
  have htrace : WordTrace (prefixWord ++ tailWord_3469264) baseStart_3469264 baseEnd_3469264 := by
    simpa [prefixWord, tailWord_3469264, baseEnd_3469264] using wordTrace_append hprefix tailTrace_3469264
  have hstable : (prefixWord ++ tailWord_3469264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469264).length < 2 ^ (prefixWord ++ tailWord_3469264).sum := by decide
  have hdescent : baseEnd_3469264 < baseStart_3469264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469271 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 2, 5, 2]
def baseStart_3469271 : Nat := 118140960795 + 3469271 * 2 ^ 59
def prefixEnd_3469271 : Nat := 4983230072969 + 3 ^ 40 * 3469271 * 2
def baseEnd_3469271 : Nat := 1781403543704401194957619

theorem tailTrace_3469271 : CollatzResearch.WordTrace tailWord_3469271 prefixEnd_3469271 1781403543704401194957619 := by
  unfold tailWord_3469271
  simp only [CollatzResearch.WordTrace]
  refine ⟨126534708614431146160231667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84356472409620764106821111 126534708614431146160231667)
  ·
    refine ⟨189802062921646719240347501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126534708614431146160231667 189802062921646719240347501)
    ·
      refine ⟨71175773595617519715130313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189802062921646719240347501 71175773595617519715130313)
      ·
        refine ⟨53381830196713139786347735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71175773595617519715130313 53381830196713139786347735)
        ·
          refine ⟨80072745295069709679521603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53381830196713139786347735 80072745295069709679521603)
          ·
            refine ⟨120109117942604564519282405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80072745295069709679521603 120109117942604564519282405)
            ·
              refine ⟨22520459614238355847365451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120109117942604564519282405 22520459614238355847365451)
              ·
                refine ⟨33780689421357533771048177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22520459614238355847365451 33780689421357533771048177)
                ·
                  refine ⟨25335517066018150328286133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33780689421357533771048177 25335517066018150328286133)
                  ·
                    refine ⟨2375204724939201593276825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25335517066018150328286133 2375204724939201593276825)
                    ·
                      refine ⟨1781403543704401194957619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375204724939201593276825 1781403543704401194957619)
                      ·
                        rfl

theorem cell23_3469271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_3469271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469271 prefixEnd_3469271 := by exact prefixLift 3469271
  have htrace : WordTrace (prefixWord ++ tailWord_3469271) baseStart_3469271 baseEnd_3469271 := by
    simpa [prefixWord, tailWord_3469271, baseEnd_3469271] using wordTrace_append hprefix tailTrace_3469271
  have hstable : (prefixWord ++ tailWord_3469271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469271).length < 2 ^ (prefixWord ++ tailWord_3469271).sum := by decide
  have hdescent : baseEnd_3469271 < baseStart_3469271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469328 : List Nat := [2, 1, 1, 1, 1, 1, 1, 10, 1, 4]
def baseStart_3469328 : Nat := 118140960795 + 3469328 * 2 ^ 59
def prefixEnd_3469328 : Nat := 4983230072969 + 3 ^ 40 * 3469328 * 2
def baseEnd_3469328 : Nat := 593810937367235823981619

theorem tailTrace_3469328 : CollatzResearch.WordTrace tailWord_3469328 prefixEnd_3469328 593810937367235823981619 := by
  unfold tailWord_3469328
  simp only [CollatzResearch.WordTrace]
  refine ⟨63268393787612322447528319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84357858383483096596704425 63268393787612322447528319)
  ·
    refine ⟨94902590681418483671292479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63268393787612322447528319 94902590681418483671292479)
    ·
      refine ⟨142353886022127725506938719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94902590681418483671292479 142353886022127725506938719)
      ·
        refine ⟨213530829033191588260408079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142353886022127725506938719 213530829033191588260408079)
        ·
          refine ⟨320296243549787382390612119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213530829033191588260408079 320296243549787382390612119)
          ·
            refine ⟨480444365324681073585918179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320296243549787382390612119 480444365324681073585918179)
            ·
              refine ⟨720666547987021610378877269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480444365324681073585918179 720666547987021610378877269)
              ·
                refine ⟨2111327777305727374156867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 720666547987021610378877269 2111327777305727374156867)
                ·
                  refine ⟨3166991665958591061235301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111327777305727374156867 3166991665958591061235301)
                  ·
                    refine ⟨593810937367235823981619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3166991665958591061235301 593810937367235823981619)
                    ·
                      rfl

theorem cell23_3469328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 4].length) (baseStart_3469328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469328 prefixEnd_3469328 := by exact prefixLift 3469328
  have htrace : WordTrace (prefixWord ++ tailWord_3469328) baseStart_3469328 baseEnd_3469328 := by
    simpa [prefixWord, tailWord_3469328, baseEnd_3469328] using wordTrace_append hprefix tailTrace_3469328
  have hstable : (prefixWord ++ tailWord_3469328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469328).length < 2 ^ (prefixWord ++ tailWord_3469328).sum := by decide
  have hdescent : baseEnd_3469328 < baseStart_3469328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469335 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 2, 4, 2]
def baseStart_3469335 : Nat := 118140960795 + 3469335 * 2 ^ 59
def prefixEnd_3469335 : Nat := 4983230072969 + 3 ^ 40 * 3469335 * 2
def baseEnd_3469335 : Nat := 1781436406466288944557325

theorem tailTrace_3469335 : CollatzResearch.WordTrace tailWord_3469335 prefixEnd_3469335 1781436406466288944557325 := by
  unfold tailWord_3469335
  simp only [CollatzResearch.WordTrace]
  refine ⟨126537042886199285090561459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84358028590799523393707639 126537042886199285090561459)
  ·
    refine ⟨189805564329298927635842189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126537042886199285090561459 189805564329298927635842189)
    ·
      refine ⟨71177086623487097863440821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189805564329298927635842189 71177086623487097863440821)
      ·
        refine ⟨6672851870951915424697577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71177086623487097863440821 6672851870951915424697577)
        ·
          refine ⟨5004638903213936568523183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6672851870951915424697577 5004638903213936568523183)
          ·
            refine ⟨7506958354820904852784775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004638903213936568523183 7506958354820904852784775)
            ·
              refine ⟨11260437532231357279177163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7506958354820904852784775 11260437532231357279177163)
              ·
                refine ⟨16890656298347035918765745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11260437532231357279177163 16890656298347035918765745)
                ·
                  refine ⟨12667992223760276939074309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16890656298347035918765745 12667992223760276939074309)
                  ·
                    refine ⟨2375248541955051926076433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12667992223760276939074309 2375248541955051926076433)
                    ·
                      refine ⟨1781436406466288944557325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375248541955051926076433 1781436406466288944557325)
                      ·
                        rfl

theorem cell23_3469335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_3469335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469335 prefixEnd_3469335 := by exact prefixLift 3469335
  have htrace : WordTrace (prefixWord ++ tailWord_3469335) baseStart_3469335 baseEnd_3469335 := by
    simpa [prefixWord, tailWord_3469335, baseEnd_3469335] using wordTrace_append hprefix tailTrace_3469335
  have hstable : (prefixWord ++ tailWord_3469335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469335).length < 2 ^ (prefixWord ++ tailWord_3469335).sum := by decide
  have hdescent : baseEnd_3469335 < baseStart_3469335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469352 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3469352 : Nat := 118140960795 + 3469352 * 2 ^ 59
def prefixEnd_3469352 : Nat := 4983230072969 + 3 ^ 40 * 3469352 * 2
def baseEnd_3469352 : Nat := 1781445135637415378044747

theorem tailTrace_3469352 : CollatzResearch.WordTrace tailWord_3469352 prefixEnd_3469352 1781445135637415378044747 := by
  unfold tailWord_3469352
  simp only [CollatzResearch.WordTrace]
  refine ⟨63268831463568848496965155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84358441951425131329286873 63268831463568848496965155)
  ·
    refine ⟨94903247195353272745447733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63268831463568848496965155 94903247195353272745447733)
    ·
      refine ⟨8897179424564369319885725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94903247195353272745447733 8897179424564369319885725)
      ·
        refine ⟨3336442284211638494957147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8897179424564369319885725 3336442284211638494957147)
        ·
          refine ⟨5004663426317457742435721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3336442284211638494957147 5004663426317457742435721)
          ·
            refine ⟨3753497569738093306826791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5004663426317457742435721 3753497569738093306826791)
            ·
              refine ⟨5630246354607139960240187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753497569738093306826791 5630246354607139960240187)
              ·
                refine ⟨8445369531910709940360281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5630246354607139960240187 8445369531910709940360281)
                ·
                  refine ⟨6334027148933032455270211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8445369531910709940360281 6334027148933032455270211)
                  ·
                    refine ⟨9501040723399548682905317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6334027148933032455270211 9501040723399548682905317)
                    ·
                      refine ⟨1781445135637415378044747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9501040723399548682905317 1781445135637415378044747)
                      ·
                        rfl

theorem cell23_3469352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3469352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469352 prefixEnd_3469352 := by exact prefixLift 3469352
  have htrace : WordTrace (prefixWord ++ tailWord_3469352) baseStart_3469352 baseEnd_3469352 := by
    simpa [prefixWord, tailWord_3469352, baseEnd_3469352] using wordTrace_append hprefix tailTrace_3469352
  have hstable : (prefixWord ++ tailWord_3469352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469352).length < 2 ^ (prefixWord ++ tailWord_3469352).sum := by decide
  have hdescent : baseEnd_3469352 < baseStart_3469352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469371 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 1, 5]
def baseStart_3469371 : Nat := 118140960795 + 3469371 * 2 ^ 59
def prefixEnd_3469371 : Nat := 4983230072969 + 3 ^ 40 * 3469371 * 2
def baseEnd_3469371 : Nat := 593818297256616934569053

theorem tailTrace_3469371 : CollatzResearch.WordTrace tailWord_3469371 prefixEnd_3469371 593818297256616934569053 := by
  unfold tailWord_3469371
  simp only [CollatzResearch.WordTrace]
  refine ⟨126538355914068863238871967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84358903942712575492581311 126538355914068863238871967)
  ·
    refine ⟨189807533871103294858307951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126538355914068863238871967 189807533871103294858307951)
    ·
      refine ⟨284711300806654942287461927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189807533871103294858307951 284711300806654942287461927)
      ·
        refine ⟨427066951209982413431192891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284711300806654942287461927 427066951209982413431192891)
        ·
          refine ⟨640600426814973620146789337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427066951209982413431192891 640600426814973620146789337)
          ·
            refine ⟨480450320111230215110092003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640600426814973620146789337 480450320111230215110092003)
            ·
              refine ⟨720675480166845322665138005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480450320111230215110092003 720675480166845322665138005)
              ·
                refine ⟨4222707891602609312491043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 720675480166845322665138005 4222707891602609312491043)
                ·
                  refine ⟨6334061837403913968736565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222707891602609312491043 6334061837403913968736565)
                  ·
                    refine ⟨593818297256616934569053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6334061837403913968736565 593818297256616934569053)
                    ·
                      rfl

theorem cell23_3469371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 5].length) (baseStart_3469371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469371 prefixEnd_3469371 := by exact prefixLift 3469371
  have htrace : WordTrace (prefixWord ++ tailWord_3469371) baseStart_3469371 baseEnd_3469371 := by
    simpa [prefixWord, tailWord_3469371, baseEnd_3469371] using wordTrace_append hprefix tailTrace_3469371
  have hstable : (prefixWord ++ tailWord_3469371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469371).length < 2 ^ (prefixWord ++ tailWord_3469371).sum := by decide
  have hdescent : baseEnd_3469371 < baseStart_3469371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469385 : List Nat := [1, 2, 1, 1, 2, 2, 3, 6, 1, 1, 3]
def baseStart_3469385 : Nat := 118140960795 + 3469385 * 2 ^ 59
def prefixEnd_3469385 : Nat := 4983230072969 + 3 ^ 40 * 3469385 * 2
def baseEnd_3469385 : Nat := 1781462080499013748932095

theorem tailTrace_3469385 : CollatzResearch.WordTrace tailWord_3469385 prefixEnd_3469385 1781462080499013748932095 := by
  unfold tailWord_3469385
  simp only [CollatzResearch.WordTrace]
  refine ⟨126538866536018143629881609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84359244357345429086587739 126538866536018143629881609)
  ·
    refine ⟨94904149902013607722411207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126538866536018143629881609 94904149902013607722411207)
    ·
      refine ⟨142356224853020411583616811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94904149902013607722411207 142356224853020411583616811)
      ·
        refine ⟨213534337279530617375425217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142356224853020411583616811 213534337279530617375425217)
        ·
          refine ⟨160150752959647963031568913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213534337279530617375425217 160150752959647963031568913)
          ·
            refine ⟨120113064719735972273676685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160150752959647963031568913 120113064719735972273676685)
            ·
              refine ⟨45042399269900989602628757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120113064719735972273676685 45042399269900989602628757)
              ·
                refine ⟨2111362465776608887623223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45042399269900989602628757 2111362465776608887623223)
                ·
                  refine ⟨3167043698664913331434835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111362465776608887623223 3167043698664913331434835)
                  ·
                    refine ⟨4750565547997369997152253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3167043698664913331434835 4750565547997369997152253)
                    ·
                      refine ⟨1781462080499013748932095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4750565547997369997152253 1781462080499013748932095)
                      ·
                        rfl

theorem cell23_3469385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 1, 3].length) (baseStart_3469385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469385 prefixEnd_3469385 := by exact prefixLift 3469385
  have htrace : WordTrace (prefixWord ++ tailWord_3469385) baseStart_3469385 baseEnd_3469385 := by
    simpa [prefixWord, tailWord_3469385, baseEnd_3469385] using wordTrace_append hprefix tailTrace_3469385
  have hstable : (prefixWord ++ tailWord_3469385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469385).length < 2 ^ (prefixWord ++ tailWord_3469385).sum := by decide
  have hdescent : baseEnd_3469385 < baseStart_3469385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469405 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3469405 : Nat := 118140960795 + 3469405 * 2 ^ 59
def prefixEnd_3469405 : Nat := 4983230072969 + 3 ^ 40 * 3469405 * 2
def baseEnd_3469405 : Nat := 593824116704034556894001

theorem tailTrace_3469405 : CollatzResearch.WordTrace tailWord_3469405 prefixEnd_3469405 593824116704034556894001 := by
  unfold tailWord_3469405
  simp only [CollatzResearch.WordTrace]
  refine ⟨126539595995945687045609669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84359730663963791363739779 126539595995945687045609669)
  ·
    refine ⟨23726174249239816321051813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126539595995945687045609669 23726174249239816321051813)
    ·
      refine ⟨4448657671732465560197215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23726174249239816321051813 4448657671732465560197215)
      ·
        refine ⟨6672986507598698340295823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4448657671732465560197215 6672986507598698340295823)
        ·
          refine ⟨10009479761398047510443735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6672986507598698340295823 10009479761398047510443735)
          ·
            refine ⟨15014219642097071265665603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10009479761398047510443735 15014219642097071265665603)
            ·
              refine ⟨22521329463145606898498405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15014219642097071265665603 22521329463145606898498405)
              ·
                refine ⟨4222749274339801293468451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22521329463145606898498405 4222749274339801293468451)
                ·
                  refine ⟨6334123911509701940202677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222749274339801293468451 6334123911509701940202677)
                  ·
                    refine ⟨593824116704034556894001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6334123911509701940202677 593824116704034556894001)
                    ·
                      rfl

theorem cell23_3469405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3469405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469405 prefixEnd_3469405 := by exact prefixLift 3469405
  have htrace : WordTrace (prefixWord ++ tailWord_3469405) baseStart_3469405 baseEnd_3469405 := by
    simpa [prefixWord, tailWord_3469405, baseEnd_3469405] using wordTrace_append hprefix tailTrace_3469405
  have hstable : (prefixWord ++ tailWord_3469405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469405).length < 2 ^ (prefixWord ++ tailWord_3469405).sum := by decide
  have hdescent : baseEnd_3469405 < baseStart_3469405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469408 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 4]
def baseStart_3469408 : Nat := 118140960795 + 3469408 * 2 ^ 59
def prefixEnd_3469408 : Nat := 4983230072969 + 3 ^ 40 * 3469408 * 2
def baseEnd_3469408 : Nat := 1781473890554067158944489

theorem tailTrace_3469408 : CollatzResearch.WordTrace tailWord_3469408 prefixEnd_3469408 1781473890554067158944489 := by
  unfold tailWord_3469408
  simp only [CollatzResearch.WordTrace]
  refine ⟨63269852707467409278984439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84359803609956545705312585 63269852707467409278984439)
  ·
    refine ⟨94904779061201113918476659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63269852707467409278984439 94904779061201113918476659)
    ·
      refine ⟨142357168591801670877714989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94904779061201113918476659 142357168591801670877714989)
      ·
        refine ⟨53383938221925626579143121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142357168591801670877714989 53383938221925626579143121)
        ·
          refine ⟨40037953666444219934357341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53383938221925626579143121 40037953666444219934357341)
          ·
            refine ⟨15014232624916582475384003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40037953666444219934357341 15014232624916582475384003)
            ·
              refine ⟨22521348937374873713076005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15014232624916582475384003 22521348937374873713076005)
              ·
                refine ⟨4222752925757788821201751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22521348937374873713076005 4222752925757788821201751)
                ·
                  refine ⟨6334129388636683231802627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222752925757788821201751 6334129388636683231802627)
                  ·
                    refine ⟨9501194082955024847703941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6334129388636683231802627 9501194082955024847703941)
                    ·
                      refine ⟨1781473890554067158944489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9501194082955024847703941 1781473890554067158944489)
                      ·
                        rfl

theorem cell23_3469408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_3469408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469408 prefixEnd_3469408 := by exact prefixLift 3469408
  have htrace : WordTrace (prefixWord ++ tailWord_3469408) baseStart_3469408 baseEnd_3469408 := by
    simpa [prefixWord, tailWord_3469408, baseEnd_3469408] using wordTrace_append hprefix tailTrace_3469408
  have hstable : (prefixWord ++ tailWord_3469408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469408).length < 2 ^ (prefixWord ++ tailWord_3469408).sum := by decide
  have hdescent : baseEnd_3469408 < baseStart_3469408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469431 : List Nat := [1, 1, 3, 1, 1, 7, 9]
def baseStart_3469431 : Nat := 118140960795 + 3469431 * 2 ^ 59
def prefixEnd_3469431 : Nat := 4983230072969 + 3 ^ 40 * 3469431 * 2
def baseEnd_3469431 : Nat := 21993650624803957641443

theorem tailTrace_3469431 : CollatzResearch.WordTrace tailWord_3469431 prefixEnd_3469431 21993650624803957641443 := by
  unfold tailWord_3469431
  simp only [CollatzResearch.WordTrace]
  refine ⟨126540544293851493486056147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84360362862567662324037431 126540544293851493486056147)
  ·
    refine ⟨189810816440777240229084221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126540544293851493486056147 189810816440777240229084221)
    ·
      refine ⟨71179056165291465085906583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189810816440777240229084221 71179056165291465085906583)
      ·
        refine ⟨106768584247937197628859875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71179056165291465085906583 106768584247937197628859875)
        ·
          refine ⟨160152876371905796443289813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106768584247937197628859875 160152876371905796443289813)
          ·
            refine ⟨3753583039966542104139605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 160152876371905796443289813 3753583039966542104139605)
            ·
              refine ⟨21993650624803957641443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3753583039966542104139605 21993650624803957641443)
              ·
                rfl

theorem cell23_3469431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 9].length) (baseStart_3469431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469431 prefixEnd_3469431 := by exact prefixLift 3469431
  have htrace : WordTrace (prefixWord ++ tailWord_3469431) baseStart_3469431 baseEnd_3469431 := by
    simpa [prefixWord, tailWord_3469431, baseEnd_3469431] using wordTrace_append hprefix tailTrace_3469431
  have hstable : (prefixWord ++ tailWord_3469431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469431).length < 2 ^ (prefixWord ++ tailWord_3469431).sum := by decide
  have hdescent : baseEnd_3469431 < baseStart_3469431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469448 : List Nat := [2, 1, 3, 4, 1, 2, 2, 8]
def baseStart_3469448 : Nat := 118140960795 + 3469448 * 2 ^ 59
def prefixEnd_3469448 : Nat := 4983230072969 + 3 ^ 40 * 3469448 * 2
def baseEnd_3469448 : Nat := 65981275177046185275715

theorem tailTrace_3469448 : CollatzResearch.WordTrace tailWord_3469448 prefixEnd_3469448 65981275177046185275715 := by
  unfold tailWord_3469448
  simp only [CollatzResearch.WordTrace]
  refine ⟨63270582167394952694712499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84360776223193270259616665 63270582167394952694712499)
  ·
    refine ⟨94905873251092429042068749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63270582167394952694712499 94905873251092429042068749)
    ·
      refine ⟨35589702469159660890775781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94905873251092429042068749 35589702469159660890775781)
      ·
        refine ⟨6673069212967436417020459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35589702469159660890775781 6673069212967436417020459)
        ·
          refine ⟨10009603819451154625530689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6673069212967436417020459 10009603819451154625530689)
          ·
            refine ⟨7507202864588365969148017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10009603819451154625530689 7507202864588365969148017)
            ·
              refine ⟨5630402148441274476861013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7507202864588365969148017 5630402148441274476861013)
              ·
                refine ⟨65981275177046185275715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5630402148441274476861013 65981275177046185275715)
                ·
                  rfl

theorem cell23_3469448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 8].length) (baseStart_3469448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469448 prefixEnd_3469448 := by exact prefixLift 3469448
  have htrace : WordTrace (prefixWord ++ tailWord_3469448) baseStart_3469448 baseEnd_3469448 := by
    simpa [prefixWord, tailWord_3469448, baseEnd_3469448] using wordTrace_append hprefix tailTrace_3469448
  have hstable : (prefixWord ++ tailWord_3469448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469448).length < 2 ^ (prefixWord ++ tailWord_3469448).sum := by decide
  have hdescent : baseEnd_3469448 < baseStart_3469448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469479 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_3469479 : Nat := 118140960795 + 3469479 * 2 ^ 59
def prefixEnd_3469479 : Nat := 4983230072969 + 3 ^ 40 * 3469479 * 2
def baseEnd_3469479 : Nat := 1781510347680536381156663

theorem tailTrace_3469479 : CollatzResearch.WordTrace tailWord_3469479 prefixEnd_3469479 1781510347680536381156663 := by
  unfold tailWord_3469479
  simp only [CollatzResearch.WordTrace]
  refine ⟨126542294997677597683803491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84361529998451731789202327 126542294997677597683803491)
  ·
    refine ⟨189813442496516396525705237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126542294997677597683803491 189813442496516396525705237)
    ·
      refine ⟨8897505117024206087142433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 189813442496516396525705237 8897505117024206087142433)
      ·
        refine ⟨6673128837768154565356825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8897505117024206087142433 6673128837768154565356825)
        ·
          refine ⟨5004846628326115924017619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6673128837768154565356825 5004846628326115924017619)
          ·
            refine ⟨7507269942489173886026429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004846628326115924017619 7507269942489173886026429)
            ·
              refine ⟨2815226228433440207259911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7507269942489173886026429 2815226228433440207259911)
              ·
                refine ⟨4222839342650160310889867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815226228433440207259911 4222839342650160310889867)
                ·
                  refine ⟨6334259013975240466334801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222839342650160310889867 6334259013975240466334801)
                  ·
                    refine ⟨4750694260481430349751101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6334259013975240466334801 4750694260481430349751101)
                    ·
                      refine ⟨1781510347680536381156663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4750694260481430349751101 1781510347680536381156663)
                      ·
                        rfl

theorem cell23_3469479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_3469479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469479 prefixEnd_3469479 := by exact prefixLift 3469479
  have htrace : WordTrace (prefixWord ++ tailWord_3469479) baseStart_3469479 baseEnd_3469479 := by
    simpa [prefixWord, tailWord_3469479, baseEnd_3469479] using wordTrace_append hprefix tailTrace_3469479
  have hstable : (prefixWord ++ tailWord_3469479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469479).length < 2 ^ (prefixWord ++ tailWord_3469479).sum := by decide
  have hdescent : baseEnd_3469479 < baseStart_3469479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469491 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 2, 6]
def baseStart_3469491 : Nat := 118140960795 + 3469491 * 2 ^ 59
def prefixEnd_3469491 : Nat := 4983230072969 + 3 ^ 40 * 3469491 * 2
def baseEnd_3469491 : Nat := 593838836482796778068869

theorem tailTrace_3469491 : CollatzResearch.WordTrace tailWord_3469491 prefixEnd_3469491 593838836482796778068869 := by
  unfold tailWord_3469491
  simp only [CollatzResearch.WordTrace]
  refine ⟨126542732673634123733240327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84361821782422749155493551 126542732673634123733240327)
  ·
    refine ⟨189814099010451185599860491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126542732673634123733240327 189814099010451185599860491)
    ·
      refine ⟨284721148515676778399790737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189814099010451185599860491 284721148515676778399790737)
      ·
        refine ⟨213540861386757583799843053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284721148515676778399790737 213540861386757583799843053)
        ·
          refine ⟨80077823020034093924941145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213540861386757583799843053 80077823020034093924941145)
          ·
            refine ⟨60058367265025570443705859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80077823020034093924941145 60058367265025570443705859)
            ·
              refine ⟨90087550897538355665558789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60058367265025570443705859 90087550897538355665558789)
              ·
                refine ⟨16891415793288441687292273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90087550897538355665558789 16891415793288441687292273)
                ·
                  refine ⟨12668561844966331265469205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16891415793288441687292273 12668561844966331265469205)
                  ·
                    refine ⟨593838836482796778068869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12668561844966331265469205 593838836482796778068869)
                    ·
                      rfl

theorem cell23_3469491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 6].length) (baseStart_3469491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469491 prefixEnd_3469491 := by exact prefixLift 3469491
  have htrace : WordTrace (prefixWord ++ tailWord_3469491) baseStart_3469491 baseEnd_3469491 := by
    simpa [prefixWord, tailWord_3469491, baseEnd_3469491] using wordTrace_append hprefix tailTrace_3469491
  have hstable : (prefixWord ++ tailWord_3469491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469491).length < 2 ^ (prefixWord ++ tailWord_3469491).sum := by decide
  have hdescent : baseEnd_3469491 < baseStart_3469491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469508 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3469508 : Nat := 118140960795 + 3469508 * 2 ^ 59
def prefixEnd_3469508 : Nat := 4983230072969 + 3 ^ 40 * 3469508 * 2
def baseEnd_3469508 : Nat := 593841746206505589231343

theorem tailTrace_3469508 : CollatzResearch.WordTrace tailWord_3469508 prefixEnd_3469508 593841746206505589231343 := by
  unfold tailWord_3469508
  simp only [CollatzResearch.WordTrace]
  refine ⟨63271676357286267818304589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84362235143048357091072785 63271676357286267818304589)
  ·
    refine ⟨23726878633982350431864221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63271676357286267818304589 23726878633982350431864221)
    ·
      refine ⟨8897579487743381411949083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23726878633982350431864221 8897579487743381411949083)
      ·
        refine ⟨13346369231615072117923625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8897579487743381411949083 13346369231615072117923625)
        ·
          refine ⟨10009776923711304088442719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13346369231615072117923625 10009776923711304088442719)
          ·
            refine ⟨15014665385566956132664079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10009776923711304088442719 15014665385566956132664079)
            ·
              refine ⟨22521998078350434198996119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15014665385566956132664079 22521998078350434198996119)
              ·
                refine ⟨33782997117525651298494179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22521998078350434198996119 33782997117525651298494179)
                ·
                  refine ⟨50674495676288476947741269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33782997117525651298494179 50674495676288476947741269)
                  ·
                    refine ⟨593841746206505589231343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50674495676288476947741269 593841746206505589231343)
                    ·
                      rfl

theorem cell23_3469508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3469508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469508 prefixEnd_3469508 := by exact prefixLift 3469508
  have htrace : WordTrace (prefixWord ++ tailWord_3469508) baseStart_3469508 baseEnd_3469508 := by
    simpa [prefixWord, tailWord_3469508, baseEnd_3469508] using wordTrace_append hprefix tailTrace_3469508
  have hstable : (prefixWord ++ tailWord_3469508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469508).length < 2 ^ (prefixWord ++ tailWord_3469508).sum := by decide
  have hdescent : baseEnd_3469508 < baseStart_3469508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469515 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 1, 4, 2]
def baseStart_3469515 : Nat := 118140960795 + 3469515 * 2 ^ 59
def prefixEnd_3469515 : Nat := 4983230072969 + 3 ^ 40 * 3469515 * 2
def baseEnd_3469515 : Nat := 1781528832984098240306497

theorem tailTrace_3469515 : CollatzResearch.WordTrace tailWord_3469515 prefixEnd_3469515 1781528832984098240306497 := by
  unfold tailWord_3469515
  simp only [CollatzResearch.WordTrace]
  refine ⟨126543608025547175832113999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84362405350364783888075999 126543608025547175832113999)
  ·
    refine ⟨189815412038320763748170999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126543608025547175832113999 189815412038320763748170999)
    ·
      refine ⟨284723118057481145622256499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189815412038320763748170999 284723118057481145622256499)
      ·
        refine ⟨427084677086221718433384749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284723118057481145622256499 427084677086221718433384749)
        ·
          refine ⟨160156753907333144412519281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427084677086221718433384749 160156753907333144412519281)
          ·
            refine ⟨120117565430499858309389461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160156753907333144412519281 120117565430499858309389461)
            ·
              refine ⟨5630510879554680858252631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120117565430499858309389461 5630510879554680858252631)
              ·
                refine ⟨8445766319332021287378947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5630510879554680858252631 8445766319332021287378947)
                ·
                  refine ⟨12668649478998031931068421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8445766319332021287378947 12668649478998031931068421)
                  ·
                    refine ⟨2375371777312130987075329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12668649478998031931068421 2375371777312130987075329)
                    ·
                      refine ⟨1781528832984098240306497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375371777312130987075329 1781528832984098240306497)
                      ·
                        rfl

theorem cell23_3469515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 4, 2].length) (baseStart_3469515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469515 prefixEnd_3469515 := by exact prefixLift 3469515
  have htrace : WordTrace (prefixWord ++ tailWord_3469515) baseStart_3469515 baseEnd_3469515 := by
    simpa [prefixWord, tailWord_3469515, baseEnd_3469515] using wordTrace_append hprefix tailTrace_3469515
  have hstable : (prefixWord ++ tailWord_3469515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469515).length < 2 ^ (prefixWord ++ tailWord_3469515).sum := by decide
  have hdescent : baseEnd_3469515 < baseStart_3469515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469521 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 9]
def baseStart_3469521 : Nat := 118140960795 + 3469521 * 2 ^ 59
def prefixEnd_3469521 : Nat := 4983230072969 + 3 ^ 40 * 3469521 * 2
def baseEnd_3469521 : Nat := 197947990429780579647941

theorem tailTrace_3469521 : CollatzResearch.WordTrace tailWord_3469521 prefixEnd_3469521 197947990429780579647941 := by
  unfold tailWord_3469521
  simp only [CollatzResearch.WordTrace]
  refine ⟨126543826863525438856832417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84362551242350292571221611 126543826863525438856832417)
  ·
    refine ⟨94907870147644079142624313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126543826863525438856832417 94907870147644079142624313)
    ·
      refine ⟨71180902610733059356968235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94907870147644079142624313 71180902610733059356968235)
      ·
        refine ⟨106771353916099589035452353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71180902610733059356968235 106771353916099589035452353)
        ·
          refine ⟨80078515437074691776589265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106771353916099589035452353 80078515437074691776589265)
          ·
            refine ⟨60058886577806018832441949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80078515437074691776589265 60058886577806018832441949)
            ·
              refine ⟨22522082466677257062165731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60058886577806018832441949 22522082466677257062165731)
              ·
                refine ⟨33783123700015885593248597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22522082466677257062165731 33783123700015885593248597)
                ·
                  refine ⟨197947990429780579647941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33783123700015885593248597 197947990429780579647941)
                  ·
                    rfl

theorem cell23_3469521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 9].length) (baseStart_3469521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469521 prefixEnd_3469521 := by exact prefixLift 3469521
  have htrace : WordTrace (prefixWord ++ tailWord_3469521) baseStart_3469521 baseEnd_3469521 := by
    simpa [prefixWord, tailWord_3469521, baseEnd_3469521] using wordTrace_append hprefix tailTrace_3469521
  have hstable : (prefixWord ++ tailWord_3469521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469521).length < 2 ^ (prefixWord ++ tailWord_3469521).sum := by decide
  have hdescent : baseEnd_3469521 < baseStart_3469521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469548 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_3469548 : Nat := 118140960795 + 3469548 * 2 ^ 59
def prefixEnd_3469548 : Nat := 4983230072969 + 3 ^ 40 * 3469548 * 2
def baseEnd_3469548 : Nat := 1781545777845696611193845

theorem tailTrace_3469548 : CollatzResearch.WordTrace tailWord_3469548 prefixEnd_3469548 1781545777845696611193845 := by
  unfold tailWord_3469548
  simp only [CollatzResearch.WordTrace]
  refine ⟨63272405817213811234032649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84363207756285081645376865 63272405817213811234032649)
  ·
    refine ⟨47454304362910358425524487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63272405817213811234032649 47454304362910358425524487)
    ·
      refine ⟨71181456544365537638286731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47454304362910358425524487 71181456544365537638286731)
      ·
        refine ⟨106772184816548306457430097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71181456544365537638286731 106772184816548306457430097)
        ·
          refine ⟨80079138612411229843072573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106772184816548306457430097 80079138612411229843072573)
          ·
            refine ⟨30029676979654211191152215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80079138612411229843072573 30029676979654211191152215)
            ·
              refine ⟨45044515469481316786728323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30029676979654211191152215 45044515469481316786728323)
              ·
                refine ⟨67566773204221975180092485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45044515469481316786728323 67566773204221975180092485)
                ·
                  refine ⟨12668769975791620346267341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67566773204221975180092485 12668769975791620346267341)
                  ·
                    refine ⟨4750788740921857629850253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12668769975791620346267341 4750788740921857629850253)
                    ·
                      refine ⟨1781545777845696611193845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4750788740921857629850253 1781545777845696611193845)
                      ·
                        rfl

theorem cell23_3469548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_3469548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469548 prefixEnd_3469548 := by exact prefixLift 3469548
  have htrace : WordTrace (prefixWord ++ tailWord_3469548) baseStart_3469548 baseEnd_3469548 := by
    simpa [prefixWord, tailWord_3469548, baseEnd_3469548] using wordTrace_append hprefix tailTrace_3469548
  have hstable : (prefixWord ++ tailWord_3469548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469548).length < 2 ^ (prefixWord ++ tailWord_3469548).sum := by decide
  have hdescent : baseEnd_3469548 < baseStart_3469548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469549 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_3469549 : Nat := 118140960795 + 3469549 * 2 ^ 59
def prefixEnd_3469549 : Nat := 4983230072969 + 3 ^ 40 * 3469549 * 2
def baseEnd_3469549 : Nat := 1781546291326351107281341

theorem tailTrace_3469549 : CollatzResearch.WordTrace tailWord_3469549 prefixEnd_3469549 1781546291326351107281341 := by
  unfold tailWord_3469549
  simp only [CollatzResearch.WordTrace]
  refine ⟨126544848107423999638851701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84363232071615999759234467 126544848107423999638851701)
  ·
    refine ⟨11863579510070999966142347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126544848107423999638851701 11863579510070999966142347)
    ·
      refine ⟨17795369265106499949213521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11863579510070999966142347 17795369265106499949213521)
      ·
        refine ⟨13346526948829874961910141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17795369265106499949213521 13346526948829874961910141)
        ·
          refine ⟨5004947605811203110716303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13346526948829874961910141 5004947605811203110716303)
          ·
            refine ⟨7507421408716804666074455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004947605811203110716303 7507421408716804666074455)
            ·
              refine ⟨11261132113075206999111683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507421408716804666074455 11261132113075206999111683)
              ·
                refine ⟨16891698169612810498667525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11261132113075206999111683 16891698169612810498667525)
                ·
                  refine ⟨3167193406802401968500161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16891698169612810498667525 3167193406802401968500161)
                  ·
                    refine ⟨2375395055101801476375121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3167193406802401968500161 2375395055101801476375121)
                    ·
                      refine ⟨1781546291326351107281341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375395055101801476375121 1781546291326351107281341)
                      ·
                        rfl

theorem cell23_3469549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_3469549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469549 prefixEnd_3469549 := by exact prefixLift 3469549
  have htrace : WordTrace (prefixWord ++ tailWord_3469549) baseStart_3469549 baseEnd_3469549 := by
    simpa [prefixWord, tailWord_3469549, baseEnd_3469549] using wordTrace_append hprefix tailTrace_3469549
  have hstable : (prefixWord ++ tailWord_3469549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469549).length < 2 ^ (prefixWord ++ tailWord_3469549).sum := by decide
  have hdescent : baseEnd_3469549 < baseStart_3469549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469566 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_3469566 : Nat := 118140960795 + 3469566 * 2 ^ 59
def prefixEnd_3469566 : Nat := 4983230072969 + 3 ^ 40 * 3469566 * 2
def baseEnd_3469566 : Nat := 1781555020497477540768763

theorem tailTrace_3469566 : CollatzResearch.WordTrace tailWord_3469566 prefixEnd_3469566 1781555020497477540768763 := by
  unfold tailWord_3469566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15818183518545301442777569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84363645432241607694813701 15818183518545301442777569)
  ·
    refine ⟨11863637638908976082083177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15818183518545301442777569 11863637638908976082083177)
    ·
      refine ⟨8897728229181732061562383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11863637638908976082083177 8897728229181732061562383)
      ·
        refine ⟨13346592343772598092343575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8897728229181732061562383 13346592343772598092343575)
        ·
          refine ⟨20019888515658897138515363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13346592343772598092343575 20019888515658897138515363)
          ·
            refine ⟨30029832773488345707773045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20019888515658897138515363 30029832773488345707773045)
            ·
              refine ⟨2815296822514532410103723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30029832773488345707773045 2815296822514532410103723)
              ·
                refine ⟨4222945233771798615155585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815296822514532410103723 4222945233771798615155585)
                ·
                  refine ⟨3167208925328848961366689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4222945233771798615155585 3167208925328848961366689)
                  ·
                    refine ⟨2375406693996636721025017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3167208925328848961366689 2375406693996636721025017)
                    ·
                      refine ⟨1781555020497477540768763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375406693996636721025017 1781555020497477540768763)
                      ·
                        rfl

theorem cell23_3469566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_3469566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469566 prefixEnd_3469566 := by exact prefixLift 3469566
  have htrace : WordTrace (prefixWord ++ tailWord_3469566) baseStart_3469566 baseEnd_3469566 := by
    simpa [prefixWord, tailWord_3469566, baseEnd_3469566] using wordTrace_append hprefix tailTrace_3469566
  have hstable : (prefixWord ++ tailWord_3469566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469566).length < 2 ^ (prefixWord ++ tailWord_3469566).sum := by decide
  have hdescent : baseEnd_3469566 < baseStart_3469566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469615 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 3, 4]
def baseStart_3469615 : Nat := 118140960795 + 3469615 * 2 ^ 59
def prefixEnd_3469615 : Nat := 4983230072969 + 3 ^ 40 * 3469615 * 2
def baseEnd_3469615 : Nat := 593860060349849283018679

theorem tailTrace_3469615 : CollatzResearch.WordTrace tailWord_3469615 prefixEnd_3469615 593860060349849283018679 := by
  unfold tailWord_3469615
  simp only [CollatzResearch.WordTrace]
  refine ⟨126547255325184892910754299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84364836883456595273836199 126547255325184892910754299)
  ·
    refine ⟨189820882987777339366131449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126547255325184892910754299 189820882987777339366131449)
    ·
      refine ⟨142365662240833004524598587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189820882987777339366131449 142365662240833004524598587)
      ·
        refine ⟨213548493361249506786897881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142365662240833004524598587 213548493361249506786897881)
        ·
          refine ⟨160161370020937130090173411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213548493361249506786897881 160161370020937130090173411)
          ·
            refine ⟨240242055031405695135260117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160161370020937130090173411 240242055031405695135260117)
            ·
              refine ⟨5630673164798570979732659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 240242055031405695135260117 5630673164798570979732659)
              ·
                refine ⟨8446009747197856469598989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5630673164798570979732659 8446009747197856469598989)
                ·
                  refine ⟨3167253655199196176099621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8446009747197856469598989 3167253655199196176099621)
                  ·
                    refine ⟨593860060349849283018679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3167253655199196176099621 593860060349849283018679)
                    ·
                      rfl

theorem cell23_3469615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 4].length) (baseStart_3469615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469615 prefixEnd_3469615 := by exact prefixLift 3469615
  have htrace : WordTrace (prefixWord ++ tailWord_3469615) baseStart_3469615 baseEnd_3469615 := by
    simpa [prefixWord, tailWord_3469615, baseEnd_3469615] using wordTrace_append hprefix tailTrace_3469615
  have hstable : (prefixWord ++ tailWord_3469615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469615).length < 2 ^ (prefixWord ++ tailWord_3469615).sum := by decide
  have hdescent : baseEnd_3469615 < baseStart_3469615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469665 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_3469665 : Nat := 118140960795 + 3469665 * 2 ^ 59
def prefixEnd_3469665 : Nat := 4983230072969 + 3 ^ 40 * 3469665 * 2
def baseEnd_3469665 : Nat := 1781605855082272653430807

theorem tailTrace_3469665 : CollatzResearch.WordTrace tailWord_3469665 prefixEnd_3469665 1781605855082272653430807 := by
  unfold tailWord_3469665
  simp only [CollatzResearch.WordTrace]
  refine ⟨126549078975003751450074449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84366052650002500966716299 126549078975003751450074449)
  ·
    refine ⟨94911809231252813587555837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126549078975003751450074449 94911809231252813587555837)
    ·
      refine ⟨35591928461719805095333439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94911809231252813587555837 35591928461719805095333439)
      ·
        refine ⟨53387892692579707643000159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35591928461719805095333439 53387892692579707643000159)
        ·
          refine ⟨80081839038869561464500239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53387892692579707643000159 80081839038869561464500239)
          ·
            refine ⟨120122758558304342196750359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80081839038869561464500239 120122758558304342196750359)
            ·
              refine ⟨180184137837456513295125539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120122758558304342196750359 180184137837456513295125539)
              ·
                refine ⟨270276206756184769942688309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180184137837456513295125539 270276206756184769942688309)
                ·
                  refine ⟨25338394383392322182127029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270276206756184769942688309 25338394383392322182127029)
                  ·
                    refine ⟨2375474473443030204574409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25338394383392322182127029 2375474473443030204574409)
                    ·
                      refine ⟨1781605855082272653430807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375474473443030204574409 1781605855082272653430807)
                      ·
                        rfl

theorem cell23_3469665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_3469665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469665 prefixEnd_3469665 := by exact prefixLift 3469665
  have htrace : WordTrace (prefixWord ++ tailWord_3469665) baseStart_3469665 baseEnd_3469665 := by
    simpa [prefixWord, tailWord_3469665, baseEnd_3469665] using wordTrace_append hprefix tailTrace_3469665
  have hstable : (prefixWord ++ tailWord_3469665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469665).length < 2 ^ (prefixWord ++ tailWord_3469665).sum := by decide
  have hdescent : baseEnd_3469665 < baseStart_3469665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469666 : List Nat := [3, 3, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3469666 : Nat := 118140960795 + 3469666 * 2 ^ 59
def prefixEnd_3469666 : Nat := 4983230072969 + 3 ^ 40 * 3469666 * 2
def baseEnd_3469666 : Nat := 593868789520975716506101

theorem tailTrace_3469666 : CollatzResearch.WordTrace tailWord_3469666 prefixEnd_3469666 593868789520975716506101 := by
  unfold tailWord_3469666
  simp only [CollatzResearch.WordTrace]
  refine ⟨31637278862000032155215213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84366076965333419080573901 31637278862000032155215213)
  ·
    refine ⟨11863979573250012058205705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31637278862000032155215213 11863979573250012058205705)
    ·
      refine ⟨8897984679937509043654279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11863979573250012058205705 8897984679937509043654279)
      ·
        refine ⟨13346977019906263565481419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8897984679937509043654279 13346977019906263565481419)
        ·
          refine ⟨20020465529859395348222129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13346977019906263565481419 20020465529859395348222129)
          ·
            refine ⟨15015349147394546511166597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20020465529859395348222129 15015349147394546511166597)
            ·
              refine ⟨2815377965136477470843737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15015349147394546511166597 2815377965136477470843737)
              ·
                refine ⟨2111533473852358103132803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815377965136477470843737 2111533473852358103132803)
                ·
                  refine ⟨3167300210778537154699205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111533473852358103132803 3167300210778537154699205)
                  ·
                    refine ⟨593868789520975716506101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3167300210778537154699205 593868789520975716506101)
                    ·
                      rfl

theorem cell23_3469666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3469666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469666 prefixEnd_3469666 := by exact prefixLift 3469666
  have htrace : WordTrace (prefixWord ++ tailWord_3469666) baseStart_3469666 baseEnd_3469666 := by
    simpa [prefixWord, tailWord_3469666, baseEnd_3469666] using wordTrace_append hprefix tailTrace_3469666
  have hstable : (prefixWord ++ tailWord_3469666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469666).length < 2 ^ (prefixWord ++ tailWord_3469666).sum := by decide
  have hdescent : baseEnd_3469666 < baseStart_3469666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469695 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 2, 6, 2]
def baseStart_3469695 : Nat := 118140960795 + 3469695 * 2 ^ 59
def prefixEnd_3469695 : Nat := 4983230072969 + 3 ^ 40 * 3469695 * 2
def baseEnd_3469695 : Nat := 1781621259501907536055669

theorem tailTrace_3469695 : CollatzResearch.WordTrace tailWord_3469695 prefixEnd_3469695 1781621259501907536055669 := by
  unfold tailWord_3469695
  simp only [CollatzResearch.WordTrace]
  refine ⟨126550173164895066573666539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84366782109930044382444359 126550173164895066573666539)
  ·
    refine ⟨189825259747342599860499809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126550173164895066573666539 189825259747342599860499809)
    ·
      refine ⟨142368944810506949895374857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189825259747342599860499809 142368944810506949895374857)
      ·
        refine ⟨106776708607880212421531143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142368944810506949895374857 106776708607880212421531143)
        ·
          refine ⟨160165062911820318632296715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106776708607880212421531143 160165062911820318632296715)
          ·
            refine ⟨240247594367730477948445073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160165062911820318632296715 240247594367730477948445073)
            ·
              refine ⟨180185695775797858461333805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240247594367730477948445073 180185695775797858461333805)
              ·
                refine ⟨67569635915924196923000177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180185695775797858461333805 67569635915924196923000177)
                ·
                  refine ⟨50677226936943147692250133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67569635915924196923000177 50677226936943147692250133)
                  ·
                    refine ⟨2375495012669210048074225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50677226936943147692250133 2375495012669210048074225)
                    ·
                      refine ⟨1781621259501907536055669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375495012669210048074225 1781621259501907536055669)
                      ·
                        rfl

theorem cell23_3469695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_3469695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469695 prefixEnd_3469695 := by exact prefixLift 3469695
  have htrace : WordTrace (prefixWord ++ tailWord_3469695) baseStart_3469695 baseEnd_3469695 := by
    simpa [prefixWord, tailWord_3469695, baseEnd_3469695] using wordTrace_append hprefix tailTrace_3469695
  have hstable : (prefixWord ++ tailWord_3469695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469695).length < 2 ^ (prefixWord ++ tailWord_3469695).sum := by decide
  have hdescent : baseEnd_3469695 < baseStart_3469695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469705 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 1, 6]
def baseStart_3469705 : Nat := 118140960795 + 3469705 * 2 ^ 59
def prefixEnd_3469705 : Nat := 4983230072969 + 3 ^ 40 * 3469705 * 2
def baseEnd_3469705 : Nat := 593875464769484165643541

theorem tailTrace_3469705 : CollatzResearch.WordTrace tailWord_3469705 prefixEnd_3469705 593875464769484165643541 := by
  unfold tailWord_3469705
  simp only [CollatzResearch.WordTrace]
  refine ⟨126550537894858838281530569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84367025263239225521020379 126550537894858838281530569)
  ·
    refine ⟨94912903421144128711147927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126550537894858838281530569 94912903421144128711147927)
    ·
      refine ⟨142369355131716193066721891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94912903421144128711147927 142369355131716193066721891)
      ·
        refine ⟨213554032697574289600082837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142369355131716193066721891 213554032697574289600082837)
        ·
          refine ⟨10010345282698794825003883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 213554032697574289600082837 10010345282698794825003883)
          ·
            refine ⟨15015517924048192237505825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10010345282698794825003883 15015517924048192237505825)
            ·
              refine ⟨11261638443036144178129369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15015517924048192237505825 11261638443036144178129369)
              ·
                refine ⟨8446228832277108133597027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11261638443036144178129369 8446228832277108133597027)
                ·
                  refine ⟨12669343248415662200395541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8446228832277108133597027 12669343248415662200395541)
                  ·
                    refine ⟨593875464769484165643541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12669343248415662200395541 593875464769484165643541)
                    ·
                      rfl

theorem cell23_3469705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_3469705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469705 prefixEnd_3469705 := by exact prefixLift 3469705
  have htrace : WordTrace (prefixWord ++ tailWord_3469705) baseStart_3469705 baseEnd_3469705 := by
    simpa [prefixWord, tailWord_3469705, baseEnd_3469705] using wordTrace_append hprefix tailTrace_3469705
  have hstable : (prefixWord ++ tailWord_3469705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469705).length < 2 ^ (prefixWord ++ tailWord_3469705).sum := by decide
  have hdescent : baseEnd_3469705 < baseStart_3469705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469722 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_3469722 : Nat := 118140960795 + 3469722 * 2 ^ 59
def prefixEnd_3469722 : Nat := 4983230072969 + 3 ^ 40 * 3469722 * 2
def baseEnd_3469722 : Nat := 593878374493192976806015

theorem tailTrace_3469722 : CollatzResearch.WordTrace tailWord_3469722 prefixEnd_3469722 593878374493192976806015 := by
  unfold tailWord_3469722
  simp only [CollatzResearch.WordTrace]
  refine ⟨31637789483949312546224855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84367438623864833456599613 31637789483949312546224855)
  ·
    refine ⟨47456684225923968819337283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31637789483949312546224855 47456684225923968819337283)
    ·
      refine ⟨71185026338885953229005925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47456684225923968819337283 71185026338885953229005925)
      ·
        refine ⟨13347192438541116230438611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71185026338885953229005925 13347192438541116230438611)
        ·
          refine ⟨20020788657811674345657917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13347192438541116230438611 20020788657811674345657917)
          ·
            refine ⟨7507795746679377879621719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20020788657811674345657917 7507795746679377879621719)
            ·
              refine ⟨11261693620019066819432579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507795746679377879621719 11261693620019066819432579)
              ·
                refine ⟨16892540430028600229148869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11261693620019066819432579 16892540430028600229148869)
                ·
                  refine ⟨3167351330630362542965413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16892540430028600229148869 3167351330630362542965413)
                  ·
                    refine ⟨593878374493192976806015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3167351330630362542965413 593878374493192976806015)
                    ·
                      rfl

theorem cell23_3469722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_3469722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469722 prefixEnd_3469722 := by exact prefixLift 3469722
  have htrace : WordTrace (prefixWord ++ tailWord_3469722) baseStart_3469722 baseEnd_3469722 := by
    simpa [prefixWord, tailWord_3469722, baseEnd_3469722] using wordTrace_append hprefix tailTrace_3469722
  have hstable : (prefixWord ++ tailWord_3469722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469722).length < 2 ^ (prefixWord ++ tailWord_3469722).sum := by decide
  have hdescent : baseEnd_3469722 < baseStart_3469722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469780 : List Nat := [2, 4, 1, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_3469780 : Nat := 118140960795 + 3469780 * 2 ^ 59
def prefixEnd_3469780 : Nat := 4983230072969 + 3 ^ 40 * 3469780 * 2
def baseEnd_3469780 : Nat := 1781664905357539703492779

theorem tailTrace_3469780 : CollatzResearch.WordTrace tailWord_3469780 prefixEnd_3469780 1781664905357539703492779 := by
  unfold tailWord_3469780
  simp only [CollatzResearch.WordTrace]
  refine ⟨63276636684793563045255397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84368848913058084060340529 63276636684793563045255397)
  ·
    refine ⟨11864369378398793070985387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63276636684793563045255397 11864369378398793070985387)
    ·
      refine ⟨17796554067598189606478081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11864369378398793070985387 17796554067598189606478081)
      ·
        refine ⟨13347415550698642204858561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17796554067598189606478081 13347415550698642204858561)
        ·
          refine ⟨10010561663023981653643921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13347415550698642204858561 10010561663023981653643921)
          ·
            refine ⟨7507921247267986240232941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10010561663023981653643921 7507921247267986240232941)
            ·
              refine ⟨2815470467725494840087353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7507921247267986240232941 2815470467725494840087353)
              ·
                refine ⟨2111602850794121130065515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815470467725494840087353 2111602850794121130065515)
                ·
                  refine ⟨3167404276191181695098273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111602850794121130065515 3167404276191181695098273)
                  ·
                    refine ⟨2375553207143386271323705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3167404276191181695098273 2375553207143386271323705)
                    ·
                      refine ⟨1781664905357539703492779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375553207143386271323705 1781664905357539703492779)
                      ·
                        rfl

theorem cell23_3469780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_3469780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469780 prefixEnd_3469780 := by exact prefixLift 3469780
  have htrace : WordTrace (prefixWord ++ tailWord_3469780) baseStart_3469780 baseEnd_3469780 := by
    simpa [prefixWord, tailWord_3469780, baseEnd_3469780] using wordTrace_append hprefix tailTrace_3469780
  have hstable : (prefixWord ++ tailWord_3469780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469780).length < 2 ^ (prefixWord ++ tailWord_3469780).sum := by decide
  have hdescent : baseEnd_3469780 < baseStart_3469780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469782 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3469782 : Nat := 118140960795 + 3469782 * 2 ^ 59
def prefixEnd_3469782 : Nat := 4983230072969 + 3 ^ 40 * 3469782 * 2
def baseEnd_3469782 : Nat := 593888644106282898555923

theorem tailTrace_3469782 : CollatzResearch.WordTrace tailWord_3469782 prefixEnd_3469782 593888644106282898555923 := by
  unfold tailWord_3469782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7909584144723742527005225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84368897543719920288055733 7909584144723742527005225)
  ·
    refine ⟨5932188108542806895253919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7909584144723742527005225 5932188108542806895253919)
    ·
      refine ⟨8898282162814210342880879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5932188108542806895253919 8898282162814210342880879)
      ·
        refine ⟨13347423244221315514321319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8898282162814210342880879 13347423244221315514321319)
        ·
          refine ⟨20021134866331973271481979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13347423244221315514321319 20021134866331973271481979)
          ·
            refine ⟨30031702299497959907222969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20021134866331973271481979 30031702299497959907222969)
            ·
              refine ⟨22523776724623469930417227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30031702299497959907222969 22523776724623469930417227)
              ·
                refine ⟨33785665086935204895625841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22523776724623469930417227 33785665086935204895625841)
                ·
                  refine ⟨25339248815201403671719381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33785665086935204895625841 25339248815201403671719381)
                  ·
                    refine ⟨593888644106282898555923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25339248815201403671719381 593888644106282898555923)
                    ·
                      rfl

theorem cell23_3469782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3469782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469782 prefixEnd_3469782 := by exact prefixLift 3469782
  have htrace : WordTrace (prefixWord ++ tailWord_3469782) baseStart_3469782 baseEnd_3469782 := by
    simpa [prefixWord, tailWord_3469782, baseEnd_3469782] using wordTrace_append hprefix tailTrace_3469782
  have hstable : (prefixWord ++ tailWord_3469782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469782).length < 2 ^ (prefixWord ++ tailWord_3469782).sum := by decide
  have hdescent : baseEnd_3469782 < baseStart_3469782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469785 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_3469785 : Nat := 118140960795 + 3469785 * 2 ^ 59
def prefixEnd_3469785 : Nat := 4983230072969 + 3 ^ 40 * 3469785 * 2
def baseEnd_3469785 : Nat := 1781667472760812183930255

theorem tailTrace_3469785 : CollatzResearch.WordTrace tailWord_3469785 prefixEnd_3469785 1781667472760812183930255 := by
  unfold tailWord_3469785
  simp only [CollatzResearch.WordTrace]
  refine ⟨126553455734569011944442809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84368970489712674629628539 126553455734569011944442809)
  ·
    refine ⟨94915091800926758958332107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126553455734569011944442809 94915091800926758958332107)
    ·
      refine ⟨142372637701390138437498161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94915091800926758958332107 142372637701390138437498161)
      ·
        refine ⟨106779478276042603828123621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142372637701390138437498161 106779478276042603828123621)
        ·
          refine ⟨20021152176757988217773179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106779478276042603828123621 20021152176757988217773179)
          ·
            refine ⟨30031728265136982326659769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20021152176757988217773179 30031728265136982326659769)
            ·
              refine ⟨22523796198852736744994827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30031728265136982326659769 22523796198852736744994827)
              ·
                refine ⟨33785694298279105117492241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22523796198852736744994827 33785694298279105117492241)
                ·
                  refine ⟨25339270723709328838119181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33785694298279105117492241 25339270723709328838119181)
                  ·
                    refine ⟨9502226521390998314294693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25339270723709328838119181 9502226521390998314294693)
                    ·
                      refine ⟨1781667472760812183930255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9502226521390998314294693 1781667472760812183930255)
                      ·
                        rfl

theorem cell23_3469785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_3469785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469785 prefixEnd_3469785 := by exact prefixLift 3469785
  have htrace : WordTrace (prefixWord ++ tailWord_3469785) baseStart_3469785 baseEnd_3469785 := by
    simpa [prefixWord, tailWord_3469785, baseEnd_3469785] using wordTrace_append hprefix tailTrace_3469785
  have hstable : (prefixWord ++ tailWord_3469785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469785).length < 2 ^ (prefixWord ++ tailWord_3469785).sum := by decide
  have hdescent : baseEnd_3469785 < baseStart_3469785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469789 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_3469789 : Nat := 118140960795 + 3469789 * 2 ^ 59
def prefixEnd_3469789 : Nat := 4983230072969 + 3 ^ 40 * 3469789 * 2
def baseEnd_3469789 : Nat := 1781669526683430168280237

theorem tailTrace_3469789 : CollatzResearch.WordTrace tailWord_3469789 prefixEnd_3469789 1781669526683430168280237 := by
  unfold tailWord_3469789
  simp only [CollatzResearch.WordTrace]
  refine ⟨126553601626554520627588421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84369067751036347085058947 126553601626554520627588421)
  ·
    refine ⟨23728800304978972617672829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126553601626554520627588421 23728800304978972617672829)
    ·
      refine ⟨8898300114367114731627311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23728800304978972617672829 8898300114367114731627311)
      ·
        refine ⟨13347450171550672097440967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8898300114367114731627311 13347450171550672097440967)
        ·
          refine ⟨20021175257326008146161451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13347450171550672097440967 20021175257326008146161451)
          ·
            refine ⟨30031762885989012219242177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20021175257326008146161451 30031762885989012219242177)
            ·
              refine ⟨22523822164491759164431633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30031762885989012219242177 22523822164491759164431633)
              ·
                refine ⟨16892866623368819373323725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22523822164491759164431633 16892866623368819373323725)
                ·
                  refine ⟨6334824983763307264996397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16892866623368819373323725 6334824983763307264996397)
                  ·
                    refine ⟨2375559368911240224373649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6334824983763307264996397 2375559368911240224373649)
                    ·
                      refine ⟨1781669526683430168280237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375559368911240224373649 1781669526683430168280237)
                      ·
                        rfl

theorem cell23_3469789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_3469789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469789 prefixEnd_3469789 := by exact prefixLift 3469789
  have htrace : WordTrace (prefixWord ++ tailWord_3469789) baseStart_3469789 baseEnd_3469789 := by
    simpa [prefixWord, tailWord_3469789, baseEnd_3469789] using wordTrace_append hprefix tailTrace_3469789
  have hstable : (prefixWord ++ tailWord_3469789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469789).length < 2 ^ (prefixWord ++ tailWord_3469789).sum := by decide
  have hdescent : baseEnd_3469789 < baseStart_3469789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469806 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_3469806 : Nat := 118140960795 + 3469806 * 2 ^ 59
def prefixEnd_3469806 : Nat := 4983230072969 + 3 ^ 40 * 3469806 * 2
def baseEnd_3469806 : Nat := 1781678255854556601767659

theorem tailTrace_3469806 : CollatzResearch.WordTrace tailWord_3469806 prefixEnd_3469806 1781678255854556601767659 := by
  unfold tailWord_3469806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15819277708436616566369659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84369481111661955020638181 15819277708436616566369659)
  ·
    refine ⟨23728916562654924849554489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15819277708436616566369659 23728916562654924849554489)
    ·
      refine ⟨17796687421991193637165867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23728916562654924849554489 17796687421991193637165867)
      ·
        refine ⟨26695031132986790455748801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17796687421991193637165867 26695031132986790455748801)
        ·
          refine ⟨20021273349740092841811601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26695031132986790455748801 20021273349740092841811601)
          ·
            refine ⟨15015955012305069631358701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20021273349740092841811601 15015955012305069631358701)
            ·
              refine ⟨5630983129614401111759513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15015955012305069631358701 5630983129614401111759513)
              ·
                refine ⟨4223237347210800833819635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5630983129614401111759513 4223237347210800833819635)
                ·
                  refine ⟨6334856020816201250729453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223237347210800833819635 6334856020816201250729453)
                  ·
                    refine ⟨2375571007806075469023545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6334856020816201250729453 2375571007806075469023545)
                    ·
                      refine ⟨1781678255854556601767659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375571007806075469023545 1781678255854556601767659)
                      ·
                        rfl

theorem cell23_3469806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_3469806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469806 prefixEnd_3469806 := by exact prefixLift 3469806
  have htrace : WordTrace (prefixWord ++ tailWord_3469806) baseStart_3469806 baseEnd_3469806 := by
    simpa [prefixWord, tailWord_3469806, baseEnd_3469806] using wordTrace_append hprefix tailTrace_3469806
  have hstable : (prefixWord ++ tailWord_3469806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469806).length < 2 ^ (prefixWord ++ tailWord_3469806).sum := by decide
  have hdescent : baseEnd_3469806 < baseStart_3469806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469830 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3469830 : Nat := 118140960795 + 3469830 * 2 ^ 59
def prefixEnd_3469830 : Nat := 4983230072969 + 3 ^ 40 * 3469830 * 2
def baseEnd_3469830 : Nat := 1781690579390264507867549

theorem tailTrace_3469830 : CollatzResearch.WordTrace tailWord_3469830 prefixEnd_3469830 1781690579390264507867549 := by
  unfold tailWord_3469830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954846781856437019682217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84370064679603989753220629 3954846781856437019682217)
  ·
    refine ⟨2966135086392327764761663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3954846781856437019682217 2966135086392327764761663)
    ·
      refine ⟨4449202629588491647142495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966135086392327764761663 4449202629588491647142495)
      ·
        refine ⟨6673803944382737470713743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449202629588491647142495 6673803944382737470713743)
        ·
          refine ⟨10010705916574106206070615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6673803944382737470713743 10010705916574106206070615)
          ·
            refine ⟨15016058874861159309105923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10010705916574106206070615 15016058874861159309105923)
            ·
              refine ⟨22524088312291738963658885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15016058874861159309105923 22524088312291738963658885)
              ·
                refine ⟨4223266558554701055686041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22524088312291738963658885 4223266558554701055686041)
                ·
                  refine ⟨3167449918916025791764531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4223266558554701055686041 3167449918916025791764531)
                  ·
                    refine ⟨4751174878374038687646797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3167449918916025791764531 4751174878374038687646797)
                    ·
                      refine ⟨1781690579390264507867549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4751174878374038687646797 1781690579390264507867549)
                      ·
                        rfl

theorem cell23_3469830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3469830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469830 prefixEnd_3469830 := by exact prefixLift 3469830
  have htrace : WordTrace (prefixWord ++ tailWord_3469830) baseStart_3469830 baseEnd_3469830 := by
    simpa [prefixWord, tailWord_3469830, baseEnd_3469830] using wordTrace_append hprefix tailTrace_3469830
  have hstable : (prefixWord ++ tailWord_3469830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469830).length < 2 ^ (prefixWord ++ tailWord_3469830).sum := by decide
  have hdescent : baseEnd_3469830 < baseStart_3469830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469836 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 2, 2, 2]
def baseStart_3469836 : Nat := 118140960795 + 3469836 * 2 ^ 59
def prefixEnd_3469836 : Nat := 4983230072969 + 3 ^ 40 * 3469836 * 2
def baseEnd_3469836 : Nat := 1781693660274191484392521

theorem tailTrace_3469836 : CollatzResearch.WordTrace tailWord_3469836 prefixEnd_3469836 1781693660274191484392521 := by
  unfold tailWord_3469836
  simp only [CollatzResearch.WordTrace]
  refine ⟨63277657928692123827274681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84370210571589498436366241 63277657928692123827274681)
  ·
    refine ⟨47458243446519092870456011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63277657928692123827274681 47458243446519092870456011)
    ·
      refine ⟨71187365169778639305684017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47458243446519092870456011 71187365169778639305684017)
      ·
        refine ⟨53390523877333979479263013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71187365169778639305684017 53390523877333979479263013)
        ·
          refine ⟨10010723227000121152361815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53390523877333979479263013 10010723227000121152361815)
          ·
            refine ⟨15016084840500181728542723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10010723227000121152361815 15016084840500181728542723)
            ·
              refine ⟨22524127260750272592814085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15016084840500181728542723 22524127260750272592814085)
              ·
                refine ⟨4223273861390676111152641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22524127260750272592814085 4223273861390676111152641)
                ·
                  refine ⟨3167455396043007083364481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4223273861390676111152641 3167455396043007083364481)
                  ·
                    refine ⟨2375591547032255312523361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3167455396043007083364481 2375591547032255312523361)
                    ·
                      refine ⟨1781693660274191484392521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375591547032255312523361 1781693660274191484392521)
                      ·
                        rfl

theorem cell23_3469836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_3469836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469836 prefixEnd_3469836 := by exact prefixLift 3469836
  have htrace : WordTrace (prefixWord ++ tailWord_3469836) baseStart_3469836 baseEnd_3469836 := by
    simpa [prefixWord, tailWord_3469836, baseEnd_3469836] using wordTrace_append hprefix tailTrace_3469836
  have hstable : (prefixWord ++ tailWord_3469836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469836).length < 2 ^ (prefixWord ++ tailWord_3469836).sum := by decide
  have hdescent : baseEnd_3469836 < baseStart_3469836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469852 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_3469852 : Nat := 118140960795 + 3469852 * 2 ^ 59
def prefixEnd_3469852 : Nat := 4983230072969 + 3 ^ 40 * 3469852 * 2
def baseEnd_3469852 : Nat := 1781701875964663421792447

theorem tailTrace_3469852 : CollatzResearch.WordTrace tailWord_3469852 prefixEnd_3469852 1781701875964663421792447 := by
  unfold tailWord_3469852
  simp only [CollatzResearch.WordTrace]
  refine ⟨63277949712663141193565905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84370599616884188258087873 63277949712663141193565905)
  ·
    refine ⟨47458462284497355895174429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63277949712663141193565905 47458462284497355895174429)
    ·
      refine ⟨17796923356686508460690411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47458462284497355895174429 17796923356686508460690411)
      ·
        refine ⟨26695385035029762691035617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17796923356686508460690411 26695385035029762691035617)
        ·
          refine ⟨20021538776272322018276713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26695385035029762691035617 20021538776272322018276713)
          ·
            refine ⟨15016154082204241513707535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20021538776272322018276713 15016154082204241513707535)
            ·
              refine ⟨22524231123306362270561303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15016154082204241513707535 22524231123306362270561303)
              ·
                refine ⟨33786346684959543405841955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22524231123306362270561303 33786346684959543405841955)
                ·
                  refine ⟨50679520027439315108762933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33786346684959543405841955 50679520027439315108762933)
                  ·
                    refine ⟨4751205002572435791446525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50679520027439315108762933 4751205002572435791446525)
                    ·
                      refine ⟨1781701875964663421792447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4751205002572435791446525 1781701875964663421792447)
                      ·
                        rfl

theorem cell23_3469852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_3469852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469852 prefixEnd_3469852 := by exact prefixLift 3469852
  have htrace : WordTrace (prefixWord ++ tailWord_3469852) baseStart_3469852 baseEnd_3469852 := by
    simpa [prefixWord, tailWord_3469852, baseEnd_3469852] using wordTrace_append hprefix tailTrace_3469852
  have hstable : (prefixWord ++ tailWord_3469852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469852).length < 2 ^ (prefixWord ++ tailWord_3469852).sum := by decide
  have hdescent : baseEnd_3469852 < baseStart_3469852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469855 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 1, 7]
def baseStart_3469855 : Nat := 118140960795 + 3469855 * 2 ^ 59
def prefixEnd_3469855 : Nat := 4983230072969 + 3 ^ 40 * 3469855 * 2
def baseEnd_3469855 : Nat := 593901138802208970018311

theorem tailTrace_3469855 : CollatzResearch.WordTrace tailWord_3469855 prefixEnd_3469855 593901138802208970018311 := by
  unfold tailWord_3469855
  simp only [CollatzResearch.WordTrace]
  refine ⟨126556008844315413899491019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84370672562876942599660679 126556008844315413899491019)
  ·
    refine ⟨189834013266473120849236529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126556008844315413899491019 189834013266473120849236529)
    ·
      refine ⟨142375509949854840636927397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189834013266473120849236529 142375509949854840636927397)
      ·
        refine ⟨26695408115597782619423887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142375509949854840636927397 26695408115597782619423887)
        ·
          refine ⟨40043112173396673929135831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26695408115597782619423887 40043112173396673929135831)
          ·
            refine ⟨60064668260095010893703747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40043112173396673929135831 60064668260095010893703747)
            ·
              refine ⟨90097002390142516340555621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60064668260095010893703747 90097002390142516340555621)
              ·
                refine ⟨16893187948151721813854179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90097002390142516340555621 16893187948151721813854179)
                ·
                  refine ⟨25339781922227582720781269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16893187948151721813854179 25339781922227582720781269)
                  ·
                    refine ⟨593901138802208970018311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25339781922227582720781269 593901138802208970018311)
                    ·
                      rfl

theorem cell23_3469855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_3469855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469855 prefixEnd_3469855 := by exact prefixLift 3469855
  have htrace : WordTrace (prefixWord ++ tailWord_3469855) baseStart_3469855 baseEnd_3469855 := by
    simpa [prefixWord, tailWord_3469855, baseEnd_3469855] using wordTrace_append hprefix tailTrace_3469855
  have hstable : (prefixWord ++ tailWord_3469855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469855).length < 2 ^ (prefixWord ++ tailWord_3469855).sum := by decide
  have hdescent : baseEnd_3469855 < baseStart_3469855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469872 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 2, 5]
def baseStart_3469872 : Nat := 118140960795 + 3469872 * 2 ^ 59
def prefixEnd_3469872 : Nat := 4983230072969 + 3 ^ 40 * 3469872 * 2
def baseEnd_3469872 : Nat := 593904048525917781180785

theorem tailTrace_3469872 : CollatzResearch.WordTrace tailWord_3469872 prefixEnd_3469872 593904048525917781180785 := by
  unfold tailWord_3469872
  simp only [CollatzResearch.WordTrace]
  refine ⟨63278314442626912901429935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84371085923502550535239913 63278314442626912901429935)
  ·
    refine ⟨94917471663940369352144903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63278314442626912901429935 94917471663940369352144903)
    ·
      refine ⟨142376207495910554028217355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94917471663940369352144903 142376207495910554028217355)
      ·
        refine ⟨213564311243865831042326033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142376207495910554028217355 213564311243865831042326033)
        ·
          refine ⟨160173233432899373281744525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213564311243865831042326033 160173233432899373281744525)
          ·
            refine ⟨60064962537337264980654197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160173233432899373281744525 60064962537337264980654197)
            ·
              refine ⟨5631090237875368591936331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60064962537337264980654197 5631090237875368591936331)
              ·
                refine ⟨8446635356813052887904497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631090237875368591936331 8446635356813052887904497)
                ·
                  refine ⟨6334976517609789665928373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8446635356813052887904497 6334976517609789665928373)
                  ·
                    refine ⟨593904048525917781180785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6334976517609789665928373 593904048525917781180785)
                    ·
                      rfl

theorem cell23_3469872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_3469872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469872 prefixEnd_3469872 := by exact prefixLift 3469872
  have htrace : WordTrace (prefixWord ++ tailWord_3469872) baseStart_3469872 baseEnd_3469872 := by
    simpa [prefixWord, tailWord_3469872, baseEnd_3469872] using wordTrace_append hprefix tailTrace_3469872
  have hstable : (prefixWord ++ tailWord_3469872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469872).length < 2 ^ (prefixWord ++ tailWord_3469872).sum := by decide
  have hdescent : baseEnd_3469872 < baseStart_3469872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469909 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_3469909 : Nat := 118140960795 + 3469909 * 2 ^ 59
def prefixEnd_3469909 : Nat := 4983230072969 + 3 ^ 40 * 3469909 * 2
def baseEnd_3469909 : Nat := 1781731144361969698779685

theorem tailTrace_3469909 : CollatzResearch.WordTrace tailWord_3469909 prefixEnd_3469909 1781731144361969698779685 := by
  unfold tailWord_3469909
  simp only [CollatzResearch.WordTrace]
  refine ⟨126557978386119781121956781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84371985590746520747971187 126557978386119781121956781)
  ·
    refine ⟨47459241894794917920733793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126557978386119781121956781 47459241894794917920733793)
    ·
      refine ⟨35594431421096188440550345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47459241894794917920733793 35594431421096188440550345)
      ·
        refine ⟨26695823565822141330412759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35594431421096188440550345 26695823565822141330412759)
        ·
          refine ⟨40043735348733211995619139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26695823565822141330412759 40043735348733211995619139)
          ·
            refine ⟨60065603023099817993428709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40043735348733211995619139 60065603023099817993428709)
            ·
              refine ⟨11262300566831215873767883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60065603023099817993428709 11262300566831215873767883)
              ·
                refine ⟨16893450850246823810651825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11262300566831215873767883 16893450850246823810651825)
                ·
                  refine ⟨12670088137685117857988869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16893450850246823810651825 12670088137685117857988869)
                  ·
                    refine ⟨2375641525815959598372913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12670088137685117857988869 2375641525815959598372913)
                    ·
                      refine ⟨1781731144361969698779685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375641525815959598372913 1781731144361969698779685)
                      ·
                        rfl

theorem cell23_3469909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_3469909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469909 prefixEnd_3469909 := by exact prefixLift 3469909
  have htrace : WordTrace (prefixWord ++ tailWord_3469909) baseStart_3469909 baseEnd_3469909 := by
    simpa [prefixWord, tailWord_3469909, baseEnd_3469909] using wordTrace_append hprefix tailTrace_3469909
  have hstable : (prefixWord ++ tailWord_3469909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469909).length < 2 ^ (prefixWord ++ tailWord_3469909).sum := by decide
  have hdescent : baseEnd_3469909 < baseStart_3469909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469912 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_3469912 : Nat := 118140960795 + 3469912 * 2 ^ 59
def prefixEnd_3469912 : Nat := 4983230072969 + 3 ^ 40 * 3469912 * 2
def baseEnd_3469912 : Nat := 1781732684803933187042171

theorem tailTrace_3469912 : CollatzResearch.WordTrace tailWord_3469912 prefixEnd_3469912 1781732684803933187042171 := by
  unfold tailWord_3469912
  simp only [CollatzResearch.WordTrace]
  refine ⟨63279043902554456317157995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84372058536739275089543993 63279043902554456317157995)
  ·
    refine ⟨94918565853831684475736993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63279043902554456317157995 94918565853831684475736993)
    ·
      refine ⟨71188924390373763356802745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94918565853831684475736993 71188924390373763356802745)
      ·
        refine ⟨53391693292780322517602059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71188924390373763356802745 53391693292780322517602059)
        ·
          refine ⟨80087539939170483776403089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53391693292780322517602059 80087539939170483776403089)
          ·
            refine ⟨60065654954377862832302317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80087539939170483776403089 60065654954377862832302317)
            ·
              refine ⟨22524620607891698562113369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60065654954377862832302317 22524620607891698562113369)
              ·
                refine ⟨16893465455918773921585027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22524620607891698562113369 16893465455918773921585027)
                ·
                  refine ⟨25340198183878160882377541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16893465455918773921585027 25340198183878160882377541)
                  ·
                    refine ⟨4751287159477155165445789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25340198183878160882377541 4751287159477155165445789)
                    ·
                      refine ⟨1781732684803933187042171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4751287159477155165445789 1781732684803933187042171)
                      ·
                        rfl

theorem cell23_3469912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_3469912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469912 prefixEnd_3469912 := by exact prefixLift 3469912
  have htrace : WordTrace (prefixWord ++ tailWord_3469912) baseStart_3469912 baseEnd_3469912 := by
    simpa [prefixWord, tailWord_3469912, baseEnd_3469912] using wordTrace_append hprefix tailTrace_3469912
  have hstable : (prefixWord ++ tailWord_3469912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469912).length < 2 ^ (prefixWord ++ tailWord_3469912).sum := by decide
  have hdescent : baseEnd_3469912 < baseStart_3469912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469953 : List Nat := [1, 2, 4, 2, 1, 1, 5, 2, 1, 4]
def baseStart_3469953 : Nat := 118140960795 + 3469953 * 2 ^ 59
def prefixEnd_3469953 : Nat := 4983230072969 + 3 ^ 40 * 3469953 * 2
def baseEnd_3469953 : Nat := 593917912503589175543161

theorem tailTrace_3469953 : CollatzResearch.WordTrace tailWord_3469953 prefixEnd_3469953 593917912503589175543161 := by
  unfold tailWord_3469953
  simp only [CollatzResearch.WordTrace]
  refine ⟨126559583197960376636558513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84373055465306917757705675 126559583197960376636558513)
  ·
    refine ⟨94919687398470282477418885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126559583197960376636558513 94919687398470282477418885)
    ·
      refine ⟨17797441387213177964516041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94919687398470282477418885 17797441387213177964516041)
      ·
        refine ⟨13348081040409883473387031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17797441387213177964516041 13348081040409883473387031)
        ·
          refine ⟨20022121560614825210080547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13348081040409883473387031 20022121560614825210080547)
          ·
            refine ⟨30033182340922237815120821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20022121560614825210080547 30033182340922237815120821)
            ·
              refine ⟨2815610844461459795167577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30033182340922237815120821 2815610844461459795167577)
              ·
                refine ⟨2111708133346094846375683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815610844461459795167577 2111708133346094846375683)
                ·
                  refine ⟨3167562200019142269563525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111708133346094846375683 3167562200019142269563525)
                  ·
                    refine ⟨593917912503589175543161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3167562200019142269563525 593917912503589175543161)
                    ·
                      rfl

theorem cell23_3469953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_3469953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3469953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3469953 prefixEnd_3469953 := by exact prefixLift 3469953
  have htrace : WordTrace (prefixWord ++ tailWord_3469953) baseStart_3469953 baseEnd_3469953 := by
    simpa [prefixWord, tailWord_3469953, baseEnd_3469953] using wordTrace_append hprefix tailTrace_3469953
  have hstable : (prefixWord ++ tailWord_3469953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469953).length < 2 ^ (prefixWord ++ tailWord_3469953).sum := by decide
  have hdescent : baseEnd_3469953 < baseStart_3469953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470026 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_3470026 : Nat := 118140960795 + 3470026 * 2 ^ 59
def prefixEnd_3470026 : Nat := 4983230072969 + 3 ^ 40 * 3470026 * 2
def baseEnd_3470026 : Nat := 593930407199515247005549

theorem tailTrace_3470026 : CollatzResearch.WordTrace tailWord_3470026 prefixEnd_3470026 593930407199515247005549 := by
  unfold tailWord_3470026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31640561431673977525991483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84374830484463940069310621 31640561431673977525991483)
  ·
    refine ⟨47460842147510966288987225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31640561431673977525991483 47460842147510966288987225)
    ·
      refine ⟨35595631610633224716740419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47460842147510966288987225 35595631610633224716740419)
      ·
        refine ⟨53393447415949837075110629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35595631610633224716740419 53393447415949837075110629)
        ·
          refine ⟨10011271390490594451583243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53393447415949837075110629 10011271390490594451583243)
          ·
            refine ⟨15016907085735891677374865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10011271390490594451583243 15016907085735891677374865)
            ·
              refine ⟨11262680314301918758031149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15016907085735891677374865 11262680314301918758031149)
              ·
                refine ⟨4223505117863219534261681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11262680314301918758031149 4223505117863219534261681)
                ·
                  refine ⟨3167628838397414650696261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4223505117863219534261681 3167628838397414650696261)
                  ·
                    refine ⟨593930407199515247005549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3167628838397414650696261 593930407199515247005549)
                    ·
                      rfl

theorem cell23_3470026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_3470026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470026 prefixEnd_3470026 := by exact prefixLift 3470026
  have htrace : WordTrace (prefixWord ++ tailWord_3470026) baseStart_3470026 baseEnd_3470026 := by
    simpa [prefixWord, tailWord_3470026, baseEnd_3470026] using wordTrace_append hprefix tailTrace_3470026
  have hstable : (prefixWord ++ tailWord_3470026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470026).length < 2 ^ (prefixWord ++ tailWord_3470026).sum := by decide
  have hdescent : baseEnd_3470026 < baseStart_3470026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470037 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3470037 : Nat := 118140960795 + 3470037 * 2 ^ 59
def prefixEnd_3470037 : Nat := 4983230072969 + 3 ^ 40 * 3470037 * 2
def baseEnd_3470037 : Nat := 1781796869885745197979097

theorem tailTrace_3470037 : CollatzResearch.WordTrace tailWord_3470037 prefixEnd_3470037 1781796869885745197979097 := by
  unfold tailWord_3470037
  simp only [CollatzResearch.WordTrace]
  refine ⟨126562646929656058982616365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84375097953104039321744243 126562646929656058982616365)
  ·
    refine ⟨47460992598621022118481137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126562646929656058982616365 47460992598621022118481137)
    ·
      refine ⟨35595744448965766588860853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47460992598621022118481137 35595744448965766588860853)
      ·
        refine ⟨3337101042090540617705705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35595744448965766588860853 3337101042090540617705705)
        ·
          refine ⟨2502825781567905463279279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3337101042090540617705705 2502825781567905463279279)
          ·
            refine ⟨3754238672351858194918919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502825781567905463279279 3754238672351858194918919)
            ·
              refine ⟨5631358008527787292378379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754238672351858194918919 5631358008527787292378379)
              ·
                refine ⟨8447037012791680938567569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631358008527787292378379 8447037012791680938567569)
                ·
                  refine ⟨6335277759593760703925677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8447037012791680938567569 6335277759593760703925677)
                  ·
                    refine ⟨2375729159847660263972129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6335277759593760703925677 2375729159847660263972129)
                    ·
                      refine ⟨1781796869885745197979097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375729159847660263972129 1781796869885745197979097)
                      ·
                        rfl

theorem cell23_3470037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3470037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470037 prefixEnd_3470037 := by exact prefixLift 3470037
  have htrace : WordTrace (prefixWord ++ tailWord_3470037) baseStart_3470037 baseEnd_3470037 := by
    simpa [prefixWord, tailWord_3470037, baseEnd_3470037] using wordTrace_append hprefix tailTrace_3470037
  have hstable : (prefixWord ++ tailWord_3470037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470037).length < 2 ^ (prefixWord ++ tailWord_3470037).sum := by decide
  have hdescent : baseEnd_3470037 < baseStart_3470037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470039 : List Nat := [1, 1, 3, 2, 1, 5, 3, 7]
def baseStart_3470039 : Nat := 118140960795 + 3470039 * 2 ^ 59
def prefixEnd_3470039 : Nat := 4983230072969 + 3 ^ 40 * 3470039 * 2
def baseEnd_3470039 : Nat := 65992514698039044079781

theorem tailTrace_3470039 : CollatzResearch.WordTrace tailWord_3470039 prefixEnd_3470039 65992514698039044079781 := by
  unfold tailWord_3470039
  simp only [CollatzResearch.WordTrace]
  refine ⟨126562719875648813324189171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84375146583765875549459447 126562719875648813324189171)
  ·
    refine ⟨189844079813473219986283757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126562719875648813324189171 189844079813473219986283757)
    ·
      refine ⟨71191529930052457494856409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189844079813473219986283757 71191529930052457494856409)
      ·
        refine ⟨53393647447539343121142307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71191529930052457494856409 53393647447539343121142307)
        ·
          refine ⟨80090471171309014681713461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53393647447539343121142307 80090471171309014681713461)
          ·
            refine ⟨7508481672310220126410637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80090471171309014681713461 7508481672310220126410637)
            ·
              refine ⟨2815680627116332547403989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7508481672310220126410637 2815680627116332547403989)
              ·
                refine ⟨65992514698039044079781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2815680627116332547403989 65992514698039044079781)
                ·
                  rfl

theorem cell23_3470039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 7].length) (baseStart_3470039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470039 prefixEnd_3470039 := by exact prefixLift 3470039
  have htrace : WordTrace (prefixWord ++ tailWord_3470039) baseStart_3470039 baseEnd_3470039 := by
    simpa [prefixWord, tailWord_3470039, baseEnd_3470039] using wordTrace_append hprefix tailTrace_3470039
  have hstable : (prefixWord ++ tailWord_3470039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470039).length < 2 ^ (prefixWord ++ tailWord_3470039).sum := by decide
  have hdescent : baseEnd_3470039 < baseStart_3470039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470053 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 1, 2, 3]
def baseStart_3470053 : Nat := 118140960795 + 3470053 * 2 ^ 59
def prefixEnd_3470053 : Nat := 4983230072969 + 3 ^ 40 * 3470053 * 2
def baseEnd_3470053 : Nat := 1781805085576217135379023

theorem tailTrace_3470053 : CollatzResearch.WordTrace tailWord_3470053 prefixEnd_3470053 1781805085576217135379023 := by
  unfold tailWord_3470053
  simp only [CollatzResearch.WordTrace]
  refine ⟨126563230497598093715198813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84375486998398729143465875 126563230497598093715198813)
  ·
    refine ⟨47461211436599285143199555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126563230497598093715198813 47461211436599285143199555)
    ·
      refine ⟨71191817154898927714799333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47461211436599285143199555 71191817154898927714799333)
      ·
        refine ⟨13348465716543548946524875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71191817154898927714799333 13348465716543548946524875)
        ·
          refine ⟨20022698574815323419787313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13348465716543548946524875 20022698574815323419787313)
          ·
            refine ⟨15017023931111492564840485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20022698574815323419787313 15017023931111492564840485)
            ·
              refine ⟨2815691987083404855907591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15017023931111492564840485 2815691987083404855907591)
              ·
                refine ⟨4223537980625107283861387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815691987083404855907591 4223537980625107283861387)
                ·
                  refine ⟨6335306970937660925792081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223537980625107283861387 6335306970937660925792081)
                  ·
                    refine ⟨4751480228203245694344061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6335306970937660925792081 4751480228203245694344061)
                    ·
                      refine ⟨1781805085576217135379023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4751480228203245694344061 1781805085576217135379023)
                      ·
                        rfl

theorem cell23_3470053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_3470053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470053 prefixEnd_3470053 := by exact prefixLift 3470053
  have htrace : WordTrace (prefixWord ++ tailWord_3470053) baseStart_3470053 baseEnd_3470053 := by
    simpa [prefixWord, tailWord_3470053, baseEnd_3470053] using wordTrace_append hprefix tailTrace_3470053
  have hstable : (prefixWord ++ tailWord_3470053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470053).length < 2 ^ (prefixWord ++ tailWord_3470053).sum := by decide
  have hdescent : baseEnd_3470053 < baseStart_3470053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470106 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2]
def baseStart_3470106 : Nat := 118140960795 + 3470106 * 2 ^ 59
def prefixEnd_3470106 : Nat := 4983230072969 + 3 ^ 40 * 3470106 * 2
def baseEnd_3470106 : Nat := 1781832300050905428016279

theorem tailTrace_3470106 : CollatzResearch.WordTrace tailWord_3470106 prefixEnd_3470106 1781832300050905428016279 := by
  unfold tailWord_3470106
  simp only [CollatzResearch.WordTrace]
  refine ⟨31641290891601520941719543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84376775710937389177918781 31641290891601520941719543)
  ·
    refine ⟨47461936337402281412579315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31641290891601520941719543 47461936337402281412579315)
    ·
      refine ⟨71192904506103422118868973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47461936337402281412579315 71192904506103422118868973)
      ·
        refine ⟨26697339189788783294575865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71192904506103422118868973 26697339189788783294575865)
        ·
          refine ⟨20023004392341587470931899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26697339189788783294575865 20023004392341587470931899)
          ·
            refine ⟨30034506588512381206397849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20023004392341587470931899 30034506588512381206397849)
            ·
              refine ⟨22525879941384285904798387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30034506588512381206397849 22525879941384285904798387)
              ·
                refine ⟨33788819912076428857197581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22525879941384285904798387 33788819912076428857197581)
                ·
                  refine ⟨12670807467028660821449093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33788819912076428857197581 12670807467028660821449093)
                  ·
                    refine ⟨2375776400067873904021705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12670807467028660821449093 2375776400067873904021705)
                    ·
                      refine ⟨1781832300050905428016279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375776400067873904021705 1781832300050905428016279)
                      ·
                        rfl

theorem cell23_3470106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_3470106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470106 prefixEnd_3470106 := by exact prefixLift 3470106
  have htrace : WordTrace (prefixWord ++ tailWord_3470106) baseStart_3470106 baseEnd_3470106 := by
    simpa [prefixWord, tailWord_3470106, baseEnd_3470106] using wordTrace_append hprefix tailTrace_3470106
  have hstable : (prefixWord ++ tailWord_3470106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470106).length < 2 ^ (prefixWord ++ tailWord_3470106).sum := by decide
  have hdescent : baseEnd_3470106 < baseStart_3470106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470134 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3470134 : Nat := 118140960795 + 3470134 * 2 ^ 59
def prefixEnd_3470134 : Nat := 4983230072969 + 3 ^ 40 * 3470134 * 2
def baseEnd_3470134 : Nat := 1781846677509231318466151

theorem tailTrace_3470134 : CollatzResearch.WordTrace tailWord_3470134 prefixEnd_3470134 1781846677509231318466151 := by
  unfold tailWord_3470134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7910386550644040284306091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84377456540203096365931637 7910386550644040284306091)
  ·
    refine ⟨11865579825966060426459137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7910386550644040284306091 11865579825966060426459137)
    ·
      refine ⟨8899184869474545319844353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11865579825966060426459137 8899184869474545319844353)
      ·
        refine ⟨6674388652105908989883265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8899184869474545319844353 6674388652105908989883265)
        ·
          refine ⟨5005791489079431742412449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6674388652105908989883265 5005791489079431742412449)
          ·
            refine ⟨3754343616809573806809337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5005791489079431742412449 3754343616809573806809337)
            ·
              refine ⟨2815757712607180355107003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3754343616809573806809337 2815757712607180355107003)
              ·
                refine ⟨4223636568910770532660505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815757712607180355107003 4223636568910770532660505)
                ·
                  refine ⟨3167727426683077899495379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4223636568910770532660505 3167727426683077899495379)
                  ·
                    refine ⟨4751591140024616849243069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3167727426683077899495379 4751591140024616849243069)
                    ·
                      refine ⟨1781846677509231318466151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4751591140024616849243069 1781846677509231318466151)
                      ·
                        rfl

theorem cell23_3470134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3470134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470134 prefixEnd_3470134 := by exact prefixLift 3470134
  have htrace : WordTrace (prefixWord ++ tailWord_3470134) baseStart_3470134 baseEnd_3470134 := by
    simpa [prefixWord, tailWord_3470134, baseEnd_3470134] using wordTrace_append hprefix tailTrace_3470134
  have hstable : (prefixWord ++ tailWord_3470134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470134).length < 2 ^ (prefixWord ++ tailWord_3470134).sum := by decide
  have hdescent : baseEnd_3470134 < baseStart_3470134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470169 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_3470169 : Nat := 118140960795 + 3470169 * 2 ^ 59
def prefixEnd_3470169 : Nat := 4983230072969 + 3 ^ 40 * 3470169 * 2
def baseEnd_3470169 : Nat := 1781864649332138681528489

theorem tailTrace_3470169 : CollatzResearch.WordTrace tailWord_3470169 prefixEnd_3470169 1781864649332138681528489 := by
  unfold tailWord_3470169
  simp only [CollatzResearch.WordTrace]
  refine ⟨126567461365177845526421561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84378307576785230350947707 126567461365177845526421561)
  ·
    refine ⟨94925596023883384144816171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126567461365177845526421561 94925596023883384144816171)
    ·
      refine ⟨142388394035825076217224257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94925596023883384144816171 142388394035825076217224257)
      ·
        refine ⟨106791295526868807162918193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142388394035825076217224257 106791295526868807162918193)
        ·
          refine ⟨80093471645151605372188645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106791295526868807162918193 80093471645151605372188645)
          ·
            refine ⟨15017525933465926007285371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80093471645151605372188645 15017525933465926007285371)
            ·
              refine ⟨22526288900198889010928057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15017525933465926007285371 22526288900198889010928057)
              ·
                refine ⟨16894716675149166758196043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22526288900198889010928057 16894716675149166758196043)
                ·
                  refine ⟨25342075012723750137294065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16894716675149166758196043 25342075012723750137294065)
                  ·
                    refine ⟨19006556259542812602970549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25342075012723750137294065 19006556259542812602970549)
                    ·
                      refine ⟨1781864649332138681528489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19006556259542812602970549 1781864649332138681528489)
                      ·
                        rfl

theorem cell23_3470169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_3470169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470169 prefixEnd_3470169 := by exact prefixLift 3470169
  have htrace : WordTrace (prefixWord ++ tailWord_3470169) baseStart_3470169 baseEnd_3470169 := by
    simpa [prefixWord, tailWord_3470169, baseEnd_3470169] using wordTrace_append hprefix tailTrace_3470169
  have hstable : (prefixWord ++ tailWord_3470169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470169).length < 2 ^ (prefixWord ++ tailWord_3470169).sum := by decide
  have hdescent : baseEnd_3470169 < baseStart_3470169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470180 : List Nat := [2, 3, 1, 1, 4, 3, 2, 2, 5]
def baseStart_3470180 : Nat := 118140960795 + 3470180 * 2 ^ 59
def prefixEnd_3470180 : Nat := 4983230072969 + 3 ^ 40 * 3470180 * 2
def baseEnd_3470180 : Nat := 197985588624370904276771

theorem tailTrace_3470180 : CollatzResearch.WordTrace tailWord_3470180 prefixEnd_3470180 197985588624370904276771 := by
  unfold tailWord_3470180
  simp only [CollatzResearch.WordTrace]
  refine ⟨63283931284068997202535997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84378575045425329603381329 63283931284068997202535997)
  ·
    refine ⟨23731474231525873950950999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63283931284068997202535997 23731474231525873950950999)
    ·
      refine ⟨35597211347288810926426499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23731474231525873950950999 35597211347288810926426499)
      ·
        refine ⟨53395817020933216389639749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35597211347288810926426499 53395817020933216389639749)
        ·
          refine ⟨10011715691424978073057453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53395817020933216389639749 10011715691424978073057453)
          ·
            refine ⟨3754393384284366777396545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10011715691424978073057453 3754393384284366777396545)
            ·
              refine ⟨2815795038213275083047409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3754393384284366777396545 2815795038213275083047409)
              ·
                refine ⟨2111846278659956312285557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815795038213275083047409 2111846278659956312285557)
                ·
                  refine ⟨197985588624370904276771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2111846278659956312285557 197985588624370904276771)
                  ·
                    rfl

theorem cell23_3470180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_3470180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470180 prefixEnd_3470180 := by exact prefixLift 3470180
  have htrace : WordTrace (prefixWord ++ tailWord_3470180) baseStart_3470180 baseEnd_3470180 := by
    simpa [prefixWord, tailWord_3470180, baseEnd_3470180] using wordTrace_append hprefix tailTrace_3470180
  have hstable : (prefixWord ++ tailWord_3470180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470180).length < 2 ^ (prefixWord ++ tailWord_3470180).sum := by decide
  have hdescent : baseEnd_3470180 < baseStart_3470180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470189 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_3470189 : Nat := 118140960795 + 3470189 * 2 ^ 59
def prefixEnd_3470189 : Nat := 4983230072969 + 3 ^ 40 * 3470189 * 2
def baseEnd_3470189 : Nat := 593958306315076201092799

theorem tailTrace_3470189 : CollatzResearch.WordTrace tailWord_3470189 prefixEnd_3470189 593958306315076201092799 := by
  unfold tailWord_3470189
  simp only [CollatzResearch.WordTrace]
  refine ⟨126568190825105388942149621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84378793883403592628099747 126568190825105388942149621)
  ·
    refine ⟨11865767889853630213326527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126568190825105388942149621 11865767889853630213326527)
    ·
      refine ⟨17798651834780445319989791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11865767889853630213326527 17798651834780445319989791)
      ·
        refine ⟨26697977752170667979984687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17798651834780445319989791 26697977752170667979984687)
        ·
          refine ⟨40046966628256001969977031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26697977752170667979984687 40046966628256001969977031)
          ·
            refine ⟨60070449942384002954965547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40046966628256001969977031 60070449942384002954965547)
            ·
              refine ⟨90105674913576004432448321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60070449942384002954965547 90105674913576004432448321)
              ·
                refine ⟨67579256185182003324336241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90105674913576004432448321 67579256185182003324336241)
                ·
                  refine ⟨50684442138886502493252181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67579256185182003324336241 50684442138886502493252181)
                  ·
                    refine ⟨593958306315076201092799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50684442138886502493252181 593958306315076201092799)
                    ·
                      rfl

theorem cell23_3470189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_3470189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470189 prefixEnd_3470189 := by exact prefixLift 3470189
  have htrace : WordTrace (prefixWord ++ tailWord_3470189) baseStart_3470189 baseEnd_3470189 := by
    simpa [prefixWord, tailWord_3470189, baseEnd_3470189] using wordTrace_append hprefix tailTrace_3470189
  have hstable : (prefixWord ++ tailWord_3470189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470189).length < 2 ^ (prefixWord ++ tailWord_3470189).sum := by decide
  have hdescent : baseEnd_3470189 < baseStart_3470189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470210 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3470210 : Nat := 118140960795 + 3470210 * 2 ^ 59
def prefixEnd_3470210 : Nat := 4983230072969 + 3 ^ 40 * 3470210 * 2
def baseEnd_3470210 : Nat := 593961900679657673705267

theorem tailTrace_3470210 : CollatzResearch.WordTrace tailWord_3470210 prefixEnd_3470210 593961900679657673705267 := by
  unfold tailWord_3470210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31642239189507327382166021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84379304505352873019109389 31642239189507327382166021)
  ·
    refine ⟨5932919848032623884156129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31642239189507327382166021 5932919848032623884156129)
    ·
      refine ⟨4449689886024467913117097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5932919848032623884156129 4449689886024467913117097)
      ·
        refine ⟨3337267414518350934837823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4449689886024467913117097 3337267414518350934837823)
        ·
          refine ⟨5005901121777526402256735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337267414518350934837823 5005901121777526402256735)
          ·
            refine ⟨7508851682666289603385103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5005901121777526402256735 7508851682666289603385103)
            ·
              refine ⟨11263277523999434405077655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508851682666289603385103 11263277523999434405077655)
              ·
                refine ⟨16894916285999151607616483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11263277523999434405077655 16894916285999151607616483)
                ·
                  refine ⟨25342374428998727411424725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16894916285999151607616483 25342374428998727411424725)
                  ·
                    refine ⟨593961900679657673705267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25342374428998727411424725 593961900679657673705267)
                    ·
                      rfl

theorem cell23_3470210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3470210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470210 prefixEnd_3470210 := by exact prefixLift 3470210
  have htrace : WordTrace (prefixWord ++ tailWord_3470210) baseStart_3470210 baseEnd_3470210 := by
    simpa [prefixWord, tailWord_3470210, baseEnd_3470210] using wordTrace_append hprefix tailTrace_3470210
  have hstable : (prefixWord ++ tailWord_3470210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470210).length < 2 ^ (prefixWord ++ tailWord_3470210).sum := by decide
  have hdescent : baseEnd_3470210 < baseStart_3470210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470213 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 4]
def baseStart_3470213 : Nat := 118140960795 + 3470213 * 2 ^ 59
def prefixEnd_3470213 : Nat := 4983230072969 + 3 ^ 40 * 3470213 * 2
def baseEnd_3470213 : Nat := 1781887242480936509378287

theorem tailTrace_3470213 : CollatzResearch.WordTrace tailWord_3470213 prefixEnd_3470213 1781887242480936509378287 := by
  unfold tailWord_3470213
  simp only [CollatzResearch.WordTrace]
  refine ⟨126569066177018441041023293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84379377451345627360682195 126569066177018441041023293)
  ·
    refine ⟨47463399816381915390383735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126569066177018441041023293 47463399816381915390383735)
    ·
      refine ⟨71195099724572873085575603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47463399816381915390383735 71195099724572873085575603)
      ·
        refine ⟨106792649586859309628363405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71195099724572873085575603 106792649586859309628363405)
        ·
          refine ⟨40047243595072241110636277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106792649586859309628363405 40047243595072241110636277)
          ·
            refine ⟨3754429087038022604122151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40047243595072241110636277 3754429087038022604122151)
            ·
              refine ⟨5631643630557033906183227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754429087038022604122151 5631643630557033906183227)
              ·
                refine ⟨8447465445835550859274841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631643630557033906183227 8447465445835550859274841)
                ·
                  refine ⟨6335599084376663144456131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8447465445835550859274841 6335599084376663144456131)
                  ·
                    refine ⟨9503398626564994716684197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6335599084376663144456131 9503398626564994716684197)
                    ·
                      refine ⟨1781887242480936509378287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9503398626564994716684197 1781887242480936509378287)
                      ·
                        rfl

theorem cell23_3470213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_3470213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470213 prefixEnd_3470213 := by exact prefixLift 3470213
  have htrace : WordTrace (prefixWord ++ tailWord_3470213) baseStart_3470213 baseEnd_3470213 := by
    simpa [prefixWord, tailWord_3470213, baseEnd_3470213] using wordTrace_append hprefix tailTrace_3470213
  have hstable : (prefixWord ++ tailWord_3470213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470213).length < 2 ^ (prefixWord ++ tailWord_3470213).sum := by decide
  have hdescent : baseEnd_3470213 < baseStart_3470213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470263 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 3]
def baseStart_3470263 : Nat := 118140960795 + 3470263 * 2 ^ 59
def prefixEnd_3470263 : Nat := 4983230072969 + 3 ^ 40 * 3470263 * 2
def baseEnd_3470263 : Nat := 1781912916513661313753057

theorem tailTrace_3470263 : CollatzResearch.WordTrace tailWord_3470263 prefixEnd_3470263 1781912916513661313753057 := by
  unfold tailWord_3470263
  simp only [CollatzResearch.WordTrace]
  refine ⟨126570889826837299580343443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84380593217891533053562295 126570889826837299580343443)
  ·
    refine ⟨189856334740255949370515165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126570889826837299580343443 189856334740255949370515165)
    ·
      refine ⟨71196125527595981013943187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189856334740255949370515165 71196125527595981013943187)
      ·
        refine ⟨106794188291393971520914781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71196125527595981013943187 106794188291393971520914781)
        ·
          refine ⟨40047820609272739320343043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106794188291393971520914781 40047820609272739320343043)
          ·
            refine ⟨60071730913909108980514565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40047820609272739320343043 60071730913909108980514565)
            ·
              refine ⟨11263449546357957933846481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60071730913909108980514565 11263449546357957933846481)
              ·
                refine ⟨8447587159768468450384861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11263449546357957933846481 8447587159768468450384861)
                ·
                  refine ⟨3167845184913175668894323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8447587159768468450384861 3167845184913175668894323)
                  ·
                    refine ⟨4751767777369763503341485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3167845184913175668894323 4751767777369763503341485)
                    ·
                      refine ⟨1781912916513661313753057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4751767777369763503341485 1781912916513661313753057)
                      ·
                        rfl

theorem cell23_3470263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_3470263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470263 prefixEnd_3470263 := by exact prefixLift 3470263
  have htrace : WordTrace (prefixWord ++ tailWord_3470263) baseStart_3470263 baseEnd_3470263 := by
    simpa [prefixWord, tailWord_3470263, baseEnd_3470263] using wordTrace_append hprefix tailTrace_3470263
  have hstable : (prefixWord ++ tailWord_3470263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470263).length < 2 ^ (prefixWord ++ tailWord_3470263).sum := by decide
  have hdescent : baseEnd_3470263 < baseStart_3470263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470290 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_3470290 : Nat := 118140960795 + 3470290 * 2 ^ 59
def prefixEnd_3470290 : Nat := 4983230072969 + 3 ^ 40 * 3470290 * 2
def baseEnd_3470290 : Nat := 1781926780491332708115433

theorem tailTrace_3470290 : CollatzResearch.WordTrace tailWord_3470290 prefixEnd_3470290 1781926780491332708115433 := by
  unfold tailWord_3470290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31642968649434870797894081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84381249731826322127717549 31642968649434870797894081)
  ·
    refine ⟨23732226487076153098420561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31642968649434870797894081 23732226487076153098420561)
    ·
      refine ⟨17799169865307114823815421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23732226487076153098420561 17799169865307114823815421)
      ·
        refine ⟨6674688699490168058930783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17799169865307114823815421 6674688699490168058930783)
        ·
          refine ⟨10012033049235252088396175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674688699490168058930783 10012033049235252088396175)
          ·
            refine ⟨15018049573852878132594263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10012033049235252088396175 15018049573852878132594263)
            ·
              refine ⟨22527074360779317198891395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15018049573852878132594263 22527074360779317198891395)
              ·
                refine ⟨33790611541168975798337093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22527074360779317198891395 33790611541168975798337093)
                ·
                  refine ⟨6335739663969182962188205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33790611541168975798337093 6335739663969182962188205)
                  ·
                    refine ⟨2375902373988443610820577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6335739663969182962188205 2375902373988443610820577)
                    ·
                      refine ⟨1781926780491332708115433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375902373988443610820577 1781926780491332708115433)
                      ·
                        rfl

theorem cell23_3470290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_3470290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470290 prefixEnd_3470290 := by exact prefixLift 3470290
  have htrace : WordTrace (prefixWord ++ tailWord_3470290) baseStart_3470290 baseEnd_3470290 := by
    simpa [prefixWord, tailWord_3470290, baseEnd_3470290] using wordTrace_append hprefix tailTrace_3470290
  have hstable : (prefixWord ++ tailWord_3470290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470290).length < 2 ^ (prefixWord ++ tailWord_3470290).sum := by decide
  have hdescent : baseEnd_3470290 < baseStart_3470290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470353 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 3]
def baseStart_3470353 : Nat := 118140960795 + 3470353 * 2 ^ 59
def prefixEnd_3470353 : Nat := 4983230072969 + 3 ^ 40 * 3470353 * 2
def baseEnd_3470353 : Nat := 1781959129772565961627643

theorem tailTrace_3470353 : CollatzResearch.WordTrace tailWord_3470353 prefixEnd_3470353 1781959129772565961627643 := by
  unfold tailWord_3470353
  simp only [CollatzResearch.WordTrace]
  refine ⟨126574172396511244951119713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84382781597674163300746475 126574172396511244951119713)
  ·
    refine ⟨94930629297383433713339785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126574172396511244951119713 94930629297383433713339785)
    ·
      refine ⟨71197971973037575285004839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94930629297383433713339785 71197971973037575285004839)
      ·
        refine ⟨106796957959556362927507259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71197971973037575285004839 106796957959556362927507259)
        ·
          refine ⟨160195436939334544391260889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106796957959556362927507259 160195436939334544391260889)
          ·
            refine ⟨120146577704500908293445667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160195436939334544391260889 120146577704500908293445667)
            ·
              refine ⟨180219866556751362440168501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120146577704500908293445667 180219866556751362440168501)
              ·
                refine ⟨16895612489695440228765797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180219866556751362440168501 16895612489695440228765797)
                ·
                  refine ⟨3167927341817895042893587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16895612489695440228765797 3167927341817895042893587)
                  ·
                    refine ⟨4751891012726842564340381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3167927341817895042893587 4751891012726842564340381)
                    ·
                      refine ⟨1781959129772565961627643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4751891012726842564340381 1781959129772565961627643)
                      ·
                        rfl

theorem cell23_3470353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_3470353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470353 prefixEnd_3470353 := by exact prefixLift 3470353
  have htrace : WordTrace (prefixWord ++ tailWord_3470353) baseStart_3470353 baseEnd_3470353 := by
    simpa [prefixWord, tailWord_3470353, baseEnd_3470353] using wordTrace_append hprefix tailTrace_3470353
  have hstable : (prefixWord ++ tailWord_3470353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470353).length < 2 ^ (prefixWord ++ tailWord_3470353).sum := by decide
  have hdescent : baseEnd_3470353 < baseStart_3470353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470370 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_3470370 : Nat := 118140960795 + 3470370 * 2 ^ 59
def prefixEnd_3470370 : Nat := 4983230072969 + 3 ^ 40 * 3470370 * 2
def baseEnd_3470370 : Nat := 1781967858943692395115065

theorem tailTrace_3470370 : CollatzResearch.WordTrace tailWord_3470370 prefixEnd_3470370 1781967858943692395115065 := by
  unfold tailWord_3470370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31643698109362414213622141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84383194958299771236325709 31643698109362414213622141)
  ·
    refine ⟨11866386791010905330108303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31643698109362414213622141 11866386791010905330108303)
    ·
      refine ⟨17799580186516357995162455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11866386791010905330108303 17799580186516357995162455)
      ·
        refine ⟨26699370279774536992743683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17799580186516357995162455 26699370279774536992743683)
        ·
          refine ⟨40049055419661805489115525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26699370279774536992743683 40049055419661805489115525)
          ·
            refine ⟨7509197891186588529209161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40049055419661805489115525 7509197891186588529209161)
            ·
              refine ⟨5631898418389941396906871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7509197891186588529209161 5631898418389941396906871)
              ·
                refine ⟨8447847627584912095360307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631898418389941396906871 8447847627584912095360307)
                ·
                  refine ⟨12671771441377368143040461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8447847627584912095360307 12671771441377368143040461)
                  ·
                    refine ⟨4751914290516513053640173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12671771441377368143040461 4751914290516513053640173)
                    ·
                      refine ⟨1781967858943692395115065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4751914290516513053640173 1781967858943692395115065)
                      ·
                        rfl

theorem cell23_3470370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_3470370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470370 prefixEnd_3470370 := by exact prefixLift 3470370
  have htrace : WordTrace (prefixWord ++ tailWord_3470370) baseStart_3470370 baseEnd_3470370 := by
    simpa [prefixWord, tailWord_3470370, baseEnd_3470370] using wordTrace_append hprefix tailTrace_3470370
  have hstable : (prefixWord ++ tailWord_3470370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470370).length < 2 ^ (prefixWord ++ tailWord_3470370).sum := by decide
  have hdescent : baseEnd_3470370 < baseStart_3470370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470380 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 1, 3, 2]
def baseStart_3470380 : Nat := 118140960795 + 3470380 * 2 ^ 59
def prefixEnd_3470380 : Nat := 4983230072969 + 3 ^ 40 * 3470380 * 2
def baseEnd_3470380 : Nat := 1781972993750237355990019

theorem tailTrace_3470380 : CollatzResearch.WordTrace tailWord_3470380 prefixEnd_3470380 1781972993750237355990019 := by
  unfold tailWord_3470380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63287578583706714281176297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84383438111608952374901729 63287578583706714281176297)
  ·
    refine ⟨47465683937780035710882223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63287578583706714281176297 47465683937780035710882223)
    ·
      refine ⟨71198525906670053566323335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47465683937780035710882223 71198525906670053566323335)
      ·
        refine ⟨106797788860005080349485003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71198525906670053566323335 106797788860005080349485003)
        ·
          refine ⟨160196683290007620524227505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106797788860005080349485003 160196683290007620524227505)
          ·
            refine ⟨120147512467505715393170629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160196683290007620524227505 120147512467505715393170629)
            ·
              refine ⟨22527658587657321636219493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120147512467505715393170629 22527658587657321636219493)
              ·
                refine ⟨4223935985185747806791155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22527658587657321636219493 4223935985185747806791155)
                ·
                  refine ⟨6335903977778621710186733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223935985185747806791155 6335903977778621710186733)
                  ·
                    refine ⟨2375963991666983141320025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6335903977778621710186733 2375963991666983141320025)
                    ·
                      refine ⟨1781972993750237355990019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375963991666983141320025 1781972993750237355990019)
                      ·
                        rfl

theorem cell23_3470380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_3470380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470380 prefixEnd_3470380 := by exact prefixLift 3470380
  have htrace : WordTrace (prefixWord ++ tailWord_3470380) baseStart_3470380 baseEnd_3470380 := by
    simpa [prefixWord, tailWord_3470380, baseEnd_3470380] using wordTrace_append hprefix tailTrace_3470380
  have hstable : (prefixWord ++ tailWord_3470380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470380).length < 2 ^ (prefixWord ++ tailWord_3470380).sum := by decide
  have hdescent : baseEnd_3470380 < baseStart_3470380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470386 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_3470386 : Nat := 118140960795 + 3470386 * 2 ^ 59
def prefixEnd_3470386 : Nat := 4983230072969 + 3 ^ 40 * 3470386 * 2
def baseEnd_3470386 : Nat := 593992024878054777504997

theorem tailTrace_3470386 : CollatzResearch.WordTrace tailWord_3470386 prefixEnd_3470386 593992024878054777504997 := by
  unfold tailWord_3470386
  simp only [CollatzResearch.WordTrace]
  refine ⟨31643844001347922896767753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84383584003594461058047341 31643844001347922896767753)
  ·
    refine ⟨23732883001010942172575815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31643844001347922896767753 23732883001010942172575815)
    ·
      refine ⟨35599324501516413258863723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23732883001010942172575815 35599324501516413258863723)
      ·
        refine ⟨53398986752274619888295585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35599324501516413258863723 53398986752274619888295585)
        ·
          refine ⟨40049240064205964916221689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53398986752274619888295585 40049240064205964916221689)
          ·
            refine ⟨30036930048154473687166267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40049240064205964916221689 30036930048154473687166267)
            ·
              refine ⟨45055395072231710530749401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30036930048154473687166267 45055395072231710530749401)
              ·
                refine ⟨33791546304173782898062051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45055395072231710530749401 33791546304173782898062051)
                ·
                  refine ⟨50687319456260674347093077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33791546304173782898062051 50687319456260674347093077)
                  ·
                    refine ⟨593992024878054777504997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50687319456260674347093077 593992024878054777504997)
                    ·
                      rfl

theorem cell23_3470386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_3470386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470386 prefixEnd_3470386 := by exact prefixLift 3470386
  have htrace : WordTrace (prefixWord ++ tailWord_3470386) baseStart_3470386 baseEnd_3470386 := by
    simpa [prefixWord, tailWord_3470386, baseEnd_3470386] using wordTrace_append hprefix tailTrace_3470386
  have hstable : (prefixWord ++ tailWord_3470386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470386).length < 2 ^ (prefixWord ++ tailWord_3470386).sum := by decide
  have hdescent : baseEnd_3470386 < baseStart_3470386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470397 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_3470397 : Nat := 118140960795 + 3470397 * 2 ^ 59
def prefixEnd_3470397 : Nat := 4983230072969 + 3 ^ 40 * 3470397 * 2
def baseEnd_3470397 : Nat := 1781981722921363789477441

theorem tailTrace_3470397 : CollatzResearch.WordTrace tailWord_3470397 prefixEnd_3470397 1781981722921363789477441 := by
  unfold tailWord_3470397
  simp only [CollatzResearch.WordTrace]
  refine ⟨126575777208351840465721445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84383851472234560310480963 126575777208351840465721445)
  ·
    refine ⟨23732958226565970087322771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126575777208351840465721445 23732958226565970087322771)
    ·
      refine ⟨35599437339848955130984157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23732958226565970087322771 35599437339848955130984157)
      ·
        refine ⟨13349789002443358174119059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35599437339848955130984157 13349789002443358174119059)
        ·
          refine ⟨20024683503665037261178589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13349789002443358174119059 20024683503665037261178589)
          ·
            refine ⟨7509256313874388972941971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20024683503665037261178589 7509256313874388972941971)
            ·
              refine ⟨11263884470811583459412957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7509256313874388972941971 11263884470811583459412957)
              ·
                refine ⟨4223956676554343797279859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11263884470811583459412957 4223956676554343797279859)
                ·
                  refine ⟨6335935014831515695919789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223956676554343797279859 6335935014831515695919789)
                  ·
                    refine ⟨2375975630561818385969921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6335935014831515695919789 2375975630561818385969921)
                    ·
                      refine ⟨1781981722921363789477441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2375975630561818385969921 1781981722921363789477441)
                      ·
                        rfl

theorem cell23_3470397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_3470397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470397 prefixEnd_3470397 := by exact prefixLift 3470397
  have htrace : WordTrace (prefixWord ++ tailWord_3470397) baseStart_3470397 baseEnd_3470397 := by
    simpa [prefixWord, tailWord_3470397, baseEnd_3470397] using wordTrace_append hprefix tailTrace_3470397
  have hstable : (prefixWord ++ tailWord_3470397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470397).length < 2 ^ (prefixWord ++ tailWord_3470397).sum := by decide
  have hdescent : baseEnd_3470397 < baseStart_3470397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470473 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_3470473 : Nat := 118140960795 + 3470473 * 2 ^ 59
def prefixEnd_3470473 : Nat := 4983230072969 + 3 ^ 40 * 3470473 * 2
def baseEnd_3470473 : Nat := 1782020747451105492127091

theorem tailTrace_3470473 : CollatzResearch.WordTrace tailWord_3470473 prefixEnd_3470473 1782020747451105492127091 := by
  unfold tailWord_3470473
  simp only [CollatzResearch.WordTrace]
  refine ⟨126578549156076505445488073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84385699437384336963658715 126578549156076505445488073)
  ·
    refine ⟨94933911867057379084116055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126578549156076505445488073 94933911867057379084116055)
    ·
      refine ⟨142400867800586068626174083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94933911867057379084116055 142400867800586068626174083)
      ·
        refine ⟨213601301700879102939261125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142400867800586068626174083 213601301700879102939261125)
        ·
          refine ⟨40050244068914831801111461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213601301700879102939261125 40050244068914831801111461)
          ·
            refine ⟨7509420762921530962708399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40050244068914831801111461 7509420762921530962708399)
            ·
              refine ⟨11264131144382296444062599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7509420762921530962708399 11264131144382296444062599)
              ·
                refine ⟨16896196716573444666093899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11264131144382296444062599 16896196716573444666093899)
                ·
                  refine ⟨25344295074860166999140849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16896196716573444666093899 25344295074860166999140849)
                  ·
                    refine ⟨19008221306145125249355637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25344295074860166999140849 19008221306145125249355637)
                    ·
                      refine ⟨1782020747451105492127091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19008221306145125249355637 1782020747451105492127091)
                      ·
                        rfl

theorem cell23_3470473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_3470473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470473 prefixEnd_3470473 := by exact prefixLift 3470473
  have htrace : WordTrace (prefixWord ++ tailWord_3470473) baseStart_3470473 baseEnd_3470473 := by
    simpa [prefixWord, tailWord_3470473, baseEnd_3470473] using wordTrace_append hprefix tailTrace_3470473
  have hstable : (prefixWord ++ tailWord_3470473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470473).length < 2 ^ (prefixWord ++ tailWord_3470473).sum := by decide
  have hdescent : baseEnd_3470473 < baseStart_3470473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470500 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_3470500 : Nat := 118140960795 + 3470500 * 2 ^ 59
def prefixEnd_3470500 : Nat := 4983230072969 + 3 ^ 40 * 3470500 * 2
def baseEnd_3470500 : Nat := 1782034611428776886489467

theorem tailTrace_3470500 : CollatzResearch.WordTrace tailWord_3470500 prefixEnd_3470500 1782034611428776886489467 := by
  unfold tailWord_3470500
  simp only [CollatzResearch.WordTrace]
  refine ⟨63289766963489344528360477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84386355951319126037813969 63289766963489344528360477)
  ·
    refine ⟨23733662611308504198135179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63289766963489344528360477 23733662611308504198135179)
    ·
      refine ⟨35600493916962756297202769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23733662611308504198135179 35600493916962756297202769)
      ·
        refine ⟨26700370437722067222902077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35600493916962756297202769 26700370437722067222902077)
        ·
          refine ⟨10012638914145775208588279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26700370437722067222902077 10012638914145775208588279)
          ·
            refine ⟨15018958371218662812882419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10012638914145775208588279 15018958371218662812882419)
            ·
              refine ⟨22528437556827994219323629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15018958371218662812882419 22528437556827994219323629)
              ·
                refine ⟨8448164083810497832246361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22528437556827994219323629 8448164083810497832246361)
                ·
                  refine ⟨6336123062857873374184771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8448164083810497832246361 6336123062857873374184771)
                  ·
                    refine ⟨9504184594286810061277157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6336123062857873374184771 9504184594286810061277157)
                    ·
                      refine ⟨1782034611428776886489467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9504184594286810061277157 1782034611428776886489467)
                      ·
                        rfl

theorem cell23_3470500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_3470500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470500 prefixEnd_3470500 := by exact prefixLift 3470500
  have htrace : WordTrace (prefixWord ++ tailWord_3470500) baseStart_3470500 baseEnd_3470500 := by
    simpa [prefixWord, tailWord_3470500, baseEnd_3470500] using wordTrace_append hprefix tailTrace_3470500
  have hstable : (prefixWord ++ tailWord_3470500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470500).length < 2 ^ (prefixWord ++ tailWord_3470500).sum := by decide
  have hdescent : baseEnd_3470500 < baseStart_3470500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470518 : List Nat := [5, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_3470518 : Nat := 118140960795 + 3470518 * 2 ^ 59
def prefixEnd_3470518 : Nat := 4983230072969 + 3 ^ 40 * 3470518 * 2
def baseEnd_3470518 : Nat := 198004872675617535118265

theorem tailTrace_3470518 : CollatzResearch.WordTrace tailWord_3470518 prefixEnd_3470518 198004872675617535118265 := by
  unfold tailWord_3470518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7911261902557092383179763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84386793627275652087250805 7911261902557092383179763)
  ·
    refine ⟨11866892853835638574769645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7911261902557092383179763 11866892853835638574769645)
    ·
      refine ⟨4450084820188364465538617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11866892853835638574769645 4450084820188364465538617)
      ·
        refine ⟨3337563615141273349153963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4450084820188364465538617 3337563615141273349153963)
        ·
          refine ⟨5006345422711910023730945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337563615141273349153963 5006345422711910023730945)
          ·
            refine ⟨3754759067033932517798209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006345422711910023730945 3754759067033932517798209)
            ·
              refine ⟨2816069300275449388348657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3754759067033932517798209 2816069300275449388348657)
              ·
                refine ⟨2112051975206587041261493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2816069300275449388348657 2112051975206587041261493)
                ·
                  refine ⟨198004872675617535118265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2112051975206587041261493 198004872675617535118265)
                  ·
                    rfl

theorem cell23_3470518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_3470518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470518 prefixEnd_3470518 := by exact prefixLift 3470518
  have htrace : WordTrace (prefixWord ++ tailWord_3470518) baseStart_3470518 baseEnd_3470518 := by
    simpa [prefixWord, tailWord_3470518, baseEnd_3470518] using wordTrace_append hprefix tailTrace_3470518
  have hstable : (prefixWord ++ tailWord_3470518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470518).length < 2 ^ (prefixWord ++ tailWord_3470518).sum := by decide
  have hdescent : baseEnd_3470518 < baseStart_3470518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470533 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_3470533 : Nat := 118140960795 + 3470533 * 2 ^ 59
def prefixEnd_3470533 : Nat := 4983230072969 + 3 ^ 40 * 3470533 * 2
def baseEnd_3470533 : Nat := 1782051556290375257376815

theorem tailTrace_3470533 : CollatzResearch.WordTrace tailWord_3470533 prefixEnd_3470533 1782051556290375257376815 := by
  unfold tailWord_3470533
  simp only [CollatzResearch.WordTrace]
  refine ⟨126580737535859135692672253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84387158357239423795114835 126580737535859135692672253)
  ·
    refine ⟨47467776575947175884752095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126580737535859135692672253 47467776575947175884752095)
    ·
      refine ⟨71201664863920763827128143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47467776575947175884752095 71201664863920763827128143)
      ·
        refine ⟨106802497295881145740692215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71201664863920763827128143 106802497295881145740692215)
        ·
          refine ⟨160203745943821718611038323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106802497295881145740692215 160203745943821718611038323)
          ·
            refine ⟨240305618915732577916557485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160203745943821718611038323 240305618915732577916557485)
            ·
              refine ⟨90114607093399716718709057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240305618915732577916557485 90114607093399716718709057)
              ·
                refine ⟨67585955320049787539031793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90114607093399716718709057 67585955320049787539031793)
                ·
                  refine ⟨50689466490037340654273845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67585955320049787539031793 50689466490037340654273845)
                  ·
                    refine ⟨4752137483441000686338173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50689466490037340654273845 4752137483441000686338173)
                    ·
                      refine ⟨1782051556290375257376815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4752137483441000686338173 1782051556290375257376815)
                      ·
                        rfl

theorem cell23_3470533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_3470533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470533 prefixEnd_3470533 := by exact prefixLift 3470533
  have htrace : WordTrace (prefixWord ++ tailWord_3470533) baseStart_3470533 baseEnd_3470533 := by
    simpa [prefixWord, tailWord_3470533, baseEnd_3470533] using wordTrace_append hprefix tailTrace_3470533
  have hstable : (prefixWord ++ tailWord_3470533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470533).length < 2 ^ (prefixWord ++ tailWord_3470533).sum := by decide
  have hdescent : baseEnd_3470533 < baseStart_3470533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470620 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3470620 : Nat := 118140960795 + 3470620 * 2 ^ 59
def prefixEnd_3470620 : Nat := 4983230072969 + 3 ^ 40 * 3470620 * 2
def baseEnd_3470620 : Nat := 1782096229107316416988915

theorem tailTrace_3470620 : CollatzResearch.WordTrace tailWord_3470620 prefixEnd_3470620 1782096229107316416988915 := by
  unfold tailWord_3470620
  simp only [CollatzResearch.WordTrace]
  refine ⟨63291955343271974775544657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84389273791029299700726209 63291955343271974775544657)
  ·
    refine ⟨47468966507453981081658493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63291955343271974775544657 47468966507453981081658493)
    ·
      refine ⟨17800862440295242905621935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47468966507453981081658493 17800862440295242905621935)
      ·
        refine ⟨26701293660442864358432903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17800862440295242905621935 26701293660442864358432903)
        ·
          refine ⟨40051940490664296537649355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26701293660442864358432903 40051940490664296537649355)
          ·
            refine ⟨60077910735996444806474033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40051940490664296537649355 60077910735996444806474033)
            ·
              refine ⟨45058433051997333604855525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60077910735996444806474033 45058433051997333604855525)
              ·
                refine ⟨8448456197249500050910411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45058433051997333604855525 8448456197249500050910411)
                ·
                  refine ⟨12672684295874250076365617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8448456197249500050910411 12672684295874250076365617)
                  ·
                    refine ⟨9504513221905687557274213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12672684295874250076365617 9504513221905687557274213)
                    ·
                      refine ⟨1782096229107316416988915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9504513221905687557274213 1782096229107316416988915)
                      ·
                        rfl

theorem cell23_3470620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3470620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470620 prefixEnd_3470620 := by exact prefixLift 3470620
  have htrace : WordTrace (prefixWord ++ tailWord_3470620) baseStart_3470620 baseEnd_3470620 := by
    simpa [prefixWord, tailWord_3470620, baseEnd_3470620] using wordTrace_append hprefix tailTrace_3470620
  have hstable : (prefixWord ++ tailWord_3470620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470620).length < 2 ^ (prefixWord ++ tailWord_3470620).sum := by decide
  have hdescent : baseEnd_3470620 < baseStart_3470620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470627 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 3]
def baseStart_3470627 : Nat := 118140960795 + 3470627 * 2 ^ 59
def prefixEnd_3470627 : Nat := 4983230072969 + 3 ^ 40 * 3470627 * 2
def baseEnd_3470627 : Nat := 1782099823471897889601383

theorem tailTrace_3470627 : CollatzResearch.WordTrace tailWord_3470627 prefixEnd_3470627 1782099823471897889601383 := by
  unfold tailWord_3470627
  simp only [CollatzResearch.WordTrace]
  refine ⟨126584165997518589746594135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84389443998345726497729423 126584165997518589746594135)
  ·
    refine ⟨189876248996277884619891203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126584165997518589746594135 189876248996277884619891203)
    ·
      refine ⟨284814373494416826929836805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189876248996277884619891203 284814373494416826929836805)
      ·
        refine ⟨53402695030203155049344401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284814373494416826929836805 53402695030203155049344401)
        ·
          refine ⟨40052021272652366287008301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53402695030203155049344401 40052021272652366287008301)
          ·
            refine ⟨15019507977244637357628113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40052021272652366287008301 15019507977244637357628113)
            ·
              refine ⟨11264630982933478018221085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15019507977244637357628113 11264630982933478018221085)
              ·
                refine ⟨4224236618600054256832907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11264630982933478018221085 4224236618600054256832907)
                ·
                  refine ⟨6336354927900081385249361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224236618600054256832907 6336354927900081385249361)
                  ·
                    refine ⟨4752266195925061038937021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6336354927900081385249361 4752266195925061038937021)
                    ·
                      refine ⟨1782099823471897889601383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4752266195925061038937021 1782099823471897889601383)
                      ·
                        rfl

theorem cell23_3470627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_3470627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470627 prefixEnd_3470627 := by exact prefixLift 3470627
  have htrace : WordTrace (prefixWord ++ tailWord_3470627) baseStart_3470627 baseEnd_3470627 := by
    simpa [prefixWord, tailWord_3470627, baseEnd_3470627] using wordTrace_append hprefix tailTrace_3470627
  have hstable : (prefixWord ++ tailWord_3470627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470627).length < 2 ^ (prefixWord ++ tailWord_3470627).sum := by decide
  have hdescent : baseEnd_3470627 < baseStart_3470627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470637 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3470637 : Nat := 118140960795 + 3470637 * 2 ^ 59
def prefixEnd_3470637 : Nat := 4983230072969 + 3 ^ 40 * 3470637 * 2
def baseEnd_3470637 : Nat := 1782104958278442850476337

theorem tailTrace_3470637 : CollatzResearch.WordTrace tailWord_3470637 prefixEnd_3470637 1782104958278442850476337 := by
  unfold tailWord_3470637
  simp only [CollatzResearch.WordTrace]
  refine ⟨126584530727482361454458165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84389687151654907636305443 126584530727482361454458165)
  ·
    refine ⟨11867299755701471386355453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126584530727482361454458165 11867299755701471386355453)
    ·
      refine ⟨4450237408388051769883295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11867299755701471386355453 4450237408388051769883295)
      ·
        refine ⟨6675356112582077654824943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4450237408388051769883295 6675356112582077654824943)
        ·
          refine ⟨10013034168873116482237415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6675356112582077654824943 10013034168873116482237415)
          ·
            refine ⟨15019551253309674723356123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10013034168873116482237415 15019551253309674723356123)
            ·
              refine ⟨22529326879964512085034185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15019551253309674723356123 22529326879964512085034185)
              ·
                refine ⟨16896995159973384063775639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22529326879964512085034185 16896995159973384063775639)
                ·
                  refine ⟨25345492739960076095663459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16896995159973384063775639 25345492739960076095663459)
                  ·
                    refine ⟨38018239109940114143495189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25345492739960076095663459 38018239109940114143495189)
                    ·
                      refine ⟨1782104958278442850476337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38018239109940114143495189 1782104958278442850476337)
                      ·
                        rfl

theorem cell23_3470637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3470637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470637 prefixEnd_3470637 := by exact prefixLift 3470637
  have htrace : WordTrace (prefixWord ++ tailWord_3470637) baseStart_3470637 baseEnd_3470637 := by
    simpa [prefixWord, tailWord_3470637, baseEnd_3470637] using wordTrace_append hprefix tailTrace_3470637
  have hstable : (prefixWord ++ tailWord_3470637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470637).length < 2 ^ (prefixWord ++ tailWord_3470637).sum := by decide
  have hdescent : baseEnd_3470637 < baseStart_3470637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470641 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 3, 2, 2]
def baseStart_3470641 : Nat := 118140960795 + 3470641 * 2 ^ 59
def prefixEnd_3470641 : Nat := 4983230072969 + 3 ^ 40 * 3470641 * 2
def baseEnd_3470641 : Nat := 1782107012201060834826319

theorem tailTrace_3470641 : CollatzResearch.WordTrace tailWord_3470641 prefixEnd_3470641 1782107012201060834826319 := by
  unfold tailWord_3470641
  simp only [CollatzResearch.WordTrace]
  refine ⟨126584676619467870137603777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84389784412978580091735851 126584676619467870137603777)
  ·
    refine ⟨94938507464600902603202833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126584676619467870137603777 94938507464600902603202833)
    ·
      refine ⟨71203880598450676952402125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94938507464600902603202833 71203880598450676952402125)
      ·
        refine ⟨26701455224419003857150797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71203880598450676952402125 26701455224419003857150797)
        ·
          refine ⟨10013045709157126446431549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26701455224419003857150797 10013045709157126446431549)
          ·
            refine ⟨3754892140933922417411831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10013045709157126446431549 3754892140933922417411831)
            ·
              refine ⟨5632338211400883626117747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754892140933922417411831 5632338211400883626117747)
              ·
                refine ⟨8448507317101325439176621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5632338211400883626117747 8448507317101325439176621)
                ·
                  refine ⟨3168190243912997039691233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8448507317101325439176621 3168190243912997039691233)
                  ·
                    refine ⟨2376142682934747779768425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3168190243912997039691233 2376142682934747779768425)
                    ·
                      refine ⟨1782107012201060834826319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376142682934747779768425 1782107012201060834826319)
                      ·
                        rfl

theorem cell23_3470641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_3470641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470641 prefixEnd_3470641 := by exact prefixLift 3470641
  have htrace : WordTrace (prefixWord ++ tailWord_3470641) baseStart_3470641 baseEnd_3470641 := by
    simpa [prefixWord, tailWord_3470641, baseEnd_3470641] using wordTrace_append hprefix tailTrace_3470641
  have hstable : (prefixWord ++ tailWord_3470641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470641).length < 2 ^ (prefixWord ++ tailWord_3470641).sum := by decide
  have hdescent : baseEnd_3470641 < baseStart_3470641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470748 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3470748 : Nat := 118140960795 + 3470748 * 2 ^ 59
def prefixEnd_3470748 : Nat := 4983230072969 + 3 ^ 40 * 3470748 * 2
def baseEnd_3470748 : Nat := 1782161954631091916188327

theorem tailTrace_3470748 : CollatzResearch.WordTrace tailWord_3470748 prefixEnd_3470748 1782161954631091916188327 := by
  unfold tailWord_3470748
  simp only [CollatzResearch.WordTrace]
  refine ⟨63294289615040113705874449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84392386153386818274499265 63294289615040113705874449)
  ·
    refine ⟨47470717211280085279405837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63294289615040113705874449 47470717211280085279405837)
    ·
      refine ⟨17801518954230031979777189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47470717211280085279405837 17801518954230031979777189)
      ·
        refine ⟨3337784803918130996208223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17801518954230031979777189 3337784803918130996208223)
        ·
          refine ⟨5006677205877196494312335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337784803918130996208223 5006677205877196494312335)
          ·
            refine ⟨7510015808815794741468503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006677205877196494312335 7510015808815794741468503)
            ·
              refine ⟨11265023713223692112202755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510015808815794741468503 11265023713223692112202755)
              ·
                refine ⟨16897535569835538168304133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11265023713223692112202755 16897535569835538168304133)
                ·
                  refine ⟨3168287919344163406557025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16897535569835538168304133 3168287919344163406557025)
                  ·
                    refine ⟨2376215939508122554917769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3168287919344163406557025 2376215939508122554917769)
                    ·
                      refine ⟨1782161954631091916188327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376215939508122554917769 1782161954631091916188327)
                      ·
                        rfl

theorem cell23_3470748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3470748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470748 prefixEnd_3470748 := by exact prefixLift 3470748
  have htrace : WordTrace (prefixWord ++ tailWord_3470748) baseStart_3470748 baseEnd_3470748 := by
    simpa [prefixWord, tailWord_3470748, baseEnd_3470748] using wordTrace_append hprefix tailTrace_3470748
  have hstable : (prefixWord ++ tailWord_3470748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470748).length < 2 ^ (prefixWord ++ tailWord_3470748).sum := by decide
  have hdescent : baseEnd_3470748 < baseStart_3470748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470754 : List Nat := [3, 3, 1, 2, 1, 2, 2, 4, 5]
def baseStart_3470754 : Nat := 118140960795 + 3470754 * 2 ^ 59
def prefixEnd_3470754 : Nat := 4983230072969 + 3 ^ 40 * 3470754 * 2
def baseEnd_3470754 : Nat := 198018337279446543634811

theorem tailTrace_3470754 : CollatzResearch.WordTrace tailWord_3470754 prefixEnd_3470754 198018337279446543634811 := by
  unfold tailWord_3470754
  simp only [CollatzResearch.WordTrace]
  refine ⟨31647199517014622609116829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84392532045372326957644877 31647199517014622609116829)
  ·
    refine ⟨11867699818880483478418811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31647199517014622609116829 11867699818880483478418811)
    ·
      refine ⟨17801549728320725217628217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11867699818880483478418811 17801549728320725217628217)
      ·
        refine ⟨13351162296240543913221163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17801549728320725217628217 13351162296240543913221163)
        ·
          refine ⟨20026743444360815869831745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13351162296240543913221163 20026743444360815869831745)
          ·
            refine ⟨15020057583270611902373809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20026743444360815869831745 15020057583270611902373809)
            ·
              refine ⟨11265043187452958926780357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15020057583270611902373809 11265043187452958926780357)
              ·
                refine ⟨2112195597647429798771317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11265043187452958926780357 2112195597647429798771317)
                ·
                  refine ⟨198018337279446543634811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2112195597647429798771317 198018337279446543634811)
                  ·
                    rfl

theorem cell23_3470754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_3470754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470754 prefixEnd_3470754 := by exact prefixLift 3470754
  have htrace : WordTrace (prefixWord ++ tailWord_3470754) baseStart_3470754 baseEnd_3470754 := by
    simpa [prefixWord, tailWord_3470754, baseEnd_3470754] using wordTrace_append hprefix tailTrace_3470754
  have hstable : (prefixWord ++ tailWord_3470754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470754).length < 2 ^ (prefixWord ++ tailWord_3470754).sum := by decide
  have hdescent : baseEnd_3470754 < baseStart_3470754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470757 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 2, 5, 2]
def baseStart_3470757 : Nat := 118140960795 + 3470757 * 2 ^ 59
def prefixEnd_3470757 : Nat := 4983230072969 + 3 ^ 40 * 3470757 * 2
def baseEnd_3470757 : Nat := 1782166575956982380975785

theorem tailTrace_3470757 : CollatzResearch.WordTrace tailWord_3470757 prefixEnd_3470757 1782166575956982380975785 := by
  unfold tailWord_3470757
  simp only [CollatzResearch.WordTrace]
  refine ⟨126588907487047621948826525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84392604991365081299217683 126588907487047621948826525)
  ·
    refine ⟨47470840307642858230809947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126588907487047621948826525 47470840307642858230809947)
    ·
      refine ⟨71206260461464287346214921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47470840307642858230809947 71206260461464287346214921)
      ·
        refine ⟨53404695346098215509661191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71206260461464287346214921 53404695346098215509661191)
        ·
          refine ⟨80107043019147323264491787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53404695346098215509661191 80107043019147323264491787)
          ·
            refine ⟨120160564528720984896737681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80107043019147323264491787 120160564528720984896737681)
            ·
              refine ⟨90120423396540738672553261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120160564528720984896737681 90120423396540738672553261)
              ·
                refine ⟨33795158773702777002207473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90120423396540738672553261 33795158773702777002207473)
                ·
                  refine ⟨25346369080277082751655605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33795158773702777002207473 25346369080277082751655605)
                  ·
                    refine ⟨2376222101275976507967713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25346369080277082751655605 2376222101275976507967713)
                    ·
                      refine ⟨1782166575956982380975785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376222101275976507967713 1782166575956982380975785)
                      ·
                        rfl

theorem cell23_3470757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_3470757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470757 prefixEnd_3470757 := by exact prefixLift 3470757
  have htrace : WordTrace (prefixWord ++ tailWord_3470757) baseStart_3470757 baseEnd_3470757 := by
    simpa [prefixWord, tailWord_3470757, baseEnd_3470757] using wordTrace_append hprefix tailTrace_3470757
  have hstable : (prefixWord ++ tailWord_3470757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470757).length < 2 ^ (prefixWord ++ tailWord_3470757).sum := by decide
  have hdescent : baseEnd_3470757 < baseStart_3470757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470765 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_3470765 : Nat := 118140960795 + 3470765 * 2 ^ 59
def prefixEnd_3470765 : Nat := 4983230072969 + 3 ^ 40 * 3470765 * 2
def baseEnd_3470765 : Nat := 1782170683802218349675749

theorem tailTrace_3470765 : CollatzResearch.WordTrace tailWord_3470765 prefixEnd_3470765 1782170683802218349675749 := by
  unfold tailWord_3470765
  simp only [CollatzResearch.WordTrace]
  refine ⟨126589199271018639315117749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84392799514012426210078499 126589199271018639315117749)
  ·
    refine ⟨11867737431657997435792289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126589199271018639315117749 11867737431657997435792289)
    ·
      refine ⟨8900803073743498076844217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11867737431657997435792289 8900803073743498076844217)
      ·
        refine ⟨6675602305307623557633163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8900803073743498076844217 6675602305307623557633163)
        ·
          refine ⟨10013403457961435336449745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6675602305307623557633163 10013403457961435336449745)
          ·
            refine ⟨7510052593471076502337309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10013403457961435336449745 7510052593471076502337309)
            ·
              refine ⟨2816269722551653688376491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7510052593471076502337309 2816269722551653688376491)
              ·
                refine ⟨4224404583827480532564737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816269722551653688376491 4224404583827480532564737)
                ·
                  refine ⟨3168303437870610399423553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4224404583827480532564737 3168303437870610399423553)
                  ·
                    refine ⟨2376227578402957799567665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3168303437870610399423553 2376227578402957799567665)
                    ·
                      refine ⟨1782170683802218349675749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376227578402957799567665 1782170683802218349675749)
                      ·
                        rfl

theorem cell23_3470765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_3470765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470765 prefixEnd_3470765 := by exact prefixLift 3470765
  have htrace : WordTrace (prefixWord ++ tailWord_3470765) baseStart_3470765 baseEnd_3470765 := by
    simpa [prefixWord, tailWord_3470765, baseEnd_3470765] using wordTrace_append hprefix tailTrace_3470765
  have hstable : (prefixWord ++ tailWord_3470765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470765).length < 2 ^ (prefixWord ++ tailWord_3470765).sum := by decide
  have hdescent : baseEnd_3470765 < baseStart_3470765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470787 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 1, 6, 2]
def baseStart_3470787 : Nat := 118140960795 + 3470787 * 2 ^ 59
def prefixEnd_3470787 : Nat := 4983230072969 + 3 ^ 40 * 3470787 * 2
def baseEnd_3470787 : Nat := 1782181980376617263600647

theorem tailTrace_3470787 : CollatzResearch.WordTrace tailWord_3470787 prefixEnd_3470787 1782181980376617263600647 := by
  unfold tailWord_3470787
  simp only [CollatzResearch.WordTrace]
  refine ⟨126590001676938937072418615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84393334451292624714945743 126590001676938937072418615)
  ·
    refine ⟨189885002515408405608627923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126590001676938937072418615 189885002515408405608627923)
    ·
      refine ⟨284827503773112608412941885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189885002515408405608627923 284827503773112608412941885)
      ·
        refine ⟨106810313914917228154853207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284827503773112608412941885 106810313914917228154853207)
        ·
          refine ⟨160215470872375842232279811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106810313914917228154853207 160215470872375842232279811)
          ·
            refine ⟨240323206308563763348419717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160215470872375842232279811 240323206308563763348419717)
            ·
              refine ⟨45060601182855705627828697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240323206308563763348419717 45060601182855705627828697)
              ·
                refine ⟨33795450887141779220871523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45060601182855705627828697 33795450887141779220871523)
                ·
                  refine ⟨50693176330712668831307285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33795450887141779220871523 50693176330712668831307285)
                  ·
                    refine ⟨2376242640502156351467529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50693176330712668831307285 2376242640502156351467529)
                    ·
                      refine ⟨1782181980376617263600647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376242640502156351467529 1782181980376617263600647)
                      ·
                        rfl

theorem cell23_3470787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_3470787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470787 prefixEnd_3470787 := by exact prefixLift 3470787
  have htrace : WordTrace (prefixWord ++ tailWord_3470787) baseStart_3470787 baseEnd_3470787 := by
    simpa [prefixWord, tailWord_3470787, baseEnd_3470787] using wordTrace_append hprefix tailTrace_3470787
  have hstable : (prefixWord ++ tailWord_3470787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470787).length < 2 ^ (prefixWord ++ tailWord_3470787).sum := by decide
  have hdescent : baseEnd_3470787 < baseStart_3470787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470800 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_3470800 : Nat := 118140960795 + 3470800 * 2 ^ 59
def prefixEnd_3470800 : Nat := 4983230072969 + 3 ^ 40 * 3470800 * 2
def baseEnd_3470800 : Nat := 1782188655625125712738087

theorem tailTrace_3470800 : CollatzResearch.WordTrace tailWord_3470800 prefixEnd_3470800 1782188655625125712738087 := by
  unfold tailWord_3470800
  simp only [CollatzResearch.WordTrace]
  refine ⟨63295237912945920146320927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84393650550594560195094569 63295237912945920146320927)
  ·
    refine ⟨94942856869418880219481391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63295237912945920146320927 94942856869418880219481391)
    ·
      refine ⟨142414285304128320329222087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94942856869418880219481391 142414285304128320329222087)
      ·
        refine ⟨213621427956192480493833131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142414285304128320329222087 213621427956192480493833131)
        ·
          refine ⟨320432141934288720740749697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213621427956192480493833131 320432141934288720740749697)
          ·
            refine ⟨240324106450716540555562273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320432141934288720740749697 240324106450716540555562273)
            ·
              refine ⟨180243079838037405416671705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240324106450716540555562273 180243079838037405416671705)
              ·
                refine ⟨135182309878528054062503779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180243079838037405416671705 135182309878528054062503779)
                ·
                  refine ⟨202773464817792081093755669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135182309878528054062503779 202773464817792081093755669)
                  ·
                    refine ⟨9505006163334003801269797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 202773464817792081093755669 9505006163334003801269797)
                    ·
                      refine ⟨1782188655625125712738087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9505006163334003801269797 1782188655625125712738087)
                      ·
                        rfl

theorem cell23_3470800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_3470800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470800 prefixEnd_3470800 := by exact prefixLift 3470800
  have htrace : WordTrace (prefixWord ++ tailWord_3470800) baseStart_3470800 baseEnd_3470800 := by
    simpa [prefixWord, tailWord_3470800, baseEnd_3470800] using wordTrace_append hprefix tailTrace_3470800
  have hstable : (prefixWord ++ tailWord_3470800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470800).length < 2 ^ (prefixWord ++ tailWord_3470800).sum := by decide
  have hdescent : baseEnd_3470800 < baseStart_3470800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470888 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3470888 : Nat := 118140960795 + 3470888 * 2 ^ 59
def prefixEnd_3470888 : Nat := 4983230072969 + 3 ^ 40 * 3470888 * 2
def baseEnd_3470888 : Nat := 1782233841922721368437683

theorem tailTrace_3470888 : CollatzResearch.WordTrace tailWord_3470888 prefixEnd_3470888 1782233841922721368437683 := by
  unfold tailWord_3470888
  simp only [CollatzResearch.WordTrace]
  refine ⟨63296842724786515660922659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84395790299715354214563545 63296842724786515660922659)
  ·
    refine ⟨94945264087179773491383989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63296842724786515660922659 94945264087179773491383989)
    ·
      refine ⟨8901118508173103764817249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94945264087179773491383989 8901118508173103764817249)
      ·
        refine ⟨6675838881129827823612937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8901118508173103764817249 6675838881129827823612937)
        ·
          refine ⟨5006879160847370867709703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6675838881129827823612937 5006879160847370867709703)
          ·
            refine ⟨7510318741271056301564555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006879160847370867709703 7510318741271056301564555)
            ·
              refine ⟨11265478111906584452346833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510318741271056301564555 11265478111906584452346833)
              ·
                refine ⟨8449108583929938339260125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11265478111906584452346833 8449108583929938339260125)
                ·
                  refine ⟨3168415718973726877222547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8449108583929938339260125 3168415718973726877222547)
                  ·
                    refine ⟨4752623578460590315833821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3168415718973726877222547 4752623578460590315833821)
                    ·
                      refine ⟨1782233841922721368437683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4752623578460590315833821 1782233841922721368437683)
                      ·
                        rfl

theorem cell23_3470888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3470888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470888 prefixEnd_3470888 := by exact prefixLift 3470888
  have htrace : WordTrace (prefixWord ++ tailWord_3470888) baseStart_3470888 baseEnd_3470888 := by
    simpa [prefixWord, tailWord_3470888, baseEnd_3470888] using wordTrace_append hprefix tailTrace_3470888
  have hstable : (prefixWord ++ tailWord_3470888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470888).length < 2 ^ (prefixWord ++ tailWord_3470888).sum := by decide
  have hdescent : baseEnd_3470888 < baseStart_3470888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470908 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_3470908 : Nat := 118140960795 + 3470908 * 2 ^ 59
def prefixEnd_3470908 : Nat := 4983230072969 + 3 ^ 40 * 3470908 * 2
def baseEnd_3470908 : Nat := 594081370511937096729197

theorem tailTrace_3470908 : CollatzResearch.WordTrace tailWord_3470908 prefixEnd_3470908 594081370511937096729197 := by
  unfold tailWord_3470908
  simp only [CollatzResearch.WordTrace]
  refine ⟨63297207454750287368786689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84396276606333716491715585 63297207454750287368786689)
  ·
    refine ⟨47472905591062715526590017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63297207454750287368786689 47472905591062715526590017)
    ·
      refine ⟨35604679193297036644942513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47472905591062715526590017 35604679193297036644942513)
      ·
        refine ⟨26703509394972777483706885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35604679193297036644942513 26703509394972777483706885)
        ·
          refine ⟨5006908011557395778195041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26703509394972777483706885 5006908011557395778195041)
          ·
            refine ⟨3755181008668046833646281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006908011557395778195041 3755181008668046833646281)
            ·
              refine ⟨2816385756501035125234711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755181008668046833646281 2816385756501035125234711)
              ·
                refine ⟨4224578634751552687852067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816385756501035125234711 4224578634751552687852067)
                ·
                  refine ⟨6336867952127329031778101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224578634751552687852067 6336867952127329031778101)
                  ·
                    refine ⟨594081370511937096729197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6336867952127329031778101 594081370511937096729197)
                    ·
                      rfl

theorem cell23_3470908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_3470908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470908 prefixEnd_3470908 := by exact prefixLift 3470908
  have htrace : WordTrace (prefixWord ++ tailWord_3470908) baseStart_3470908 baseEnd_3470908 := by
    simpa [prefixWord, tailWord_3470908, baseEnd_3470908] using wordTrace_append hprefix tailTrace_3470908
  have hstable : (prefixWord ++ tailWord_3470908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470908).length < 2 ^ (prefixWord ++ tailWord_3470908).sum := by decide
  have hdescent : baseEnd_3470908 < baseStart_3470908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470911 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 1, 1, 4]
def baseStart_3470911 : Nat := 118140960795 + 3470911 * 2 ^ 59
def prefixEnd_3470911 : Nat := 4983230072969 + 3 ^ 40 * 3470911 * 2
def baseEnd_3470911 : Nat := 1782245651977774778450077

theorem tailTrace_3470911 : CollatzResearch.WordTrace tailWord_3470911 prefixEnd_3470911 1782245651977774778450077 := by
  unfold tailWord_3470911
  simp only [CollatzResearch.WordTrace]
  refine ⟨126594524328489706249932587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84396349552326470833288391 126594524328489706249932587)
  ·
    refine ⟨189891786492734559374898881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126594524328489706249932587 189891786492734559374898881)
    ·
      refine ⟨142418839869550919531174161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189891786492734559374898881 142418839869550919531174161)
      ·
        refine ⟨106814129902163189648380621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142418839869550919531174161 106814129902163189648380621)
        ·
          refine ⟨40055298713311196118142733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106814129902163189648380621 40055298713311196118142733)
          ·
            refine ⟨15020737017491698544303525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40055298713311196118142733 15020737017491698544303525)
            ·
              refine ⟨2816388190779693477056911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15020737017491698544303525 2816388190779693477056911)
              ·
                refine ⟨4224582286169540215585367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816388190779693477056911 4224582286169540215585367)
                ·
                  refine ⟨6336873429254310323378051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224582286169540215585367 6336873429254310323378051)
                  ·
                    refine ⟨9505310143881465485067077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6336873429254310323378051 9505310143881465485067077)
                    ·
                      refine ⟨1782245651977774778450077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9505310143881465485067077 1782245651977774778450077)
                      ·
                        rfl

theorem cell23_3470911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_3470911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470911 prefixEnd_3470911 := by exact prefixLift 3470911
  have htrace : WordTrace (prefixWord ++ tailWord_3470911) baseStart_3470911 baseEnd_3470911 := by
    simpa [prefixWord, tailWord_3470911, baseEnd_3470911] using wordTrace_append hprefix tailTrace_3470911
  have hstable : (prefixWord ++ tailWord_3470911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470911).length < 2 ^ (prefixWord ++ tailWord_3470911).sum := by decide
  have hdescent : baseEnd_3470911 < baseStart_3470911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470928 : List Nat := [2, 1, 1, 1, 1, 3, 3, 6, 1, 2, 2]
def baseStart_3470928 : Nat := 118140960795 + 3470928 * 2 ^ 59
def prefixEnd_3470928 : Nat := 4983230072969 + 3 ^ 40 * 3470928 * 2
def baseEnd_3470928 : Nat := 1782254381148901211937499

theorem tailTrace_3470928 : CollatzResearch.WordTrace tailWord_3470928 prefixEnd_3470928 1782254381148901211937499 := by
  unfold tailWord_3470928
  simp only [CollatzResearch.WordTrace]
  refine ⟨63297572184714059076650719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84396762912952078768867625 63297572184714059076650719)
  ·
    refine ⟨94946358277071088614976079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63297572184714059076650719 94946358277071088614976079)
    ·
      refine ⟨142419537415606632922464119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94946358277071088614976079 142419537415606632922464119)
      ·
        refine ⟨213629306123409949383696179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142419537415606632922464119 213629306123409949383696179)
        ·
          refine ⟨320443959185114924075544269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213629306123409949383696179 320443959185114924075544269)
          ·
            refine ⟨120166484694418096528329101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320443959185114924075544269 120166484694418096528329101)
            ·
              refine ⟨45062431760406786198123413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120166484694418096528329101 45062431760406786198123413)
              ·
                refine ⟨2112301488769068103037035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45062431760406786198123413 2112301488769068103037035)
                ·
                  refine ⟨3168452233153602154555553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112301488769068103037035 3168452233153602154555553)
                  ·
                    refine ⟨2376339174865201615916665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3168452233153602154555553 2376339174865201615916665)
                    ·
                      refine ⟨1782254381148901211937499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376339174865201615916665 1782254381148901211937499)
                      ·
                        rfl

theorem cell23_3470928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 2, 2].length) (baseStart_3470928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470928 prefixEnd_3470928 := by exact prefixLift 3470928
  have htrace : WordTrace (prefixWord ++ tailWord_3470928) baseStart_3470928 baseEnd_3470928 := by
    simpa [prefixWord, tailWord_3470928, baseEnd_3470928] using wordTrace_append hprefix tailTrace_3470928
  have hstable : (prefixWord ++ tailWord_3470928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470928).length < 2 ^ (prefixWord ++ tailWord_3470928).sum := by decide
  have hdescent : baseEnd_3470928 < baseStart_3470928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470962 : List Nat := [3, 2, 1, 2, 3, 3, 1, 3, 1, 2, 2]
def baseStart_3470962 : Nat := 118140960795 + 3470962 * 2 ^ 59
def prefixEnd_3470962 : Nat := 4983230072969 + 3 ^ 40 * 3470962 * 2
def baseEnd_3470962 : Nat := 1782271839491154078912343

theorem tailTrace_3470962 : CollatzResearch.WordTrace tailWord_3470962 prefixEnd_3470962 1782271839491154078912343 := by
  unfold tailWord_3470962
  simp only [CollatzResearch.WordTrace]
  refine ⟨31649096112826235490009785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84397589634203294640026093 31649096112826235490009785)
  ·
    refine ⟨23736822084619676617507339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31649096112826235490009785 23736822084619676617507339)
    ·
      refine ⟨35605233126929514926261009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23736822084619676617507339 35605233126929514926261009)
      ·
        refine ⟨26703924845197136194695757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35605233126929514926261009 26703924845197136194695757)
        ·
          refine ⟨10013971816948926073010909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26703924845197136194695757 10013971816948926073010909)
          ·
            refine ⟨3755239431355847277379091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10013971816948926073010909 3755239431355847277379091)
            ·
              refine ⟨5632859147033770916068637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3755239431355847277379091 5632859147033770916068637)
              ·
                refine ⟨2112322180137664093525739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5632859147033770916068637 2112322180137664093525739)
                ·
                  refine ⟨3168483270206496140288609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112322180137664093525739 3168483270206496140288609)
                  ·
                    refine ⟨2376362452654872105216457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3168483270206496140288609 2376362452654872105216457)
                    ·
                      refine ⟨1782271839491154078912343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376362452654872105216457 1782271839491154078912343)
                      ·
                        rfl

theorem cell23_3470962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_3470962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470962 prefixEnd_3470962 := by exact prefixLift 3470962
  have htrace : WordTrace (prefixWord ++ tailWord_3470962) baseStart_3470962 baseEnd_3470962 := by
    simpa [prefixWord, tailWord_3470962, baseEnd_3470962] using wordTrace_append hprefix tailTrace_3470962
  have hstable : (prefixWord ++ tailWord_3470962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470962).length < 2 ^ (prefixWord ++ tailWord_3470962).sum := by decide
  have hdescent : baseEnd_3470962 < baseStart_3470962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470967 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_3470967 : Nat := 118140960795 + 3470967 * 2 ^ 59
def prefixEnd_3470967 : Nat := 4983230072969 + 3 ^ 40 * 3470967 * 2
def baseEnd_3470967 : Nat := 1782274406894426559349819

theorem tailTrace_3470967 : CollatzResearch.WordTrace tailWord_3470967 prefixEnd_3470967 1782274406894426559349819 := by
  unfold tailWord_3470967
  simp only [CollatzResearch.WordTrace]
  refine ⟨126596566816286827813971155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84397711210857885209314103 126596566816286827813971155)
  ·
    refine ⟨189894850224430241720956733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126596566816286827813971155 189894850224430241720956733)
    ·
      refine ⟨71210568834161340645358775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189894850224430241720956733 71210568834161340645358775)
      ·
        refine ⟨106815853251242010968038163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71210568834161340645358775 106815853251242010968038163)
        ·
          refine ⟨160223779876863016452057245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106815853251242010968038163 160223779876863016452057245)
          ·
            refine ⟨60083917453823631169521467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160223779876863016452057245 60083917453823631169521467)
            ·
              refine ⟨90125876180735446754282201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60083917453823631169521467 90125876180735446754282201)
              ·
                refine ⟨67594407135551585065711651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90125876180735446754282201 67594407135551585065711651)
                ·
                  refine ⟨101391610703327377598567477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67594407135551585065711651 101391610703327377598567477)
                  ·
                    refine ⟨9505463503436941649865701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101391610703327377598567477 9505463503436941649865701)
                    ·
                      refine ⟨1782274406894426559349819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9505463503436941649865701 1782274406894426559349819)
                      ·
                        rfl

theorem cell23_3470967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_3470967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470967 prefixEnd_3470967 := by exact prefixLift 3470967
  have htrace : WordTrace (prefixWord ++ tailWord_3470967) baseStart_3470967 baseEnd_3470967 := by
    simpa [prefixWord, tailWord_3470967, baseEnd_3470967] using wordTrace_append hprefix tailTrace_3470967
  have hstable : (prefixWord ++ tailWord_3470967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470967).length < 2 ^ (prefixWord ++ tailWord_3470967).sum := by decide
  have hdescent : baseEnd_3470967 < baseStart_3470967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470971 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 1, 3, 2]
def baseStart_3470971 : Nat := 118140960795 + 3470971 * 2 ^ 59
def prefixEnd_3470971 : Nat := 4983230072969 + 3 ^ 40 * 3470971 * 2
def baseEnd_3470971 : Nat := 1782276460817044543699801

theorem tailTrace_3470971 : CollatzResearch.WordTrace tailWord_3470971 prefixEnd_3470971 1782276460817044543699801 := by
  unfold tailWord_3470971
  simp only [CollatzResearch.WordTrace]
  refine ⟨126596712708272336497116767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84397808472181557664744511 126596712708272336497116767)
  ·
    refine ⟨189895069062408504745675151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126596712708272336497116767 189895069062408504745675151)
    ·
      refine ⟨284842603593612757118512727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189895069062408504745675151 284842603593612757118512727)
      ·
        refine ⟨427263905390419135677769091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284842603593612757118512727 427263905390419135677769091)
        ·
          refine ⟨640895858085628703516653637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427263905390419135677769091 640895858085628703516653637)
          ·
            refine ⟨120167973391055381909372557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 640895858085628703516653637 120167973391055381909372557)
            ·
              refine ⟨45062990021645768216014709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120167973391055381909372557 45062990021645768216014709)
              ·
                refine ⟨4224655314529290770251379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45062990021645768216014709 4224655314529290770251379)
                ·
                  refine ⟨6336982971793936155377069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224655314529290770251379 6336982971793936155377069)
                  ·
                    refine ⟨2376368614422726058266401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6336982971793936155377069 2376368614422726058266401)
                    ·
                      refine ⟨1782276460817044543699801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376368614422726058266401 1782276460817044543699801)
                      ·
                        rfl

theorem cell23_3470971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 3, 2].length) (baseStart_3470971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470971 prefixEnd_3470971 := by exact prefixLift 3470971
  have htrace : WordTrace (prefixWord ++ tailWord_3470971) baseStart_3470971 baseEnd_3470971 := by
    simpa [prefixWord, tailWord_3470971, baseEnd_3470971] using wordTrace_append hprefix tailTrace_3470971
  have hstable : (prefixWord ++ tailWord_3470971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470971).length < 2 ^ (prefixWord ++ tailWord_3470971).sum := by decide
  have hdescent : baseEnd_3470971 < baseStart_3470971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470987 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 5]
def baseStart_3470987 : Nat := 118140960795 + 3470987 * 2 ^ 59
def prefixEnd_3470987 : Nat := 4983230072969 + 3 ^ 40 * 3470987 * 2
def baseEnd_3470987 : Nat := 1782284676507516481099727

theorem tailTrace_3470987 : CollatzResearch.WordTrace tailWord_3470987 prefixEnd_3470987 1782284676507516481099727 := by
  unfold tailWord_3470987
  simp only [CollatzResearch.WordTrace]
  refine ⟨126597296276214371229699215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84398197517476247486466143 126597296276214371229699215)
  ·
    refine ⟨189895944414321556844548823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126597296276214371229699215 189895944414321556844548823)
    ·
      refine ⟨284843916621482335266823235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189895944414321556844548823 284843916621482335266823235)
      ·
        refine ⟨427265874932223502900234853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284843916621482335266823235 427265874932223502900234853)
        ·
          refine ⟨80112351549791906793794035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 427265874932223502900234853 80112351549791906793794035)
          ·
            refine ⟨120168527324687860190691053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80112351549791906793794035 120168527324687860190691053)
            ·
              refine ⟨45063197746757947571509145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120168527324687860190691053 45063197746757947571509145)
              ·
                refine ⟨33797398310068460678631859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45063197746757947571509145 33797398310068460678631859)
                ·
                  refine ⟨50696097465102691017947789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33797398310068460678631859 50696097465102691017947789)
                  ·
                    refine ⟨19011036549413509131730421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50696097465102691017947789 19011036549413509131730421)
                    ·
                      refine ⟨1782284676507516481099727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19011036549413509131730421 1782284676507516481099727)
                      ·
                        rfl

theorem cell23_3470987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_3470987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470987 prefixEnd_3470987 := by exact prefixLift 3470987
  have htrace : WordTrace (prefixWord ++ tailWord_3470987) baseStart_3470987 baseEnd_3470987 := by
    simpa [prefixWord, tailWord_3470987, baseEnd_3470987] using wordTrace_append hprefix tailTrace_3470987
  have hstable : (prefixWord ++ tailWord_3470987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470987).length < 2 ^ (prefixWord ++ tailWord_3470987).sum := by decide
  have hdescent : baseEnd_3470987 < baseStart_3470987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470997 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_3470997 : Nat := 118140960795 + 3470997 * 2 ^ 59
def prefixEnd_3470997 : Nat := 4983230072969 + 3 ^ 40 * 3470997 * 2
def baseEnd_3470997 : Nat := 1782289811314061441974681

theorem tailTrace_3470997 : CollatzResearch.WordTrace tailWord_3470997 prefixEnd_3470997 1782289811314061441974681 := by
  unfold tailWord_3470997
  simp only [CollatzResearch.WordTrace]
  refine ⟨126597661006178142937563245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84398440670785428625042163 126597661006178142937563245)
  ·
    refine ⟨47474122877316803601586217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126597661006178142937563245 47474122877316803601586217)
    ·
      refine ⟨35605592157987602701189663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47474122877316803601586217 35605592157987602701189663)
      ·
        refine ⟨53408388236981404051784495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35605592157987602701189663 53408388236981404051784495)
        ·
          refine ⟨80112582355472106077676743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53408388236981404051784495 80112582355472106077676743)
          ·
            refine ⟨120168873533208159116515115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80112582355472106077676743 120168873533208159116515115)
            ·
              refine ⟨180253310299812238674772673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120168873533208159116515115 180253310299812238674772673)
              ·
                refine ⟨135189982724859179006079505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180253310299812238674772673 135189982724859179006079505)
                ·
                  refine ⟨101392487043644384254559629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135189982724859179006079505 101392487043644384254559629)
                  ·
                    refine ⟨38022182641366644095459861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101392487043644384254559629 38022182641366644095459861)
                    ·
                      refine ⟨1782289811314061441974681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38022182641366644095459861 1782289811314061441974681)
                      ·
                        rfl

theorem cell23_3470997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_3470997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3470997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3470997 prefixEnd_3470997 := by exact prefixLift 3470997
  have htrace : WordTrace (prefixWord ++ tailWord_3470997) baseStart_3470997 baseEnd_3470997 := by
    simpa [prefixWord, tailWord_3470997, baseEnd_3470997] using wordTrace_append hprefix tailTrace_3470997
  have hstable : (prefixWord ++ tailWord_3470997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470997).length < 2 ^ (prefixWord ++ tailWord_3470997).sum := by decide
  have hdescent : baseEnd_3470997 < baseStart_3470997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471001 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 6, 2, 2]
def baseStart_3471001 : Nat := 118140960795 + 3471001 * 2 ^ 59
def prefixEnd_3471001 : Nat := 4983230072969 + 3 ^ 40 * 3471001 * 2
def baseEnd_3471001 : Nat := 1782291865236679426324663

theorem tailTrace_3471001 : CollatzResearch.WordTrace tailWord_3471001 prefixEnd_3471001 1782291865236679426324663 := by
  unfold tailWord_3471001
  simp only [CollatzResearch.WordTrace]
  refine ⟨126597806898163651620708857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84398537932109101080472571 126597806898163651620708857)
  ·
    refine ⟨94948355173622738715531643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126597806898163651620708857 94948355173622738715531643)
    ·
      refine ⟨142422532760434108073297465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94948355173622738715531643 142422532760434108073297465)
      ·
        refine ⟨106816899570325581054973099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142422532760434108073297465 106816899570325581054973099)
        ·
          refine ⟨160225349355488371582459649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106816899570325581054973099 160225349355488371582459649)
          ·
            refine ⟨120169012016616278686844737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160225349355488371582459649 120169012016616278686844737)
            ·
              refine ⟨90126759012462209015133553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120169012016616278686844737 90126759012462209015133553)
              ·
                refine ⟨67595069259346656761350165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90126759012462209015133553 67595069259346656761350165)
                ·
                  refine ⟨3168518871531874535688289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67595069259346656761350165 3168518871531874535688289)
                  ·
                    refine ⟨2376389153648905901766217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3168518871531874535688289 2376389153648905901766217)
                    ·
                      refine ⟨1782291865236679426324663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376389153648905901766217 1782291865236679426324663)
                      ·
                        rfl

theorem cell23_3471001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_3471001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471001 prefixEnd_3471001 := by exact prefixLift 3471001
  have htrace : WordTrace (prefixWord ++ tailWord_3471001) baseStart_3471001 baseEnd_3471001 := by
    simpa [prefixWord, tailWord_3471001, baseEnd_3471001] using wordTrace_append hprefix tailTrace_3471001
  have hstable : (prefixWord ++ tailWord_3471001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471001).length < 2 ^ (prefixWord ++ tailWord_3471001).sum := by decide
  have hdescent : baseEnd_3471001 < baseStart_3471001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471054 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_3471054 : Nat := 118140960795 + 3471054 * 2 ^ 59
def prefixEnd_3471054 : Nat := 4983230072969 + 3 ^ 40 * 3471054 * 2
def baseEnd_3471054 : Nat := 594106359903789239653973

theorem tailTrace_3471054 : CollatzResearch.WordTrace tailWord_3471054 prefixEnd_3471054 594106359903789239653973 := by
  unfold tailWord_3471054
  simp only [CollatzResearch.WordTrace]
  refine ⟨15824967495871455209048527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84399826644647761114925477 15824967495871455209048527)
  ·
    refine ⟨23737451243807182813572791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15824967495871455209048527 23737451243807182813572791)
    ·
      refine ⟨35606176865710774220359187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23737451243807182813572791 35606176865710774220359187)
      ·
        refine ⟨53409265298566161330538781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35606176865710774220359187 53409265298566161330538781)
        ·
          refine ⟨20028474486962310498952043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53409265298566161330538781 20028474486962310498952043)
          ·
            refine ⟨30042711730443465748428065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20028474486962310498952043 30042711730443465748428065)
            ·
              refine ⟨22532033797832599311321049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30042711730443465748428065 22532033797832599311321049)
              ·
                refine ⟨16899025348374449483490787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22532033797832599311321049 16899025348374449483490787)
                ·
                  refine ⟨25348538022561674225236181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16899025348374449483490787 25348538022561674225236181)
                  ·
                    refine ⟨594106359903789239653973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25348538022561674225236181 594106359903789239653973)
                    ·
                      rfl

theorem cell23_3471054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_3471054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471054 prefixEnd_3471054 := by exact prefixLift 3471054
  have htrace : WordTrace (prefixWord ++ tailWord_3471054) baseStart_3471054 baseEnd_3471054 := by
    simpa [prefixWord, tailWord_3471054, baseEnd_3471054] using wordTrace_append hprefix tailTrace_3471054
  have hstable : (prefixWord ++ tailWord_3471054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471054).length < 2 ^ (prefixWord ++ tailWord_3471054).sum := by decide
  have hdescent : baseEnd_3471054 < baseStart_3471054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471091 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 2, 4, 2]
def baseStart_3471091 : Nat := 118140960795 + 3471091 * 2 ^ 59
def prefixEnd_3471091 : Nat := 4983230072969 + 3 ^ 40 * 3471091 * 2
def baseEnd_3471091 : Nat := 1782338078495584074199249

theorem tailTrace_3471091 : CollatzResearch.WordTrace tailWord_3471091 prefixEnd_3471091 1782338078495584074199249 := by
  unfold tailWord_3471091
  simp only [CollatzResearch.WordTrace]
  refine ⟨126601089467837596991485127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84400726311891731327656751 126601089467837596991485127)
  ·
    refine ⟨189901634201756395487227691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126601089467837596991485127 189901634201756395487227691)
    ·
      refine ⟨284852451302634593230841537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189901634201756395487227691 284852451302634593230841537)
      ·
        refine ⟨213639338476975944923131153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284852451302634593230841537 213639338476975944923131153)
        ·
          refine ⟨160229503857731958692348365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213639338476975944923131153 160229503857731958692348365)
          ·
            refine ⟨60086063946649484509630637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160229503857731958692348365 60086063946649484509630637)
            ·
              refine ⟨22532273979993556691111489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60086063946649484509630637 22532273979993556691111489)
              ·
                refine ⟨16899205484995167518333617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22532273979993556691111489 16899205484995167518333617)
                ·
                  refine ⟨12674404113746375638750213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16899205484995167518333617 12674404113746375638750213)
                  ·
                    refine ⟨2376450771327445432265665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12674404113746375638750213 2376450771327445432265665)
                    ·
                      refine ⟨1782338078495584074199249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376450771327445432265665 1782338078495584074199249)
                      ·
                        rfl

theorem cell23_3471091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 4, 2].length) (baseStart_3471091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471091 prefixEnd_3471091 := by exact prefixLift 3471091
  have htrace : WordTrace (prefixWord ++ tailWord_3471091) baseStart_3471091 baseEnd_3471091 := by
    simpa [prefixWord, tailWord_3471091, baseEnd_3471091] using wordTrace_append hprefix tailTrace_3471091
  have hstable : (prefixWord ++ tailWord_3471091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471091).length < 2 ^ (prefixWord ++ tailWord_3471091).sum := by decide
  have hdescent : baseEnd_3471091 < baseStart_3471091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471108 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_3471108 : Nat := 118140960795 + 3471108 * 2 ^ 59
def prefixEnd_3471108 : Nat := 4983230072969 + 3 ^ 40 * 3471108 * 2
def baseEnd_3471108 : Nat := 1782346807666710507686671

theorem tailTrace_3471108 : CollatzResearch.WordTrace tailWord_3471108 prefixEnd_3471108 1782346807666710507686671 := by
  unfold tailWord_3471108
  simp only [CollatzResearch.WordTrace]
  refine ⟨63300854754388004447426989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84401139672517339263235985 63300854754388004447426989)
  ·
    refine ⟨23737820532895501667785121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63300854754388004447426989 23737820532895501667785121)
    ·
      refine ⟨17803365399671626250838841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23737820532895501667785121 17803365399671626250838841)
      ·
        refine ⟨13352524049753719688129131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17803365399671626250838841 13352524049753719688129131)
        ·
          refine ⟨20028786074630579532193697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13352524049753719688129131 20028786074630579532193697)
          ·
            refine ⟨15021589555972934649145273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20028786074630579532193697 15021589555972934649145273)
            ·
              refine ⟨11266192166979700986858955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15021589555972934649145273 11266192166979700986858955)
              ·
                refine ⟨16899288250469551480288433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11266192166979700986858955 16899288250469551480288433)
                ·
                  refine ⟨12674466187852163610216325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16899288250469551480288433 12674466187852163610216325)
                  ·
                    refine ⟨2376462410222280676915561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12674466187852163610216325 2376462410222280676915561)
                    ·
                      refine ⟨1782346807666710507686671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376462410222280676915561 1782346807666710507686671)
                      ·
                        rfl

theorem cell23_3471108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_3471108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471108 prefixEnd_3471108 := by exact prefixLift 3471108
  have htrace : WordTrace (prefixWord ++ tailWord_3471108) baseStart_3471108 baseEnd_3471108 := by
    simpa [prefixWord, tailWord_3471108, baseEnd_3471108] using wordTrace_append hprefix tailTrace_3471108
  have hstable : (prefixWord ++ tailWord_3471108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471108).length < 2 ^ (prefixWord ++ tailWord_3471108).sum := by decide
  have hdescent : baseEnd_3471108 < baseStart_3471108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471165 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 6]
def baseStart_3471165 : Nat := 118140960795 + 3471165 * 2 ^ 59
def prefixEnd_3471165 : Nat := 4983230072969 + 3 ^ 40 * 3471165 * 2
def baseEnd_3471165 : Nat := 198041786229335198297101

theorem tailTrace_3471165 : CollatzResearch.WordTrace tailWord_3471165 prefixEnd_3471165 198041786229335198297101 := by
  unfold tailWord_3471165
  simp only [CollatzResearch.WordTrace]
  refine ⟨126603788469569507629678949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84402525646379671753119299 126603788469569507629678949)
  ·
    refine ⟨23738210338044282680564803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126603788469569507629678949 23738210338044282680564803)
    ·
      refine ⟨35607315507066424020847205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23738210338044282680564803 35607315507066424020847205)
      ·
        refine ⟨6676371657574954503908851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35607315507066424020847205 6676371657574954503908851)
        ·
          refine ⟨10014557486362431755863277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6676371657574954503908851 10014557486362431755863277)
          ·
            refine ⟨3755459057385911908448729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10014557486362431755863277 3755459057385911908448729)
            ·
              refine ⟨2816594293039433931336547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755459057385911908448729 2816594293039433931336547)
              ·
                refine ⟨4224891439559150897004821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816594293039433931336547 4224891439559150897004821)
                ·
                  refine ⟨198041786229335198297101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4224891439559150897004821 198041786229335198297101)
                  ·
                    rfl

theorem cell23_3471165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_3471165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471165 prefixEnd_3471165 := by exact prefixLift 3471165
  have htrace : WordTrace (prefixWord ++ tailWord_3471165) baseStart_3471165 baseEnd_3471165 := by
    simpa [prefixWord, tailWord_3471165, baseEnd_3471165] using wordTrace_append hprefix tailTrace_3471165
  have hstable : (prefixWord ++ tailWord_3471165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471165).length < 2 ^ (prefixWord ++ tailWord_3471165).sum := by decide
  have hdescent : baseEnd_3471165 < baseStart_3471165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471185 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 2, 3, 2]
def baseStart_3471185 : Nat := 118140960795 + 3471185 * 2 ^ 59
def prefixEnd_3471185 : Nat := 4983230072969 + 3 ^ 40 * 3471185 * 2
def baseEnd_3471185 : Nat := 1782386345677106706423817

theorem tailTrace_3471185 : CollatzResearch.WordTrace tailWord_3471185 prefixEnd_3471185 1782386345677106706423817 := by
  unfold tailWord_3471185
  simp only [CollatzResearch.WordTrace]
  refine ⟨126604517929497051045407009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84403011952998034030271339 126604517929497051045407009)
  ·
    refine ⟨94953388447122788284055257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126604517929497051045407009 94953388447122788284055257)
    ·
      refine ⟨71215041335342091213041443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94953388447122788284055257 71215041335342091213041443)
      ·
        refine ⟨106822562003013136819562165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71215041335342091213041443 106822562003013136819562165)
        ·
          refine ⟨10014615187782481576833953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106822562003013136819562165 10014615187782481576833953)
          ·
            refine ⟨7510961390836861182625465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10014615187782481576833953 7510961390836861182625465)
            ·
              refine ⟨5633221043127645886969099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7510961390836861182625465 5633221043127645886969099)
              ·
                refine ⟨8449831564691468830453649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633221043127645886969099 8449831564691468830453649)
                ·
                  refine ⟨6337373673518601622840237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8449831564691468830453649 6337373673518601622840237)
                  ·
                    refine ⟨2376515127569475608565089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6337373673518601622840237 2376515127569475608565089)
                    ·
                      refine ⟨1782386345677106706423817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376515127569475608565089 1782386345677106706423817)
                      ·
                        rfl

theorem cell23_3471185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_3471185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471185 prefixEnd_3471185 := by exact prefixLift 3471185
  have htrace : WordTrace (prefixWord ++ tailWord_3471185) baseStart_3471185 baseEnd_3471185 := by
    simpa [prefixWord, tailWord_3471185, baseEnd_3471185] using wordTrace_append hprefix tailTrace_3471185
  have hstable : (prefixWord ++ tailWord_3471185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471185).length < 2 ^ (prefixWord ++ tailWord_3471185).sum := by decide
  have hdescent : baseEnd_3471185 < baseStart_3471185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471204 : List Nat := [2, 3, 1, 1, 16]
def baseStart_3471204 : Nat := 118140960795 + 3471204 * 2 ^ 59
def prefixEnd_3471204 : Nat := 4983230072969 + 3 ^ 40 * 3471204 * 2
def baseEnd_3471204 : Nat := 2444987793977424049501

theorem tailTrace_3471204 : CollatzResearch.WordTrace tailWord_3471204 prefixEnd_3471204 2444987793977424049501 := by
  unfold tailWord_3471204
  simp only [CollatzResearch.WordTrace]
  refine ⟨63302605458214108645174333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84403473944285478193565777 63302605458214108645174333)
  ·
    refine ⟨23738477046830290741940375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63302605458214108645174333 23738477046830290741940375)
    ·
      refine ⟨35607715570245436112910563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23738477046830290741940375 35607715570245436112910563)
      ·
        refine ⟨53411573355368154169365845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35607715570245436112910563 53411573355368154169365845)
        ·
          refine ⟨2444987793977424049501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 53411573355368154169365845 2444987793977424049501)
          ·
            rfl

theorem cell23_3471204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 16].length) (baseStart_3471204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471204 prefixEnd_3471204 := by exact prefixLift 3471204
  have htrace : WordTrace (prefixWord ++ tailWord_3471204) baseStart_3471204 baseEnd_3471204 := by
    simpa [prefixWord, tailWord_3471204, baseEnd_3471204] using wordTrace_append hprefix tailTrace_3471204
  have hstable : (prefixWord ++ tailWord_3471204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471204).length < 2 ^ (prefixWord ++ tailWord_3471204).sum := by decide
  have hdescent : baseEnd_3471204 < baseStart_3471204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471252 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_3471252 : Nat := 118140960795 + 3471252 * 2 ^ 59
def prefixEnd_3471252 : Nat := 4983230072969 + 3 ^ 40 * 3471252 * 2
def baseEnd_3471252 : Nat := 1782420748880957944286009

theorem tailTrace_3471252 : CollatzResearch.WordTrace tailWord_3471252 prefixEnd_3471252 1782420748880957944286009 := by
  unfold tailWord_3471252
  simp only [CollatzResearch.WordTrace]
  refine ⟨63303480810127160744048005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84404641080169547658730673 63303480810127160744048005)
  ·
    refine ⟨11869402651898842639509001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63303480810127160744048005 11869402651898842639509001)
    ·
      refine ⟨8902051988924131979631751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11869402651898842639509001 8902051988924131979631751)
      ·
        refine ⟨13353077983386197969447627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8902051988924131979631751 13353077983386197969447627)
        ·
          refine ⟨20029616975079296954171441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13353077983386197969447627 20029616975079296954171441)
          ·
            refine ⟨15022212731309472715628581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20029616975079296954171441 15022212731309472715628581)
            ·
              refine ⟨2816664887120526134180359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15022212731309472715628581 2816664887120526134180359)
              ·
                refine ⟨4224997330680789201270539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816664887120526134180359 4224997330680789201270539)
                ·
                  refine ⟨6337495996021183801905809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224997330680789201270539 6337495996021183801905809)
                  ·
                    refine ⟨4753121997015887851429357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6337495996021183801905809 4753121997015887851429357)
                    ·
                      refine ⟨1782420748880957944286009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4753121997015887851429357 1782420748880957944286009)
                      ·
                        rfl

theorem cell23_3471252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_3471252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471252 prefixEnd_3471252 := by exact prefixLift 3471252
  have htrace : WordTrace (prefixWord ++ tailWord_3471252) baseStart_3471252 baseEnd_3471252 := by
    simpa [prefixWord, tailWord_3471252, baseEnd_3471252] using wordTrace_append hprefix tailTrace_3471252
  have hstable : (prefixWord ++ tailWord_3471252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471252).length < 2 ^ (prefixWord ++ tailWord_3471252).sum := by decide
  have hdescent : baseEnd_3471252 < baseStart_3471252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471291 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 3]
def baseStart_3471291 : Nat := 118140960795 + 3471291 * 2 ^ 59
def prefixEnd_3471291 : Nat := 4983230072969 + 3 ^ 40 * 3471291 * 2
def baseEnd_3471291 : Nat := 1782440774626483291698329

theorem tailTrace_3471291 : CollatzResearch.WordTrace tailWord_3471291 prefixEnd_3471291 1782440774626483291698329 := by
  unfold tailWord_3471291
  simp only [CollatzResearch.WordTrace]
  refine ⟨126608384067113031148765727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84405589378075354099177151 126608384067113031148765727)
  ·
    refine ⟨189912576100669546723148591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126608384067113031148765727 189912576100669546723148591)
    ·
      refine ⟨284868864151004320084722887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189912576100669546723148591 284868864151004320084722887)
      ·
        refine ⟨427303296226506480127084331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284868864151004320084722887 427303296226506480127084331)
        ·
          refine ⟨640954944339759720190626497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427303296226506480127084331 640954944339759720190626497)
          ·
            refine ⟨480716208254819790142969873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640954944339759720190626497 480716208254819790142969873)
            ·
              refine ⟨360537156191114842607227405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480716208254819790142969873 360537156191114842607227405)
              ·
                refine ⟨135201433571668065977710277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360537156191114842607227405 135201433571668065977710277)
                ·
                  refine ⟨25350268794687762370820677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135201433571668065977710277 25350268794687762370820677)
                  ·
                    refine ⟨4753175399003955444528877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25350268794687762370820677 4753175399003955444528877)
                    ·
                      refine ⟨1782440774626483291698329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4753175399003955444528877 1782440774626483291698329)
                      ·
                        rfl

theorem cell23_3471291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 3].length) (baseStart_3471291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471291 prefixEnd_3471291 := by exact prefixLift 3471291
  have htrace : WordTrace (prefixWord ++ tailWord_3471291) baseStart_3471291 baseEnd_3471291 := by
    simpa [prefixWord, tailWord_3471291, baseEnd_3471291] using wordTrace_append hprefix tailTrace_3471291
  have hstable : (prefixWord ++ tailWord_3471291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471291).length < 2 ^ (prefixWord ++ tailWord_3471291).sum := by decide
  have hdescent : baseEnd_3471291 < baseStart_3471291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471301 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_3471301 : Nat := 118140960795 + 3471301 * 2 ^ 59
def prefixEnd_3471301 : Nat := 4983230072969 + 3 ^ 40 * 3471301 * 2
def baseEnd_3471301 : Nat := 1782445909433028252573283

theorem tailTrace_3471301 : CollatzResearch.WordTrace tailWord_3471301 prefixEnd_3471301 1782445909433028252573283 := by
  unfold tailWord_3471301
  simp only [CollatzResearch.WordTrace]
  refine ⟨126608748797076802856629757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84405832531384535237753171 126608748797076802856629757)
  ·
    refine ⟨47478280798903801071236159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126608748797076802856629757 47478280798903801071236159)
    ·
      refine ⟨71217421198355701606854239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47478280798903801071236159 71217421198355701606854239)
      ·
        refine ⟨106826131797533552410281359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71217421198355701606854239 106826131797533552410281359)
        ·
          refine ⟨160239197696300328615422039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106826131797533552410281359 160239197696300328615422039)
          ·
            refine ⟨240358796544450492923133059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160239197696300328615422039 240358796544450492923133059)
            ·
              refine ⟨360538194816675739384699589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240358796544450492923133059 360538194816675739384699589)
              ·
                refine ⟨67600911528126701134631173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360538194816675739384699589 67600911528126701134631173)
                ·
                  refine ⟨12675170911523756462743345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67600911528126701134631173 12675170911523756462743345)
                  ·
                    refine ⟨9506378183642817347057509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12675170911523756462743345 9506378183642817347057509)
                    ·
                      refine ⟨1782445909433028252573283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9506378183642817347057509 1782445909433028252573283)
                      ·
                        rfl

theorem cell23_3471301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_3471301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471301 prefixEnd_3471301 := by exact prefixLift 3471301
  have htrace : WordTrace (prefixWord ++ tailWord_3471301) baseStart_3471301 baseEnd_3471301 := by
    simpa [prefixWord, tailWord_3471301, baseEnd_3471301] using wordTrace_append hprefix tailTrace_3471301
  have hstable : (prefixWord ++ tailWord_3471301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471301).length < 2 ^ (prefixWord ++ tailWord_3471301).sum := by decide
  have hdescent : baseEnd_3471301 < baseStart_3471301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471308 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3471308 : Nat := 118140960795 + 3471308 * 2 ^ 59
def prefixEnd_3471308 : Nat := 4983230072969 + 3 ^ 40 * 3471308 * 2
def baseEnd_3471308 : Nat := 1782449503797609725185751

theorem tailTrace_3471308 : CollatzResearch.WordTrace tailWord_3471308 prefixEnd_3471308 1782449503797609725185751 := by
  unfold tailWord_3471308
  simp only [CollatzResearch.WordTrace]
  refine ⟨63304502054025721526067289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84406002738700962034756385 63304502054025721526067289)
  ·
    refine ⟨47478376540519291144550467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63304502054025721526067289 47478376540519291144550467)
    ·
      refine ⟨71217564810778936716825701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47478376540519291144550467 71217564810778936716825701)
      ·
        refine ⟨13353293402021050634404819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71217564810778936716825701 13353293402021050634404819)
        ·
          refine ⟨20029940103031575951607229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13353293402021050634404819 20029940103031575951607229)
          ·
            refine ⟨7511227538636840981852711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20029940103031575951607229 7511227538636840981852711)
            ·
              refine ⟨11266841307955261472779067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511227538636840981852711 11266841307955261472779067)
              ·
                refine ⟨16900261961932892209168601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11266841307955261472779067 16900261961932892209168601)
                ·
                  refine ⟨12675196471449669156876451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16900261961932892209168601 12675196471449669156876451)
                  ·
                    refine ⟨19012794707174503735314677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12675196471449669156876451 19012794707174503735314677)
                    ·
                      refine ⟨1782449503797609725185751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19012794707174503735314677 1782449503797609725185751)
                      ·
                        rfl

theorem cell23_3471308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3471308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471308 prefixEnd_3471308 := by exact prefixLift 3471308
  have htrace : WordTrace (prefixWord ++ tailWord_3471308) baseStart_3471308 baseEnd_3471308 := by
    simpa [prefixWord, tailWord_3471308, baseEnd_3471308] using wordTrace_append hprefix tailTrace_3471308
  have hstable : (prefixWord ++ tailWord_3471308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471308).length < 2 ^ (prefixWord ++ tailWord_3471308).sum := by decide
  have hdescent : baseEnd_3471308 < baseStart_3471308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471328 : List Nat := [2, 1, 1, 3, 1, 1, 1, 8, 5]
def baseStart_3471328 : Nat := 118140960795 + 3471328 * 2 ^ 59
def prefixEnd_3471328 : Nat := 4983230072969 + 3 ^ 40 * 3471328 * 2
def baseEnd_3471328 : Nat := 198051085934522182992851

theorem tailTrace_3471328 : CollatzResearch.WordTrace tailWord_3471328 prefixEnd_3471328 198051085934522182992851 := by
  unfold tailWord_3471328
  simp only [CollatzResearch.WordTrace]
  refine ⟨63304866783989493233931319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84406489045319324311908425 63304866783989493233931319)
  ·
    refine ⟨94957300175984239850896979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63304866783989493233931319 94957300175984239850896979)
    ·
      refine ⟨142435950263976359776345469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94957300175984239850896979 142435950263976359776345469)
      ·
        refine ⟨53413481348991134916129551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142435950263976359776345469 53413481348991134916129551)
        ·
          refine ⟨80120222023486702374194327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53413481348991134916129551 80120222023486702374194327)
          ·
            refine ⟨120180333035230053561291491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80120222023486702374194327 120180333035230053561291491)
            ·
              refine ⟨180270499552845080341937237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120180333035230053561291491 180270499552845080341937237)
              ·
                refine ⟨2112544916634903285257077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 180270499552845080341937237 2112544916634903285257077)
                ·
                  refine ⟨198051085934522182992851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2112544916634903285257077 198051085934522182992851)
                  ·
                    rfl

theorem cell23_3471328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 5].length) (baseStart_3471328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471328 prefixEnd_3471328 := by exact prefixLift 3471328
  have htrace : WordTrace (prefixWord ++ tailWord_3471328) baseStart_3471328 baseEnd_3471328 := by
    simpa [prefixWord, tailWord_3471328, baseEnd_3471328] using wordTrace_append hprefix tailTrace_3471328
  have hstable : (prefixWord ++ tailWord_3471328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471328).length < 2 ^ (prefixWord ++ tailWord_3471328).sum := by decide
  have hdescent : baseEnd_3471328 < baseStart_3471328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471338 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_3471338 : Nat := 118140960795 + 3471338 * 2 ^ 59
def prefixEnd_3471338 : Nat := 4983230072969 + 3 ^ 40 * 3471338 * 2
def baseEnd_3471338 : Nat := 1782464908217244607810613

theorem tailTrace_3471338 : CollatzResearch.WordTrace tailWord_3471338 prefixEnd_3471338 1782464908217244607810613 := by
  unfold tailWord_3471338
  simp only [CollatzResearch.WordTrace]
  refine ⟨31652524574485689543931667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84406732198628505450484445 31652524574485689543931667)
  ·
    refine ⟨47478786861728534315897501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31652524574485689543931667 47478786861728534315897501)
    ·
      refine ⟨17804545073148200368461563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47478786861728534315897501 17804545073148200368461563)
      ·
        refine ⟨26706817609722300552692345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17804545073148200368461563 26706817609722300552692345)
        ·
          refine ⟨20030113207291725414519259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26706817609722300552692345 20030113207291725414519259)
          ·
            refine ⟨30045169810937588121778889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20030113207291725414519259 30045169810937588121778889)
            ·
              refine ⟨22533877358203191091334167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30045169810937588121778889 22533877358203191091334167)
              ·
                refine ⟨33800816037304786637001251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22533877358203191091334167 33800816037304786637001251)
                ·
                  refine ⟨50701224055957179955501877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33800816037304786637001251 50701224055957179955501877)
                  ·
                    refine ⟨4753239755245985620828301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50701224055957179955501877 4753239755245985620828301)
                    ·
                      refine ⟨1782464908217244607810613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4753239755245985620828301 1782464908217244607810613)
                      ·
                        rfl

theorem cell23_3471338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_3471338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471338 prefixEnd_3471338 := by exact prefixLift 3471338
  have htrace : WordTrace (prefixWord ++ tailWord_3471338) baseStart_3471338 baseEnd_3471338 := by
    simpa [prefixWord, tailWord_3471338, baseEnd_3471338] using wordTrace_append hprefix tailTrace_3471338
  have hstable : (prefixWord ++ tailWord_3471338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471338).length < 2 ^ (prefixWord ++ tailWord_3471338).sum := by decide
  have hdescent : baseEnd_3471338 < baseStart_3471338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471395 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 2, 4, 2]
def baseStart_3471395 : Nat := 118140960795 + 3471395 * 2 ^ 59
def prefixEnd_3471395 : Nat := 4983230072969 + 3 ^ 40 * 3471395 * 2
def baseEnd_3471395 : Nat := 1782494176614550884797851

theorem tailTrace_3471395 : CollatzResearch.WordTrace tailWord_3471395 prefixEnd_3471395 1782494176614550884797851 := by
  unfold tailWord_3471395
  simp only [CollatzResearch.WordTrace]
  refine ⟨126612177258736256910551639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84408118172490837940367759 126612177258736256910551639)
  ·
    refine ⟨189918265888104385365827459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126612177258736256910551639 189918265888104385365827459)
    ·
      refine ⟨284877398832156578048741189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189918265888104385365827459 284877398832156578048741189)
      ·
        refine ⟨53414512281029358384138973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284877398832156578048741189 53414512281029358384138973)
        ·
          refine ⟨20030442105386009394052115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53414512281029358384138973 20030442105386009394052115)
          ·
            refine ⟨30045663158079014091078173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20030442105386009394052115 30045663158079014091078173)
            ·
              refine ⟨11267123684279630284154315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30045663158079014091078173 11267123684279630284154315)
              ·
                refine ⟨16900685526419445426231473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11267123684279630284154315 16900685526419445426231473)
                ·
                  refine ⟨12675514144814584069673605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16900685526419445426231473 12675514144814584069673605)
                  ·
                    refine ⟨2376658902152734513063801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12675514144814584069673605 2376658902152734513063801)
                    ·
                      refine ⟨1782494176614550884797851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2376658902152734513063801 1782494176614550884797851)
                      ·
                        rfl

theorem cell23_3471395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_3471395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471395 prefixEnd_3471395 := by exact prefixLift 3471395
  have htrace : WordTrace (prefixWord ++ tailWord_3471395) baseStart_3471395 baseEnd_3471395 := by
    simpa [prefixWord, tailWord_3471395, baseEnd_3471395] using wordTrace_append hprefix tailTrace_3471395
  have hstable : (prefixWord ++ tailWord_3471395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471395).length < 2 ^ (prefixWord ++ tailWord_3471395).sum := by decide
  have hdescent : baseEnd_3471395 < baseStart_3471395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471412 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3471412 : Nat := 118140960795 + 3471412 * 2 ^ 59
def prefixEnd_3471412 : Nat := 4983230072969 + 3 ^ 40 * 3471412 * 2
def baseEnd_3471412 : Nat := 1782502905785677318285273

theorem tailTrace_3471412 : CollatzResearch.WordTrace tailWord_3471412 prefixEnd_3471412 1782502905785677318285273 := by
  unfold tailWord_3471412
  simp only [CollatzResearch.WordTrace]
  refine ⟨63306398649837334406960245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84408531533116445875946993 63306398649837334406960245)
  ·
    refine ⟨5934974873422250100652523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63306398649837334406960245 5934974873422250100652523)
    ·
      refine ⟨8902462310133375150978785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5934974873422250100652523 8902462310133375150978785)
      ·
        refine ⟨6676846732600031363234089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8902462310133375150978785 6676846732600031363234089)
        ·
          refine ⟨5007635049450023522425567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6676846732600031363234089 5007635049450023522425567)
          ·
            refine ⟨7511452574175035283638351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007635049450023522425567 7511452574175035283638351)
            ·
              refine ⟨11267178861262552925457527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511452574175035283638351 11267178861262552925457527)
              ·
                refine ⟨16900768291893829388186291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11267178861262552925457527 16900768291893829388186291)
                ·
                  refine ⟨25351152437840744082279437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16900768291893829388186291 25351152437840744082279437)
                  ·
                    refine ⟨9506682164190279030854789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25351152437840744082279437 9506682164190279030854789)
                    ·
                      refine ⟨1782502905785677318285273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9506682164190279030854789 1782502905785677318285273)
                      ·
                        rfl

theorem cell23_3471412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3471412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471412 prefixEnd_3471412 := by exact prefixLift 3471412
  have htrace : WordTrace (prefixWord ++ tailWord_3471412) baseStart_3471412 baseEnd_3471412 := by
    simpa [prefixWord, tailWord_3471412, baseEnd_3471412] using wordTrace_append hprefix tailTrace_3471412
  have hstable : (prefixWord ++ tailWord_3471412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471412).length < 2 ^ (prefixWord ++ tailWord_3471412).sum := by decide
  have hdescent : baseEnd_3471412 < baseStart_3471412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471415 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_3471415 : Nat := 118140960795 + 3471415 * 2 ^ 59
def prefixEnd_3471415 : Nat := 4983230072969 + 3 ^ 40 * 3471415 * 2
def baseEnd_3471415 : Nat := 1782504446227640806547759

theorem tailTrace_3471415 : CollatzResearch.WordTrace tailWord_3471415 prefixEnd_3471415 1782504446227640806547759 := by
  unfold tailWord_3471415
  simp only [CollatzResearch.WordTrace]
  refine ⟨126612906718663800326279699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84408604479109200217519799 126612906718663800326279699)
  ·
    refine ⟨189919360077995700489419549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126612906718663800326279699 189919360077995700489419549)
    ·
      refine ⟨71219760029248387683532331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189919360077995700489419549 71219760029248387683532331)
      ·
        refine ⟨106829640043872581525298497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71219760029248387683532331 106829640043872581525298497)
        ·
          refine ⟨80122230032904436143973873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106829640043872581525298497 80122230032904436143973873)
          ·
            refine ⟨60091672524678327107980405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80122230032904436143973873 60091672524678327107980405)
            ·
              refine ⟨5633594299188593166373163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60091672524678327107980405 5633594299188593166373163)
              ·
                refine ⟨8450391448782889749559745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633594299188593166373163 8450391448782889749559745)
                ·
                  refine ⟨6337793586587167312169809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8450391448782889749559745 6337793586587167312169809)
                  ·
                    refine ⟨4753345189940375484127357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6337793586587167312169809 4753345189940375484127357)
                    ·
                      refine ⟨1782504446227640806547759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4753345189940375484127357 1782504446227640806547759)
                      ·
                        rfl

theorem cell23_3471415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_3471415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471415 prefixEnd_3471415 := by exact prefixLift 3471415
  have htrace : WordTrace (prefixWord ++ tailWord_3471415) baseStart_3471415 baseEnd_3471415 := by
    simpa [prefixWord, tailWord_3471415, baseEnd_3471415] using wordTrace_append hprefix tailTrace_3471415
  have hstable : (prefixWord ++ tailWord_3471415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471415).length < 2 ^ (prefixWord ++ tailWord_3471415).sum := by decide
  have hdescent : baseEnd_3471415 < baseStart_3471415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471438 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3471438 : Nat := 118140960795 + 3471438 * 2 ^ 59
def prefixEnd_3471438 : Nat := 4983230072969 + 3 ^ 40 * 3471438 * 2
def baseEnd_3471438 : Nat := 1782516256282694216560153

theorem tailTrace_3471438 : CollatzResearch.WordTrace tailWord_3471438 prefixEnd_3471438 1782516256282694216560153 := by
  unfold tailWord_3471438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15826718199697559406795871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84409163731720316836244645 15826718199697559406795871)
  ·
    refine ⟨23740077299546339110193807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15826718199697559406795871 23740077299546339110193807)
    ·
      refine ⟨35610115949319508665290711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23740077299546339110193807 35610115949319508665290711)
      ·
        refine ⟨53415173923979262997936067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35610115949319508665290711 53415173923979262997936067)
        ·
          refine ⟨80122760885968894496904101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53415173923979262997936067 80122760885968894496904101)
          ·
            refine ⟨15023017666119167718169519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80122760885968894496904101 15023017666119167718169519)
            ·
              refine ⟨22534526499178751577254279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15023017666119167718169519 22534526499178751577254279)
              ·
                refine ⟨33801789748768127365881419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22534526499178751577254279 33801789748768127365881419)
                ·
                  refine ⟨50702684623152191048822129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33801789748768127365881419 50702684623152191048822129)
                  ·
                    refine ⟨38027013467364143286616597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50702684623152191048822129 38027013467364143286616597)
                    ·
                      refine ⟨1782516256282694216560153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38027013467364143286616597 1782516256282694216560153)
                      ·
                        rfl

theorem cell23_3471438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3471438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3471438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3471438 prefixEnd_3471438 := by exact prefixLift 3471438
  have htrace : WordTrace (prefixWord ++ tailWord_3471438) baseStart_3471438 baseEnd_3471438 := by
    simpa [prefixWord, tailWord_3471438, baseEnd_3471438] using wordTrace_append hprefix tailTrace_3471438
  have hstable : (prefixWord ++ tailWord_3471438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471438).length < 2 ^ (prefixWord ++ tailWord_3471438).sum := by decide
  have hdescent : baseEnd_3471438 < baseStart_3471438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
