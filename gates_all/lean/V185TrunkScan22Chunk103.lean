import V185TrunkScan22Chunk102

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_925149 : List Nat := [1, 4, 3, 1, 1, 3, 3, 2, 4]
def baseStart_925149 : Nat := 118140960795 + 925149 * 2 ^ 59
def prefixEnd_925149 : Nat := 4983230072969 + 3 ^ 40 * 925149 * 2
def baseEnd_925149 : Nat := 105565803117001351996183

theorem tailTrace_925149 : CollatzResearch.WordTrace tailWord_925149 prefixEnd_925149 105565803117001351996183 := by
  unfold tailWord_925149
  simp only [CollatzResearch.WordTrace]
  refine ⟨33742956125350650715058501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22495304083567100476705667 33742956125350650715058501)
  ·
    refine ⟨6326804273503247009073469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33742956125350650715058501 6326804273503247009073469)
    ·
      refine ⟨2372551602563717628402551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6326804273503247009073469 2372551602563717628402551)
      ·
        refine ⟨3558827403845576442603827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372551602563717628402551 3558827403845576442603827)
        ·
          refine ⟨5338241105768364663905741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3558827403845576442603827 5338241105768364663905741)
          ·
            refine ⟨2001840414663136748964653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5338241105768364663905741 2001840414663136748964653)
            ·
              refine ⟨750690155498676280861745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2001840414663136748964653 750690155498676280861745)
              ·
                refine ⟨563017616624007210646309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750690155498676280861745 563017616624007210646309)
                ·
                  refine ⟨105565803117001351996183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563017616624007210646309 105565803117001351996183)
                  ·
                    rfl

theorem cell22_925149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_925149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925149 prefixEnd_925149 := by exact prefixLift 925149
  have htrace : WordTrace (prefixWord ++ tailWord_925149) baseStart_925149 baseEnd_925149 := by
    simpa [prefixWord, tailWord_925149, baseEnd_925149] using wordTrace_append hprefix tailTrace_925149
  have hstable : (prefixWord ++ tailWord_925149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925149).length < 2 ^ (prefixWord ++ tailWord_925149).sum := by decide
  have hdescent : baseEnd_925149 < baseStart_925149 := by decide
  rcases family_descends (prefixWord ++ tailWord_925149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925205 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 5]
def baseStart_925205 : Nat := 118140960795 + 925205 * 2 ^ 59
def prefixEnd_925205 : Nat := 4983230072969 + 3 ^ 40 * 925205 * 2
def baseEnd_925205 : Nat := 105572193098479525529459

theorem tailTrace_925205 : CollatzResearch.WordTrace tailWord_925205 prefixEnd_925205 105572193098479525529459 := by
  unfold tailWord_925205
  simp only [CollatzResearch.WordTrace]
  refine ⟨33744998613147772279097069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22496665742098514852731379 33744998613147772279097069)
  ·
    refine ⟨12654374479930414604661401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33744998613147772279097069 12654374479930414604661401)
    ·
      refine ⟨9490780859947810953496051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12654374479930414604661401 9490780859947810953496051)
      ·
        refine ⟨14236171289921716430244077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9490780859947810953496051 14236171289921716430244077)
        ·
          refine ⟨5338564233720643661341529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14236171289921716430244077 5338564233720643661341529)
          ·
            refine ⟨4003923175290482746006147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5338564233720643661341529 4003923175290482746006147)
            ·
              refine ⟨6005884762935724119009221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003923175290482746006147 6005884762935724119009221)
              ·
                refine ⟨1126103393050448272314229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6005884762935724119009221 1126103393050448272314229)
                ·
                  refine ⟨105572193098479525529459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1126103393050448272314229 105572193098479525529459)
                  ·
                    rfl

theorem cell22_925205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_925205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925205 prefixEnd_925205 := by exact prefixLift 925205
  have htrace : WordTrace (prefixWord ++ tailWord_925205) baseStart_925205 baseEnd_925205 := by
    simpa [prefixWord, tailWord_925205, baseEnd_925205] using wordTrace_append hprefix tailTrace_925205
  have hstable : (prefixWord ++ tailWord_925205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925205).length < 2 ^ (prefixWord ++ tailWord_925205).sum := by decide
  have hdescent : baseEnd_925205 < baseStart_925205 := by decide
  rcases family_descends (prefixWord ++ tailWord_925205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925235 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 3, 4]
def baseStart_925235 : Nat := 118140960795 + 925235 * 2 ^ 59
def prefixEnd_925235 : Nat := 4983230072969 + 3 ^ 40 * 925235 * 2
def baseEnd_925235 : Nat := 316726848908528498338285

theorem tailTrace_925235 : CollatzResearch.WordTrace tailWord_925235 prefixEnd_925235 316726848908528498338285 := by
  unfold tailWord_925235
  simp only [CollatzResearch.WordTrace]
  refine ⟨33746092803039087402689159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22497395202026058268459439 33746092803039087402689159)
  ·
    refine ⟨50619139204558631104033739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33746092803039087402689159 50619139204558631104033739)
    ·
      refine ⟨75928708806837946656050609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50619139204558631104033739 75928708806837946656050609)
      ·
        refine ⟨56946531605128459992037957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75928708806837946656050609 56946531605128459992037957)
        ·
          refine ⟨10677474675961586248507117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56946531605128459992037957 10677474675961586248507117)
          ·
            refine ⟨4004053003485594843190169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10677474675961586248507117 4004053003485594843190169)
            ·
              refine ⟨3003039752614196132392627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4004053003485594843190169 3003039752614196132392627)
              ·
                refine ⟨4504559628921294198588941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003039752614196132392627 4504559628921294198588941)
                ·
                  refine ⟨1689209860845485324470853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4504559628921294198588941 1689209860845485324470853)
                  ·
                    refine ⟨316726848908528498338285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1689209860845485324470853 316726848908528498338285)
                    ·
                      rfl

theorem cell22_925235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 4].length) (baseStart_925235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925235 prefixEnd_925235 := by exact prefixLift 925235
  have htrace : WordTrace (prefixWord ++ tailWord_925235) baseStart_925235 baseEnd_925235 := by
    simpa [prefixWord, tailWord_925235, baseEnd_925235] using wordTrace_append hprefix tailTrace_925235
  have hstable : (prefixWord ++ tailWord_925235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925235).length < 2 ^ (prefixWord ++ tailWord_925235).sum := by decide
  have hdescent : baseEnd_925235 < baseStart_925235 := by decide
  rcases family_descends (prefixWord ++ tailWord_925235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925301 : List Nat := [1, 3, 4, 2, 1, 3, 1, 3, 4]
def baseStart_925301 : Nat := 118140960795 + 925301 * 2 ^ 59
def prefixEnd_925301 : Nat := 4983230072969 + 3 ^ 40 * 925301 * 2
def baseEnd_925301 : Nat := 105583147352442108729361

theorem tailTrace_925301 : CollatzResearch.WordTrace tailWord_925301 prefixEnd_925301 105583147352442108729361 := by
  unfold tailWord_925301
  simp only [CollatzResearch.WordTrace]
  refine ⟨33748500020799980674591757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22499000013866653783061171 33748500020799980674591757)
  ·
    refine ⟨12655687507799992752971909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33748500020799980674591757 12655687507799992752971909)
    ·
      refine ⟨2372941407712498641182233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12655687507799992752971909 2372941407712498641182233)
      ·
        refine ⟨1779706055784373980886675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2372941407712498641182233 1779706055784373980886675)
        ·
          refine ⟨2669559083676560971330013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779706055784373980886675 2669559083676560971330013)
          ·
            refine ⟨1001084656378710364248755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2669559083676560971330013 1001084656378710364248755)
            ·
              refine ⟨1501626984568065546373133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001084656378710364248755 1501626984568065546373133)
              ·
                refine ⟨563110119213024579889925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1501626984568065546373133 563110119213024579889925)
                ·
                  refine ⟨105583147352442108729361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563110119213024579889925 105583147352442108729361)
                  ·
                    rfl

theorem cell22_925301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_925301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925301 prefixEnd_925301 := by exact prefixLift 925301
  have htrace : WordTrace (prefixWord ++ tailWord_925301) baseStart_925301 baseEnd_925301 := by
    simpa [prefixWord, tailWord_925301, baseEnd_925301] using wordTrace_append hprefix tailTrace_925301
  have hstable : (prefixWord ++ tailWord_925301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925301).length < 2 ^ (prefixWord ++ tailWord_925301).sum := by decide
  have hdescent : baseEnd_925301 < baseStart_925301 := by decide
  rcases family_descends (prefixWord ++ tailWord_925301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925374 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_925374 : Nat := 118140960795 + 925374 * 2 ^ 59
def prefixEnd_925374 : Nat := 4983230072969 + 3 ^ 40 * 925374 * 2
def baseEnd_925374 : Nat := 105591477149726156370953

theorem tailTrace_925374 : CollatzResearch.WordTrace tailWord_925374 prefixEnd_925374 105591477149726156370953 := by
  unfold tailWord_925374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218895318691939267749897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22500775033023676094666117 4218895318691939267749897)
  ·
    refine ⟨3164171489018954450812423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4218895318691939267749897 3164171489018954450812423)
    ·
      refine ⟨4746257233528431676218635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3164171489018954450812423 4746257233528431676218635)
      ·
        refine ⟨7119385850292647514327953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4746257233528431676218635 7119385850292647514327953)
        ·
          refine ⟨5339539387719485635745965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7119385850292647514327953 5339539387719485635745965)
          ·
            refine ⟨2002327270394807113404737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5339539387719485635745965 2002327270394807113404737)
            ·
              refine ⟨1501745452796105335053553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002327270394807113404737 1501745452796105335053553)
              ·
                refine ⟨1126309089597079001290165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501745452796105335053553 1126309089597079001290165)
                ·
                  refine ⟨105591477149726156370953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1126309089597079001290165 105591477149726156370953)
                  ·
                    rfl

theorem cell22_925374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_925374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925374 prefixEnd_925374 := by exact prefixLift 925374
  have htrace : WordTrace (prefixWord ++ tailWord_925374) baseStart_925374 baseEnd_925374 := by
    simpa [prefixWord, tailWord_925374, baseEnd_925374] using wordTrace_append hprefix tailTrace_925374
  have hstable : (prefixWord ++ tailWord_925374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925374).length < 2 ^ (prefixWord ++ tailWord_925374).sum := by decide
  have hdescent : baseEnd_925374 < baseStart_925374 := by decide
  rcases family_descends (prefixWord ++ tailWord_925374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925389 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_925389 : Nat := 118140960795 + 925389 * 2 ^ 59
def prefixEnd_925389 : Nat := 4983230072969 + 3 ^ 40 * 925389 * 2
def baseEnd_925389 : Nat := 316779566255723429987813

theorem tailTrace_925389 : CollatzResearch.WordTrace tailWord_925389 prefixEnd_925389 316779566255723429987813 := by
  unfold tailWord_925389
  simp only [CollatzResearch.WordTrace]
  refine ⟨33751709644481171703795221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22501139762987447802530147 33751709644481171703795221)
  ·
    refine ⟨1582111389585054923615401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33751709644481171703795221 1582111389585054923615401)
    ·
      refine ⟨1186583542188791192711551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1582111389585054923615401 1186583542188791192711551)
      ·
        refine ⟨1779875313283186789067327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186583542188791192711551 1779875313283186789067327)
        ·
          refine ⟨2669812969924780183600991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779875313283186789067327 2669812969924780183600991)
          ·
            refine ⟨4004719454887170275401487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2669812969924780183600991 4004719454887170275401487)
            ·
              refine ⟨6007079182330755413102231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004719454887170275401487 6007079182330755413102231)
              ·
                refine ⟨9010618773496133119653347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007079182330755413102231 9010618773496133119653347)
                ·
                  refine ⟨13515928160244199679480021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9010618773496133119653347 13515928160244199679480021)
                  ·
                    refine ⟨316779566255723429987813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13515928160244199679480021 316779566255723429987813)
                    ·
                      rfl

theorem cell22_925389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_925389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925389 prefixEnd_925389 := by exact prefixLift 925389
  have htrace : WordTrace (prefixWord ++ tailWord_925389) baseStart_925389 baseEnd_925389 := by
    simpa [prefixWord, tailWord_925389, baseEnd_925389] using wordTrace_append hprefix tailTrace_925389
  have hstable : (prefixWord ++ tailWord_925389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925389).length < 2 ^ (prefixWord ++ tailWord_925389).sum := by decide
  have hdescent : baseEnd_925389 < baseStart_925389 := by decide
  rcases family_descends (prefixWord ++ tailWord_925389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925402 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_925402 : Nat := 118140960795 + 925402 * 2 ^ 59
def prefixEnd_925402 : Nat := 4983230072969 + 3 ^ 40 * 925402 * 2
def baseEnd_925402 : Nat := 105594672140465243137591

theorem tailTrace_925402 : CollatzResearch.WordTrace tailWord_925402 prefixEnd_925402 105594672140465243137591 := by
  unfold tailWord_925402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438045948358518731004615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22501455862289383282678973 8438045948358518731004615)
  ·
    refine ⟨12657068922537778096506923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8438045948358518731004615 12657068922537778096506923)
    ·
      refine ⟨18985603383806667144760385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12657068922537778096506923 18985603383806667144760385)
      ·
        refine ⟨14239202537855000358570289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18985603383806667144760385 14239202537855000358570289)
        ·
          refine ⟨10679401903391250268927717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14239202537855000358570289 10679401903391250268927717)
          ·
            refine ⟨2002387856885859425423947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10679401903391250268927717 2002387856885859425423947)
            ·
              refine ⟨3003581785328789138135921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002387856885859425423947 3003581785328789138135921)
              ·
                refine ⟨2252686338996591853601941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3003581785328789138135921 2252686338996591853601941)
                ·
                  refine ⟨105594672140465243137591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2252686338996591853601941 105594672140465243137591)
                  ·
                    rfl

theorem cell22_925402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_925402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925402 prefixEnd_925402 := by exact prefixLift 925402
  have htrace : WordTrace (prefixWord ++ tailWord_925402) baseStart_925402 baseEnd_925402 := by
    simpa [prefixWord, tailWord_925402, baseEnd_925402] using wordTrace_append hprefix tailTrace_925402
  have hstable : (prefixWord ++ tailWord_925402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925402).length < 2 ^ (prefixWord ++ tailWord_925402).sum := by decide
  have hdescent : baseEnd_925402 < baseStart_925402 := by decide
  rcases family_descends (prefixWord ++ tailWord_925402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925417 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 4, 3]
def baseStart_925417 : Nat := 118140960795 + 925417 * 2 ^ 59
def prefixEnd_925417 : Nat := 4983230072969 + 3 ^ 40 * 925417 * 2
def baseEnd_925417 : Nat := 316789151227940690287727

theorem tailTrace_925417 : CollatzResearch.WordTrace tailWord_925417 prefixEnd_925417 316789151227940690287727 := by
  unfold tailWord_925417
  simp only [CollatzResearch.WordTrace]
  refine ⟨33752730888379732485814505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22501820592253154990543003 33752730888379732485814505)
  ·
    refine ⟨25314548166284799364360879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33752730888379732485814505 25314548166284799364360879)
    ·
      refine ⟨37971822249427199046541319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25314548166284799364360879 37971822249427199046541319)
      ·
        refine ⟨56957733374140798569811979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37971822249427199046541319 56957733374140798569811979)
        ·
          refine ⟨85436600061211197854717969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56957733374140798569811979 85436600061211197854717969)
          ·
            refine ⟨64077450045908398391038477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85436600061211197854717969 64077450045908398391038477)
            ·
              refine ⟨24029043767215649396639429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64077450045908398391038477 24029043767215649396639429)
              ·
                refine ⟨4505445706352934261869893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24029043767215649396639429 4505445706352934261869893)
                ·
                  refine ⟨844771069941175174100605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4505445706352934261869893 844771069941175174100605)
                  ·
                    refine ⟨316789151227940690287727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844771069941175174100605 316789151227940690287727)
                    ·
                      rfl

theorem cell22_925417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_925417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925417 prefixEnd_925417 := by exact prefixLift 925417
  have htrace : WordTrace (prefixWord ++ tailWord_925417) baseStart_925417 baseEnd_925417 := by
    simpa [prefixWord, tailWord_925417, baseEnd_925417] using wordTrace_append hprefix tailTrace_925417
  have hstable : (prefixWord ++ tailWord_925417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925417).length < 2 ^ (prefixWord ++ tailWord_925417).sum := by decide
  have hdescent : baseEnd_925417 < baseStart_925417 := by decide
  rcases family_descends (prefixWord ++ tailWord_925417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925421 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_925421 : Nat := 118140960795 + 925421 * 2 ^ 59
def prefixEnd_925421 : Nat := 4983230072969 + 3 ^ 40 * 925421 * 2
def baseEnd_925421 : Nat := 316790520509686013187715

theorem tailTrace_925421 : CollatzResearch.WordTrace tailWord_925421 prefixEnd_925421 316790520509686013187715 := by
  unfold tailWord_925421
  simp only [CollatzResearch.WordTrace]
  refine ⟨33752876780365241168960117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22501917853576827445973411 33752876780365241168960117)
  ·
    refine ⟨3164332198159241359590011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33752876780365241168960117 3164332198159241359590011)
    ·
      refine ⟨4746498297238862039385017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3164332198159241359590011 4746498297238862039385017)
      ·
        refine ⟨3559873722929146529538763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4746498297238862039385017 3559873722929146529538763)
        ·
          refine ⟨5339810584393719794308145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559873722929146529538763 5339810584393719794308145)
          ·
            refine ⟨4004857938295289845731109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5339810584393719794308145 4004857938295289845731109)
            ·
              refine ⟨750910863430366846074583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4004857938295289845731109 750910863430366846074583)
              ·
                refine ⟨1126366295145550269111875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750910863430366846074583 1126366295145550269111875)
                ·
                  refine ⟨1689549442718325403667813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126366295145550269111875 1689549442718325403667813)
                  ·
                    refine ⟨316790520509686013187715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1689549442718325403667813 316790520509686013187715)
                    ·
                      rfl

theorem cell22_925421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_925421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925421 prefixEnd_925421 := by exact prefixLift 925421
  have htrace : WordTrace (prefixWord ++ tailWord_925421) baseStart_925421 baseEnd_925421 := by
    simpa [prefixWord, tailWord_925421, baseEnd_925421] using wordTrace_append hprefix tailTrace_925421
  have hstable : (prefixWord ++ tailWord_925421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925421).length < 2 ^ (prefixWord ++ tailWord_925421).sum := by decide
  have hdescent : baseEnd_925421 < baseStart_925421 := by decide
  rcases family_descends (prefixWord ++ tailWord_925421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925496 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 3, 3]
def baseStart_925496 : Nat := 118140960795 + 925496 * 2 ^ 59
def prefixEnd_925496 : Nat := 4983230072969 + 3 ^ 40 * 925496 * 2
def baseEnd_925496 : Nat := 316816194542410817562485

theorem tailTrace_925496 : CollatzResearch.WordTrace tailWord_925496 prefixEnd_925496 316816194542410817562485 := by
  unfold tailWord_925496
  simp only [CollatzResearch.WordTrace]
  refine ⟨16877806127546764488970171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22503741503395685985293561 16877806127546764488970171)
  ·
    refine ⟨25316709191320146733455257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16877806127546764488970171 25316709191320146733455257)
    ·
      refine ⟨18987531893490110050091443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25316709191320146733455257 18987531893490110050091443)
      ·
        refine ⟨28481297840235165075137165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18987531893490110050091443 28481297840235165075137165)
        ·
          refine ⟨10680486690088186903176437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28481297840235165075137165 10680486690088186903176437)
          ·
            refine ⟨1001295627195767522172791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10680486690088186903176437 1001295627195767522172791)
            ·
              refine ⟨1501943440793651283259187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001295627195767522172791 1501943440793651283259187)
              ·
                refine ⟨2252915161190476924888781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501943440793651283259187 2252915161190476924888781)
                ·
                  refine ⟨844843185446428846833293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2252915161190476924888781 844843185446428846833293)
                  ·
                    refine ⟨316816194542410817562485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844843185446428846833293 316816194542410817562485)
                    ·
                      rfl

theorem cell22_925496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_925496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925496 prefixEnd_925496 := by exact prefixLift 925496
  have htrace : WordTrace (prefixWord ++ tailWord_925496) baseStart_925496 baseEnd_925496 := by
    simpa [prefixWord, tailWord_925496, baseEnd_925496] using wordTrace_append hprefix tailTrace_925496
  have hstable : (prefixWord ++ tailWord_925496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925496).length < 2 ^ (prefixWord ++ tailWord_925496).sum := by decide
  have hdescent : baseEnd_925496 < baseStart_925496 := by decide
  rcases family_descends (prefixWord ++ tailWord_925496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925552 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_925552 : Nat := 118140960795 + 925552 * 2 ^ 59
def prefixEnd_925552 : Nat := 4983230072969 + 3 ^ 40 * 925552 * 2
def baseEnd_925552 : Nat := 316835364486845338162313

theorem tailTrace_925552 : CollatzResearch.WordTrace tailWord_925552 prefixEnd_925552 316835364486845338162313 := by
  unfold tailWord_925552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16878827371445325270989455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22505103161927100361319273 16878827371445325270989455)
  ·
    refine ⟨25318241057167987906484183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16878827371445325270989455 25318241057167987906484183)
    ·
      refine ⟨37977361585751981859726275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25318241057167987906484183 37977361585751981859726275)
      ·
        refine ⟨56966042378627972789589413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37977361585751981859726275 56966042378627972789589413)
        ·
          refine ⟨10681132945992744898048015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56966042378627972789589413 10681132945992744898048015)
          ·
            refine ⟨16021699418989117347072023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10681132945992744898048015 16021699418989117347072023)
            ·
              refine ⟨24032549128483676020608035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16021699418989117347072023 24032549128483676020608035)
              ·
                refine ⟨36048823692725514030912053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24032549128483676020608035 36048823692725514030912053)
                ·
                  refine ⟨3379577221193016940398005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36048823692725514030912053 3379577221193016940398005)
                  ·
                    refine ⟨316835364486845338162313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3379577221193016940398005 316835364486845338162313)
                    ·
                      rfl

theorem cell22_925552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_925552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925552 prefixEnd_925552 := by exact prefixLift 925552
  have htrace : WordTrace (prefixWord ++ tailWord_925552) baseStart_925552 baseEnd_925552 := by
    simpa [prefixWord, tailWord_925552, baseEnd_925552] using wordTrace_append hprefix tailTrace_925552
  have hstable : (prefixWord ++ tailWord_925552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925552).length < 2 ^ (prefixWord ++ tailWord_925552).sum := by decide
  have hdescent : baseEnd_925552 < baseStart_925552 := by decide
  rcases family_descends (prefixWord ++ tailWord_925552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925567 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 1, 6]
def baseStart_925567 : Nat := 118140960795 + 925567 * 2 ^ 59
def prefixEnd_925567 : Nat := 4983230072969 + 3 ^ 40 * 925567 * 2
def baseEnd_925567 : Nat := 316840499293390299037267

theorem tailTrace_925567 : CollatzResearch.WordTrace tailWord_925567 prefixEnd_925567 316840499293390299037267 := by
  unfold tailWord_925567
  simp only [CollatzResearch.WordTrace]
  refine ⟨33758201837836308103774955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22505467891890872069183303 33758201837836308103774955)
  ·
    refine ⟨50637302756754462155662433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33758201837836308103774955 50637302756754462155662433)
    ·
      refine ⟨37977977067565846616746825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50637302756754462155662433 37977977067565846616746825)
      ·
        refine ⟨28483482800674384962560119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37977977067565846616746825 28483482800674384962560119)
        ·
          refine ⟨42725224201011577443840179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28483482800674384962560119 42725224201011577443840179)
          ·
            refine ⟨64087836301517366165760269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42725224201011577443840179 64087836301517366165760269)
            ·
              refine ⟨24032938613069012312160101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64087836301517366165760269 24032938613069012312160101)
              ·
                refine ⟨4506175989950439808530019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24032938613069012312160101 4506175989950439808530019)
                ·
                  refine ⟨6759263984925659712795029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506175989950439808530019 6759263984925659712795029)
                  ·
                    refine ⟨316840499293390299037267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6759263984925659712795029 316840499293390299037267)
                    ·
                      rfl

theorem cell22_925567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_925567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925567 prefixEnd_925567 := by exact prefixLift 925567
  have htrace : WordTrace (prefixWord ++ tailWord_925567) baseStart_925567 baseEnd_925567 := by
    simpa [prefixWord, tailWord_925567, baseEnd_925567] using wordTrace_append hprefix tailTrace_925567
  have hstable : (prefixWord ++ tailWord_925567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925567).length < 2 ^ (prefixWord ++ tailWord_925567).sum := by decide
  have hdescent : baseEnd_925567 < baseStart_925567 := by decide
  rcases family_descends (prefixWord ++ tailWord_925567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925586 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_925586 : Nat := 118140960795 + 925586 * 2 ^ 59
def prefixEnd_925586 : Nat := 4983230072969 + 3 ^ 40 * 925586 * 2
def baseEnd_925586 : Nat := 316847003381680582812209

theorem tailTrace_925586 : CollatzResearch.WordTrace tailWord_925586 prefixEnd_925586 316847003381680582812209 := by
  unfold tailWord_925586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8439723706191868587179153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22505929883178316232477741 8439723706191868587179153)
  ·
    refine ⟨6329792779643901440384365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8439723706191868587179153 6329792779643901440384365)
    ·
      refine ⟨2373672292366463040144137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6329792779643901440384365 2373672292366463040144137)
      ·
        refine ⟨1780254219274847280108103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373672292366463040144137 1780254219274847280108103)
        ·
          refine ⟨2670381328912270920162155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780254219274847280108103 2670381328912270920162155)
          ·
            refine ⟨4005571993368406380243233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670381328912270920162155 4005571993368406380243233)
            ·
              refine ⟨3004178995026304785182425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005571993368406380243233 3004178995026304785182425)
              ·
                refine ⟨2253134246269728588886819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3004178995026304785182425 2253134246269728588886819)
                ·
                  refine ⟨3379701369404592883330229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253134246269728588886819 3379701369404592883330229)
                  ·
                    refine ⟨316847003381680582812209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3379701369404592883330229 316847003381680582812209)
                    ·
                      rfl

theorem cell22_925586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_925586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925586 prefixEnd_925586 := by exact prefixLift 925586
  have htrace : WordTrace (prefixWord ++ tailWord_925586) baseStart_925586 baseEnd_925586 := by
    simpa [prefixWord, tailWord_925586, baseEnd_925586] using wordTrace_append hprefix tailTrace_925586
  have hstable : (prefixWord ++ tailWord_925586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925586).length < 2 ^ (prefixWord ++ tailWord_925586).sum := by decide
  have hdescent : baseEnd_925586 < baseStart_925586 := by decide
  rcases family_descends (prefixWord ++ tailWord_925586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925588 : List Nat := [2, 4, 2, 1, 1, 3, 2, 3, 4]
def baseStart_925588 : Nat := 118140960795 + 925588 * 2 ^ 59
def prefixEnd_925588 : Nat := 4983230072969 + 3 ^ 40 * 925588 * 2
def baseEnd_925588 : Nat := 105615896007517748087401

theorem tailTrace_925588 : CollatzResearch.WordTrace tailWord_925588 prefixEnd_925588 105615896007517748087401 := by
  unfold tailWord_925588
  simp only [CollatzResearch.WordTrace]
  refine ⟨16879483885380114345144709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22505978513840152460192945 16879483885380114345144709)
  ·
    refine ⟨3164903228508771439714633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16879483885380114345144709 3164903228508771439714633)
    ·
      refine ⟨2373677421381578579785975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3164903228508771439714633 2373677421381578579785975)
      ·
        refine ⟨3560516132072367869678963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373677421381578579785975 3560516132072367869678963)
        ·
          refine ⟨5340774198108551804518445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560516132072367869678963 5340774198108551804518445)
          ·
            refine ⟨2002790324290706926694417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5340774198108551804518445 2002790324290706926694417)
            ·
              refine ⟨1502092743218030195020813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002790324290706926694417 1502092743218030195020813)
              ·
                refine ⟨563284778706761323132805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1502092743218030195020813 563284778706761323132805)
                ·
                  refine ⟨105615896007517748087401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563284778706761323132805 105615896007517748087401)
                  ·
                    rfl

theorem cell22_925588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_925588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925588 prefixEnd_925588 := by exact prefixLift 925588
  have htrace : WordTrace (prefixWord ++ tailWord_925588) baseStart_925588 baseEnd_925588 := by
    simpa [prefixWord, tailWord_925588, baseEnd_925588] using wordTrace_append hprefix tailTrace_925588
  have hstable : (prefixWord ++ tailWord_925588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925588).length < 2 ^ (prefixWord ++ tailWord_925588).sum := by decide
  have hdescent : baseEnd_925588 < baseStart_925588 := by decide
  rcases family_descends (prefixWord ++ tailWord_925588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925599 : List Nat := [1, 1, 2, 5, 3, 1, 9]
def baseStart_925599 : Nat := 118140960795 + 925599 * 2 ^ 59
def prefixEnd_925599 : Nat := 4983230072969 + 3 ^ 40 * 925599 * 2
def baseEnd_925599 : Nat := 11735239020272328971747

theorem tailTrace_925599 : CollatzResearch.WordTrace tailWord_925599 prefixEnd_925599 11735239020272328971747 := by
  unfold tailWord_925599
  simp only [CollatzResearch.WordTrace]
  refine ⟨33759368973720377568939851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22506245982480251712626567 33759368973720377568939851)
  ·
    refine ⟨50639053460580566353409777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33759368973720377568939851 50639053460580566353409777)
    ·
      refine ⟨37979290095435424765057333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50639053460580566353409777 37979290095435424765057333)
      ·
        refine ⟨3560558446447071071724125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37979290095435424765057333 3560558446447071071724125)
        ·
          refine ⟨1335209417417651651896547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3560558446447071071724125 1335209417417651651896547)
          ·
            refine ⟨2002814126126477477844821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335209417417651651896547 2002814126126477477844821)
            ·
              refine ⟨11735239020272328971747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2002814126126477477844821 11735239020272328971747)
              ·
                rfl

theorem cell22_925599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 9].length) (baseStart_925599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925599 prefixEnd_925599 := by exact prefixLift 925599
  have htrace : WordTrace (prefixWord ++ tailWord_925599) baseStart_925599 baseEnd_925599 := by
    simpa [prefixWord, tailWord_925599, baseEnd_925599] using wordTrace_append hprefix tailTrace_925599
  have hstable : (prefixWord ++ tailWord_925599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925599).length < 2 ^ (prefixWord ++ tailWord_925599).sum := by decide
  have hdescent : baseEnd_925599 < baseStart_925599 := by decide
  rcases family_descends (prefixWord ++ tailWord_925599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925620 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_925620 : Nat := 118140960795 + 925620 * 2 ^ 59
def prefixEnd_925620 : Nat := 4983230072969 + 3 ^ 40 * 925620 * 2
def baseEnd_925620 : Nat := 316858642276515827462105

theorem tailTrace_925620 : CollatzResearch.WordTrace tailWord_925620 prefixEnd_925620 316858642276515827462105 := by
  unfold tailWord_925620
  simp only [CollatzResearch.WordTrace]
  refine ⟨16880067453322149077727157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22506756604429532103636209 16880067453322149077727157)
  ·
    refine ⟨1582506323748951476036921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16880067453322149077727157 1582506323748951476036921)
    ·
      refine ⟨1186879742811713607027691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1582506323748951476036921 1186879742811713607027691)
      ·
        refine ⟨1780319614217570410541537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186879742811713607027691 1780319614217570410541537)
        ·
          refine ⟨1335239710663177807906153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780319614217570410541537 1335239710663177807906153)
          ·
            refine ⟨1001429782997383355929615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335239710663177807906153 1001429782997383355929615)
            ·
              refine ⟨1502144674496075033894423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001429782997383355929615 1502144674496075033894423)
              ·
                refine ⟨2253217011744112550841635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502144674496075033894423 2253217011744112550841635)
                ·
                  refine ⟨3379825517616168826262453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253217011744112550841635 3379825517616168826262453)
                  ·
                    refine ⟨316858642276515827462105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3379825517616168826262453 316858642276515827462105)
                    ·
                      rfl

theorem cell22_925620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_925620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925620 prefixEnd_925620 := by exact prefixLift 925620
  have htrace : WordTrace (prefixWord ++ tailWord_925620) baseStart_925620 baseEnd_925620 := by
    simpa [prefixWord, tailWord_925620, baseEnd_925620] using wordTrace_append hprefix tailTrace_925620
  have hstable : (prefixWord ++ tailWord_925620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925620).length < 2 ^ (prefixWord ++ tailWord_925620).sum := by decide
  have hdescent : baseEnd_925620 < baseStart_925620 := by decide
  rcases family_descends (prefixWord ++ tailWord_925620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925627 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 9]
def baseStart_925627 : Nat := 118140960795 + 925627 * 2 ^ 59
def prefixEnd_925627 : Nat := 4983230072969 + 3 ^ 40 * 925627 * 2
def baseEnd_925627 : Nat := 105620346173190047512361

theorem tailTrace_925627 : CollatzResearch.WordTrace tailWord_925627 prefixEnd_925627 105620346173190047512361 := by
  unfold tailWord_925627
  simp only [CollatzResearch.WordTrace]
  refine ⟨33760390217618938350959135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22506926811745958900639423 33760390217618938350959135)
  ·
    refine ⟨50640585326428407526438703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33760390217618938350959135 50640585326428407526438703)
    ·
      refine ⟨75960877989642611289658055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50640585326428407526438703 75960877989642611289658055)
      ·
        refine ⟨113941316984463916934487083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75960877989642611289658055 113941316984463916934487083)
        ·
          refine ⟨170911975476695875401730625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113941316984463916934487083 170911975476695875401730625)
          ·
            refine ⟨128183981607521906551297969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170911975476695875401730625 128183981607521906551297969)
            ·
              refine ⟨96137986205641429913473477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128183981607521906551297969 96137986205641429913473477)
              ·
                refine ⟨18025872413557768108776277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96137986205641429913473477 18025872413557768108776277)
                ·
                  refine ⟨105620346173190047512361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18025872413557768108776277 105620346173190047512361)
                  ·
                    rfl

theorem cell22_925627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 9].length) (baseStart_925627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925627 prefixEnd_925627 := by exact prefixLift 925627
  have htrace : WordTrace (prefixWord ++ tailWord_925627) baseStart_925627 baseEnd_925627 := by
    simpa [prefixWord, tailWord_925627, baseEnd_925627] using wordTrace_append hprefix tailTrace_925627
  have hstable : (prefixWord ++ tailWord_925627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925627).length < 2 ^ (prefixWord ++ tailWord_925627).sum := by decide
  have hdescent : baseEnd_925627 < baseStart_925627 := by decide
  rcases family_descends (prefixWord ++ tailWord_925627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925644 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 7]
def baseStart_925644 : Nat := 118140960795 + 925644 * 2 ^ 59
def prefixEnd_925644 : Nat := 4983230072969 + 3 ^ 40 * 925644 * 2
def baseEnd_925644 : Nat := 105622285988995921620677

theorem tailTrace_925644 : CollatzResearch.WordTrace tailWord_925644 prefixEnd_925644 105622285988995921620677 := by
  unfold tailWord_925644
  simp only [CollatzResearch.WordTrace]
  refine ⟨16880505129278675127163993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22507340172371566836218657 16880505129278675127163993)
  ·
    refine ⟨12660378846959006345372995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16880505129278675127163993 12660378846959006345372995)
    ·
      refine ⟨18990568270438509518059493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12660378846959006345372995 18990568270438509518059493)
      ·
        refine ⟨3560731550707220534636155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18990568270438509518059493 3560731550707220534636155)
        ·
          refine ⟨5341097326060830801954233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560731550707220534636155 5341097326060830801954233)
          ·
            refine ⟨4005822994545623101465675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5341097326060830801954233 4005822994545623101465675)
            ·
              refine ⟨6008734491818434652198513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005822994545623101465675 6008734491818434652198513)
              ·
                refine ⟨4506550868863825989148885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6008734491818434652198513 4506550868863825989148885)
                ·
                  refine ⟨105622285988995921620677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4506550868863825989148885 105622285988995921620677)
                  ·
                    rfl

theorem cell22_925644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_925644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925644 prefixEnd_925644 := by exact prefixLift 925644
  have htrace : WordTrace (prefixWord ++ tailWord_925644) baseStart_925644 baseEnd_925644 := by
    simpa [prefixWord, tailWord_925644, baseEnd_925644] using wordTrace_append hprefix tailTrace_925644
  have hstable : (prefixWord ++ tailWord_925644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925644).length < 2 ^ (prefixWord ++ tailWord_925644).sum := by decide
  have hdescent : baseEnd_925644 < baseStart_925644 := by decide
  rcases family_descends (prefixWord ++ tailWord_925644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925648 : List Nat := [2, 1, 1, 1, 1, 2, 7, 3, 1, 3]
def baseStart_925648 : Nat := 118140960795 + 925648 * 2 ^ 59
def prefixEnd_925648 : Nat := 4983230072969 + 3 ^ 40 * 925648 * 2
def baseEnd_925648 : Nat := 316868227248733087762019

theorem tailTrace_925648 : CollatzResearch.WordTrace tailWord_925648 prefixEnd_925648 316868227248733087762019 := by
  unfold tailWord_925648
  simp only [CollatzResearch.WordTrace]
  refine ⟨16880578075271429468736799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22507437433695239291649065 16880578075271429468736799)
  ·
    refine ⟨25320867112907144203105199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16880578075271429468736799 25320867112907144203105199)
    ·
      refine ⟨37981300669360716304657799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25320867112907144203105199 37981300669360716304657799)
      ·
        refine ⟨56971951004041074456986699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37981300669360716304657799 56971951004041074456986699)
        ·
          refine ⟨85457926506061611685480049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56971951004041074456986699 85457926506061611685480049)
          ·
            refine ⟨64093444879546208764110037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85457926506061611685480049 64093444879546208764110037)
            ·
              refine ⟨1502190114364364267908829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64093444879546208764110037 1502190114364364267908829)
              ·
                refine ⟨563321292886636600465811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1502190114364364267908829 563321292886636600465811)
                ·
                  refine ⟨844981939329954900698717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563321292886636600465811 844981939329954900698717)
                  ·
                    refine ⟨316868227248733087762019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844981939329954900698717 316868227248733087762019)
                    ·
                      rfl

theorem cell22_925648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 3].length) (baseStart_925648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925648 prefixEnd_925648 := by exact prefixLift 925648
  have htrace : WordTrace (prefixWord ++ tailWord_925648) baseStart_925648 baseEnd_925648 := by
    simpa [prefixWord, tailWord_925648, baseEnd_925648] using wordTrace_append hprefix tailTrace_925648
  have hstable : (prefixWord ++ tailWord_925648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925648).length < 2 ^ (prefixWord ++ tailWord_925648).sum := by decide
  have hdescent : baseEnd_925648 < baseStart_925648 := by decide
  rcases family_descends (prefixWord ++ tailWord_925648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925678 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_925678 : Nat := 118140960795 + 925678 * 2 ^ 59
def prefixEnd_925678 : Nat := 4983230072969 + 3 ^ 40 * 925678 * 2
def baseEnd_925678 : Nat := 105626165620607669837309

theorem tailTrace_925678 : CollatzResearch.WordTrace tailWord_925678 prefixEnd_925678 105626165620607669837309 := by
  unfold tailWord_925678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220281292554271757633211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22508166893622782707377125 4220281292554271757633211)
  ·
    refine ⟨6330421938831407636449817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4220281292554271757633211 6330421938831407636449817)
    ·
      refine ⟨4747816454123555727337363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6330421938831407636449817 4747816454123555727337363)
      ·
        refine ⟨7121724681185333591006045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747816454123555727337363 7121724681185333591006045)
        ·
          refine ⟨2670646755444500096627267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7121724681185333591006045 2670646755444500096627267)
          ·
            refine ⟨4005970133166750144940901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670646755444500096627267 4005970133166750144940901)
            ·
              refine ⟨751119399968765652176419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4005970133166750144940901 751119399968765652176419)
              ·
                refine ⟨1126679099953148478264629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751119399968765652176419 1126679099953148478264629)
                ·
                  refine ⟨105626165620607669837309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1126679099953148478264629 105626165620607669837309)
                  ·
                    rfl

theorem cell22_925678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_925678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925678 prefixEnd_925678 := by exact prefixLift 925678
  have htrace : WordTrace (prefixWord ++ tailWord_925678) baseStart_925678 baseEnd_925678 := by
    simpa [prefixWord, tailWord_925678, baseEnd_925678] using wordTrace_append hprefix tailTrace_925678
  have hstable : (prefixWord ++ tailWord_925678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925678).length < 2 ^ (prefixWord ++ tailWord_925678).sum := by decide
  have hdescent : baseEnd_925678 < baseStart_925678 := by decide
  rcases family_descends (prefixWord ++ tailWord_925678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925691 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 1, 4]
def baseStart_925691 : Nat := 118140960795 + 925691 * 2 ^ 59
def prefixEnd_925691 : Nat := 4983230072969 + 3 ^ 40 * 925691 * 2
def baseEnd_925691 : Nat := 316882947027495308936887

theorem tailTrace_925691 : CollatzResearch.WordTrace tailWord_925691 prefixEnd_925691 316882947027495308936887 := by
  unfold tailWord_925691
  simp only [CollatzResearch.WordTrace]
  refine ⟨33762724489387077281288927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22508482992924718187525951 33762724489387077281288927)
  ·
    refine ⟨50644086734080615921933391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33762724489387077281288927 50644086734080615921933391)
    ·
      refine ⟨75966130101120923882900087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50644086734080615921933391 75966130101120923882900087)
      ·
        refine ⟨113949195151681385824350131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75966130101120923882900087 113949195151681385824350131)
        ·
          refine ⟨170923792727522078736525197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113949195151681385824350131 170923792727522078736525197)
          ·
            refine ⟨64096422272820779526196949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170923792727522078736525197 64096422272820779526196949)
            ·
              refine ⟨1502259897019237020145241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64096422272820779526196949 1502259897019237020145241)
              ·
                refine ⟨1126694922764427765108931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502259897019237020145241 1126694922764427765108931)
                ·
                  refine ⟨1690042384146641647663397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126694922764427765108931 1690042384146641647663397)
                  ·
                    refine ⟨316882947027495308936887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1690042384146641647663397 316882947027495308936887)
                    ·
                      rfl

theorem cell22_925691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 4].length) (baseStart_925691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925691 prefixEnd_925691 := by exact prefixLift 925691
  have htrace : WordTrace (prefixWord ++ tailWord_925691) baseStart_925691 baseEnd_925691 := by
    simpa [prefixWord, tailWord_925691, baseEnd_925691] using wordTrace_append hprefix tailTrace_925691
  have hstable : (prefixWord ++ tailWord_925691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925691).length < 2 ^ (prefixWord ++ tailWord_925691).sum := by decide
  have hdescent : baseEnd_925691 < baseStart_925691 := by decide
  rcases family_descends (prefixWord ++ tailWord_925691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925708 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 1, 4]
def baseStart_925708 : Nat := 118140960795 + 925708 * 2 ^ 59
def prefixEnd_925708 : Nat := 4983230072969 + 3 ^ 40 * 925708 * 2
def baseEnd_925708 : Nat := 316888766474912931261835

theorem tailTrace_925708 : CollatzResearch.WordTrace tailWord_925708 prefixEnd_925708 316888766474912931261835 := by
  unfold tailWord_925708
  simp only [CollatzResearch.WordTrace]
  refine ⟨16881672265162744592328889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22508896353550326123105185 16881672265162744592328889)
  ·
    refine ⟨12661254198872058444246667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16881672265162744592328889 12661254198872058444246667)
    ·
      refine ⟨18991881298308087666370001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12661254198872058444246667 18991881298308087666370001)
      ·
        refine ⟨14243910973731065749777501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18991881298308087666370001 14243910973731065749777501)
        ·
          refine ⟨5341466615149149656166563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14243910973731065749777501 5341466615149149656166563)
          ·
            refine ⟨8012199922723724484249845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5341466615149149656166563 8012199922723724484249845)
            ·
              refine ⟨751143742755349170398423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8012199922723724484249845 751143742755349170398423)
              ·
                refine ⟨1126715614133023755597635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751143742755349170398423 1126715614133023755597635)
                ·
                  refine ⟨1690073421199535633396453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126715614133023755597635 1690073421199535633396453)
                  ·
                    refine ⟨316888766474912931261835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1690073421199535633396453 316888766474912931261835)
                    ·
                      rfl

theorem cell22_925708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_925708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925708 prefixEnd_925708 := by exact prefixLift 925708
  have htrace : WordTrace (prefixWord ++ tailWord_925708) baseStart_925708 baseEnd_925708 := by
    simpa [prefixWord, tailWord_925708, baseEnd_925708] using wordTrace_append hprefix tailTrace_925708
  have hstable : (prefixWord ++ tailWord_925708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925708).length < 2 ^ (prefixWord ++ tailWord_925708).sum := by decide
  have hdescent : baseEnd_925708 < baseStart_925708 := by decide
  rcases family_descends (prefixWord ++ tailWord_925708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925716 : List Nat := [2, 4, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_925716 : Nat := 118140960795 + 925716 * 2 ^ 59
def prefixEnd_925716 : Nat := 4983230072969 + 3 ^ 40 * 925716 * 2
def baseEnd_925716 : Nat := 316891505038403577061811

theorem tailTrace_925716 : CollatzResearch.WordTrace tailWord_925716 prefixEnd_925716 316891505038403577061811 := by
  unfold tailWord_925716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16881818157148253275474501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22509090876197671033966001 16881818157148253275474501)
  ·
    refine ⟨3165340904465297489151469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16881818157148253275474501 3165340904465297489151469)
    ·
      refine ⟨1187002839174486558431801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3165340904465297489151469 1187002839174486558431801)
      ·
        refine ⟨890252129380864918823851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1187002839174486558431801 890252129380864918823851)
        ·
          refine ⟨1335378194071297378235777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890252129380864918823851 1335378194071297378235777)
          ·
            refine ⟨1001533645553473033676833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335378194071297378235777 1001533645553473033676833)
            ·
              refine ⟨751150234165104775257625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001533645553473033676833 751150234165104775257625)
              ·
                refine ⟨563362675623828581443219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751150234165104775257625 563362675623828581443219)
                ·
                  refine ⟨845044013435742872164829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563362675623828581443219 845044013435742872164829)
                  ·
                    refine ⟨316891505038403577061811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 845044013435742872164829 316891505038403577061811)
                    ·
                      rfl

theorem cell22_925716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_925716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925716 prefixEnd_925716 := by exact prefixLift 925716
  have htrace : WordTrace (prefixWord ++ tailWord_925716) baseStart_925716 baseEnd_925716 := by
    simpa [prefixWord, tailWord_925716, baseEnd_925716] using wordTrace_append hprefix tailTrace_925716
  have hstable : (prefixWord ++ tailWord_925716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925716).length < 2 ^ (prefixWord ++ tailWord_925716).sum := by decide
  have hdescent : baseEnd_925716 < baseStart_925716 := by decide
  rcases family_descends (prefixWord ++ tailWord_925716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925738 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_925738 : Nat := 118140960795 + 925738 * 2 ^ 59
def prefixEnd_925738 : Nat := 4983230072969 + 3 ^ 40 * 925738 * 2
def baseEnd_925738 : Nat := 316899036088002853011743

theorem tailTrace_925738 : CollatzResearch.WordTrace tailWord_925738 prefixEnd_925738 316899036088002853011743 := by
  unfold tailWord_925738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8441109680054201077062467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22509625813477869538833245 8441109680054201077062467)
  ·
    refine ⟨12661664520081301615593701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8441109680054201077062467 12661664520081301615593701)
    ·
      refine ⟨2374062097515244052923819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12661664520081301615593701 2374062097515244052923819)
      ·
        refine ⟨3561093146272866079385729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374062097515244052923819 3561093146272866079385729)
        ·
          refine ⟨2670819859704649559539297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3561093146272866079385729 2670819859704649559539297)
          ·
            refine ⟨2003114894778487169654473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2670819859704649559539297 2003114894778487169654473)
            ·
              refine ⟨1502336171083865377240855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003114894778487169654473 1502336171083865377240855)
              ·
                refine ⟨2253504256625798065861283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502336171083865377240855 2253504256625798065861283)
                ·
                  refine ⟨3380256384938697098791925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253504256625798065861283 3380256384938697098791925)
                  ·
                    refine ⟨316899036088002853011743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3380256384938697098791925 316899036088002853011743)
                    ·
                      rfl

theorem cell22_925738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_925738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925738 prefixEnd_925738 := by exact prefixLift 925738
  have htrace : WordTrace (prefixWord ++ tailWord_925738) baseStart_925738 baseEnd_925738 := by
    simpa [prefixWord, tailWord_925738, baseEnd_925738] using wordTrace_append hprefix tailTrace_925738
  have hstable : (prefixWord ++ tailWord_925738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925738).length < 2 ^ (prefixWord ++ tailWord_925738).sum := by decide
  have hdescent : baseEnd_925738 < baseStart_925738 := by decide
  rcases family_descends (prefixWord ++ tailWord_925738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925796 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 5]
def baseStart_925796 : Nat := 118140960795 + 925796 * 2 ^ 59
def prefixEnd_925796 : Nat := 4983230072969 + 3 ^ 40 * 925796 * 2
def baseEnd_925796 : Nat := 105639630224436678353855

theorem tailTrace_925796 : CollatzResearch.WordTrace tailWord_925796 prefixEnd_925796 105639630224436678353855 := by
  unfold tailWord_925796
  simp only [CollatzResearch.WordTrace]
  refine ⟨16883277077003340106930621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22511036102671120142574161 16883277077003340106930621)
  ·
    refine ⟨6331228903876252540098983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16883277077003340106930621 6331228903876252540098983)
    ·
      refine ⟨9496843355814378810148475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6331228903876252540098983 9496843355814378810148475)
      ·
        refine ⟨14245265033721568215222713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496843355814378810148475 14245265033721568215222713)
        ·
          refine ⟨10683948775291176161417035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14245265033721568215222713 10683948775291176161417035)
          ·
            refine ⟨16025923162936764242125553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10683948775291176161417035 16025923162936764242125553)
            ·
              refine ⟨12019442372202573181594165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16025923162936764242125553 12019442372202573181594165)
              ·
                refine ⟨1126822722393991235774453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12019442372202573181594165 1126822722393991235774453)
                ·
                  refine ⟨105639630224436678353855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1126822722393991235774453 105639630224436678353855)
                  ·
                    rfl

theorem cell22_925796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_925796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925796 prefixEnd_925796 := by exact prefixLift 925796
  have htrace : WordTrace (prefixWord ++ tailWord_925796) baseStart_925796 baseEnd_925796 := by
    simpa [prefixWord, tailWord_925796, baseEnd_925796] using wordTrace_append hprefix tailTrace_925796
  have hstable : (prefixWord ++ tailWord_925796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925796).length < 2 ^ (prefixWord ++ tailWord_925796).sum := by decide
  have hdescent : baseEnd_925796 < baseStart_925796 := by decide
  rcases family_descends (prefixWord ++ tailWord_925796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925817 : List Nat := [1, 2, 1, 3, 4, 3, 1, 3, 1, 3]
def baseStart_925817 : Nat := 118140960795 + 925817 * 2 ^ 59
def prefixEnd_925817 : Nat := 4983230072969 + 3 ^ 40 * 925817 * 2
def baseEnd_925817 : Nat := 316926079402472980286501

theorem tailTrace_925817 : CollatzResearch.WordTrace tailWord_925817 prefixEnd_925817 316926079402472980286501 := by
  unfold tailWord_925817
  simp only [CollatzResearch.WordTrace]
  refine ⟨33767320086930600800375705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22511546724620400533583803 33767320086930600800375705)
  ·
    refine ⟨25325490065197950600281779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33767320086930600800375705 25325490065197950600281779)
    ·
      refine ⟨37988235097796925900422669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25325490065197950600281779 37988235097796925900422669)
      ·
        refine ⟨14245588161673847212658501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37988235097796925900422669 14245588161673847212658501)
        ·
          refine ⟨2671047780313846352373469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14245588161673847212658501 2671047780313846352373469)
          ·
            refine ⟨1001642917617692382140051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2671047780313846352373469 1001642917617692382140051)
            ·
              refine ⟨1502464376426538573210077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001642917617692382140051 1502464376426538573210077)
              ·
                refine ⟨563424141159951964953779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1502464376426538573210077 563424141159951964953779)
                ·
                  refine ⟨845136211739927947430669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563424141159951964953779 845136211739927947430669)
                  ·
                    refine ⟨316926079402472980286501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 845136211739927947430669 316926079402472980286501)
                    ·
                      rfl

theorem cell22_925817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 3].length) (baseStart_925817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925817 prefixEnd_925817 := by exact prefixLift 925817
  have htrace : WordTrace (prefixWord ++ tailWord_925817) baseStart_925817 baseEnd_925817 := by
    simpa [prefixWord, tailWord_925817, baseEnd_925817] using wordTrace_append hprefix tailTrace_925817
  have hstable : (prefixWord ++ tailWord_925817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925817).length < 2 ^ (prefixWord ++ tailWord_925817).sum := by decide
  have hdescent : baseEnd_925817 < baseStart_925817 := by decide
  rcases family_descends (prefixWord ++ tailWord_925817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925847 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 5]
def baseStart_925847 : Nat := 118140960795 + 925847 * 2 ^ 59
def prefixEnd_925847 : Nat := 4983230072969 + 3 ^ 40 * 925847 * 2
def baseEnd_925847 : Nat := 105645449671854300678803

theorem tailTrace_925847 : CollatzResearch.WordTrace tailWord_925847 prefixEnd_925847 105645449671854300678803 := by
  unfold tailWord_925847
  simp only [CollatzResearch.WordTrace]
  refine ⟨33768414276821915923967795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22512276184547943949311863 33768414276821915923967795)
  ·
    refine ⟨50652621415232873885951693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33768414276821915923967795 50652621415232873885951693)
    ·
      refine ⟨18994733030712327707231885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50652621415232873885951693 18994733030712327707231885)
      ·
        refine ⟨7123024886517122890211957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18994733030712327707231885 7123024886517122890211957)
        ·
          refine ⟨667783583110980270957371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7123024886517122890211957 667783583110980270957371)
          ·
            refine ⟨1001675374666470406436057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667783583110980270957371 1001675374666470406436057)
            ·
              refine ⟨751256530999852804827043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001675374666470406436057 751256530999852804827043)
              ·
                refine ⟨1126884796499779207240565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751256530999852804827043 1126884796499779207240565)
                ·
                  refine ⟨105645449671854300678803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1126884796499779207240565 105645449671854300678803)
                  ·
                    rfl

theorem cell22_925847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 5].length) (baseStart_925847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925847 prefixEnd_925847 := by exact prefixLift 925847
  have htrace : WordTrace (prefixWord ++ tailWord_925847) baseStart_925847 baseEnd_925847 := by
    simpa [prefixWord, tailWord_925847, baseEnd_925847] using wordTrace_append hprefix tailTrace_925847
  have hstable : (prefixWord ++ tailWord_925847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925847).length < 2 ^ (prefixWord ++ tailWord_925847).sum := by decide
  have hdescent : baseEnd_925847 < baseStart_925847 := by decide
  rcases family_descends (prefixWord ++ tailWord_925847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925886 : List Nat := [4, 2, 1, 1, 14]
def baseStart_925886 : Nat := 118140960795 + 925886 * 2 ^ 59
def prefixEnd_925886 : Nat := 4983230072969 + 3 ^ 40 * 925886 * 2
def baseEnd_925886 : Nat := 1304319751080575309923

theorem tailTrace_925886 : CollatzResearch.WordTrace tailWord_925886 prefixEnd_925886 1304319751080575309923 := by
  unfold tailWord_925886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4221229590460078198079689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22513224482453750389758341 4221229590460078198079689)
  ·
    refine ⟨3165922192845058648559767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4221229590460078198079689 3165922192845058648559767)
    ·
      refine ⟨4748883289267587972839651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165922192845058648559767 4748883289267587972839651)
      ·
        refine ⟨7123324933901381959259477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4748883289267587972839651 7123324933901381959259477)
        ·
          refine ⟨1304319751080575309923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 7123324933901381959259477 1304319751080575309923)
          ·
            rfl

theorem cell22_925886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 14].length) (baseStart_925886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925886 prefixEnd_925886 := by exact prefixLift 925886
  have htrace : WordTrace (prefixWord ++ tailWord_925886) baseStart_925886 baseEnd_925886 := by
    simpa [prefixWord, tailWord_925886, baseEnd_925886] using wordTrace_append hprefix tailTrace_925886
  have hstable : (prefixWord ++ tailWord_925886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925886).length < 2 ^ (prefixWord ++ tailWord_925886).sum := by decide
  have hdescent : baseEnd_925886 < baseStart_925886 := by decide
  rcases family_descends (prefixWord ++ tailWord_925886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925888 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_925888 : Nat := 118140960795 + 925888 * 2 ^ 59
def prefixEnd_925888 : Nat := 4983230072969 + 3 ^ 40 * 925888 * 2
def baseEnd_925888 : Nat := 316950384153452461761283

theorem tailTrace_925888 : CollatzResearch.WordTrace tailWord_925888 prefixEnd_925888 316950384153452461761283 := by
  unfold tailWord_925888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16884954834836689963105159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22513273113115586617473545 16884954834836689963105159)
  ·
    refine ⟨25327432252255034944657739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16884954834836689963105159 25327432252255034944657739)
    ·
      refine ⟨37991148378382552416986609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25327432252255034944657739 37991148378382552416986609)
      ·
        refine ⟨28493361283786914312739957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37991148378382552416986609 28493361283786914312739957)
        ·
          refine ⟨2671252620355023216819371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28493361283786914312739957 2671252620355023216819371)
          ·
            refine ⟨4006878930532534825229057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671252620355023216819371 4006878930532534825229057)
            ·
              refine ⟨3005159197899401118921793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006878930532534825229057 3005159197899401118921793)
              ·
                refine ⟨2253869398424550839191345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005159197899401118921793 2253869398424550839191345)
                ·
                  refine ⟨1690402048818413129393509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2253869398424550839191345 1690402048818413129393509)
                  ·
                    refine ⟨316950384153452461761283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1690402048818413129393509 316950384153452461761283)
                    ·
                      rfl

theorem cell22_925888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_925888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925888 prefixEnd_925888 := by exact prefixLift 925888
  have htrace : WordTrace (prefixWord ++ tailWord_925888) baseStart_925888 baseEnd_925888 := by
    simpa [prefixWord, tailWord_925888, baseEnd_925888] using wordTrace_append hprefix tailTrace_925888
  have hstable : (prefixWord ++ tailWord_925888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925888).length < 2 ^ (prefixWord ++ tailWord_925888).sum := by decide
  have hdescent : baseEnd_925888 < baseStart_925888 := by decide
  rcases family_descends (prefixWord ++ tailWord_925888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925892 : List Nat := [2, 3, 3, 1, 2, 1, 4, 2, 4]
def baseStart_925892 : Nat := 118140960795 + 925892 * 2 ^ 59
def prefixEnd_925892 : Nat := 4983230072969 + 3 ^ 40 * 925892 * 2
def baseEnd_925892 : Nat := 105650584478399261553757

theorem tailTrace_925892 : CollatzResearch.WordTrace tailWord_925892 prefixEnd_925892 105650584478399261553757 := by
  unfold tailWord_925892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16885027780829444304677965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22513370374439259072903953 16885027780829444304677965)
  ·
    refine ⟨6331885417811041614254237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16885027780829444304677965 6331885417811041614254237)
    ·
      refine ⟨2374457031679140605345339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6331885417811041614254237 2374457031679140605345339)
      ·
        refine ⟨3561685547518710908018009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374457031679140605345339 3561685547518710908018009)
        ·
          refine ⟨2671264160639033181013507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3561685547518710908018009 2671264160639033181013507)
          ·
            refine ⟨4006896240958549771520261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671264160639033181013507 4006896240958549771520261)
            ·
              refine ⟨751293045179728082160049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4006896240958549771520261 751293045179728082160049)
              ·
                refine ⟨563469783884796061620037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751293045179728082160049 563469783884796061620037)
                ·
                  refine ⟨105650584478399261553757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563469783884796061620037 105650584478399261553757)
                  ·
                    rfl

theorem cell22_925892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_925892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925892 prefixEnd_925892 := by exact prefixLift 925892
  have htrace : WordTrace (prefixWord ++ tailWord_925892) baseStart_925892 baseEnd_925892 := by
    simpa [prefixWord, tailWord_925892, baseEnd_925892] using wordTrace_append hprefix tailTrace_925892
  have hstable : (prefixWord ++ tailWord_925892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925892).length < 2 ^ (prefixWord ++ tailWord_925892).sum := by decide
  have hdescent : baseEnd_925892 < baseStart_925892 := by decide
  rcases family_descends (prefixWord ++ tailWord_925892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925931 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 7]
def baseStart_925931 : Nat := 118140960795 + 925931 * 2 ^ 59
def prefixEnd_925931 : Nat := 4983230072969 + 3 ^ 40 * 925931 * 2
def baseEnd_925931 : Nat := 105655034644071560978717

theorem tailTrace_925931 : CollatzResearch.WordTrace tailWord_925931 prefixEnd_925931 105655034644071560978717 := by
  unfold tailWord_925931
  simp only [CollatzResearch.WordTrace]
  refine ⟨33771478008517598270025647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22514318672345065513350431 33771478008517598270025647)
  ·
    refine ⟨50657217012776397405038471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33771478008517598270025647 50657217012776397405038471)
    ·
      refine ⟨75985825519164596107557707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50657217012776397405038471 75985825519164596107557707)
      ·
        refine ⟨113978738278746894161336561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75985825519164596107557707 113978738278746894161336561)
        ·
          refine ⟨85484053709060170621002421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113978738278746894161336561 85484053709060170621002421)
          ·
            refine ⟨8014130035224390995718977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85484053709060170621002421 8014130035224390995718977)
            ·
              refine ⟨6010597526418293246789233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8014130035224390995718977 6010597526418293246789233)
              ·
                refine ⟨4507948144813719935091925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010597526418293246789233 4507948144813719935091925)
                ·
                  refine ⟨105655034644071560978717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4507948144813719935091925 105655034644071560978717)
                  ·
                    rfl

theorem cell22_925931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 7].length) (baseStart_925931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925931 prefixEnd_925931 := by exact prefixLift 925931
  have htrace : WordTrace (prefixWord ++ tailWord_925931) baseStart_925931 baseEnd_925931 := by
    simpa [prefixWord, tailWord_925931, baseEnd_925931] using wordTrace_append hprefix tailTrace_925931
  have hstable : (prefixWord ++ tailWord_925931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925931).length < 2 ^ (prefixWord ++ tailWord_925931).sum := by decide
  have hdescent : baseEnd_925931 < baseStart_925931 := by decide
  rcases family_descends (prefixWord ++ tailWord_925931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925948 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 7]
def baseStart_925948 : Nat := 118140960795 + 925948 * 2 ^ 59
def prefixEnd_925948 : Nat := 4983230072969 + 3 ^ 40 * 925948 * 2
def baseEnd_925948 : Nat := 105656974459877435087033

theorem tailTrace_925948 : CollatzResearch.WordTrace tailWord_925948 prefixEnd_925948 105656974459877435087033 := by
  unfold tailWord_925948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16886049024728005086697249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22514732032970673448929665 16886049024728005086697249)
  ·
    refine ⟨12664536768546003815022937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16886049024728005086697249 12664536768546003815022937)
    ·
      refine ⟨9498402576409502861267203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12664536768546003815022937 9498402576409502861267203)
      ·
        refine ⟨14247603864614254291900805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9498402576409502861267203 14247603864614254291900805)
        ·
          refine ⟨2671425724615172679731401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14247603864614254291900805 2671425724615172679731401)
          ·
            refine ⟨2003569293461379509798551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2671425724615172679731401 2003569293461379509798551)
            ·
              refine ⟨3005353940192069264697827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003569293461379509798551 3005353940192069264697827)
              ·
                refine ⟨4508030910288103897046741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005353940192069264697827 4508030910288103897046741)
                ·
                  refine ⟨105656974459877435087033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4508030910288103897046741 105656974459877435087033)
                  ·
                    rfl

theorem cell22_925948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_925948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925948 prefixEnd_925948 := by exact prefixLift 925948
  have htrace : WordTrace (prefixWord ++ tailWord_925948) baseStart_925948 baseEnd_925948 := by
    simpa [prefixWord, tailWord_925948, baseEnd_925948] using wordTrace_append hprefix tailTrace_925948
  have hstable : (prefixWord ++ tailWord_925948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925948).length < 2 ^ (prefixWord ++ tailWord_925948).sum := by decide
  have hdescent : baseEnd_925948 < baseStart_925948 := by decide
  rcases family_descends (prefixWord ++ tailWord_925948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926010 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_926010 : Nat := 118140960795 + 926010 * 2 ^ 59
def prefixEnd_926010 : Nat := 4983230072969 + 3 ^ 40 * 926010 * 2
def baseEnd_926010 : Nat := 105664049082228270070303

theorem tailTrace_926010 : CollatzResearch.WordTrace tailWord_926010 prefixEnd_926010 105664049082228270070303 := by
  unfold tailWord_926010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443589843807848690537871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22516239583487596508100989 8443589843807848690537871)
  ·
    refine ⟨12665384765711773035806807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8443589843807848690537871 12665384765711773035806807)
    ·
      refine ⟨18998077148567659553710211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12665384765711773035806807 18998077148567659553710211)
      ·
        refine ⟨28497115722851489330565317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18998077148567659553710211 28497115722851489330565317)
        ·
          refine ⟨5343209198034654249480997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28497115722851489330565317 5343209198034654249480997)
          ·
            refine ⟨1001851724631497671777687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5343209198034654249480997 1001851724631497671777687)
            ·
              refine ⟨1502777586947246507666531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001851724631497671777687 1502777586947246507666531)
              ·
                refine ⟨2254166380420869761499797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502777586947246507666531 2254166380420869761499797)
                ·
                  refine ⟨105664049082228270070303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2254166380420869761499797 105664049082228270070303)
                  ·
                    rfl

theorem cell22_926010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_926010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926010 prefixEnd_926010 := by exact prefixLift 926010
  have htrace : WordTrace (prefixWord ++ tailWord_926010) baseStart_926010 baseEnd_926010 := by
    simpa [prefixWord, tailWord_926010, baseEnd_926010] using wordTrace_append hprefix tailTrace_926010
  have hstable : (prefixWord ++ tailWord_926010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926010).length < 2 ^ (prefixWord ++ tailWord_926010).sum := by decide
  have hdescent : baseEnd_926010 < baseStart_926010 := by decide
  rcases family_descends (prefixWord ++ tailWord_926010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926023 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 4, 4]
def baseStart_926023 : Nat := 118140960795 + 926023 * 2 ^ 59
def prefixEnd_926023 : Nat := 4983230072969 + 3 ^ 40 * 926023 * 2
def baseEnd_926023 : Nat := 316996597412357109635869

theorem tailTrace_926023 : CollatzResearch.WordTrace tailWord_926023 prefixEnd_926023 316996597412357109635869 := by
  unfold tailWord_926023
  simp only [CollatzResearch.WordTrace]
  refine ⟨33774833524184297982374723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22516555682789531988249815 33774833524184297982374723)
  ·
    refine ⟨50662250286276446973562085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33774833524184297982374723 50662250286276446973562085)
    ·
      refine ⟨9499171928676833807542891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50662250286276446973562085 9499171928676833807542891)
      ·
        refine ⟨14248757893015250711314337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9499171928676833807542891 14248757893015250711314337)
        ·
          refine ⟨10686568419761438033485753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14248757893015250711314337 10686568419761438033485753)
          ·
            refine ⟨8014926314821078525114315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10686568419761438033485753 8014926314821078525114315)
            ·
              refine ⟨12022389472231617787671473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8014926314821078525114315 12022389472231617787671473)
              ·
                refine ⟨9016792104173713340753605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12022389472231617787671473 9016792104173713340753605)
                ·
                  refine ⟨1690648519532571251391301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9016792104173713340753605 1690648519532571251391301)
                  ·
                    refine ⟨316996597412357109635869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1690648519532571251391301 316996597412357109635869)
                    ·
                      rfl

theorem cell22_926023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_926023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926023 prefixEnd_926023 := by exact prefixLift 926023
  have htrace : WordTrace (prefixWord ++ tailWord_926023) baseStart_926023 baseEnd_926023 := by
    simpa [prefixWord, tailWord_926023, baseEnd_926023] using wordTrace_append hprefix tailTrace_926023
  have hstable : (prefixWord ++ tailWord_926023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926023).length < 2 ^ (prefixWord ++ tailWord_926023).sum := by decide
  have hdescent : baseEnd_926023 < baseStart_926023 := by decide
  rcases family_descends (prefixWord ++ tailWord_926023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926104 : List Nat := [2, 1, 2, 5, 1, 1, 1, 5, 1, 3]
def baseStart_926104 : Nat := 118140960795 + 926104 * 2 ^ 59
def prefixEnd_926104 : Nat := 4983230072969 + 3 ^ 40 * 926104 * 2
def baseEnd_926104 : Nat := 317024325367699898360621

theorem tailTrace_926104 : CollatzResearch.WordTrace tailWord_926104 prefixEnd_926104 317024325367699898360621 := by
  unfold tailWord_926104
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888893918445424408036683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22518525224593899210715577 16888893918445424408036683)
  ·
    refine ⟨25333340877668136612055025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16888893918445424408036683 25333340877668136612055025)
    ·
      refine ⟨19000005658251102459041269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25333340877668136612055025 19000005658251102459041269)
      ·
        refine ⟨1781250530461040855535119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19000005658251102459041269 1781250530461040855535119)
        ·
          refine ⟨2671875795691561283302679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1781250530461040855535119 2671875795691561283302679)
          ·
            refine ⟨4007813693537341924954019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671875795691561283302679 4007813693537341924954019)
            ·
              refine ⟨6011720540306012887431029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4007813693537341924954019 6011720540306012887431029)
              ·
                refine ⟨563598800653688708196659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6011720540306012887431029 563598800653688708196659)
                ·
                  refine ⟨845398200980533062294989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563598800653688708196659 845398200980533062294989)
                  ·
                    refine ⟨317024325367699898360621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 845398200980533062294989 317024325367699898360621)
                    ·
                      rfl

theorem cell22_926104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_926104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926104 prefixEnd_926104 := by exact prefixLift 926104
  have htrace : WordTrace (prefixWord ++ tailWord_926104) baseStart_926104 baseEnd_926104 := by
    simpa [prefixWord, tailWord_926104, baseEnd_926104] using wordTrace_append hprefix tailTrace_926104
  have hstable : (prefixWord ++ tailWord_926104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926104).length < 2 ^ (prefixWord ++ tailWord_926104).sum := by decide
  have hdescent : baseEnd_926104 < baseStart_926104 := by decide
  rcases family_descends (prefixWord ++ tailWord_926104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926175 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 4, 4]
def baseStart_926175 : Nat := 118140960795 + 926175 * 2 ^ 59
def prefixEnd_926175 : Nat := 4983230072969 + 3 ^ 40 * 926175 * 2
def baseEnd_926175 : Nat := 317048630118679379835403

theorem tailTrace_926175 : CollatzResearch.WordTrace tailWord_926175 prefixEnd_926175 317048630118679379835403 := by
  unfold tailWord_926175
  simp only [CollatzResearch.WordTrace]
  refine ⟨33780377419633627941907979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22520251613089085294605319 33780377419633627941907979)
  ·
    refine ⟨50670566129450441912861969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33780377419633627941907979 50670566129450441912861969)
    ·
      refine ⟨38002924597087831434646477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50670566129450441912861969 38002924597087831434646477)
      ·
        refine ⟨14251096723907936787992429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38002924597087831434646477 14251096723907936787992429)
        ·
          refine ⟨5344161271465476295497161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14251096723907936787992429 5344161271465476295497161)
          ·
            refine ⟨4008120953599107221622871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5344161271465476295497161 4008120953599107221622871)
            ·
              refine ⟨6012181430398660832434307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4008120953599107221622871 6012181430398660832434307)
              ·
                refine ⟨9018272145597991248651461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012181430398660832434307 9018272145597991248651461)
                ·
                  refine ⟨1690926027299623359122149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9018272145597991248651461 1690926027299623359122149)
                  ·
                    refine ⟨317048630118679379835403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1690926027299623359122149 317048630118679379835403)
                    ·
                      rfl

theorem cell22_926175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_926175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926175 prefixEnd_926175 := by exact prefixLift 926175
  have htrace : WordTrace (prefixWord ++ tailWord_926175) baseStart_926175 baseEnd_926175 := by
    simpa [prefixWord, tailWord_926175, baseEnd_926175] using wordTrace_append hprefix tailTrace_926175
  have hstable : (prefixWord ++ tailWord_926175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926175).length < 2 ^ (prefixWord ++ tailWord_926175).sum := by decide
  have hdescent : baseEnd_926175 < baseStart_926175 := by decide
  rcases family_descends (prefixWord ++ tailWord_926175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926177 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 2, 3]
def baseStart_926177 : Nat := 118140960795 + 926177 * 2 ^ 59
def prefixEnd_926177 : Nat := 4983230072969 + 3 ^ 40 * 926177 * 2
def baseEnd_926177 : Nat := 317049314759552041285397

theorem tailTrace_926177 : CollatzResearch.WordTrace tailWord_926177 prefixEnd_926177 317049314759552041285397 := by
  unfold tailWord_926177
  simp only [CollatzResearch.WordTrace]
  refine ⟨33780450365626382283480785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22520300243750921522320523 33780450365626382283480785)
  ·
    refine ⟨25335337774219786712610589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33780450365626382283480785 25335337774219786712610589)
    ·
      refine ⟨9500751665332420017228971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25335337774219786712610589 9500751665332420017228971)
      ·
        refine ⟨14251127497998630025843457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9500751665332420017228971 14251127497998630025843457)
        ·
          refine ⟨10688345623498972519382593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14251127497998630025843457 10688345623498972519382593)
          ·
            refine ⟨8016259217624229389536945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10688345623498972519382593 8016259217624229389536945)
            ·
              refine ⟨6012194413218172042152709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8016259217624229389536945 6012194413218172042152709)
              ·
                refine ⟨1127286452478407257903633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6012194413218172042152709 1127286452478407257903633)
                ·
                  refine ⟨845464839358805443427725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1127286452478407257903633 845464839358805443427725)
                  ·
                    refine ⟨317049314759552041285397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 845464839358805443427725 317049314759552041285397)
                    ·
                      rfl

theorem cell22_926177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_926177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926177 prefixEnd_926177 := by exact prefixLift 926177
  have htrace : WordTrace (prefixWord ++ tailWord_926177) baseStart_926177 baseEnd_926177 := by
    simpa [prefixWord, tailWord_926177, baseEnd_926177] using wordTrace_append hprefix tailTrace_926177
  have hstable : (prefixWord ++ tailWord_926177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926177).length < 2 ^ (prefixWord ++ tailWord_926177).sum := by decide
  have hdescent : baseEnd_926177 < baseStart_926177 := by decide
  rcases family_descends (prefixWord ++ tailWord_926177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926179 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 6]
def baseStart_926179 : Nat := 118140960795 + 926179 * 2 ^ 59
def prefixEnd_926179 : Nat := 4983230072969 + 3 ^ 40 * 926179 * 2
def baseEnd_926179 : Nat := 105683333133474900911797

theorem tailTrace_926179 : CollatzResearch.WordTrace tailWord_926179 prefixEnd_926179 105683333133474900911797 := by
  unfold tailWord_926179
  simp only [CollatzResearch.WordTrace]
  refine ⟨33780523311619136625053591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22520348874412757750035727 33780523311619136625053591)
  ·
    refine ⟨50670784967428704937580387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33780523311619136625053591 50670784967428704937580387)
    ·
      refine ⟨76006177451143057406370581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50670784967428704937580387 76006177451143057406370581)
      ·
        refine ⟨3562789568022330815923621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76006177451143057406370581 3562789568022330815923621)
        ·
          refine ⟨668023044004187027985679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3562789568022330815923621 668023044004187027985679)
          ·
            refine ⟨1002034566006280541978519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668023044004187027985679 1002034566006280541978519)
            ·
              refine ⟨1503051849009420812967779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002034566006280541978519 1503051849009420812967779)
              ·
                refine ⟨2254577773514131219451669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503051849009420812967779 2254577773514131219451669)
                ·
                  refine ⟨105683333133474900911797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2254577773514131219451669 105683333133474900911797)
                  ·
                    rfl

theorem cell22_926179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 6].length) (baseStart_926179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926179 prefixEnd_926179 := by exact prefixLift 926179
  have htrace : WordTrace (prefixWord ++ tailWord_926179) baseStart_926179 baseEnd_926179 := by
    simpa [prefixWord, tailWord_926179, baseEnd_926179] using wordTrace_append hprefix tailTrace_926179
  have hstable : (prefixWord ++ tailWord_926179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926179).length < 2 ^ (prefixWord ++ tailWord_926179).sum := by decide
  have hdescent : baseEnd_926179 < baseStart_926179 := by decide
  rcases family_descends (prefixWord ++ tailWord_926179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926190 : List Nat := [4, 1, 2, 1, 2, 2, 1, 9]
def baseStart_926190 : Nat := 118140960795 + 926190 * 2 ^ 59
def prefixEnd_926190 : Nat := 4983230072969 + 3 ^ 40 * 926190 * 2
def baseEnd_926190 : Nat := 35228196102802704523373

theorem tailTrace_926190 : CollatzResearch.WordTrace tailWord_926190 prefixEnd_926190 35228196102802704523373 := by
  unfold tailWord_926190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4222615564322410687963003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22520616343052857002469349 4222615564322410687963003)
  ·
    refine ⟨6333923346483616031944505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4222615564322410687963003 6333923346483616031944505)
    ·
      refine ⟨4750442509862712023958379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6333923346483616031944505 4750442509862712023958379)
      ·
        refine ⟨7125663764794068035937569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4750442509862712023958379 7125663764794068035937569)
        ·
          refine ⟨5344247823595551026953177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7125663764794068035937569 5344247823595551026953177)
          ·
            refine ⟨4008185867696663270214883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5344247823595551026953177 4008185867696663270214883)
            ·
              refine ⟨6012278801544994905322325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4008185867696663270214883 6012278801544994905322325)
              ·
                refine ⟨35228196102802704523373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6012278801544994905322325 35228196102802704523373)
                ·
                  rfl

theorem cell22_926190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_926190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926190 prefixEnd_926190 := by exact prefixLift 926190
  have htrace : WordTrace (prefixWord ++ tailWord_926190) baseStart_926190 baseEnd_926190 := by
    simpa [prefixWord, tailWord_926190, baseEnd_926190] using wordTrace_append hprefix tailTrace_926190
  have hstable : (prefixWord ++ tailWord_926190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926190).length < 2 ^ (prefixWord ++ tailWord_926190).sum := by decide
  have hdescent : baseEnd_926190 < baseStart_926190 := by decide
  rcases family_descends (prefixWord ++ tailWord_926190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926355 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 1, 8]
def baseStart_926355 : Nat := 118140960795 + 926355 * 2 ^ 59
def prefixEnd_926355 : Nat := 4983230072969 + 3 ^ 40 * 926355 * 2
def baseEnd_926355 : Nat := 317110247797218910334851

theorem tailTrace_926355 : CollatzResearch.WordTrace tailWord_926355 prefixEnd_926355 317110247797218910334851 := by
  unfold tailWord_926355
  simp only [CollatzResearch.WordTrace]
  refine ⟨33786942558981518683460519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22524628372654345788973679 33786942558981518683460519)
  ·
    refine ⟨50680413838472278025190779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33786942558981518683460519 50680413838472278025190779)
    ·
      refine ⟨76020620757708417037786169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50680413838472278025190779 76020620757708417037786169)
      ·
        refine ⟨57015465568281312778339627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76020620757708417037786169 57015465568281312778339627)
        ·
          refine ⟨85523198352421969167509441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57015465568281312778339627 85523198352421969167509441)
          ·
            refine ⟨64142398764316476875632081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85523198352421969167509441 64142398764316476875632081)
            ·
              refine ⟨48106799073237357656724061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64142398764316476875632081 48106799073237357656724061)
              ·
                refine ⟨18040049652464009121271523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48106799073237357656724061 18040049652464009121271523)
                ·
                  refine ⟨27060074478696013681907285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18040049652464009121271523 27060074478696013681907285)
                  ·
                    refine ⟨317110247797218910334851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27060074478696013681907285 317110247797218910334851)
                    ·
                      rfl

theorem cell22_926355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_926355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926355 prefixEnd_926355 := by exact prefixLift 926355
  have htrace : WordTrace (prefixWord ++ tailWord_926355) baseStart_926355 baseEnd_926355 := by
    simpa [prefixWord, tailWord_926355, baseEnd_926355] using wordTrace_append hprefix tailTrace_926355
  have hstable : (prefixWord ++ tailWord_926355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926355).length < 2 ^ (prefixWord ++ tailWord_926355).sum := by decide
  have hdescent : baseEnd_926355 < baseStart_926355 := by decide
  rcases family_descends (prefixWord ++ tailWord_926355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926378 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_926378 : Nat := 118140960795 + 926378 * 2 ^ 59
def prefixEnd_926378 : Nat := 4983230072969 + 3 ^ 40 * 926378 * 2
def baseEnd_926378 : Nat := 317118121167254517009781

theorem tailTrace_926378 : CollatzResearch.WordTrace tailWord_926378 prefixEnd_926378 317118121167254517009781 := by
  unfold tailWord_926378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8446945359474548402886947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22525187625265462407698525 8446945359474548402886947)
  ·
    refine ⟨12670418039211822604330421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8446945359474548402886947 12670418039211822604330421)
    ·
      refine ⟨1187851691176108369155977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12670418039211822604330421 1187851691176108369155977)
      ·
        refine ⟨890888768382081276866983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1187851691176108369155977 890888768382081276866983)
        ·
          refine ⟨1336333152573121915300475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890888768382081276866983 1336333152573121915300475)
          ·
            refine ⟨2004499728859682872950713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336333152573121915300475 2004499728859682872950713)
            ·
              refine ⟨1503374796644762154713035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004499728859682872950713 1503374796644762154713035)
              ·
                refine ⟨2255062194967143232069553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503374796644762154713035 2255062194967143232069553)
                ·
                  refine ⟨1691296646225357424052165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2255062194967143232069553 1691296646225357424052165)
                  ·
                    refine ⟨317118121167254517009781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1691296646225357424052165 317118121167254517009781)
                    ·
                      rfl

theorem cell22_926378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_926378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926378 prefixEnd_926378 := by exact prefixLift 926378
  have htrace : WordTrace (prefixWord ++ tailWord_926378) baseStart_926378 baseEnd_926378 := by
    simpa [prefixWord, tailWord_926378, baseEnd_926378] using wordTrace_append hprefix tailTrace_926378
  have hstable : (prefixWord ++ tailWord_926378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926378).length < 2 ^ (prefixWord ++ tailWord_926378).sum := by decide
  have hdescent : baseEnd_926378 < baseStart_926378 := by decide
  rcases family_descends (prefixWord ++ tailWord_926378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926404 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 5]
def baseStart_926404 : Nat := 118140960795 + 926404 * 2 ^ 59
def prefixEnd_926404 : Nat := 4983230072969 + 3 ^ 40 * 926404 * 2
def baseEnd_926404 : Nat := 105709007166199705286567

theorem tailTrace_926404 : CollatzResearch.WordTrace tailWord_926404 prefixEnd_926404 105709007166199705286567 := by
  unfold tailWord_926404
  simp only [CollatzResearch.WordTrace]
  refine ⟨16894364867902000025997133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22525819823869333367996177 16894364867902000025997133)
  ·
    refine ⟨6335386825463250009748925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16894364867902000025997133 6335386825463250009748925)
    ·
      refine ⟨2375770059548718753655847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6335386825463250009748925 2375770059548718753655847)
      ·
        refine ⟨3563655089323078130483771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375770059548718753655847 3563655089323078130483771)
        ·
          refine ⟨5345482633984617195725657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563655089323078130483771 5345482633984617195725657)
          ·
            refine ⟨4009111975488462896794243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5345482633984617195725657 4009111975488462896794243)
            ·
              refine ⟨6013667963232694345191365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009111975488462896794243 6013667963232694345191365)
              ·
                refine ⟨1127562743106130189723381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6013667963232694345191365 1127562743106130189723381)
                ·
                  refine ⟨105709007166199705286567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1127562743106130189723381 105709007166199705286567)
                  ·
                    rfl

theorem cell22_926404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_926404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926404 prefixEnd_926404 := by exact prefixLift 926404
  have htrace : WordTrace (prefixWord ++ tailWord_926404) baseStart_926404 baseEnd_926404 := by
    simpa [prefixWord, tailWord_926404, baseEnd_926404] using wordTrace_append hprefix tailTrace_926404
  have hstable : (prefixWord ++ tailWord_926404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926404).length < 2 ^ (prefixWord ++ tailWord_926404).sum := by decide
  have hdescent : baseEnd_926404 < baseStart_926404 := by decide
  rcases family_descends (prefixWord ++ tailWord_926404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926408 : List Nat := [2, 1, 3, 1, 2, 3, 4, 2, 1, 3]
def baseStart_926408 : Nat := 118140960795 + 926408 * 2 ^ 59
def prefixEnd_926408 : Nat := 4983230072969 + 3 ^ 40 * 926408 * 2
def baseEnd_926408 : Nat := 317128390780344438759689

theorem tailTrace_926408 : CollatzResearch.WordTrace tailWord_926408 prefixEnd_926408 317128390780344438759689 := by
  unfold tailWord_926408
  simp only [CollatzResearch.WordTrace]
  refine ⟨16894437813894754367569939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22525917085193005823426585 16894437813894754367569939)
  ·
    refine ⟨25341656720842131551354909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16894437813894754367569939 25341656720842131551354909)
    ·
      refine ⟨9503121270315799331758091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25341656720842131551354909 9503121270315799331758091)
      ·
        refine ⟨14254681905473698997637137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9503121270315799331758091 14254681905473698997637137)
        ·
          refine ⟨10691011429105274248227853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14254681905473698997637137 10691011429105274248227853)
          ·
            refine ⟨4009129285914477843085445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10691011429105274248227853 4009129285914477843085445)
            ·
              refine ⟨751711741108964595578521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4009129285914477843085445 751711741108964595578521)
              ·
                refine ⟨563783805831723446683891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751711741108964595578521 563783805831723446683891)
                ·
                  refine ⟨845675708747585170025837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563783805831723446683891 845675708747585170025837)
                  ·
                    refine ⟨317128390780344438759689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 845675708747585170025837 317128390780344438759689)
                    ·
                      rfl

theorem cell22_926408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_926408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926408 prefixEnd_926408 := by exact prefixLift 926408
  have htrace : WordTrace (prefixWord ++ tailWord_926408) baseStart_926408 baseEnd_926408 := by
    simpa [prefixWord, tailWord_926408, baseEnd_926408] using wordTrace_append hprefix tailTrace_926408
  have hstable : (prefixWord ++ tailWord_926408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926408).length < 2 ^ (prefixWord ++ tailWord_926408).sum := by decide
  have hdescent : baseEnd_926408 < baseStart_926408 := by decide
  rcases family_descends (prefixWord ++ tailWord_926408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926417 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_926417 : Nat := 118140960795 + 926417 * 2 ^ 59
def prefixEnd_926417 : Nat := 4983230072969 + 3 ^ 40 * 926417 * 2
def baseEnd_926417 : Nat := 317131471664271415284661

theorem tailTrace_926417 : CollatzResearch.WordTrace tailWord_926417 prefixEnd_926417 317131471664271415284661 := by
  unfold tailWord_926417
  simp only [CollatzResearch.WordTrace]
  refine ⟨33789203884756903272217505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22526135923171268848145003 33789203884756903272217505)
  ·
    refine ⟨25341902913567677454163129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33789203884756903272217505 25341902913567677454163129)
    ·
      refine ⟨19006427185175758090622347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25341902913567677454163129 19006427185175758090622347)
      ·
        refine ⟨28509640777763637135933521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19006427185175758090622347 28509640777763637135933521)
        ·
          refine ⟨21382230583322727851950141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28509640777763637135933521 21382230583322727851950141)
          ·
            refine ⟨8018336468746022944481303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21382230583322727851950141 8018336468746022944481303)
            ·
              refine ⟨12027504703119034416721955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018336468746022944481303 12027504703119034416721955)
              ·
                refine ⟨18041257054678551625082933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12027504703119034416721955 18041257054678551625082933)
                ·
                  refine ⟨1691367848876114214851525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18041257054678551625082933 1691367848876114214851525)
                  ·
                    refine ⟨317131471664271415284661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1691367848876114214851525 317131471664271415284661)
                    ·
                      rfl

theorem cell22_926417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_926417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926417 prefixEnd_926417 := by exact prefixLift 926417
  have htrace : WordTrace (prefixWord ++ tailWord_926417) baseStart_926417 baseEnd_926417 := by
    simpa [prefixWord, tailWord_926417, baseEnd_926417] using wordTrace_append hprefix tailTrace_926417
  have hstable : (prefixWord ++ tailWord_926417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926417).length < 2 ^ (prefixWord ++ tailWord_926417).sum := by decide
  have hdescent : baseEnd_926417 < baseStart_926417 := by decide
  rcases family_descends (prefixWord ++ tailWord_926417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926466 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_926466 : Nat := 118140960795 + 926466 * 2 ^ 59
def prefixEnd_926466 : Nat := 4983230072969 + 3 ^ 40 * 926466 * 2
def baseEnd_926466 : Nat := 105716081788550540269837

theorem tailTrace_926466 : CollatzResearch.WordTrace tailWord_926466 prefixEnd_926466 105716081788550540269837 := by
  unfold tailWord_926466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8447747765394846160187813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22527327374386256427167501 8447747765394846160187813)
  ·
    refine ⟨1583952706011533655035215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8447747765394846160187813 1583952706011533655035215)
    ·
      refine ⟨2375929059017300482552823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583952706011533655035215 2375929059017300482552823)
      ·
        refine ⟨3563893588525950723829235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375929059017300482552823 3563893588525950723829235)
        ·
          refine ⟨5345840382788926085743853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563893588525950723829235 5345840382788926085743853)
          ·
            refine ⟨2004690143545847282153945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5345840382788926085743853 2004690143545847282153945)
            ·
              refine ⟨1503517607659385461615459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004690143545847282153945 1503517607659385461615459)
              ·
                refine ⟨2255276411489078192423189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503517607659385461615459 2255276411489078192423189)
                ·
                  refine ⟨105716081788550540269837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2255276411489078192423189 105716081788550540269837)
                  ·
                    rfl

theorem cell22_926466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_926466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926466 prefixEnd_926466 := by exact prefixLift 926466
  have htrace : WordTrace (prefixWord ++ tailWord_926466) baseStart_926466 baseEnd_926466 := by
    simpa [prefixWord, tailWord_926466, baseEnd_926466] using wordTrace_append hprefix tailTrace_926466
  have hstable : (prefixWord ++ tailWord_926466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926466).length < 2 ^ (prefixWord ++ tailWord_926466).sum := by decide
  have hdescent : baseEnd_926466 < baseStart_926466 := by decide
  rcases family_descends (prefixWord ++ tailWord_926466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926500 : List Nat := [2, 3, 1, 3, 4, 1, 1, 3, 4]
def baseStart_926500 : Nat := 118140960795 + 926500 * 2 ^ 59
def prefixEnd_926500 : Nat := 4983230072969 + 3 ^ 40 * 926500 * 2
def baseEnd_926500 : Nat := 105719961420162288486469

theorem tailTrace_926500 : CollatzResearch.WordTrace tailWord_926500 prefixEnd_926500 105719961420162288486469 := by
  unfold tailWord_926500
  simp only [CollatzResearch.WordTrace]
  refine ⟨16896115571728104223744477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22528154095637472298325969 16896115571728104223744477)
  ·
    refine ⟨6336043339398039083904179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16896115571728104223744477 6336043339398039083904179)
    ·
      refine ⟨9504065009097058625856269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6336043339398039083904179 9504065009097058625856269)
      ·
        refine ⟨3564024378411396984696101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9504065009097058625856269 3564024378411396984696101)
        ·
          refine ⟨668254570952136934630519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3564024378411396984696101 668254570952136934630519)
          ·
            refine ⟨1002381856428205401945779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668254570952136934630519 1002381856428205401945779)
            ·
              refine ⟨1503572784642308102918669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002381856428205401945779 1503572784642308102918669)
              ·
                refine ⟨563839794240865538594501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1503572784642308102918669 563839794240865538594501)
                ·
                  refine ⟨105719961420162288486469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563839794240865538594501 105719961420162288486469)
                  ·
                    rfl

theorem cell22_926500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_926500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926500 prefixEnd_926500 := by exact prefixLift 926500
  have htrace : WordTrace (prefixWord ++ tailWord_926500) baseStart_926500 baseEnd_926500 := by
    simpa [prefixWord, tailWord_926500, baseEnd_926500] using wordTrace_append hprefix tailTrace_926500
  have hstable : (prefixWord ++ tailWord_926500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926500).length < 2 ^ (prefixWord ++ tailWord_926500).sum := by decide
  have hdescent : baseEnd_926500 < baseStart_926500 := by decide
  rcases family_descends (prefixWord ++ tailWord_926500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926691 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 5]
def baseStart_926691 : Nat := 118140960795 + 926691 * 2 ^ 59
def prefixEnd_926691 : Nat := 4983230072969 + 3 ^ 40 * 926691 * 2
def baseEnd_926691 : Nat := 105741755821275344644607

theorem tailTrace_926691 : CollatzResearch.WordTrace tailWord_926691 prefixEnd_926691 105741755821275344644607 := by
  unfold tailWord_926691
  simp only [CollatzResearch.WordTrace]
  refine ⟨33799197485764248067691927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22532798323842832045127951 33799197485764248067691927)
  ·
    refine ⟨50698796228646372101537891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33799197485764248067691927 50698796228646372101537891)
    ·
      refine ⟨76048194342969558152306837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50698796228646372101537891 76048194342969558152306837)
      ·
        refine ⟨3564759109826698038389383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76048194342969558152306837 3564759109826698038389383)
        ·
          refine ⟨5347138664740047057584075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564759109826698038389383 5347138664740047057584075)
          ·
            refine ⟨8020707997110070586376113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347138664740047057584075 8020707997110070586376113)
            ·
              refine ⟨6015530997832552939782085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8020707997110070586376113 6015530997832552939782085)
              ·
                refine ⟨1127912062093603676209141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6015530997832552939782085 1127912062093603676209141)
                ·
                  refine ⟨105741755821275344644607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1127912062093603676209141 105741755821275344644607)
                  ·
                    rfl

theorem cell22_926691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 5].length) (baseStart_926691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926691 prefixEnd_926691 := by exact prefixLift 926691
  have htrace : WordTrace (prefixWord ++ tailWord_926691) baseStart_926691 baseEnd_926691 := by
    simpa [prefixWord, tailWord_926691, baseEnd_926691] using wordTrace_append hprefix tailTrace_926691
  have hstable : (prefixWord ++ tailWord_926691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926691).length < 2 ^ (prefixWord ++ tailWord_926691).sum := by decide
  have hdescent : baseEnd_926691 < baseStart_926691 := by decide
  rcases family_descends (prefixWord ++ tailWord_926691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926695 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 3, 3]
def baseStart_926695 : Nat := 118140960795 + 926695 * 2 ^ 59
def prefixEnd_926695 : Nat := 4983230072969 + 3 ^ 40 * 926695 * 2
def baseEnd_926695 : Nat := 317226636745571356833809

theorem tailTrace_926695 : CollatzResearch.WordTrace tailWord_926695 prefixEnd_926695 317226636745571356833809 := by
  unfold tailWord_926695
  simp only [CollatzResearch.WordTrace]
  refine ⟨33799343377749756750837539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22532895585166504500558359 33799343377749756750837539)
  ·
    refine ⟨50699015066624635126256309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33799343377749756750837539 50699015066624635126256309)
    ·
      refine ⟨4753032662496059543086529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50699015066624635126256309 4753032662496059543086529)
      ·
        refine ⟨3564774496872044657314897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4753032662496059543086529 3564774496872044657314897)
        ·
          refine ⟨2673580872654033492986173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3564774496872044657314897 2673580872654033492986173)
          ·
            refine ⟨1002592827245262559869815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2673580872654033492986173 1002592827245262559869815)
            ·
              refine ⟨1503889240867893839804723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002592827245262559869815 1503889240867893839804723)
              ·
                refine ⟨2255833861301840759707085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503889240867893839804723 2255833861301840759707085)
                ·
                  refine ⟨845937697988190284890157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2255833861301840759707085 845937697988190284890157)
                  ·
                    refine ⟨317226636745571356833809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 845937697988190284890157 317226636745571356833809)
                    ·
                      rfl

theorem cell22_926695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_926695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926695 prefixEnd_926695 := by exact prefixLift 926695
  have htrace : WordTrace (prefixWord ++ tailWord_926695) baseStart_926695 baseEnd_926695 := by
    simpa [prefixWord, tailWord_926695, baseEnd_926695] using wordTrace_append hprefix tailTrace_926695
  have hstable : (prefixWord ++ tailWord_926695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926695).length < 2 ^ (prefixWord ++ tailWord_926695).sum := by decide
  have hdescent : baseEnd_926695 < baseStart_926695 := by decide
  rcases family_descends (prefixWord ++ tailWord_926695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926704 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_926704 : Nat := 118140960795 + 926704 * 2 ^ 59
def prefixEnd_926704 : Nat := 4983230072969 + 3 ^ 40 * 926704 * 2
def baseEnd_926704 : Nat := 317229717629498333358781

theorem tailTrace_926704 : CollatzResearch.WordTrace tailWord_926704 prefixEnd_926704 317229717629498333358781 := by
  unfold tailWord_926704
  simp only [CollatzResearch.WordTrace]
  refine ⟨16899835817358575643957583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22533114423144767525276777 16899835817358575643957583)
  ·
    refine ⟨25349753726037863465936375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16899835817358575643957583 25349753726037863465936375)
    ·
      refine ⟨38024630589056795198904563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25349753726037863465936375 38024630589056795198904563)
      ·
        refine ⟨57036945883585192798356845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38024630589056795198904563 57036945883585192798356845)
        ·
          refine ⟨21388854706344447299383817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57036945883585192798356845 21388854706344447299383817)
          ·
            refine ⟨16041641029758335474537863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21388854706344447299383817 16041641029758335474537863)
            ·
              refine ⟨24062461544637503211806795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16041641029758335474537863 24062461544637503211806795)
              ·
                refine ⟨36093692316956254817710193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24062461544637503211806795 36093692316956254817710193)
                ·
                  refine ⟨27070269237717191113282645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36093692316956254817710193 27070269237717191113282645)
                  ·
                    refine ⟨317229717629498333358781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27070269237717191113282645 317229717629498333358781)
                    ·
                      rfl

theorem cell22_926704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_926704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926704 prefixEnd_926704 := by exact prefixLift 926704
  have htrace : WordTrace (prefixWord ++ tailWord_926704) baseStart_926704 baseEnd_926704 := by
    simpa [prefixWord, tailWord_926704, baseEnd_926704] using wordTrace_append hprefix tailTrace_926704
  have hstable : (prefixWord ++ tailWord_926704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926704).length < 2 ^ (prefixWord ++ tailWord_926704).sum := by decide
  have hdescent : baseEnd_926704 < baseStart_926704 := by decide
  rcases family_descends (prefixWord ++ tailWord_926704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926768 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 2, 3]
def baseStart_926768 : Nat := 118140960795 + 926768 * 2 ^ 59
def prefixEnd_926768 : Nat := 4983230072969 + 3 ^ 40 * 926768 * 2
def baseEnd_926768 : Nat := 317251626137423499758585

theorem tailTrace_926768 : CollatzResearch.WordTrace tailWord_926768 prefixEnd_926768 317251626137423499758585 := by
  unfold tailWord_926768
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901002953242645109122479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22534670604323526812163305 16901002953242645109122479)
  ·
    refine ⟨25351504429863967663683719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16901002953242645109122479 25351504429863967663683719)
    ·
      refine ⟨38027256644795951495525579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25351504429863967663683719 38027256644795951495525579)
      ·
        refine ⟨57040884967193927243288369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38027256644795951495525579 57040884967193927243288369)
        ·
          refine ⟨42780663725395445432466277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57040884967193927243288369 42780663725395445432466277)
          ·
            refine ⟨8021374448511646018587427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42780663725395445432466277 8021374448511646018587427)
            ·
              refine ⟨12032061672767469027881141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021374448511646018587427 12032061672767469027881141)
              ·
                refine ⟨1128005781821950221363857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12032061672767469027881141 1128005781821950221363857)
                ·
                  refine ⟨846004336366462666022893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128005781821950221363857 846004336366462666022893)
                  ·
                    refine ⟨317251626137423499758585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846004336366462666022893 317251626137423499758585)
                    ·
                      rfl

theorem cell22_926768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_926768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926768 prefixEnd_926768 := by exact prefixLift 926768
  have htrace : WordTrace (prefixWord ++ tailWord_926768) baseStart_926768 baseEnd_926768 := by
    simpa [prefixWord, tailWord_926768, baseEnd_926768] using wordTrace_append hprefix tailTrace_926768
  have hstable : (prefixWord ++ tailWord_926768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926768).length < 2 ^ (prefixWord ++ tailWord_926768).sum := by decide
  have hdescent : baseEnd_926768 < baseStart_926768 := by decide
  rcases family_descends (prefixWord ++ tailWord_926768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926802 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_926802 : Nat := 118140960795 + 926802 * 2 ^ 59
def prefixEnd_926802 : Nat := 4983230072969 + 3 ^ 40 * 926802 * 2
def baseEnd_926802 : Nat := 317263265032258744408481

theorem tailTrace_926802 : CollatzResearch.WordTrace tailWord_926802 prefixEnd_926802 317263265032258744408481 := by
  unfold tailWord_926802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8450811497090528506245665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22535497325574742683321773 8450811497090528506245665)
  ·
    refine ⟨6338108622817896379684249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8450811497090528506245665 6338108622817896379684249)
    ·
      refine ⟨4753581467113422284763187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6338108622817896379684249 4753581467113422284763187)
      ·
        refine ⟨7130372200670133427144781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753581467113422284763187 7130372200670133427144781)
        ·
          refine ⟨2673889575251300035179293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7130372200670133427144781 2673889575251300035179293)
          ·
            refine ⟨1002708590719237513192235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2673889575251300035179293 1002708590719237513192235)
            ·
              refine ⟨1504062886078856269788353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002708590719237513192235 1504062886078856269788353)
              ·
                refine ⟨1128047164559142202341265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504062886078856269788353 1128047164559142202341265)
                ·
                  refine ⟨846035373419356651755949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128047164559142202341265 846035373419356651755949)
                  ·
                    refine ⟨317263265032258744408481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846035373419356651755949 317263265032258744408481)
                    ·
                      rfl

theorem cell22_926802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_926802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926802 prefixEnd_926802 := by exact prefixLift 926802
  have htrace : WordTrace (prefixWord ++ tailWord_926802) baseStart_926802 baseEnd_926802 := by
    simpa [prefixWord, tailWord_926802, baseEnd_926802] using wordTrace_append hprefix tailTrace_926802
  have hstable : (prefixWord ++ tailWord_926802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926802).length < 2 ^ (prefixWord ++ tailWord_926802).sum := by decide
  have hdescent : baseEnd_926802 < baseStart_926802 := by decide
  rcases family_descends (prefixWord ++ tailWord_926802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926830 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_926830 : Nat := 118140960795 + 926830 * 2 ^ 59
def prefixEnd_926830 : Nat := 4983230072969 + 3 ^ 40 * 926830 * 2
def baseEnd_926830 : Nat := 317272850004476004708395

theorem tailTrace_926830 : CollatzResearch.WordTrace tailWord_926830 prefixEnd_926830 317272850004476004708395 := by
  unfold tailWord_926830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225533404032584350875243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22536178154840449871334629 4225533404032584350875243)
  ·
    refine ⟨6338300106048876526312865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4225533404032584350875243 6338300106048876526312865)
    ·
      refine ⟨4753725079536657394734649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6338300106048876526312865 4753725079536657394734649)
      ·
        refine ⟨3565293809652493046050987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4753725079536657394734649 3565293809652493046050987)
        ·
          refine ⟨5347940714478739569076481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565293809652493046050987 5347940714478739569076481)
          ·
            refine ⟨4010955535859054676807361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5347940714478739569076481 4010955535859054676807361)
            ·
              refine ⟨3008216651894291007605521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4010955535859054676807361 3008216651894291007605521)
              ·
                refine ⟨2256162488920718255704141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3008216651894291007605521 2256162488920718255704141)
                ·
                  refine ⟨846060933345269345889053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2256162488920718255704141 846060933345269345889053)
                  ·
                    refine ⟨317272850004476004708395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846060933345269345889053 317272850004476004708395)
                    ·
                      rfl

theorem cell22_926830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_926830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926830 prefixEnd_926830 := by exact prefixLift 926830
  have htrace : WordTrace (prefixWord ++ tailWord_926830) baseStart_926830 baseEnd_926830 := by
    simpa [prefixWord, tailWord_926830, baseEnd_926830] using wordTrace_append hprefix tailTrace_926830
  have hstable : (prefixWord ++ tailWord_926830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926830).length < 2 ^ (prefixWord ++ tailWord_926830).sum := by decide
  have hdescent : baseEnd_926830 < baseStart_926830 := by decide
  rcases family_descends (prefixWord ++ tailWord_926830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926903 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 1, 5]
def baseStart_926903 : Nat := 118140960795 + 926903 * 2 ^ 59
def prefixEnd_926903 : Nat := 4983230072969 + 3 ^ 40 * 926903 * 2
def baseEnd_926903 : Nat := 317297839396328147633171

theorem tailTrace_926903 : CollatzResearch.WordTrace tailWord_926903 prefixEnd_926903 317297839396328147633171 := by
  unfold tailWord_926903
  simp only [CollatzResearch.WordTrace]
  refine ⟨33806929760996208274409363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22537953173997472182939575 33806929760996208274409363)
  ·
    refine ⟨50710394641494312411614045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33806929760996208274409363 50710394641494312411614045)
    ·
      refine ⟨19016397990560367154355267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50710394641494312411614045 19016397990560367154355267)
      ·
        refine ⟨28524596985840550731532901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19016397990560367154355267 28524596985840550731532901)
        ·
          refine ⟨5348361934845103262162419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28524596985840550731532901 5348361934845103262162419)
          ·
            refine ⟨8022542902267654893243629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5348361934845103262162419 8022542902267654893243629)
            ·
              refine ⟨3008453588350370584966361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8022542902267654893243629 3008453588350370584966361)
              ·
                refine ⟨2256340191262777938724771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3008453588350370584966361 2256340191262777938724771)
                ·
                  refine ⟨3384510286894166908087157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256340191262777938724771 3384510286894166908087157)
                  ·
                    refine ⟨317297839396328147633171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3384510286894166908087157 317297839396328147633171)
                    ·
                      rfl

theorem cell22_926903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_926903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926903 prefixEnd_926903 := by exact prefixLift 926903
  have htrace : WordTrace (prefixWord ++ tailWord_926903) baseStart_926903 baseEnd_926903 := by
    simpa [prefixWord, tailWord_926903, baseEnd_926903] using wordTrace_append hprefix tailTrace_926903
  have hstable : (prefixWord ++ tailWord_926903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926903).length < 2 ^ (prefixWord ++ tailWord_926903).sum := by decide
  have hdescent : baseEnd_926903 < baseStart_926903 := by decide
  rcases family_descends (prefixWord ++ tailWord_926903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926920 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 2, 3]
def baseStart_926920 : Nat := 118140960795 + 926920 * 2 ^ 59
def prefixEnd_926920 : Nat := 4983230072969 + 3 ^ 40 * 926920 * 2
def baseEnd_926920 : Nat := 317303658843745769958119

theorem tailTrace_926920 : CollatzResearch.WordTrace tailWord_926920 prefixEnd_926920 317303658843745769958119 := by
  unfold tailWord_926920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16903774900967310088889107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22538366534623080118518809 16903774900967310088889107)
  ·
    refine ⟨25355662351450965133333661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16903774900967310088889107 25355662351450965133333661)
    ·
      refine ⟨9508373381794111925000123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25355662351450965133333661 9508373381794111925000123)
      ·
        refine ⟨14262560072691167887500185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9508373381794111925000123 14262560072691167887500185)
        ·
          refine ⟨10696920054518375915625139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14262560072691167887500185 10696920054518375915625139)
          ·
            refine ⟨16045380081777563873437709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10696920054518375915625139 16045380081777563873437709)
            ·
              refine ⟨6017017530666586452539141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16045380081777563873437709 6017017530666586452539141)
              ·
                refine ⟨1128190786999984959851089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6017017530666586452539141 1128190786999984959851089)
                ·
                  refine ⟨846143090249988719888317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128190786999984959851089 846143090249988719888317)
                  ·
                    refine ⟨317303658843745769958119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846143090249988719888317 317303658843745769958119)
                    ·
                      rfl

theorem cell22_926920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_926920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926920 prefixEnd_926920 := by exact prefixLift 926920
  have htrace : WordTrace (prefixWord ++ tailWord_926920) baseStart_926920 baseEnd_926920 := by
    simpa [prefixWord, tailWord_926920, baseEnd_926920] using wordTrace_append hprefix tailTrace_926920
  have hstable : (prefixWord ++ tailWord_926920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926920).length < 2 ^ (prefixWord ++ tailWord_926920).sum := by decide
  have hdescent : baseEnd_926920 < baseStart_926920 := by decide
  rcases family_descends (prefixWord ++ tailWord_926920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926922 : List Nat := [3, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_926922 : Nat := 118140960795 + 926922 * 2 ^ 59
def prefixEnd_926922 : Nat := 4983230072969 + 3 ^ 40 * 926922 * 2
def baseEnd_926922 : Nat := 105768114494872810469371

theorem tailTrace_926922 : CollatzResearch.WordTrace tailWord_926922 prefixEnd_926922 105768114494872810469371 := by
  unfold tailWord_926922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451905686981843629837755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22538415165284916346234013 8451905686981843629837755)
  ·
    refine ⟨12677858530472765444756633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8451905686981843629837755 12677858530472765444756633)
    ·
      refine ⟨9508393897854574083567475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12677858530472765444756633 9508393897854574083567475)
      ·
        refine ⟨14262590846781861125351213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9508393897854574083567475 14262590846781861125351213)
        ·
          refine ⟨5348471567543197922006705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14262590846781861125351213 5348471567543197922006705)
          ·
            refine ⟨4011353675657398441505029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5348471567543197922006705 4011353675657398441505029)
            ·
              refine ⟨752128814185762207782193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4011353675657398441505029 752128814185762207782193)
              ·
                refine ⟨564096610639321655836645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752128814185762207782193 564096610639321655836645)
                ·
                  refine ⟨105768114494872810469371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564096610639321655836645 105768114494872810469371)
                  ·
                    rfl

theorem cell22_926922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_926922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926922 prefixEnd_926922 := by exact prefixLift 926922
  have htrace : WordTrace (prefixWord ++ tailWord_926922) baseStart_926922 baseEnd_926922 := by
    simpa [prefixWord, tailWord_926922, baseEnd_926922] using wordTrace_append hprefix tailTrace_926922
  have hstable : (prefixWord ++ tailWord_926922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926922).length < 2 ^ (prefixWord ++ tailWord_926922).sum := by decide
  have hdescent : baseEnd_926922 < baseStart_926922 := by decide
  rcases family_descends (prefixWord ++ tailWord_926922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926993 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_926993 : Nat := 118140960795 + 926993 * 2 ^ 59
def prefixEnd_926993 : Nat := 4983230072969 + 3 ^ 40 * 926993 * 2
def baseEnd_926993 : Nat := 317328648235597912882895

theorem tailTrace_926993 : CollatzResearch.WordTrace tailWord_926993 prefixEnd_926993 317328648235597912882895 := by
  unfold tailWord_926993
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810212330670153645185633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22540141553780102430123755 33810212330670153645185633)
  ·
    refine ⟨25357659248002615233889225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33810212330670153645185633 25357659248002615233889225)
    ·
      refine ⟨19018244436001961425416919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25357659248002615233889225 19018244436001961425416919)
      ·
        refine ⟨28527366654002942138125379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19018244436001961425416919 28527366654002942138125379)
        ·
          refine ⟨42791049981004413207188069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28527366654002942138125379 42791049981004413207188069)
          ·
            refine ⟨8023321871438327476347763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42791049981004413207188069 8023321871438327476347763)
            ·
              refine ⟨12034982807157491214521645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8023321871438327476347763 12034982807157491214521645)
              ·
                refine ⟨4513118552684059205445617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12034982807157491214521645 4513118552684059205445617)
                ·
                  refine ⟨3384838914513044404084213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4513118552684059205445617 3384838914513044404084213)
                  ·
                    refine ⟨317328648235597912882895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3384838914513044404084213 317328648235597912882895)
                    ·
                      rfl

theorem cell22_926993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_926993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_926993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_926993 prefixEnd_926993 := by exact prefixLift 926993
  have htrace : WordTrace (prefixWord ++ tailWord_926993) baseStart_926993 baseEnd_926993 := by
    simpa [prefixWord, tailWord_926993, baseEnd_926993] using wordTrace_append hprefix tailTrace_926993
  have hstable : (prefixWord ++ tailWord_926993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926993).length < 2 ^ (prefixWord ++ tailWord_926993).sum := by decide
  have hdescent : baseEnd_926993 < baseStart_926993 := by decide
  rcases family_descends (prefixWord ++ tailWord_926993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927016 : List Nat := [2, 1, 5, 1, 2, 3, 1, 3, 1, 3]
def baseStart_927016 : Nat := 118140960795 + 927016 * 2 ^ 59
def prefixEnd_927016 : Nat := 4983230072969 + 3 ^ 40 * 927016 * 2
def baseEnd_927016 : Nat := 317336521605633519557825

theorem tailTrace_927016 : CollatzResearch.WordTrace tailWord_927016 prefixEnd_927016 317336521605633519557825 := by
  unfold tailWord_927016
  simp only [CollatzResearch.WordTrace]
  refine ⟨16905525604793414286636451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22540700806391219048848601 16905525604793414286636451)
  ·
    refine ⟨25358288407190121429954677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16905525604793414286636451 25358288407190121429954677)
    ·
      refine ⟨2377339538174073884058251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25358288407190121429954677 2377339538174073884058251)
      ·
        refine ⟨3566009307261110826087377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377339538174073884058251 3566009307261110826087377)
        ·
          refine ⟨2674506980445833119565533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3566009307261110826087377 2674506980445833119565533)
          ·
            refine ⟨1002940117667187419837075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2674506980445833119565533 1002940117667187419837075)
            ·
              refine ⟨1504410176500781129755613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002940117667187419837075 1504410176500781129755613)
              ·
                refine ⟨564153816187792923658355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1504410176500781129755613 564153816187792923658355)
                ·
                  refine ⟨846230724281689385487533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564153816187792923658355 846230724281689385487533)
                  ·
                    refine ⟨317336521605633519557825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846230724281689385487533 317336521605633519557825)
                    ·
                      rfl

theorem cell22_927016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_927016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927016 prefixEnd_927016 := by exact prefixLift 927016
  have htrace : WordTrace (prefixWord ++ tailWord_927016) baseStart_927016 baseEnd_927016 := by
    simpa [prefixWord, tailWord_927016, baseEnd_927016] using wordTrace_append hprefix tailTrace_927016
  have hstable : (prefixWord ++ tailWord_927016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927016).length < 2 ^ (prefixWord ++ tailWord_927016).sum := by decide
  have hdescent : baseEnd_927016 < baseStart_927016 := by decide
  rcases family_descends (prefixWord ++ tailWord_927016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927046 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_927046 : Nat := 118140960795 + 927046 * 2 ^ 59
def prefixEnd_927046 : Nat := 4983230072969 + 3 ^ 40 * 927046 * 2
def baseEnd_927046 : Nat := 105782263739574480435911

theorem tailTrace_927046 : CollatzResearch.WordTrace tailWord_927046 prefixEnd_927046 105782263739574480435911 := by
  unfold tailWord_927046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1056629543733691990527031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22541430266318762464576661 1056629543733691990527031)
  ·
    refine ⟨1584944315600537985790547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1056629543733691990527031 1584944315600537985790547)
    ·
      refine ⟨2377416473400806978685821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1584944315600537985790547 2377416473400806978685821)
      ·
        refine ⟨891531177525302617007183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2377416473400806978685821 891531177525302617007183)
        ·
          refine ⟨1337296766287953925510775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891531177525302617007183 1337296766287953925510775)
          ·
            refine ⟨2005945149431930888266163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337296766287953925510775 2005945149431930888266163)
            ·
              refine ⟨3008917724147896332399245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2005945149431930888266163 3008917724147896332399245)
              ·
                refine ⟨1128344146555461124649717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3008917724147896332399245 1128344146555461124649717)
                ·
                  refine ⟨105782263739574480435911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1128344146555461124649717 105782263739574480435911)
                  ·
                    rfl

theorem cell22_927046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_927046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927046 prefixEnd_927046 := by exact prefixLift 927046
  have htrace : WordTrace (prefixWord ++ tailWord_927046) baseStart_927046 baseEnd_927046 := by
    simpa [prefixWord, tailWord_927046, baseEnd_927046] using wordTrace_append hprefix tailTrace_927046
  have hstable : (prefixWord ++ tailWord_927046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927046).length < 2 ^ (prefixWord ++ tailWord_927046).sum := by decide
  have hdescent : baseEnd_927046 < baseStart_927046 := by decide
  rcases family_descends (prefixWord ++ tailWord_927046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927106 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_927106 : Nat := 118140960795 + 927106 * 2 ^ 59
def prefixEnd_927106 : Nat := 4983230072969 + 3 ^ 40 * 927106 * 2
def baseEnd_927106 : Nat := 317367330444903284807549

theorem tailTrace_927106 : CollatzResearch.WordTrace tailWord_927106 prefixEnd_927106 317367330444903284807549 := by
  unfold tailWord_927106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453583444815193486012293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22542889186173849296032781 8453583444815193486012293)
  ·
    refine ⟨1585046895902848778627305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8453583444815193486012293 1585046895902848778627305)
    ·
      refine ⟨1188785171927136583970479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1585046895902848778627305 1188785171927136583970479)
      ·
        refine ⟨1783177757890704875955719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188785171927136583970479 1783177757890704875955719)
        ·
          refine ⟨2674766636836057313933579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783177757890704875955719 2674766636836057313933579)
          ·
            refine ⟨4012149955254085970900369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674766636836057313933579 4012149955254085970900369)
            ·
              refine ⟨3009112466440564478175277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4012149955254085970900369 3009112466440564478175277)
              ·
                refine ⟨1128417174915211679315729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3009112466440564478175277 1128417174915211679315729)
                ·
                  refine ⟨846312881186408759486797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128417174915211679315729 846312881186408759486797)
                  ·
                    refine ⟨317367330444903284807549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846312881186408759486797 317367330444903284807549)
                    ·
                      rfl

theorem cell22_927106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_927106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927106 prefixEnd_927106 := by exact prefixLift 927106
  have htrace : WordTrace (prefixWord ++ tailWord_927106) baseStart_927106 baseEnd_927106 := by
    simpa [prefixWord, tailWord_927106, baseEnd_927106] using wordTrace_append hprefix tailTrace_927106
  have hstable : (prefixWord ++ tailWord_927106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927106).length < 2 ^ (prefixWord ++ tailWord_927106).sum := by decide
  have hdescent : baseEnd_927106 < baseStart_927106 := by decide
  rcases family_descends (prefixWord ++ tailWord_927106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927130 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_927130 : Nat := 118140960795 + 927130 * 2 ^ 59
def prefixEnd_927130 : Nat := 4983230072969 + 3 ^ 40 * 927130 * 2
def baseEnd_927130 : Nat := 105791848711791740735825

theorem tailTrace_927130 : CollatzResearch.WordTrace tailWord_927130 prefixEnd_927130 105791848711791740735825 := by
  unfold tailWord_927130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453802282793456510730711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22543472754115884028615229 8453802282793456510730711)
  ·
    refine ⟨12680703424190184766096067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8453802282793456510730711 12680703424190184766096067)
    ·
      refine ⟨19021055136285277149144101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12680703424190184766096067 19021055136285277149144101)
      ·
        refine ⟨3566447838053489465464519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19021055136285277149144101 3566447838053489465464519)
        ·
          refine ⟨5349671757080234198196779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3566447838053489465464519 5349671757080234198196779)
          ·
            refine ⟨8024507635620351297295169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5349671757080234198196779 8024507635620351297295169)
            ·
              refine ⟨6018380726715263472971377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8024507635620351297295169 6018380726715263472971377)
              ·
                refine ⟨4513785545036447604728533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6018380726715263472971377 4513785545036447604728533)
                ·
                  refine ⟨105791848711791740735825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4513785545036447604728533 105791848711791740735825)
                  ·
                    rfl

theorem cell22_927130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_927130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927130 prefixEnd_927130 := by exact prefixLift 927130
  have htrace : WordTrace (prefixWord ++ tailWord_927130) baseStart_927130 baseEnd_927130 := by
    simpa [prefixWord, tailWord_927130, baseEnd_927130] using wordTrace_append hprefix tailTrace_927130
  have hstable : (prefixWord ++ tailWord_927130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927130).length < 2 ^ (prefixWord ++ tailWord_927130).sum := by decide
  have hdescent : baseEnd_927130 < baseStart_927130 := by decide
  rcases family_descends (prefixWord ++ tailWord_927130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927160 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_927160 : Nat := 118140960795 + 927160 * 2 ^ 59
def prefixEnd_927160 : Nat := 4983230072969 + 3 ^ 40 * 927160 * 2
def baseEnd_927160 : Nat := 317385815748465143957383

theorem tailTrace_927160 : CollatzResearch.WordTrace tailWord_927160 prefixEnd_927160 317385815748465143957383 := by
  unfold tailWord_927160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16908151660532570583257467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22544202214043427444343289 16908151660532570583257467)
  ·
    refine ⟨25362227490798855874886201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16908151660532570583257467 25362227490798855874886201)
    ·
      refine ⟨19021670618099141906164651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25362227490798855874886201 19021670618099141906164651)
      ·
        refine ⟨28532505927148712859246977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19021670618099141906164651 28532505927148712859246977)
        ·
          refine ⟨21399379445361534644435233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28532505927148712859246977 21399379445361534644435233)
          ·
            refine ⟨16049534584021150983326425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21399379445361534644435233 16049534584021150983326425)
            ·
              refine ⟨12037150938015863237494819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16049534584021150983326425 12037150938015863237494819)
              ·
                refine ⟨18055726407023794856242229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12037150938015863237494819 18055726407023794856242229)
                ·
                  refine ⟨1692724350658480767772709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18055726407023794856242229 1692724350658480767772709)
                  ·
                    refine ⟨317385815748465143957383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692724350658480767772709 317385815748465143957383)
                    ·
                      rfl

theorem cell22_927160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_927160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927160 prefixEnd_927160 := by exact prefixLift 927160
  have htrace : WordTrace (prefixWord ++ tailWord_927160) baseStart_927160 baseEnd_927160 := by
    simpa [prefixWord, tailWord_927160, baseEnd_927160] using wordTrace_append hprefix tailTrace_927160
  have hstable : (prefixWord ++ tailWord_927160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927160).length < 2 ^ (prefixWord ++ tailWord_927160).sum := by decide
  have hdescent : baseEnd_927160 < baseStart_927160 := by decide
  rcases family_descends (prefixWord ++ tailWord_927160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927170 : List Nat := [3, 5, 2, 1, 1, 2, 2, 6]
def baseStart_927170 : Nat := 118140960795 + 927170 * 2 ^ 59
def prefixEnd_927170 : Nat := 4983230072969 + 3 ^ 40 * 927170 * 2
def baseEnd_927170 : Nat := 35265470994758716800817

theorem tailTrace_927170 : CollatzResearch.WordTrace tailWord_927170 prefixEnd_927170 35265470994758716800817 := by
  unfold tailWord_927170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8454167012757228218594741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22544445367352608582919309 8454167012757228218594741)
  ·
    refine ⟨792578157445990145493257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8454167012757228218594741 792578157445990145493257)
    ·
      refine ⟨594433618084492609119943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 792578157445990145493257 594433618084492609119943)
      ·
        refine ⟨891650427126738913679915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594433618084492609119943 891650427126738913679915)
        ·
          refine ⟨1337475640690108370519873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891650427126738913679915 1337475640690108370519873)
          ·
            refine ⟨1003106730517581277889905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1337475640690108370519873 1003106730517581277889905)
            ·
              refine ⟨752330047888185958417429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003106730517581277889905 752330047888185958417429)
              ·
                refine ⟨35265470994758716800817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 752330047888185958417429 35265470994758716800817)
                ·
                  rfl

theorem cell22_927170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_927170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927170 prefixEnd_927170 := by exact prefixLift 927170
  have htrace : WordTrace (prefixWord ++ tailWord_927170) baseStart_927170 baseEnd_927170 := by
    simpa [prefixWord, tailWord_927170, baseEnd_927170] using wordTrace_append hprefix tailTrace_927170
  have hstable : (prefixWord ++ tailWord_927170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927170).length < 2 ^ (prefixWord ++ tailWord_927170).sum := by decide
  have hdescent : baseEnd_927170 < baseStart_927170 := by decide
  rcases family_descends (prefixWord ++ tailWord_927170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927175 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 6]
def baseStart_927175 : Nat := 118140960795 + 927175 * 2 ^ 59
def prefixEnd_927175 : Nat := 4983230072969 + 3 ^ 40 * 927175 * 2
def baseEnd_927175 : Nat := 105796983518336701610779

theorem tailTrace_927175 : CollatzResearch.WordTrace tailWord_927175 prefixEnd_927175 105796983518336701610779 := by
  unfold tailWord_927175
  simp only [CollatzResearch.WordTrace]
  refine ⟨33816850416010798728310979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22544566944007199152207319 33816850416010798728310979)
  ·
    refine ⟨50725275624016198092466469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33816850416010798728310979 50725275624016198092466469)
    ·
      refine ⟨9510989179503037142337463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50725275624016198092466469 9510989179503037142337463)
      ·
        refine ⟨14266483769254555713506195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9510989179503037142337463 14266483769254555713506195)
        ·
          refine ⟨21399725653881833570259293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14266483769254555713506195 21399725653881833570259293)
          ·
            refine ⟨8024897120205687588847235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21399725653881833570259293 8024897120205687588847235)
            ·
              refine ⟨12037345680308531383270853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8024897120205687588847235 12037345680308531383270853)
              ·
                refine ⟨2257002315057849634363285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12037345680308531383270853 2257002315057849634363285)
                ·
                  refine ⟨105796983518336701610779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2257002315057849634363285 105796983518336701610779)
                  ·
                    rfl

theorem cell22_927175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 6].length) (baseStart_927175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927175 prefixEnd_927175 := by exact prefixLift 927175
  have htrace : WordTrace (prefixWord ++ tailWord_927175) baseStart_927175 baseEnd_927175 := by
    simpa [prefixWord, tailWord_927175, baseEnd_927175] using wordTrace_append hprefix tailTrace_927175
  have hstable : (prefixWord ++ tailWord_927175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927175).length < 2 ^ (prefixWord ++ tailWord_927175).sum := by decide
  have hdescent : baseEnd_927175 < baseStart_927175 := by decide
  rcases family_descends (prefixWord ++ tailWord_927175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927224 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 2, 3]
def baseStart_927224 : Nat := 118140960795 + 927224 * 2 ^ 59
def prefixEnd_927224 : Nat := 4983230072969 + 3 ^ 40 * 927224 * 2
def baseEnd_927224 : Nat := 317407724256390310357187

theorem tailTrace_927224 : CollatzResearch.WordTrace tailWord_927224 prefixEnd_927224 317407724256390310357187 := by
  unfold tailWord_927224
  simp only [CollatzResearch.WordTrace]
  refine ⟨16909318796416640048422363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22545758395222186731229817 16909318796416640048422363)
  ·
    refine ⟨25363978194624960072633545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16909318796416640048422363 25363978194624960072633545)
    ·
      refine ⟨19022983645968720054475159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25363978194624960072633545 19022983645968720054475159)
      ·
        refine ⟨28534475468953080081712739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19022983645968720054475159 28534475468953080081712739)
        ·
          refine ⟨42801713203429620122569109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28534475468953080081712739 42801713203429620122569109)
          ·
            refine ⟨2006330306410763443245427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42801713203429620122569109 2006330306410763443245427)
            ·
              refine ⟨3009495459616145164868141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006330306410763443245427 3009495459616145164868141)
              ·
                refine ⟨1128560797356054436825553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3009495459616145164868141 1128560797356054436825553)
                ·
                  refine ⟨846420598017040827619165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128560797356054436825553 846420598017040827619165)
                  ·
                    refine ⟨317407724256390310357187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846420598017040827619165 317407724256390310357187)
                    ·
                      rfl

theorem cell22_927224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_927224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927224 prefixEnd_927224 := by exact prefixLift 927224
  have htrace : WordTrace (prefixWord ++ tailWord_927224) baseStart_927224 baseEnd_927224 := by
    simpa [prefixWord, tailWord_927224, baseEnd_927224] using wordTrace_append hprefix tailTrace_927224
  have hstable : (prefixWord ++ tailWord_927224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927224).length < 2 ^ (prefixWord ++ tailWord_927224).sum := by decide
  have hdescent : baseEnd_927224 < baseStart_927224 := by decide
  rcases family_descends (prefixWord ++ tailWord_927224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927239 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 2, 4]
def baseStart_927239 : Nat := 118140960795 + 927239 * 2 ^ 59
def prefixEnd_927239 : Nat := 4983230072969 + 3 ^ 40 * 927239 * 2
def baseEnd_927239 : Nat := 317412859062935271232141

theorem tailTrace_927239 : CollatzResearch.WordTrace tailWord_927239 prefixEnd_927239 317412859062935271232141 := by
  unfold tailWord_927239
  simp only [CollatzResearch.WordTrace]
  refine ⟨33819184687778937658640771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22546123125185958439093847 33819184687778937658640771)
  ·
    refine ⟨50728777031668406487961157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33819184687778937658640771 50728777031668406487961157)
    ·
      refine ⟨9511645693437826216492717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50728777031668406487961157 9511645693437826216492717)
      ·
        refine ⟨3566867135039184831184769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9511645693437826216492717 3566867135039184831184769)
        ·
          refine ⟨2675150351279388623388577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3566867135039184831184769 2675150351279388623388577)
          ·
            refine ⟨2006362763459541467541433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2675150351279388623388577 2006362763459541467541433)
            ·
              refine ⟨1504772072594656100656075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006362763459541467541433 1504772072594656100656075)
              ·
                refine ⟨2257158108891984150984113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504772072594656100656075 2257158108891984150984113)
                ·
                  refine ⟨1692868581668988113238085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2257158108891984150984113 1692868581668988113238085)
                  ·
                    refine ⟨317412859062935271232141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692868581668988113238085 317412859062935271232141)
                    ·
                      rfl

theorem cell22_927239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_927239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927239 prefixEnd_927239 := by exact prefixLift 927239
  have htrace : WordTrace (prefixWord ++ tailWord_927239) baseStart_927239 baseEnd_927239 := by
    simpa [prefixWord, tailWord_927239, baseEnd_927239] using wordTrace_append hprefix tailTrace_927239
  have hstable : (prefixWord ++ tailWord_927239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927239).length < 2 ^ (prefixWord ++ tailWord_927239).sum := by decide
  have hdescent : baseEnd_927239 < baseStart_927239 := by decide
  rcases family_descends (prefixWord ++ tailWord_927239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927245 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_927245 : Nat := 118140960795 + 927245 * 2 ^ 59
def prefixEnd_927245 : Nat := 4983230072969 + 3 ^ 40 * 927245 * 2
def baseEnd_927245 : Nat := 317414912985553255582123

theorem tailTrace_927245 : CollatzResearch.WordTrace tailWord_927245 prefixEnd_927245 317414912985553255582123 := by
  unfold tailWord_927245
  simp only [CollatzResearch.WordTrace]
  refine ⟨33819403525757200683359189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22546269017171467122239459 33819403525757200683359189)
  ·
    refine ⟨792642270134934391016231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 33819403525757200683359189 792642270134934391016231)
    ·
      refine ⟨1188963405202401586524347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 792642270134934391016231 1188963405202401586524347)
      ·
        refine ⟨1783445107803602379786521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188963405202401586524347 1783445107803602379786521)
        ·
          refine ⟨1337583830852701784839891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1783445107803602379786521 1337583830852701784839891)
          ·
            refine ⟨2006375746279052677259837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337583830852701784839891 2006375746279052677259837)
            ·
              refine ⟨752390904854644753972439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2006375746279052677259837 752390904854644753972439)
              ·
                refine ⟨1128586357281967130958659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752390904854644753972439 1128586357281967130958659)
                ·
                  refine ⟨1692879535922950696437989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128586357281967130958659 1692879535922950696437989)
                  ·
                    refine ⟨317414912985553255582123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692879535922950696437989 317414912985553255582123)
                    ·
                      rfl

theorem cell22_927245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_927245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927245 prefixEnd_927245 := by exact prefixLift 927245
  have htrace : WordTrace (prefixWord ++ tailWord_927245) baseStart_927245 baseEnd_927245 := by
    simpa [prefixWord, tailWord_927245, baseEnd_927245] using wordTrace_append hprefix tailTrace_927245
  have hstable : (prefixWord ++ tailWord_927245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927245).length < 2 ^ (prefixWord ++ tailWord_927245).sum := by decide
  have hdescent : baseEnd_927245 < baseStart_927245 := by decide
  rcases family_descends (prefixWord ++ tailWord_927245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927297 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_927297 : Nat := 118140960795 + 927297 * 2 ^ 59
def prefixEnd_927297 : Nat := 4983230072969 + 3 ^ 40 * 927297 * 2
def baseEnd_927297 : Nat := 317432713648242453281963

theorem tailTrace_927297 : CollatzResearch.WordTrace tailWord_927297 prefixEnd_927297 317432713648242453281963 := by
  unfold tailWord_927297
  simp only [CollatzResearch.WordTrace]
  refine ⟨33821300121568813564252145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22547533414379209042834763 33821300121568813564252145)
  ·
    refine ⟨25365975091176610173189109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33821300121568813564252145 25365975091176610173189109)
    ·
      refine ⟨2378060164797807203736479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25365975091176610173189109 2378060164797807203736479)
      ·
        refine ⟨3567090247196710805604719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378060164797807203736479 3567090247196710805604719)
        ·
          refine ⟨5350635370795066208407079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567090247196710805604719 5350635370795066208407079)
          ·
            refine ⟨8025953056192599312610619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350635370795066208407079 8025953056192599312610619)
            ·
              refine ⟨12038929584288898968915929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8025953056192599312610619 12038929584288898968915929)
              ·
                refine ⟨9029197188216674226686947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12038929584288898968915929 9029197188216674226686947)
                ·
                  refine ⟨13543795782325011340030421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9029197188216674226686947 13543795782325011340030421)
                  ·
                    refine ⟨317432713648242453281963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13543795782325011340030421 317432713648242453281963)
                    ·
                      rfl

theorem cell22_927297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_927297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927297 prefixEnd_927297 := by exact prefixLift 927297
  have htrace : WordTrace (prefixWord ++ tailWord_927297) baseStart_927297 baseEnd_927297 := by
    simpa [prefixWord, tailWord_927297, baseEnd_927297] using wordTrace_append hprefix tailTrace_927297
  have hstable : (prefixWord ++ tailWord_927297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927297).length < 2 ^ (prefixWord ++ tailWord_927297).sum := by decide
  have hdescent : baseEnd_927297 < baseStart_927297 := by decide
  rcases family_descends (prefixWord ++ tailWord_927297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927303 : List Nat := [1, 1, 4, 1, 5, 1, 2, 3, 1, 3]
def baseStart_927303 : Nat := 118140960795 + 927303 * 2 ^ 59
def prefixEnd_927303 : Nat := 4983230072969 + 3 ^ 40 * 927303 * 2
def baseEnd_927303 : Nat := 317434767570860437631945

theorem tailTrace_927303 : CollatzResearch.WordTrace tailWord_927303 prefixEnd_927303 317434767570860437631945 := by
  unfold tailWord_927303
  simp only [CollatzResearch.WordTrace]
  refine ⟨33821518959547076588970563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22547679306364717725980375 33821518959547076588970563)
  ·
    refine ⟨50732278439320614883455845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33821518959547076588970563 50732278439320614883455845)
    ·
      refine ⟨9512302207372615290647971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50732278439320614883455845 9512302207372615290647971)
      ·
        refine ⟨14268453311058922935971957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9512302207372615290647971 14268453311058922935971957)
        ·
          refine ⟨1337667497911774025247371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14268453311058922935971957 1337667497911774025247371)
          ·
            refine ⟨2006501246867661037871057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337667497911774025247371 2006501246867661037871057)
            ·
              refine ⟨1504875935150745778403293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006501246867661037871057 1504875935150745778403293)
              ·
                refine ⟨564328475681529666901235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1504875935150745778403293 564328475681529666901235)
                ·
                  refine ⟨846492713522294500351853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564328475681529666901235 846492713522294500351853)
                  ·
                    refine ⟨317434767570860437631945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846492713522294500351853 317434767570860437631945)
                    ·
                      rfl

theorem cell22_927303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_927303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927303 prefixEnd_927303 := by exact prefixLift 927303
  have htrace : WordTrace (prefixWord ++ tailWord_927303) baseStart_927303 baseEnd_927303 := by
    simpa [prefixWord, tailWord_927303, baseEnd_927303] using wordTrace_append hprefix tailTrace_927303
  have hstable : (prefixWord ++ tailWord_927303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927303).length < 2 ^ (prefixWord ++ tailWord_927303).sum := by decide
  have hdescent : baseEnd_927303 < baseStart_927303 := by decide
  rcases family_descends (prefixWord ++ tailWord_927303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927346 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_927346 : Nat := 118140960795 + 927346 * 2 ^ 59
def prefixEnd_927346 : Nat := 4983230072969 + 3 ^ 40 * 927346 * 2
def baseEnd_927346 : Nat := 317449487349622658806813

theorem tailTrace_927346 : CollatzResearch.WordTrace tailWord_927346 prefixEnd_927346 317449487349622658806813 := by
  unfold tailWord_927346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8455771824597823733196473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22548724865594196621857261 8455771824597823733196473)
  ·
    refine ⟨6341828868448367799897355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8455771824597823733196473 6341828868448367799897355)
    ·
      refine ⟨9512743302672551699846033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6341828868448367799897355 9512743302672551699846033)
      ·
        refine ⟨7134557477004413774884525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9512743302672551699846033 7134557477004413774884525)
        ·
          refine ⟨2675459053876655165581697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7134557477004413774884525 2675459053876655165581697)
          ·
            refine ⟨2006594290407491374186273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2675459053876655165581697 2006594290407491374186273)
            ·
              refine ⟨1504945717805618530639705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006594290407491374186273 1504945717805618530639705)
              ·
                refine ⟨1128709288354213897979779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504945717805618530639705 1128709288354213897979779)
                ·
                  refine ⟨1693063932531320846969669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128709288354213897979779 1693063932531320846969669)
                  ·
                    refine ⟨317449487349622658806813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1693063932531320846969669 317449487349622658806813)
                    ·
                      rfl

theorem cell22_927346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_927346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927346 prefixEnd_927346 := by exact prefixLift 927346
  have htrace : WordTrace (prefixWord ++ tailWord_927346) baseStart_927346 baseEnd_927346 := by
    simpa [prefixWord, tailWord_927346, baseEnd_927346] using wordTrace_append hprefix tailTrace_927346
  have hstable : (prefixWord ++ tailWord_927346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927346).length < 2 ^ (prefixWord ++ tailWord_927346).sum := by decide
  have hdescent : baseEnd_927346 < baseStart_927346 := by decide
  rcases family_descends (prefixWord ++ tailWord_927346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927361 : List Nat := [1, 2, 4, 2, 1, 2, 3, 3, 4]
def baseStart_927361 : Nat := 118140960795 + 927361 * 2 ^ 59
def prefixEnd_927361 : Nat := 4983230072969 + 3 ^ 40 * 927361 * 2
def baseEnd_927361 : Nat := 105818207385389206560589

theorem tailTrace_927361 : CollatzResearch.WordTrace tailWord_927361 prefixEnd_927361 105818207385389206560589 := by
  unfold tailWord_927361
  simp only [CollatzResearch.WordTrace]
  refine ⟨33823634393336952494581937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22549089595557968329721291 33823634393336952494581937)
  ·
    refine ⟨25367725795002714370936453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33823634393336952494581937 25367725795002714370936453)
    ·
      refine ⟨4756448586563008944550585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25367725795002714370936453 4756448586563008944550585)
      ·
        refine ⟨3567336439922256708412939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4756448586563008944550585 3567336439922256708412939)
        ·
          refine ⟨5351004659883385062619409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567336439922256708412939 5351004659883385062619409)
          ·
            refine ⟨4013253494912538796964557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5351004659883385062619409 4013253494912538796964557)
            ·
              refine ⟨1504970060592202048861709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4013253494912538796964557 1504970060592202048861709)
              ·
                refine ⟨564363772722075768323141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1504970060592202048861709 564363772722075768323141)
                ·
                  refine ⟨105818207385389206560589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564363772722075768323141 105818207385389206560589)
                  ·
                    rfl

theorem cell22_927361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 4].length) (baseStart_927361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927361 prefixEnd_927361 := by exact prefixLift 927361
  have htrace : WordTrace (prefixWord ++ tailWord_927361) baseStart_927361 baseEnd_927361 := by
    simpa [prefixWord, tailWord_927361, baseEnd_927361] using wordTrace_append hprefix tailTrace_927361
  have hstable : (prefixWord ++ tailWord_927361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927361).length < 2 ^ (prefixWord ++ tailWord_927361).sum := by decide
  have hdescent : baseEnd_927361 < baseStart_927361 := by decide
  rcases family_descends (prefixWord ++ tailWord_927361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927374 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_927374 : Nat := 118140960795 + 927374 * 2 ^ 59
def prefixEnd_927374 : Nat := 4983230072969 + 3 ^ 40 * 927374 * 2
def baseEnd_927374 : Nat := 317459072321839919106727

theorem tailTrace_927374 : CollatzResearch.WordTrace tailWord_927374 prefixEnd_927374 317459072321839919106727 := by
  unfold tailWord_927374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228013567786231964350647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22549405694859903809870117 4228013567786231964350647)
  ·
    refine ⟨6342020351679347946525971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4228013567786231964350647 6342020351679347946525971)
    ·
      refine ⟨9513030527519021919788957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6342020351679347946525971 9513030527519021919788957)
      ·
        refine ⟨3567386447819633219920859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9513030527519021919788957 3567386447819633219920859)
        ·
          refine ⟨5351079671729449829881289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567386447819633219920859 5351079671729449829881289)
          ·
            refine ⟨4013309753797087372410967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5351079671729449829881289 4013309753797087372410967)
            ·
              refine ⟨6019964630695631058616451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013309753797087372410967 6019964630695631058616451)
              ·
                refine ⟨9029946946043446587924677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019964630695631058616451 9029946946043446587924677)
                ·
                  refine ⟨1693115052383146235235877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9029946946043446587924677 1693115052383146235235877)
                  ·
                    refine ⟨317459072321839919106727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1693115052383146235235877 317459072321839919106727)
                    ·
                      rfl

theorem cell22_927374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_927374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927374 prefixEnd_927374 := by exact prefixLift 927374
  have htrace : WordTrace (prefixWord ++ tailWord_927374) baseStart_927374 baseEnd_927374 := by
    simpa [prefixWord, tailWord_927374, baseEnd_927374] using wordTrace_append hprefix tailTrace_927374
  have hstable : (prefixWord ++ tailWord_927374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927374).length < 2 ^ (prefixWord ++ tailWord_927374).sum := by decide
  have hdescent : baseEnd_927374 < baseStart_927374 := by decide
  rcases family_descends (prefixWord ++ tailWord_927374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927378 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_927378 : Nat := 118140960795 + 927378 * 2 ^ 59
def prefixEnd_927378 : Nat := 4983230072969 + 3 ^ 40 * 927378 * 2
def baseEnd_927378 : Nat := 105820147201195080668905

theorem tailTrace_927378 : CollatzResearch.WordTrace tailWord_927378 prefixEnd_927378 105820147201195080668905 := by
  unfold tailWord_927378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8456063608568841099487697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22549502956183576265300525 8456063608568841099487697)
  ·
    refine ⟨6342047706426630824615773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8456063608568841099487697 6342047706426630824615773)
    ·
      refine ⟨2378267889909986559230915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6342047706426630824615773 2378267889909986559230915)
      ·
        refine ⟨3567401834864979838846373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378267889909986559230915 3567401834864979838846373)
        ·
          refine ⟨668887844037183719783695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3567401834864979838846373 668887844037183719783695)
          ·
            refine ⟨1003331766055775579675543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668887844037183719783695 1003331766055775579675543)
            ·
              refine ⟨1504997649083663369513315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003331766055775579675543 1504997649083663369513315)
              ·
                refine ⟨2257496473625495054269973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504997649083663369513315 2257496473625495054269973)
                ·
                  refine ⟨105820147201195080668905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2257496473625495054269973 105820147201195080668905)
                  ·
                    rfl

theorem cell22_927378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_927378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927378 prefixEnd_927378 := by exact prefixLift 927378
  have htrace : WordTrace (prefixWord ++ tailWord_927378) baseStart_927378 baseEnd_927378 := by
    simpa [prefixWord, tailWord_927378, baseEnd_927378] using wordTrace_append hprefix tailTrace_927378
  have hstable : (prefixWord ++ tailWord_927378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927378).length < 2 ^ (prefixWord ++ tailWord_927378).sum := by decide
  have hdescent : baseEnd_927378 < baseStart_927378 := by decide
  rcases family_descends (prefixWord ++ tailWord_927378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927393 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 2, 3]
def baseStart_927393 : Nat := 118140960795 + 927393 * 2 ^ 59
def prefixEnd_927393 : Nat := 4983230072969 + 3 ^ 40 * 927393 * 2
def baseEnd_927393 : Nat := 317465576410130202881669

theorem tailTrace_927393 : CollatzResearch.WordTrace tailWord_927393 prefixEnd_927393 317465576410130202881669 := by
  unfold tailWord_927393
  simp only [CollatzResearch.WordTrace]
  refine ⟨33824801529221021959746833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22549867686147347973164555 33824801529221021959746833)
  ·
    refine ⟨25368601146915766469810125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33824801529221021959746833 25368601146915766469810125)
    ·
      refine ⟨9513225430093412426178797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25368601146915766469810125 9513225430093412426178797)
      ·
        refine ⟨3567459536285029659817049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9513225430093412426178797 3567459536285029659817049)
        ·
          refine ⟨2675594652213772244862787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3567459536285029659817049 2675594652213772244862787)
          ·
            refine ⟨4013391978320658367294181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675594652213772244862787 4013391978320658367294181)
            ·
              refine ⟨752510995935123443867659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4013391978320658367294181 752510995935123443867659)
              ·
                refine ⟨1128766493902685165801489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752510995935123443867659 1128766493902685165801489)
                ·
                  refine ⟨846574870427013874351117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128766493902685165801489 846574870427013874351117)
                  ·
                    refine ⟨317465576410130202881669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846574870427013874351117 317465576410130202881669)
                    ·
                      rfl

theorem cell22_927393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_927393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927393 prefixEnd_927393 := by exact prefixLift 927393
  have htrace : WordTrace (prefixWord ++ tailWord_927393) baseStart_927393 baseEnd_927393 := by
    simpa [prefixWord, tailWord_927393, baseEnd_927393] using wordTrace_append hprefix tailTrace_927393
  have hstable : (prefixWord ++ tailWord_927393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927393).length < 2 ^ (prefixWord ++ tailWord_927393).sum := by decide
  have hdescent : baseEnd_927393 < baseStart_927393 := by decide
  rcases family_descends (prefixWord ++ tailWord_927393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927417 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 9]
def baseStart_927417 : Nat := 118140960795 + 927417 * 2 ^ 59
def prefixEnd_927417 : Nat := 4983230072969 + 3 ^ 40 * 927417 * 2
def baseEnd_927417 : Nat := 105824597366867380093865

theorem tailTrace_927417 : CollatzResearch.WordTrace tailWord_927417 prefixEnd_927417 105824597366867380093865 := by
  unfold tailWord_927417
  simp only [CollatzResearch.WordTrace]
  refine ⟨33825676881134074058620505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22550451254089382705747003 33825676881134074058620505)
  ·
    refine ⟨25369257660850555543965379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33825676881134074058620505 25369257660850555543965379)
    ·
      refine ⟨38053886491275833315948069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25369257660850555543965379 38053886491275833315948069)
      ·
        refine ⟨7135103717114218746740263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38053886491275833315948069 7135103717114218746740263)
        ·
          refine ⟨10702655575671328120110395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135103717114218746740263 10702655575671328120110395)
          ·
            refine ⟨16053983363506992180165593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10702655575671328120110395 16053983363506992180165593)
            ·
              refine ⟨12040487522630244135124195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16053983363506992180165593 12040487522630244135124195)
              ·
                refine ⟨18060731283945366202686293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12040487522630244135124195 18060731283945366202686293)
                ·
                  refine ⟨105824597366867380093865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18060731283945366202686293 105824597366867380093865)
                  ·
                    rfl

theorem cell22_927417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_927417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927417 prefixEnd_927417 := by exact prefixLift 927417
  have htrace : WordTrace (prefixWord ++ tailWord_927417) baseStart_927417 baseEnd_927417 := by
    simpa [prefixWord, tailWord_927417, baseEnd_927417] using wordTrace_append hprefix tailTrace_927417
  have hstable : (prefixWord ++ tailWord_927417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927417).length < 2 ^ (prefixWord ++ tailWord_927417).sum := by decide
  have hdescent : baseEnd_927417 < baseStart_927417 := by decide
  rcases family_descends (prefixWord ++ tailWord_927417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927438 : List Nat := [4, 1, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_927438 : Nat := 118140960795 + 927438 * 2 ^ 59
def prefixEnd_927438 : Nat := 4983230072969 + 3 ^ 40 * 927438 * 2
def baseEnd_927438 : Nat := 317480980829765085506531

theorem tailTrace_927438 : CollatzResearch.WordTrace tailWord_927438 prefixEnd_927438 317480980829765085506531 := by
  unfold tailWord_927438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228305351757249330641871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22550961876038663096756645 4228305351757249330641871)
  ·
    refine ⟨6342458027635873995962807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4228305351757249330641871 6342458027635873995962807)
    ·
      refine ⟨9513687041453810993944211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6342458027635873995962807 9513687041453810993944211)
      ·
        refine ⟨14270530562180716490916317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9513687041453810993944211 14270530562180716490916317)
        ·
          refine ⟨5351448960817768684093619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14270530562180716490916317 5351448960817768684093619)
          ·
            refine ⟨8027173441226653026140429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351448960817768684093619 8027173441226653026140429)
            ·
              refine ⟨3010190040459994884802661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8027173441226653026140429 3010190040459994884802661)
              ·
                refine ⟨564410632586249040900499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3010190040459994884802661 564410632586249040900499)
                ·
                  refine ⟨846615948879373561350749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564410632586249040900499 846615948879373561350749)
                  ·
                    refine ⟨317480980829765085506531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846615948879373561350749 317480980829765085506531)
                    ·
                      rfl

theorem cell22_927438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_927438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927438 prefixEnd_927438 := by exact prefixLift 927438
  have htrace : WordTrace (prefixWord ++ tailWord_927438) baseStart_927438 baseEnd_927438 := by
    simpa [prefixWord, tailWord_927438, baseEnd_927438] using wordTrace_append hprefix tailTrace_927438
  have hstable : (prefixWord ++ tailWord_927438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927438).length < 2 ^ (prefixWord ++ tailWord_927438).sum := by decide
  have hdescent : baseEnd_927438 < baseStart_927438 := by decide
  rcases family_descends (prefixWord ++ tailWord_927438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927449 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_927449 : Nat := 118140960795 + 927449 * 2 ^ 59
def prefixEnd_927449 : Nat := 4983230072969 + 3 ^ 40 * 927449 * 2
def baseEnd_927449 : Nat := 317484746354564723481497

theorem tailTrace_927449 : CollatzResearch.WordTrace tailWord_927449 prefixEnd_927449 317484746354564723481497 := by
  unfold tailWord_927449
  simp only [CollatzResearch.WordTrace]
  refine ⟨33826844017018143523785401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22551229344678762349190267 33826844017018143523785401)
  ·
    refine ⟨25370133012763607642839051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33826844017018143523785401 25370133012763607642839051)
    ·
      refine ⟨38055199519145411464258577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25370133012763607642839051 38055199519145411464258577)
      ·
        refine ⟨28541399639359058598193933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38055199519145411464258577 28541399639359058598193933)
        ·
          refine ⟨10703024864759646974322725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28541399639359058598193933 10703024864759646974322725)
          ·
            refine ⟨2006817162142433807685511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10703024864759646974322725 2006817162142433807685511)
            ·
              refine ⟨3010225743213650711528267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006817162142433807685511 3010225743213650711528267)
              ·
                refine ⟨4515338614820476067292401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010225743213650711528267 4515338614820476067292401)
                ·
                  refine ⟨3386503961115357050469301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4515338614820476067292401 3386503961115357050469301)
                  ·
                    refine ⟨317484746354564723481497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3386503961115357050469301 317484746354564723481497)
                    ·
                      rfl

theorem cell22_927449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_927449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927449 prefixEnd_927449 := by exact prefixLift 927449
  have htrace : WordTrace (prefixWord ++ tailWord_927449) baseStart_927449 baseEnd_927449 := by
    simpa [prefixWord, tailWord_927449, baseEnd_927449] using wordTrace_append hprefix tailTrace_927449
  have hstable : (prefixWord ++ tailWord_927449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927449).length < 2 ^ (prefixWord ++ tailWord_927449).sum := by decide
  have hdescent : baseEnd_927449 < baseStart_927449 := by decide
  rcases family_descends (prefixWord ++ tailWord_927449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927496 : List Nat := [2, 1, 3, 2, 2, 1, 1, 6, 4]
def baseStart_927496 : Nat := 118140960795 + 927496 * 2 ^ 59
def prefixEnd_927496 : Nat := 4983230072969 + 3 ^ 40 * 927496 * 2
def baseEnd_927496 : Nat := 105833611805024089185451

theorem tailTrace_927496 : CollatzResearch.WordTrace tailWord_927496 prefixEnd_927496 105833611805024089185451 := by
  unfold tailWord_927496
  simp only [CollatzResearch.WordTrace]
  refine ⟨16914279123923935275373171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22552372165231913700497561 16914279123923935275373171)
  ·
    refine ⟨25371418685885902913059757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16914279123923935275373171 25371418685885902913059757)
    ·
      refine ⟨9514282007207213592397409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25371418685885902913059757 9514282007207213592397409)
      ·
        refine ⟨7135711505405410194298057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9514282007207213592397409 7135711505405410194298057)
        ·
          refine ⟨5351783629054057645723543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7135711505405410194298057 5351783629054057645723543)
          ·
            refine ⟨8027675443581086468585315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351783629054057645723543 8027675443581086468585315)
            ·
              refine ⟨12041513165371629702877973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8027675443581086468585315 12041513165371629702877973)
              ·
                refine ⟨564445929626795142322405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12041513165371629702877973 564445929626795142322405)
                ·
                  refine ⟨105833611805024089185451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564445929626795142322405 105833611805024089185451)
                  ·
                    rfl

theorem cell22_927496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 4].length) (baseStart_927496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927496 prefixEnd_927496 := by exact prefixLift 927496
  have htrace : WordTrace (prefixWord ++ tailWord_927496) baseStart_927496 baseEnd_927496 := by
    simpa [prefixWord, tailWord_927496, baseEnd_927496] using wordTrace_append hprefix tailTrace_927496
  have hstable : (prefixWord ++ tailWord_927496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927496).length < 2 ^ (prefixWord ++ tailWord_927496).sum := by decide
  have hdescent : baseEnd_927496 < baseStart_927496 := by decide
  rcases family_descends (prefixWord ++ tailWord_927496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927509 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_927509 : Nat := 118140960795 + 927509 * 2 ^ 59
def prefixEnd_927509 : Nat := 4983230072969 + 3 ^ 40 * 927509 * 2
def baseEnd_927509 : Nat := 317505285580744566981313

theorem tailTrace_927509 : CollatzResearch.WordTrace tailWord_927509 prefixEnd_927509 317505285580744566981313 := by
  unfold tailWord_927509
  simp only [CollatzResearch.WordTrace]
  refine ⟨33829032396800773770969581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22552688264533849180646387 33829032396800773770969581)
  ·
    refine ⟨12685887148800290164113593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33829032396800773770969581 12685887148800290164113593)
    ·
      refine ⟨9514415361600217623085195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12685887148800290164113593 9514415361600217623085195)
      ·
        refine ⟨14271623042400326434627793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9514415361600217623085195 14271623042400326434627793)
        ·
          refine ⟨10703717281800244825970845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14271623042400326434627793 10703717281800244825970845)
          ·
            refine ⟨4013893980675091809739067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10703717281800244825970845 4013893980675091809739067)
            ·
              refine ⟨6020840971012637714608601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013893980675091809739067 6020840971012637714608601)
              ·
                refine ⟨4515630728259478285956451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6020840971012637714608601 4515630728259478285956451)
                ·
                  refine ⟨6773446092389217428934677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515630728259478285956451 6773446092389217428934677)
                  ·
                    refine ⟨317505285580744566981313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6773446092389217428934677 317505285580744566981313)
                    ·
                      rfl

theorem cell22_927509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_927509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927509 prefixEnd_927509 := by exact prefixLift 927509
  have htrace : WordTrace (prefixWord ++ tailWord_927509) baseStart_927509 baseEnd_927509 := by
    simpa [prefixWord, tailWord_927509, baseEnd_927509] using wordTrace_append hprefix tailTrace_927509
  have hstable : (prefixWord ++ tailWord_927509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927509).length < 2 ^ (prefixWord ++ tailWord_927509).sum := by decide
  have hdescent : baseEnd_927509 < baseStart_927509 := by decide
  rcases family_descends (prefixWord ++ tailWord_927509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927511 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 1, 5]
def baseStart_927511 : Nat := 118140960795 + 927511 * 2 ^ 59
def prefixEnd_927511 : Nat := 4983230072969 + 3 ^ 40 * 927511 * 2
def baseEnd_927511 : Nat := 317505970221617228431307

theorem tailTrace_927511 : CollatzResearch.WordTrace tailWord_927511 prefixEnd_927511 317505970221617228431307 := by
  unfold tailWord_927511
  simp only [CollatzResearch.WordTrace]
  refine ⟨33829105342793528112542387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22552736895195685408361591 33829105342793528112542387)
  ·
    refine ⟨50743658014190292168813581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33829105342793528112542387 50743658014190292168813581)
    ·
      refine ⟨19028871755321359563305093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50743658014190292168813581 19028871755321359563305093)
      ·
        refine ⟨3567913454122754918119705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19028871755321359563305093 3567913454122754918119705)
        ·
          refine ⟨2675935090592066188589779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3567913454122754918119705 2675935090592066188589779)
          ·
            refine ⟨4013902635888099282884669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675935090592066188589779 4013902635888099282884669)
            ·
              refine ⟨1505213488458037231081751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4013902635888099282884669 1505213488458037231081751)
              ·
                refine ⟨2257820232687055846622627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505213488458037231081751 2257820232687055846622627)
                ·
                  refine ⟨3386730349030583769933941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2257820232687055846622627 3386730349030583769933941)
                  ·
                    refine ⟨317505970221617228431307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3386730349030583769933941 317505970221617228431307)
                    ·
                      rfl

theorem cell22_927511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_927511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927511 prefixEnd_927511 := by exact prefixLift 927511
  have htrace : WordTrace (prefixWord ++ tailWord_927511) baseStart_927511 baseEnd_927511 := by
    simpa [prefixWord, tailWord_927511, baseEnd_927511] using wordTrace_append hprefix tailTrace_927511
  have hstable : (prefixWord ++ tailWord_927511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927511).length < 2 ^ (prefixWord ++ tailWord_927511).sum := by decide
  have hdescent : baseEnd_927511 < baseStart_927511 := by decide
  rcases family_descends (prefixWord ++ tailWord_927511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927541 : List Nat := [1, 3, 3, 1, 4, 2, 8]
def baseStart_927541 : Nat := 118140960795 + 927541 * 2 ^ 59
def prefixEnd_927541 : Nat := 4983230072969 + 3 ^ 40 * 927541 * 2
def baseEnd_927541 : Nat := 11759860734618783340045

theorem tailTrace_927541 : CollatzResearch.WordTrace tailWord_927541 prefixEnd_927541 11759860734618783340045 := by
  unfold tailWord_927541
  simp only [CollatzResearch.WordTrace]
  refine ⟨33830199532684843236134477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22553466355123228824089651 33830199532684843236134477)
  ·
    refine ⟨12686324824756816213550429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33830199532684843236134477 12686324824756816213550429)
    ·
      refine ⟨4757371809283806080081411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12686324824756816213550429 4757371809283806080081411)
      ·
        refine ⟨7136057713925709120122117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757371809283806080081411 7136057713925709120122117)
        ·
          refine ⟨1338010821361070460022897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7136057713925709120122117 1338010821361070460022897)
          ·
            refine ⟨1003508116020802845017173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338010821361070460022897 1003508116020802845017173)
            ·
              refine ⟨11759860734618783340045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1003508116020802845017173 11759860734618783340045)
              ·
                rfl

theorem cell22_927541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 8].length) (baseStart_927541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927541 prefixEnd_927541 := by exact prefixLift 927541
  have htrace : WordTrace (prefixWord ++ tailWord_927541) baseStart_927541 baseEnd_927541 := by
    simpa [prefixWord, tailWord_927541, baseEnd_927541] using wordTrace_append hprefix tailTrace_927541
  have hstable : (prefixWord ++ tailWord_927541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927541).length < 2 ^ (prefixWord ++ tailWord_927541).sum := by decide
  have hdescent : baseEnd_927541 < baseStart_927541 := by decide
  rcases family_descends (prefixWord ++ tailWord_927541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927558 : List Nat := [6, 1, 1, 2, 1, 1, 1, 9]
def baseStart_927558 : Nat := 118140960795 + 927558 * 2 ^ 59
def prefixEnd_927558 : Nat := 4983230072969 + 3 ^ 40 * 927558 * 2
def baseEnd_927558 : Nat := 35280228809124974722907

theorem tailTrace_927558 : CollatzResearch.WordTrace tailWord_927558 prefixEnd_927558 35280228809124974722907 := by
  unfold tailWord_927558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057213111675726723109479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22553879715748836759668885 1057213111675726723109479)
  ·
    refine ⟨1585819667513590084664219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1057213111675726723109479 1585819667513590084664219)
    ·
      refine ⟨2378729501270385126996329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1585819667513590084664219 2378729501270385126996329)
      ·
        refine ⟨1784047125952788845247247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2378729501270385126996329 1784047125952788845247247)
        ·
          refine ⟨2676070688929183267870871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784047125952788845247247 2676070688929183267870871)
          ·
            refine ⟨4014106033393774901806307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676070688929183267870871 4014106033393774901806307)
            ·
              refine ⟨6021159050090662352709461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014106033393774901806307 6021159050090662352709461)
              ·
                refine ⟨35280228809124974722907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6021159050090662352709461 35280228809124974722907)
                ·
                  rfl

theorem cell22_927558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_927558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927558 prefixEnd_927558 := by exact prefixLift 927558
  have htrace : WordTrace (prefixWord ++ tailWord_927558) baseStart_927558 baseEnd_927558 := by
    simpa [prefixWord, tailWord_927558, baseEnd_927558] using wordTrace_append hprefix tailTrace_927558
  have hstable : (prefixWord ++ tailWord_927558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927558).length < 2 ^ (prefixWord ++ tailWord_927558).sum := by decide
  have hdescent : baseEnd_927558 < baseStart_927558 := by decide
  rcases family_descends (prefixWord ++ tailWord_927558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927650 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_927650 : Nat := 118140960795 + 927650 * 2 ^ 59
def prefixEnd_927650 : Nat := 4983230072969 + 3 ^ 40 * 927650 * 2
def baseEnd_927650 : Nat := 317553552762267199205881

theorem tailTrace_927650 : CollatzResearch.WordTrace tailWord_927650 prefixEnd_927650 317553552762267199205881 := by
  unfold tailWord_927650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8458543772322488712963101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22556116726193303234568269 8458543772322488712963101)
  ·
    refine ⟨3171953914620933267361163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8458543772322488712963101 3171953914620933267361163)
    ·
      refine ⟨4757930871931399901041745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3171953914620933267361163 4757930871931399901041745)
      ·
        refine ⟨3568448153948549925781309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4757930871931399901041745 3568448153948549925781309)
        ·
          refine ⟨1338168057730706222167991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3568448153948549925781309 1338168057730706222167991)
          ·
            refine ⟨2007252086596059333251987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338168057730706222167991 2007252086596059333251987)
            ·
              refine ⟨3010878129894088999877981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007252086596059333251987 3010878129894088999877981)
              ·
                refine ⟨1129079298710283374954243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3010878129894088999877981 1129079298710283374954243)
                ·
                  refine ⟨1693618948065425062431365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129079298710283374954243 1693618948065425062431365)
                  ·
                    refine ⟨317553552762267199205881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1693618948065425062431365 317553552762267199205881)
                    ·
                      rfl

theorem cell22_927650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_927650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927650 prefixEnd_927650 := by exact prefixLift 927650
  have htrace : WordTrace (prefixWord ++ tailWord_927650) baseStart_927650 baseEnd_927650 := by
    simpa [prefixWord, tailWord_927650, baseEnd_927650] using wordTrace_append hprefix tailTrace_927650
  have hstable : (prefixWord ++ tailWord_927650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927650).length < 2 ^ (prefixWord ++ tailWord_927650).sum := by decide
  have hdescent : baseEnd_927650 < baseStart_927650 := by decide
  rcases family_descends (prefixWord ++ tailWord_927650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927680 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 2, 3]
def baseStart_927680 : Nat := 118140960795 + 927680 * 2 ^ 59
def prefixEnd_927680 : Nat := 4983230072969 + 3 ^ 40 * 927680 * 2
def baseEnd_927680 : Nat := 317563822375357120955789

theorem tailTrace_927680 : CollatzResearch.WordTrace tailWord_927680 prefixEnd_927680 317563822375357120955789 := by
  unfold tailWord_927680
  simp only [CollatzResearch.WordTrace]
  refine ⟨16917634639590634987722247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22556846186120846650296329 16917634639590634987722247)
  ·
    refine ⟨25376451959385952481583371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16917634639590634987722247 25376451959385952481583371)
    ·
      refine ⟨38064677939078928722375057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25376451959385952481583371 38064677939078928722375057)
      ·
        refine ⟨28548508454309196541781293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38064677939078928722375057 28548508454309196541781293)
        ·
          refine ⟨10705690670365948703167985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28548508454309196541781293 10705690670365948703167985)
          ·
            refine ⟨8029268002774461527375989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10705690670365948703167985 8029268002774461527375989)
            ·
              refine ⟨752743875260105768191499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8029268002774461527375989 752743875260105768191499)
              ·
                refine ⟨1129115812890158652287249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752743875260105768191499 1129115812890158652287249)
                ·
                  refine ⟨846836859667618989215437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129115812890158652287249 846836859667618989215437)
                  ·
                    refine ⟨317563822375357120955789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846836859667618989215437 317563822375357120955789)
                    ·
                      rfl

theorem cell22_927680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 3].length) (baseStart_927680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927680 prefixEnd_927680 := by exact prefixLift 927680
  have htrace : WordTrace (prefixWord ++ tailWord_927680) baseStart_927680 baseEnd_927680 := by
    simpa [prefixWord, tailWord_927680, baseEnd_927680] using wordTrace_append hprefix tailTrace_927680
  have hstable : (prefixWord ++ tailWord_927680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927680).length < 2 ^ (prefixWord ++ tailWord_927680).sum := by decide
  have hdescent : baseEnd_927680 < baseStart_927680 := by decide
  rcases family_descends (prefixWord ++ tailWord_927680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927736 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_927736 : Nat := 118140960795 + 927736 * 2 ^ 59
def prefixEnd_927736 : Nat := 4983230072969 + 3 ^ 40 * 927736 * 2
def baseEnd_927736 : Nat := 317582992319791641555617

theorem tailTrace_927736 : CollatzResearch.WordTrace tailWord_927736 prefixEnd_927736 317582992319791641555617 := by
  unfold tailWord_927736
  simp only [CollatzResearch.WordTrace]
  refine ⟨16918655883489195769741531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22558207844652261026322041 16918655883489195769741531)
  ·
    refine ⟨25377983825233793654612297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16918655883489195769741531 25377983825233793654612297)
    ·
      refine ⟨19033487868925345240959223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25377983825233793654612297 19033487868925345240959223)
      ·
        refine ⟨28550231803388017861438835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19033487868925345240959223 28550231803388017861438835)
        ·
          refine ⟨42825347705082026792158253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28550231803388017861438835 42825347705082026792158253)
          ·
            refine ⟨16059505389405760047059345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42825347705082026792158253 16059505389405760047059345)
            ·
              refine ⟨12044629042054320035294509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16059505389405760047059345 12044629042054320035294509)
              ·
                refine ⟨4516735890770370013235441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12044629042054320035294509 4516735890770370013235441)
                ·
                  refine ⟨3387551918077777509926581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4516735890770370013235441 3387551918077777509926581)
                  ·
                    refine ⟨317582992319791641555617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3387551918077777509926581 317582992319791641555617)
                    ·
                      rfl

theorem cell22_927736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_927736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927736 prefixEnd_927736 := by exact prefixLift 927736
  have htrace : WordTrace (prefixWord ++ tailWord_927736) baseStart_927736 baseEnd_927736 := by
    simpa [prefixWord, tailWord_927736, baseEnd_927736] using wordTrace_append hprefix tailTrace_927736
  have hstable : (prefixWord ++ tailWord_927736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927736).length < 2 ^ (prefixWord ++ tailWord_927736).sum := by decide
  have hdescent : baseEnd_927736 < baseStart_927736 := by decide
  rcases family_descends (prefixWord ++ tailWord_927736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927832 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 2, 3]
def baseStart_927832 : Nat := 118140960795 + 927832 * 2 ^ 59
def prefixEnd_927832 : Nat := 4983230072969 + 3 ^ 40 * 927832 * 2
def baseEnd_927832 : Nat := 317615855081679391155323

theorem tailTrace_927832 : CollatzResearch.WordTrace tailWord_927832 prefixEnd_927832 317615855081679391155323 := by
  unfold tailWord_927832
  simp only [CollatzResearch.WordTrace]
  refine ⟨16920406587315299967488875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22560542116420399956651833 16920406587315299967488875)
  ·
    refine ⟨25380609880972949951233313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16920406587315299967488875 25380609880972949951233313)
    ·
      refine ⟨19035457410729712463424985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25380609880972949951233313 19035457410729712463424985)
      ·
        refine ⟨14276593058047284347568739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19035457410729712463424985 14276593058047284347568739)
        ·
          refine ⟨21414889587070926521353109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14276593058047284347568739 21414889587070926521353109)
          ·
            refine ⟨1003822949393949680688427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21414889587070926521353109 1003822949393949680688427)
            ·
              refine ⟨1505734424090924521032641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003822949393949680688427 1505734424090924521032641)
              ·
                refine ⟨1129300818068193390774481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1505734424090924521032641 1129300818068193390774481)
                ·
                  refine ⟨846975613551145043080861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129300818068193390774481 846975613551145043080861)
                  ·
                    refine ⟨317615855081679391155323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846975613551145043080861 317615855081679391155323)
                    ·
                      rfl

theorem cell22_927832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_927832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927832 prefixEnd_927832 := by exact prefixLift 927832
  have htrace : WordTrace (prefixWord ++ tailWord_927832) baseStart_927832 baseEnd_927832 := by
    simpa [prefixWord, tailWord_927832, baseEnd_927832] using wordTrace_append hprefix tailTrace_927832
  have hstable : (prefixWord ++ tailWord_927832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927832).length < 2 ^ (prefixWord ++ tailWord_927832).sum := by decide
  have hdescent : baseEnd_927832 < baseStart_927832 := by decide
  rcases family_descends (prefixWord ++ tailWord_927832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927862 : List Nat := [5, 1, 1, 2, 1, 4, 2, 6]
def baseStart_927862 : Nat := 118140960795 + 927862 * 2 ^ 59
def prefixEnd_927862 : Nat := 4983230072969 + 3 ^ 40 * 927862 * 2
def baseEnd_927862 : Nat := 35291791632752145878359

theorem tailTrace_927862 : CollatzResearch.WordTrace tailWord_927862 prefixEnd_927862 35291791632752145878359 := by
  unfold tailWord_927862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115119210282619691160615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22561271576347943372379893 2115119210282619691160615)
  ·
    refine ⟨3172678815423929536740923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2115119210282619691160615 3172678815423929536740923)
    ·
      refine ⟨4759018223135894305111385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3172678815423929536740923 4759018223135894305111385)
      ·
        refine ⟨3569263667351920728833539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4759018223135894305111385 3569263667351920728833539)
        ·
          refine ⟨5353895501027881093250309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3569263667351920728833539 5353895501027881093250309)
          ·
            refine ⟨1003855406442727704984433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5353895501027881093250309 1003855406442727704984433)
            ·
              refine ⟨752891554832045778738325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003855406442727704984433 752891554832045778738325)
              ·
                refine ⟨35291791632752145878359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 752891554832045778738325 35291791632752145878359)
                ·
                  rfl

theorem cell22_927862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_927862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927862 prefixEnd_927862 := by exact prefixLift 927862
  have htrace : WordTrace (prefixWord ++ tailWord_927862) baseStart_927862 baseEnd_927862 := by
    simpa [prefixWord, tailWord_927862, baseEnd_927862] using wordTrace_append hprefix tailTrace_927862
  have hstable : (prefixWord ++ tailWord_927862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927862).length < 2 ^ (prefixWord ++ tailWord_927862).sum := by decide
  have hdescent : baseEnd_927862 < baseStart_927862 := by decide
  rcases family_descends (prefixWord ++ tailWord_927862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927890 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_927890 : Nat := 118140960795 + 927890 * 2 ^ 59
def prefixEnd_927890 : Nat := 4983230072969 + 3 ^ 40 * 927890 * 2
def baseEnd_927890 : Nat := 105878569888995524401715

theorem tailTrace_927890 : CollatzResearch.WordTrace tailWord_927890 prefixEnd_927890 105878569888995524401715 := by
  unfold tailWord_927890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8460732152105118960147281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22561952405613650560392749 8460732152105118960147281)
  ·
    refine ⟨6345549114078839220110461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8460732152105118960147281 6345549114078839220110461)
    ·
      refine ⟨2379580917779564707541423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6345549114078839220110461 2379580917779564707541423)
      ·
        refine ⟨3569371376669347061312135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379580917779564707541423 3569371376669347061312135)
        ·
          refine ⟨5354057065004020591968203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3569371376669347061312135 5354057065004020591968203)
          ·
            refine ⟨8031085597506030887952305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5354057065004020591968203 8031085597506030887952305)
            ·
              refine ⟨6023314198129523165964229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8031085597506030887952305 6023314198129523165964229)
              ·
                refine ⟨1129371412149285593618293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6023314198129523165964229 1129371412149285593618293)
                ·
                  refine ⟨105878569888995524401715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1129371412149285593618293 105878569888995524401715)
                  ·
                    rfl

theorem cell22_927890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_927890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927890 prefixEnd_927890 := by exact prefixLift 927890
  have htrace : WordTrace (prefixWord ++ tailWord_927890) baseStart_927890 baseEnd_927890 := by
    simpa [prefixWord, tailWord_927890, baseEnd_927890] using wordTrace_append hprefix tailTrace_927890
  have hstable : (prefixWord ++ tailWord_927890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927890).length < 2 ^ (prefixWord ++ tailWord_927890).sum := by decide
  have hdescent : baseEnd_927890 < baseStart_927890 := by decide
  rcases family_descends (prefixWord ++ tailWord_927890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927935 : List Nat := [1, 1, 2, 2, 2, 2, 1, 7, 4]
def baseStart_927935 : Nat := 118140960795 + 927935 * 2 ^ 59
def prefixEnd_927935 : Nat := 4983230072969 + 3 ^ 40 * 927935 * 2
def baseEnd_927935 : Nat := 105883704695540485276669

theorem tailTrace_927935 : CollatzResearch.WordTrace tailWord_927935 prefixEnd_927935 105883704695540485276669 := by
  unfold tailWord_927935
  simp only [CollatzResearch.WordTrace]
  refine ⟨33844569893257448525977259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22563046595504965683984839 33844569893257448525977259)
  ·
    refine ⟨50766854839886172788965889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33844569893257448525977259 50766854839886172788965889)
    ·
      refine ⟨38075141129914629591724417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50766854839886172788965889 38075141129914629591724417)
      ·
        refine ⟨28556355847435972193793313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38075141129914629591724417 28556355847435972193793313)
        ·
          refine ⟨21417266885576979145344985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28556355847435972193793313 21417266885576979145344985)
          ·
            refine ⟨16062950164182734359008739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21417266885576979145344985 16062950164182734359008739)
            ·
              refine ⟨24094425246274101538513109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16062950164182734359008739 24094425246274101538513109)
              ·
                refine ⟨564713091709549254808901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24094425246274101538513109 564713091709549254808901)
                ·
                  refine ⟨105883704695540485276669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564713091709549254808901 105883704695540485276669)
                  ·
                    rfl

theorem cell22_927935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 4].length) (baseStart_927935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927935 prefixEnd_927935 := by exact prefixLift 927935
  have htrace : WordTrace (prefixWord ++ tailWord_927935) baseStart_927935 baseEnd_927935 := by
    simpa [prefixWord, tailWord_927935, baseEnd_927935] using wordTrace_append hprefix tailTrace_927935
  have hstable : (prefixWord ++ tailWord_927935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927935).length < 2 ^ (prefixWord ++ tailWord_927935).sum := by decide
  have hdescent : baseEnd_927935 < baseStart_927935 := by decide
  rcases family_descends (prefixWord ++ tailWord_927935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927980 : List Nat := [2, 2, 1, 1, 2, 3, 5, 6]
def baseStart_927980 : Nat := 118140960795 + 927980 * 2 ^ 59
def prefixEnd_927980 : Nat := 4983230072969 + 3 ^ 40 * 927980 * 2
def baseEnd_927980 : Nat := 35296279834028482050541

theorem tailTrace_927980 : CollatzResearch.WordTrace tailWord_927980 prefixEnd_927980 35296279834028482050541 := by
  unfold tailWord_927980
  simp only [CollatzResearch.WordTrace]
  refine ⟨16923105589047210605682697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22564140785396280807576929 16923105589047210605682697)
  ·
    refine ⟨12692329191785407954262023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16923105589047210605682697 12692329191785407954262023)
    ·
      refine ⟨19038493787678111931393035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12692329191785407954262023 19038493787678111931393035)
      ·
        refine ⟨28557740681517167897089553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19038493787678111931393035 28557740681517167897089553)
        ·
          refine ⟨21418305511137875922817165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28557740681517167897089553 21418305511137875922817165)
          ·
            refine ⟨8031864566676703471056437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21418305511137875922817165 8031864566676703471056437)
            ·
              refine ⟨752987303125940950411541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8031864566676703471056437 752987303125940950411541)
              ·
                refine ⟨35296279834028482050541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 752987303125940950411541 35296279834028482050541)
                ·
                  rfl

theorem cell22_927980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 6].length) (baseStart_927980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927980 prefixEnd_927980 := by exact prefixLift 927980
  have htrace : WordTrace (prefixWord ++ tailWord_927980) baseStart_927980 baseEnd_927980 := by
    simpa [prefixWord, tailWord_927980, baseEnd_927980] using wordTrace_append hprefix tailTrace_927980
  have hstable : (prefixWord ++ tailWord_927980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927980).length < 2 ^ (prefixWord ++ tailWord_927980).sum := by decide
  have hdescent : baseEnd_927980 < baseStart_927980 := by decide
  rcases family_descends (prefixWord ++ tailWord_927980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927993 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_927993 : Nat := 118140960795 + 927993 * 2 ^ 59
def prefixEnd_927993 : Nat := 4983230072969 + 3 ^ 40 * 927993 * 2
def baseEnd_927993 : Nat := 317670968671928637879829

theorem tailTrace_927993 : CollatzResearch.WordTrace tailWord_927993 prefixEnd_927993 317670968671928637879829 := by
  unfold tailWord_927993
  simp only [CollatzResearch.WordTrace]
  refine ⟨33846685327047324431588633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22564456884698216287725755 33846685327047324431588633)
  ·
    refine ⟨25385013995285493323691475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33846685327047324431588633 25385013995285493323691475)
    ·
      refine ⟨38077520992928239985537213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25385013995285493323691475 38077520992928239985537213)
      ·
        refine ⟨14279070372348089994576455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38077520992928239985537213 14279070372348089994576455)
        ·
          refine ⟨21418605558522134991864683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14279070372348089994576455 21418605558522134991864683)
          ·
            refine ⟨32127908337783202487797025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21418605558522134991864683 32127908337783202487797025)
            ·
              refine ⟨24095931253337401865847769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32127908337783202487797025 24095931253337401865847769)
              ·
                refine ⟨18071948440003051399385827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24095931253337401865847769 18071948440003051399385827)
                ·
                  refine ⟨27107922660004577099078741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18071948440003051399385827 27107922660004577099078741)
                  ·
                    refine ⟨317670968671928637879829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27107922660004577099078741 317670968671928637879829)
                    ·
                      rfl

theorem cell22_927993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_927993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_927993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_927993 prefixEnd_927993 := by exact prefixLift 927993
  have htrace : WordTrace (prefixWord ++ tailWord_927993) baseStart_927993 baseEnd_927993 := by
    simpa [prefixWord, tailWord_927993, baseEnd_927993] using wordTrace_append hprefix tailTrace_927993
  have hstable : (prefixWord ++ tailWord_927993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927993).length < 2 ^ (prefixWord ++ tailWord_927993).sum := by decide
  have hdescent : baseEnd_927993 < baseStart_927993 := by decide
  rcases family_descends (prefixWord ++ tailWord_927993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928012 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_928012 : Nat := 118140960795 + 928012 * 2 ^ 59
def prefixEnd_928012 : Nat := 4983230072969 + 3 ^ 40 * 928012 * 2
def baseEnd_928012 : Nat := 317677472760218921654771

theorem tailTrace_928012 : CollatzResearch.WordTrace tailWord_928012 prefixEnd_928012 317677472760218921654771 := by
  unfold tailWord_928012
  simp only [CollatzResearch.WordTrace]
  refine ⟨16923689156989245338265145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22564918875985660451020193 16923689156989245338265145)
  ·
    refine ⟨12692766867741934003698859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16923689156989245338265145 12692766867741934003698859)
    ·
      refine ⟨19039150301612901005548289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12692766867741934003698859 19039150301612901005548289)
      ·
        refine ⟨14279362726209675754161217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19039150301612901005548289 14279362726209675754161217)
        ·
          refine ⟨10709522044657256815620913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14279362726209675754161217 10709522044657256815620913)
          ·
            refine ⟨8032141533492942611715685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10709522044657256815620913 8032141533492942611715685)
            ·
              refine ⟨1506026537529926739696691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8032141533492942611715685 1506026537529926739696691)
              ·
                refine ⟨2259039806294890109545037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506026537529926739696691 2259039806294890109545037)
                ·
                  refine ⟨847139927360583791079389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2259039806294890109545037 847139927360583791079389)
                  ·
                    refine ⟨317677472760218921654771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 847139927360583791079389 317677472760218921654771)
                    ·
                      rfl

theorem cell22_928012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_928012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928012 prefixEnd_928012 := by exact prefixLift 928012
  have htrace : WordTrace (prefixWord ++ tailWord_928012) baseStart_928012 baseEnd_928012 := by
    simpa [prefixWord, tailWord_928012, baseEnd_928012] using wordTrace_append hprefix tailTrace_928012
  have hstable : (prefixWord ++ tailWord_928012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928012).length < 2 ^ (prefixWord ++ tailWord_928012).sum := by decide
  have hdescent : baseEnd_928012 < baseStart_928012 := by decide
  rcases family_descends (prefixWord ++ tailWord_928012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928106 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 1, 4]
def baseStart_928106 : Nat := 118140960795 + 928106 * 2 ^ 59
def prefixEnd_928106 : Nat := 4983230072969 + 3 ^ 40 * 928106 * 2
def baseEnd_928106 : Nat := 317709650881234009804483

theorem tailTrace_928106 : CollatzResearch.WordTrace tailWord_928106 prefixEnd_928106 317709650881234009804483 := by
  unfold tailWord_928106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8462701693909486182613043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22567204517091963153634781 8462701693909486182613043)
  ·
    refine ⟨12694052540864229273919565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8462701693909486182613043 12694052540864229273919565)
    ·
      refine ⟨4760269702824085977719837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12694052540864229273919565 4760269702824085977719837)
      ·
        refine ⟨1785101138559032241644939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4760269702824085977719837 1785101138559032241644939)
        ·
          refine ⟨2677651707838548362467409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785101138559032241644939 2677651707838548362467409)
          ·
            refine ⟨2008238780878911271850557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2677651707838548362467409 2008238780878911271850557)
            ·
              refine ⟨753089542829591726943959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2008238780878911271850557 753089542829591726943959)
              ·
                refine ⟨1129634314244387590415939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753089542829591726943959 1129634314244387590415939)
                ·
                  refine ⟨1694451471366581385623909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129634314244387590415939 1694451471366581385623909)
                  ·
                    refine ⟨317709650881234009804483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1694451471366581385623909 317709650881234009804483)
                    ·
                      rfl

theorem cell22_928106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_928106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928106 prefixEnd_928106 := by exact prefixLift 928106
  have htrace : WordTrace (prefixWord ++ tailWord_928106) baseStart_928106 baseEnd_928106 := by
    simpa [prefixWord, tailWord_928106, baseEnd_928106] using wordTrace_append hprefix tailTrace_928106
  have hstable : (prefixWord ++ tailWord_928106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928106).length < 2 ^ (prefixWord ++ tailWord_928106).sum := by decide
  have hdescent : baseEnd_928106 < baseStart_928106 := by decide
  rcases family_descends (prefixWord ++ tailWord_928106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928177 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 7]
def baseStart_928177 : Nat := 118140960795 + 928177 * 2 ^ 59
def prefixEnd_928177 : Nat := 4983230072969 + 3 ^ 40 * 928177 * 2
def baseEnd_928177 : Nat := 105911318544071163759755

theorem tailTrace_928177 : CollatzResearch.WordTrace tailWord_928177 prefixEnd_928177 105911318544071163759755 := by
  unfold tailWord_928177
  simp only [CollatzResearch.WordTrace]
  refine ⟨33853396358380723856286785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22568930905587149237524523 33853396358380723856286785)
  ·
    refine ⟨25390047268785542892215089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33853396358380723856286785 25390047268785542892215089)
    ·
      refine ⟨19042535451589157169161317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25390047268785542892215089 19042535451589157169161317)
      ·
        refine ⟨3570475397172966969217747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19042535451589157169161317 3570475397172966969217747)
        ·
          refine ⟨5355713095759450453826621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570475397172966969217747 5355713095759450453826621)
          ·
            refine ⟨2008392410909793920184983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5355713095759450453826621 2008392410909793920184983)
            ·
              refine ⟨3012588616364690880277475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008392410909793920184983 3012588616364690880277475)
              ·
                refine ⟨4518882924547036320416213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012588616364690880277475 4518882924547036320416213)
                ·
                  refine ⟨105911318544071163759755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4518882924547036320416213 105911318544071163759755)
                  ·
                    rfl

theorem cell22_928177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_928177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928177 prefixEnd_928177 := by exact prefixLift 928177
  have htrace : WordTrace (prefixWord ++ tailWord_928177) baseStart_928177 baseEnd_928177 := by
    simpa [prefixWord, tailWord_928177, baseEnd_928177] using wordTrace_append hprefix tailTrace_928177
  have hstable : (prefixWord ++ tailWord_928177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928177).length < 2 ^ (prefixWord ++ tailWord_928177).sum := by decide
  have hdescent : baseEnd_928177 < baseStart_928177 := by decide
  rcases family_descends (prefixWord ++ tailWord_928177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928181 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_928181 : Nat := 118140960795 + 928181 * 2 ^ 59
def prefixEnd_928181 : Nat := 4983230072969 + 3 ^ 40 * 928181 * 2
def baseEnd_928181 : Nat := 317735324913958814179253

theorem tailTrace_928181 : CollatzResearch.WordTrace tailWord_928181 prefixEnd_928181 317735324913958814179253 := by
  unfold tailWord_928181
  simp only [CollatzResearch.WordTrace]
  refine ⟨33853542250366232539432397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22569028166910821692954931 33853542250366232539432397)
  ·
    refine ⟨12695078343887337202287149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33853542250366232539432397 12695078343887337202287149)
    ·
      refine ⟨4760654378957751450857681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12695078343887337202287149 4760654378957751450857681)
      ·
        refine ⟨3570490784218313588143261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4760654378957751450857681 3570490784218313588143261)
        ·
          refine ⟨1338934044081867595553723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3570490784218313588143261 1338934044081867595553723)
          ·
            refine ⟨2008401066122801393330585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338934044081867595553723 2008401066122801393330585)
            ·
              refine ⟨1506300799592101044997939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008401066122801393330585 1506300799592101044997939)
              ·
                refine ⟨2259451199388151567496909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506300799592101044997939 2259451199388151567496909)
                ·
                  refine ⟨847294199770556837811341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2259451199388151567496909 847294199770556837811341)
                  ·
                    refine ⟨317735324913958814179253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 847294199770556837811341 317735324913958814179253)
                    ·
                      rfl

theorem cell22_928181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_928181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928181 prefixEnd_928181 := by exact prefixLift 928181
  have htrace : WordTrace (prefixWord ++ tailWord_928181) baseStart_928181 baseEnd_928181 := by
    simpa [prefixWord, tailWord_928181, baseEnd_928181] using wordTrace_append hprefix tailTrace_928181
  have hstable : (prefixWord ++ tailWord_928181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928181).length < 2 ^ (prefixWord ++ tailWord_928181).sum := by decide
  have hdescent : baseEnd_928181 < baseStart_928181 := by decide
  rcases family_descends (prefixWord ++ tailWord_928181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928245 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 5]
def baseStart_928245 : Nat := 118140960795 + 928245 * 2 ^ 59
def prefixEnd_928245 : Nat := 4983230072969 + 3 ^ 40 * 928245 * 2
def baseEnd_928245 : Nat := 105919077807294660193019

theorem tailTrace_928245 : CollatzResearch.WordTrace tailWord_928245 prefixEnd_928245 105919077807294660193019 := by
  unfold tailWord_928245
  simp only [CollatzResearch.WordTrace]
  refine ⟨33855876522134371469762189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22570584348089580979841459 33855876522134371469762189)
  ·
    refine ⟨12695953695800389301160821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33855876522134371469762189 12695953695800389301160821)
    ·
      refine ⟨1190245658981286496983827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12695953695800389301160821 1190245658981286496983827)
      ·
        refine ⟨1785368488471929745475741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1190245658981286496983827 1785368488471929745475741)
        ·
          refine ⟨669513183176973654553403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1785368488471929745475741 669513183176973654553403)
          ·
            refine ⟨1004269774765460481830105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669513183176973654553403 1004269774765460481830105)
            ·
              refine ⟨753202331074095361372579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004269774765460481830105 753202331074095361372579)
              ·
                refine ⟨1129803496611143042058869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753202331074095361372579 1129803496611143042058869)
                ·
                  refine ⟨105919077807294660193019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1129803496611143042058869 105919077807294660193019)
                  ·
                    rfl

theorem cell22_928245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_928245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928245 prefixEnd_928245 := by exact prefixLift 928245
  have htrace : WordTrace (prefixWord ++ tailWord_928245) baseStart_928245 baseEnd_928245 := by
    simpa [prefixWord, tailWord_928245, baseEnd_928245] using wordTrace_append hprefix tailTrace_928245
  have hstable : (prefixWord ++ tailWord_928245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928245).length < 2 ^ (prefixWord ++ tailWord_928245).sum := by decide
  have hdescent : baseEnd_928245 < baseStart_928245 := by decide
  rcases family_descends (prefixWord ++ tailWord_928245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928252 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_928252 : Nat := 118140960795 + 928252 * 2 ^ 59
def prefixEnd_928252 : Nat := 4983230072969 + 3 ^ 40 * 928252 * 2
def baseEnd_928252 : Nat := 317759629664938295654035

theorem tailTrace_928252 : CollatzResearch.WordTrace tailWord_928252 prefixEnd_928252 317759629664938295654035 := by
  unfold tailWord_928252
  simp only [CollatzResearch.WordTrace]
  refine ⟨16928065916554505832633505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22570754555406007776844673 16928065916554505832633505)
  ·
    refine ⟨12696049437415879374475129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16928065916554505832633505 12696049437415879374475129)
    ·
      refine ⟨9522037078061909530856347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12696049437415879374475129 9522037078061909530856347)
      ·
        refine ⟨14283055617092864296284521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9522037078061909530856347 14283055617092864296284521)
        ·
          refine ⟨10712291712819648222213391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14283055617092864296284521 10712291712819648222213391)
          ·
            refine ⟨16068437569229472333320087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10712291712819648222213391 16068437569229472333320087)
            ·
              refine ⟨24102656353844208499980131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16068437569229472333320087 24102656353844208499980131)
              ·
                refine ⟨36153984530766312749970197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24102656353844208499980131 36153984530766312749970197)
                ·
                  refine ⟨1694718024879670910154853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36153984530766312749970197 1694718024879670910154853)
                  ·
                    refine ⟨317759629664938295654035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1694718024879670910154853 317759629664938295654035)
                    ·
                      rfl

theorem cell22_928252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_928252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928252 prefixEnd_928252 := by exact prefixLift 928252
  have htrace : WordTrace (prefixWord ++ tailWord_928252) baseStart_928252 baseEnd_928252 := by
    simpa [prefixWord, tailWord_928252, baseEnd_928252] using wordTrace_append hprefix tailTrace_928252
  have hstable : (prefixWord ++ tailWord_928252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928252).length < 2 ^ (prefixWord ++ tailWord_928252).sum := by decide
  have hdescent : baseEnd_928252 < baseStart_928252 := by decide
  rcases family_descends (prefixWord ++ tailWord_928252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928267 : List Nat := [1, 1, 1, 1, 7, 1, 2, 8]
def baseStart_928267 : Nat := 118140960795 + 928267 * 2 ^ 59
def prefixEnd_928267 : Nat := 4983230072969 + 3 ^ 40 * 928267 * 2
def baseEnd_928267 : Nat := 35307196052387028503221

theorem tailTrace_928267 : CollatzResearch.WordTrace tailWord_928267 prefixEnd_928267 35307196052387028503221 := by
  unfold tailWord_928267
  simp only [CollatzResearch.WordTrace]
  refine ⟨33856678928054669227063055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22571119285369779484708703 33856678928054669227063055)
  ·
    refine ⟨50785018392082003840594583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33856678928054669227063055 50785018392082003840594583)
    ·
      refine ⟨76177527588123005760891875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50785018392082003840594583 76177527588123005760891875)
      ·
        refine ⟨114266291382184508641337813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76177527588123005760891875 114266291382184508641337813)
        ·
          refine ⟨2678116204269949421281355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 114266291382184508641337813 2678116204269949421281355)
          ·
            refine ⟨4017174306404924131922033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678116204269949421281355 4017174306404924131922033)
            ·
              refine ⟨3012880729803693098941525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4017174306404924131922033 3012880729803693098941525)
              ·
                refine ⟨35307196052387028503221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3012880729803693098941525 35307196052387028503221)
                ·
                  rfl

theorem cell22_928267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 8].length) (baseStart_928267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928267 prefixEnd_928267 := by exact prefixLift 928267
  have htrace : WordTrace (prefixWord ++ tailWord_928267) baseStart_928267 baseEnd_928267 := by
    simpa [prefixWord, tailWord_928267, baseEnd_928267] using wordTrace_append hprefix tailTrace_928267
  have hstable : (prefixWord ++ tailWord_928267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928267).length < 2 ^ (prefixWord ++ tailWord_928267).sum := by decide
  have hdescent : baseEnd_928267 < baseStart_928267 := by decide
  rcases family_descends (prefixWord ++ tailWord_928267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928288 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 2, 3]
def baseStart_928288 : Nat := 118140960795 + 928288 * 2 ^ 59
def prefixEnd_928288 : Nat := 4983230072969 + 3 ^ 40 * 928288 * 2
def baseEnd_928288 : Nat := 317771953200646201753925

theorem tailTrace_928288 : CollatzResearch.WordTrace tailWord_928288 prefixEnd_928288 317771953200646201753925 := by
  unfold tailWord_928288
  simp only [CollatzResearch.WordTrace]
  refine ⟨16928722430489294906788759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22571629907319059875718345 16928722430489294906788759)
  ·
    refine ⟨25393083645733942360183139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16928722430489294906788759 25393083645733942360183139)
    ·
      refine ⟨38089625468600913540274709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25393083645733942360183139 38089625468600913540274709)
      ·
        refine ⟨1785451193840667822200377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38089625468600913540274709 1785451193840667822200377)
        ·
          refine ⟨1339088395380500866650283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1785451193840667822200377 1339088395380500866650283)
          ·
            refine ⟨2008632593070751299975425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339088395380500866650283 2008632593070751299975425)
            ·
              refine ⟨1506474444803063474981569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008632593070751299975425 1506474444803063474981569)
              ·
                refine ⟨1129855833602297606236177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506474444803063474981569 1129855833602297606236177)
                ·
                  refine ⟨847391875201723204677133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129855833602297606236177 847391875201723204677133)
                  ·
                    refine ⟨317771953200646201753925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 847391875201723204677133 317771953200646201753925)
                    ·
                      rfl

theorem cell22_928288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_928288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928288 prefixEnd_928288 := by exact prefixLift 928288
  have htrace : WordTrace (prefixWord ++ tailWord_928288) baseStart_928288 baseEnd_928288 := by
    simpa [prefixWord, tailWord_928288, baseEnd_928288] using wordTrace_append hprefix tailTrace_928288
  have hstable : (prefixWord ++ tailWord_928288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928288).length < 2 ^ (prefixWord ++ tailWord_928288).sum := by decide
  have hdescent : baseEnd_928288 < baseStart_928288 := by decide
  rcases family_descends (prefixWord ++ tailWord_928288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928316 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_928316 : Nat := 118140960795 + 928316 * 2 ^ 59
def prefixEnd_928316 : Nat := 4983230072969 + 3 ^ 40 * 928316 * 2
def baseEnd_928316 : Nat := 317781538172863462053839

theorem tailTrace_928316 : CollatzResearch.WordTrace tailWord_928316 prefixEnd_928316 317781538172863462053839 := by
  unfold tailWord_928316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16929233052438575297798401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22572310736584767063731201 16929233052438575297798401)
  ·
    refine ⟨12696924789328931473348801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16929233052438575297798401 12696924789328931473348801)
    ·
      refine ⟨9522693591996698605011601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12696924789328931473348801 9522693591996698605011601)
      ·
        refine ⟨7142020193997523953758701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9522693591996698605011601 7142020193997523953758701)
        ·
          refine ⟨2678257572749071482659513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7142020193997523953758701 2678257572749071482659513)
          ·
            refine ⟨2008693179561803611994635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678257572749071482659513 2008693179561803611994635)
            ·
              refine ⟨3013039769342705417991953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008693179561803611994635 3013039769342705417991953)
              ·
                refine ⟨2259779827007029063493965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3013039769342705417991953 2259779827007029063493965)
                ·
                  refine ⟨847417435127635898810237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2259779827007029063493965 847417435127635898810237)
                  ·
                    refine ⟨317781538172863462053839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 847417435127635898810237 317781538172863462053839)
                    ·
                      rfl

theorem cell22_928316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_928316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928316 prefixEnd_928316 := by exact prefixLift 928316
  have htrace : WordTrace (prefixWord ++ tailWord_928316) baseStart_928316 baseEnd_928316 := by
    simpa [prefixWord, tailWord_928316, baseEnd_928316] using wordTrace_append hprefix tailTrace_928316
  have hstable : (prefixWord ++ tailWord_928316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928316).length < 2 ^ (prefixWord ++ tailWord_928316).sum := by decide
  have hdescent : baseEnd_928316 < baseStart_928316 := by decide
  rcases family_descends (prefixWord ++ tailWord_928316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928318 : List Nat := [4, 2, 1, 4, 1, 1, 3, 6]
def baseStart_928318 : Nat := 118140960795 + 928318 * 2 ^ 59
def prefixEnd_928318 : Nat := 4983230072969 + 3 ^ 40 * 928318 * 2
def baseEnd_928318 : Nat := 35309135868192902611537

theorem tailTrace_928318 : CollatzResearch.WordTrace tailWord_928318 prefixEnd_928318 35309135868192902611537 := by
  unfold tailWord_928318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4232317381358738117146201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22572359367246603291446405 4232317381358738117146201)
  ·
    refine ⟨3174238036019053587859651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4232317381358738117146201 3174238036019053587859651)
    ·
      refine ⟨4761357054028580381789477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174238036019053587859651 4761357054028580381789477)
      ·
        refine ⟨892754447630358821585527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4761357054028580381789477 892754447630358821585527)
        ·
          refine ⟨1339131671445538232378291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892754447630358821585527 1339131671445538232378291)
          ·
            refine ⟨2008697507168307348567437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339131671445538232378291 2008697507168307348567437)
            ·
              refine ⟨753261565188115255712789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2008697507168307348567437 753261565188115255712789)
              ·
                refine ⟨35309135868192902611537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 753261565188115255712789 35309135868192902611537)
                ·
                  rfl

theorem cell22_928318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_928318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928318 prefixEnd_928318 := by exact prefixLift 928318
  have htrace : WordTrace (prefixWord ++ tailWord_928318) baseStart_928318 baseEnd_928318 := by
    simpa [prefixWord, tailWord_928318, baseEnd_928318] using wordTrace_append hprefix tailTrace_928318
  have hstable : (prefixWord ++ tailWord_928318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928318).length < 2 ^ (prefixWord ++ tailWord_928318).sum := by decide
  have hdescent : baseEnd_928318 < baseStart_928318 := by decide
  rcases family_descends (prefixWord ++ tailWord_928318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928408 : List Nat := [2, 1, 2, 4, 1, 1, 5, 2, 4]
def baseStart_928408 : Nat := 118140960795 + 928408 * 2 ^ 59
def prefixEnd_928408 : Nat := 4983230072969 + 3 ^ 40 * 928408 * 2
def baseEnd_928408 : Nat := 105937677217668629584519

theorem tailTrace_928408 : CollatzResearch.WordTrace tailWord_928408 prefixEnd_928408 105937677217668629584519 := by
  unfold tailWord_928408
  simp only [CollatzResearch.WordTrace]
  refine ⟨16930910810271925153972939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22574547747029233538630585 16930910810271925153972939)
  ·
    refine ⟨25396366215407887730959409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16930910810271925153972939 25396366215407887730959409)
    ·
      refine ⟨19047274661555915798219557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25396366215407887730959409 19047274661555915798219557)
      ·
        refine ⟨3571363999041734212166167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19047274661555915798219557 3571363999041734212166167)
        ·
          refine ⟨5357045998562601318249251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571363999041734212166167 5357045998562601318249251)
          ·
            refine ⟨8035568997843901977373877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357045998562601318249251 8035568997843901977373877)
            ·
              refine ⟨753334593547865810378801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8035568997843901977373877 753334593547865810378801)
              ·
                refine ⟨565000945160899357784101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753334593547865810378801 565000945160899357784101)
                ·
                  refine ⟨105937677217668629584519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565000945160899357784101 105937677217668629584519)
                  ·
                    rfl

theorem cell22_928408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 4].length) (baseStart_928408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928408 prefixEnd_928408 := by exact prefixLift 928408
  have htrace : WordTrace (prefixWord ++ tailWord_928408) baseStart_928408 baseEnd_928408 := by
    simpa [prefixWord, tailWord_928408, baseEnd_928408] using wordTrace_append hprefix tailTrace_928408
  have hstable : (prefixWord ++ tailWord_928408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928408).length < 2 ^ (prefixWord ++ tailWord_928408).sum := by decide
  have hdescent : baseEnd_928408 < baseStart_928408 := by decide
  rcases family_descends (prefixWord ++ tailWord_928408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928479 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 1, 7]
def baseStart_928479 : Nat := 118140960795 + 928479 * 2 ^ 59
def prefixEnd_928479 : Nat := 4983230072969 + 3 ^ 40 * 928479 * 2
def baseEnd_928479 : Nat := 317837336403985370228339

theorem tailTrace_928479 : CollatzResearch.WordTrace tailWord_928479 prefixEnd_928479 317837336403985370228339 := by
  unfold tailWord_928479
  simp only [CollatzResearch.WordTrace]
  refine ⟨33864411203286629433780491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22576274135524419622520327 33864411203286629433780491)
  ·
    refine ⟨50796616804929944150670737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33864411203286629433780491 50796616804929944150670737)
    ·
      refine ⟨38097462603697458113003053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50796616804929944150670737 38097462603697458113003053)
      ·
        refine ⟨14286548476386546792376145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38097462603697458113003053 14286548476386546792376145)
        ·
          refine ⟨10714911357289910094282109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14286548476386546792376145 10714911357289910094282109)
          ·
            refine ⟨4018091758983716285355791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10714911357289910094282109 4018091758983716285355791)
            ·
              refine ⟨6027137638475574428033687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018091758983716285355791 6027137638475574428033687)
              ·
                refine ⟨9040706457713361642050531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6027137638475574428033687 9040706457713361642050531)
                ·
                  refine ⟨13561059686570042463075797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040706457713361642050531 13561059686570042463075797)
                  ·
                    refine ⟨317837336403985370228339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13561059686570042463075797 317837336403985370228339)
                    ·
                      rfl

theorem cell22_928479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_928479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928479 prefixEnd_928479 := by exact prefixLift 928479
  have htrace : WordTrace (prefixWord ++ tailWord_928479) baseStart_928479 baseEnd_928479 := by
    simpa [prefixWord, tailWord_928479, baseEnd_928479] using wordTrace_append hprefix tailTrace_928479
  have hstable : (prefixWord ++ tailWord_928479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928479).length < 2 ^ (prefixWord ++ tailWord_928479).sum := by decide
  have hdescent : baseEnd_928479 < baseStart_928479 := by decide
  rcases family_descends (prefixWord ++ tailWord_928479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928481 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 5]
def baseStart_928481 : Nat := 118140960795 + 928481 * 2 ^ 59
def prefixEnd_928481 : Nat := 4983230072969 + 3 ^ 40 * 928481 * 2
def baseEnd_928481 : Nat := 105946007014952677226111

theorem tailTrace_928481 : CollatzResearch.WordTrace tailWord_928481 prefixEnd_928481 105946007014952677226111 := by
  unfold tailWord_928481
  simp only [CollatzResearch.WordTrace]
  refine ⟨33864484149279383775353297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22576322766186255850235531 33864484149279383775353297)
  ·
    refine ⟨25398363111959537831514973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33864484149279383775353297 25398363111959537831514973)
    ·
      refine ⟨9524386166984826686818115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25398363111959537831514973 9524386166984826686818115)
      ·
        refine ⟨14286579250477240030227173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9524386166984826686818115 14286579250477240030227173)
        ·
          refine ⟨2678733609464482505667595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14286579250477240030227173 2678733609464482505667595)
          ·
            refine ⟨4018100414196723758501393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678733609464482505667595 4018100414196723758501393)
            ·
              refine ⟨3013575310647542818876045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4018100414196723758501393 3013575310647542818876045)
              ·
                refine ⟨1130090741492828557078517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3013575310647542818876045 1130090741492828557078517)
                ·
                  refine ⟨105946007014952677226111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1130090741492828557078517 105946007014952677226111)
                  ·
                    rfl

theorem cell22_928481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_928481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928481 prefixEnd_928481 := by exact prefixLift 928481
  have htrace : WordTrace (prefixWord ++ tailWord_928481) baseStart_928481 baseEnd_928481 := by
    simpa [prefixWord, tailWord_928481, baseEnd_928481] using wordTrace_append hprefix tailTrace_928481
  have hstable : (prefixWord ++ tailWord_928481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928481).length < 2 ^ (prefixWord ++ tailWord_928481).sum := by decide
  have hdescent : baseEnd_928481 < baseStart_928481 := by decide
  rcases family_descends (prefixWord ++ tailWord_928481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928509 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 8]
def baseStart_928509 : Nat := 118140960795 + 928509 * 2 ^ 59
def prefixEnd_928509 : Nat := 4983230072969 + 3 ^ 40 * 928509 * 2
def baseEnd_928509 : Nat := 105949202005691763992749

theorem tailTrace_928509 : CollatzResearch.WordTrace tailWord_928509 prefixEnd_928509 105949202005691763992749 := by
  unfold tailWord_928509
  simp only [CollatzResearch.WordTrace]
  refine ⟨33865505393177944557372581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22577003595451963038248387 33865505393177944557372581)
  ·
    refine ⟨6349782261220864604507359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33865505393177944557372581 6349782261220864604507359)
    ·
      refine ⟨9524673391831296906761039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6349782261220864604507359 9524673391831296906761039)
      ·
        refine ⟨14287010087746945360141559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9524673391831296906761039 14287010087746945360141559)
        ·
          refine ⟨21430515131620418040212339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14287010087746945360141559 21430515131620418040212339)
          ·
            refine ⟨32145772697430627060318509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21430515131620418040212339 32145772697430627060318509)
            ·
              refine ⟨12054664761536485147619441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32145772697430627060318509 12054664761536485147619441)
              ·
                refine ⟨9040998571152363860714581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12054664761536485147619441 9040998571152363860714581)
                ·
                  refine ⟨105949202005691763992749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9040998571152363860714581 105949202005691763992749)
                  ·
                    rfl

theorem cell22_928509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_928509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928509 prefixEnd_928509 := by exact prefixLift 928509
  have htrace : WordTrace (prefixWord ++ tailWord_928509) baseStart_928509 baseEnd_928509 := by
    simpa [prefixWord, tailWord_928509, baseEnd_928509] using wordTrace_append hprefix tailTrace_928509
  have hstable : (prefixWord ++ tailWord_928509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928509).length < 2 ^ (prefixWord ++ tailWord_928509).sum := by decide
  have hdescent : baseEnd_928509 < baseStart_928509 := by decide
  rcases family_descends (prefixWord ++ tailWord_928509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928556 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_928556 : Nat := 118140960795 + 928556 * 2 ^ 59
def prefixEnd_928556 : Nat := 4983230072969 + 3 ^ 40 * 928556 * 2
def baseEnd_928556 : Nat := 317863695077582836053103

theorem tailTrace_928556 : CollatzResearch.WordTrace tailWord_928556 prefixEnd_928556 317863695077582836053103 := by
  unfold tailWord_928556
  simp only [CollatzResearch.WordTrace]
  refine ⟨16933609812003835792166761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22578146416005114389555681 16933609812003835792166761)
  ·
    refine ⟨12700207359002876844125071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16933609812003835792166761 12700207359002876844125071)
    ·
      refine ⟨19050311038504315266187607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12700207359002876844125071 19050311038504315266187607)
      ·
        refine ⟨28575466557756472899281411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19050311038504315266187607 28575466557756472899281411)
        ·
          refine ⟨42863199836634709348922117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28575466557756472899281411 42863199836634709348922117)
          ·
            refine ⟨8036849969369008002922897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42863199836634709348922117 8036849969369008002922897)
            ·
              refine ⟨6027637477026756002192173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8036849969369008002922897 6027637477026756002192173)
              ·
                refine ⟨2260364053885033500822065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6027637477026756002192173 2260364053885033500822065)
                ·
                  refine ⟨1695273040413775125616549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2260364053885033500822065 1695273040413775125616549)
                  ·
                    refine ⟨317863695077582836053103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1695273040413775125616549 317863695077582836053103)
                    ·
                      rfl

theorem cell22_928556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_928556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928556 prefixEnd_928556 := by exact prefixLift 928556
  have htrace : WordTrace (prefixWord ++ tailWord_928556) baseStart_928556 baseEnd_928556 := by
    simpa [prefixWord, tailWord_928556, baseEnd_928556] using wordTrace_append hprefix tailTrace_928556
  have hstable : (prefixWord ++ tailWord_928556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928556).length < 2 ^ (prefixWord ++ tailWord_928556).sum := by decide
  have hdescent : baseEnd_928556 < baseStart_928556 := by decide
  rcases family_descends (prefixWord ++ tailWord_928556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928577 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 6]
def baseStart_928577 : Nat := 118140960795 + 928577 * 2 ^ 59
def prefixEnd_928577 : Nat := 4983230072969 + 3 ^ 40 * 928577 * 2
def baseEnd_928577 : Nat := 105956961268915260426013

theorem tailTrace_928577 : CollatzResearch.WordTrace tailWord_928577 prefixEnd_928577 105956961268915260426013 := by
  unfold tailWord_928577
  simp only [CollatzResearch.WordTrace]
  refine ⟨33867985556931592170847985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22578657037954394780565323 33867985556931592170847985)
  ·
    refine ⟨25400989167698694128135989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33867985556931592170847985 25400989167698694128135989)
    ·
      refine ⟨2381342734471752574512749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25400989167698694128135989 2381342734471752574512749)
      ·
        refine ⟨893003525426907215442281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2381342734471752574512749 893003525426907215442281)
        ·
          refine ⟨669752644070180411581711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893003525426907215442281 669752644070180411581711)
          ·
            refine ⟨1004628966105270617372567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669752644070180411581711 1004628966105270617372567)
            ·
              refine ⟨1506943449157905926058851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004628966105270617372567 1506943449157905926058851)
              ·
                refine ⟨2260415173736858889088277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506943449157905926058851 2260415173736858889088277)
                ·
                  refine ⟨105956961268915260426013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2260415173736858889088277 105956961268915260426013)
                  ·
                    rfl

theorem cell22_928577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 6].length) (baseStart_928577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928577 prefixEnd_928577 := by exact prefixLift 928577
  have htrace : WordTrace (prefixWord ++ tailWord_928577) baseStart_928577 baseEnd_928577 := by
    simpa [prefixWord, tailWord_928577, baseEnd_928577] using wordTrace_append hprefix tailTrace_928577
  have hstable : (prefixWord ++ tailWord_928577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928577).length < 2 ^ (prefixWord ++ tailWord_928577).sum := by decide
  have hdescent : baseEnd_928577 < baseStart_928577 := by decide
  rcases family_descends (prefixWord ++ tailWord_928577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928620 : List Nat := [2, 2, 1, 1, 4, 1, 2, 5, 1, 3]
def baseStart_928620 : Nat := 118140960795 + 928620 * 2 ^ 59
def prefixEnd_928620 : Nat := 4983230072969 + 3 ^ 40 * 928620 * 2
def baseEnd_928620 : Nat := 317885603585508002452907

theorem tailTrace_928620 : CollatzResearch.WordTrace tailWord_928620 prefixEnd_928620 317885603585508002452907 := by
  unfold tailWord_928620
  simp only [CollatzResearch.WordTrace]
  refine ⟨16934776947887905257331657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22579702597183873676442209 16934776947887905257331657)
  ·
    refine ⟨12701082710915928942998743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16934776947887905257331657 12701082710915928942998743)
    ·
      refine ⟨19051624066373893414498115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12701082710915928942998743 19051624066373893414498115)
      ·
        refine ⟨28577436099560840121747173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19051624066373893414498115 28577436099560840121747173)
        ·
          refine ⟨5358269268667657522827595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28577436099560840121747173 5358269268667657522827595)
          ·
            refine ⟨8037403903001486284241393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358269268667657522827595 8037403903001486284241393)
            ·
              refine ⟨6028052927251114713181045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8037403903001486284241393 6028052927251114713181045)
              ·
                refine ⟨565129961929792004360723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6028052927251114713181045 565129961929792004360723)
                ·
                  refine ⟨847694942894688006541085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565129961929792004360723 847694942894688006541085)
                  ·
                    refine ⟨317885603585508002452907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 847694942894688006541085 317885603585508002452907)
                    ·
                      rfl

theorem cell22_928620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_928620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928620 prefixEnd_928620 := by exact prefixLift 928620
  have htrace : WordTrace (prefixWord ++ tailWord_928620) baseStart_928620 baseEnd_928620 := by
    simpa [prefixWord, tailWord_928620, baseEnd_928620] using wordTrace_append hprefix tailTrace_928620
  have hstable : (prefixWord ++ tailWord_928620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928620).length < 2 ^ (prefixWord ++ tailWord_928620).sum := by decide
  have hdescent : baseEnd_928620 < baseStart_928620 := by decide
  rcases family_descends (prefixWord ++ tailWord_928620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928633 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 5]
def baseStart_928633 : Nat := 118140960795 + 928633 * 2 ^ 59
def prefixEnd_928633 : Nat := 4983230072969 + 3 ^ 40 * 928633 * 2
def baseEnd_928633 : Nat := 105963351250393433959289

theorem tailTrace_928633 : CollatzResearch.WordTrace tailWord_928633 prefixEnd_928633 105963351250393433959289 := by
  unfold tailWord_928633
  simp only [CollatzResearch.WordTrace]
  refine ⟨33870028044728713734886553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22580018696485809156591035 33870028044728713734886553)
  ·
    refine ⟨25402521033546535301164915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33870028044728713734886553 25402521033546535301164915)
    ·
      refine ⟨38103781550319802951747373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25402521033546535301164915 38103781550319802951747373)
      ·
        refine ⟨14288918081369926106905265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38103781550319802951747373 14288918081369926106905265)
        ·
          refine ⟨10716688561027444580178949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14288918081369926106905265 10716688561027444580178949)
          ·
            refine ⟨2009379105192645858783553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10716688561027444580178949 2009379105192645858783553)
            ·
              refine ⟨1507034328894484394087665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009379105192645858783553 1507034328894484394087665)
              ·
                refine ⟨1130275746670863295565749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1507034328894484394087665 1130275746670863295565749)
                ·
                  refine ⟨105963351250393433959289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1130275746670863295565749 105963351250393433959289)
                  ·
                    rfl

theorem cell22_928633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_928633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928633 prefixEnd_928633 := by exact prefixLift 928633
  have htrace : WordTrace (prefixWord ++ tailWord_928633) baseStart_928633 baseEnd_928633 := by
    simpa [prefixWord, tailWord_928633, baseEnd_928633] using wordTrace_append hprefix tailTrace_928633
  have hstable : (prefixWord ++ tailWord_928633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928633).length < 2 ^ (prefixWord ++ tailWord_928633).sum := by decide
  have hdescent : baseEnd_928633 < baseStart_928633 := by decide
  rcases family_descends (prefixWord ++ tailWord_928633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928637 : List Nat := [1, 4, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_928637 : Nat := 118140960795 + 928637 * 2 ^ 59
def prefixEnd_928637 : Nat := 4983230072969 + 3 ^ 40 * 928637 * 2
def baseEnd_928637 : Nat := 317891423032925624777855

theorem tailTrace_928637 : CollatzResearch.WordTrace tailWord_928637 prefixEnd_928637 317891423032925624777855 := by
  unfold tailWord_928637
  simp only [CollatzResearch.WordTrace]
  refine ⟨33870173936714222418032165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22580115957809481612021443 33870173936714222418032165)
  ·
    refine ⟨6350657613133916703381031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33870173936714222418032165 6350657613133916703381031)
    ·
      refine ⟨9525986419700875055071547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6350657613133916703381031 9525986419700875055071547)
      ·
        refine ⟨14288979629551312582607321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9525986419700875055071547 14288979629551312582607321)
        ·
          refine ⟨10716734722163484436955491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14288979629551312582607321 10716734722163484436955491)
          ·
            refine ⟨16075102083245226655433237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10716734722163484436955491 16075102083245226655433237)
            ·
              refine ⟨753520410152119999473433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16075102083245226655433237 753520410152119999473433)
              ·
                refine ⟨565140307614089999605075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753520410152119999473433 565140307614089999605075)
                ·
                  refine ⟨847710461421134999407613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565140307614089999605075 847710461421134999407613)
                  ·
                    refine ⟨317891423032925624777855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 847710461421134999407613 317891423032925624777855)
                    ·
                      rfl

theorem cell22_928637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_928637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928637 prefixEnd_928637 := by exact prefixLift 928637
  have htrace : WordTrace (prefixWord ++ tailWord_928637) baseStart_928637 baseEnd_928637 := by
    simpa [prefixWord, tailWord_928637, baseEnd_928637] using wordTrace_append hprefix tailTrace_928637
  have hstable : (prefixWord ++ tailWord_928637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928637).length < 2 ^ (prefixWord ++ tailWord_928637).sum := by decide
  have hdescent : baseEnd_928637 < baseStart_928637 := by decide
  rcases family_descends (prefixWord ++ tailWord_928637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928648 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_928648 : Nat := 118140960795 + 928648 * 2 ^ 59
def prefixEnd_928648 : Nat := 4983230072969 + 3 ^ 40 * 928648 * 2
def baseEnd_928648 : Nat := 317895188557725262752821

theorem tailTrace_928648 : CollatzResearch.WordTrace tailWord_928648 prefixEnd_928648 317895188557725262752821 := by
  unfold tailWord_928648
  simp only [CollatzResearch.WordTrace]
  refine ⟨16935287569837185648341299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22580383426449580864455065 16935287569837185648341299)
  ·
    refine ⟨25402931354755778472511949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16935287569837185648341299 25402931354755778472511949)
    ·
      refine ⟨9526099258033416927191981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25402931354755778472511949 9526099258033416927191981)
      ·
        refine ⟨3572287221762531347696993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9526099258033416927191981 3572287221762531347696993)
        ·
          refine ⟨2679215416321898510772745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3572287221762531347696993 2679215416321898510772745)
          ·
            refine ⟨2009411562241423883079559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679215416321898510772745 2009411562241423883079559)
            ·
              refine ⟨3014117343362135824619339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009411562241423883079559 3014117343362135824619339)
              ·
                refine ⟨4521176015043203736929009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014117343362135824619339 4521176015043203736929009)
                ·
                  refine ⟨3390882011282402802696757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4521176015043203736929009 3390882011282402802696757)
                  ·
                    refine ⟨317895188557725262752821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3390882011282402802696757 317895188557725262752821)
                    ·
                      rfl

theorem cell22_928648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_928648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928648 prefixEnd_928648 := by exact prefixLift 928648
  have htrace : WordTrace (prefixWord ++ tailWord_928648) baseStart_928648 baseEnd_928648 := by
    simpa [prefixWord, tailWord_928648, baseEnd_928648] using wordTrace_append hprefix tailTrace_928648
  have hstable : (prefixWord ++ tailWord_928648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928648).length < 2 ^ (prefixWord ++ tailWord_928648).sum := by decide
  have hdescent : baseEnd_928648 < baseStart_928648 := by decide
  rcases family_descends (prefixWord ++ tailWord_928648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928661 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 8]
def baseStart_928661 : Nat := 118140960795 + 928661 * 2 ^ 59
def prefixEnd_928661 : Nat := 4983230072969 + 3 ^ 40 * 928661 * 2
def baseEnd_928661 : Nat := 105966546241132520725927

theorem tailTrace_928661 : CollatzResearch.WordTrace tailWord_928661 prefixEnd_928661 105966546241132520725927 := by
  unfold tailWord_928661
  simp only [CollatzResearch.WordTrace]
  refine ⟨33871049288627274516905837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22580699525751516344603891 33871049288627274516905837)
  ·
    refine ⟨12701643483235227943839689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33871049288627274516905837 12701643483235227943839689)
    ·
      refine ⟨9526232612426420957879767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12701643483235227943839689 9526232612426420957879767)
      ·
        refine ⟨14289348918639631436819651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9526232612426420957879767 14289348918639631436819651)
        ·
          refine ⟨21434023377959447155229477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14289348918639631436819651 21434023377959447155229477)
          ·
            refine ⟨4018879383367396341605527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21434023377959447155229477 4018879383367396341605527)
            ·
              refine ⟨6028319075051094512408291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018879383367396341605527 6028319075051094512408291)
              ·
                refine ⟨9042478612576641768612437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6028319075051094512408291 9042478612576641768612437)
                ·
                  refine ⟨105966546241132520725927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9042478612576641768612437 105966546241132520725927)
                  ·
                    rfl

theorem cell22_928661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_928661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928661 prefixEnd_928661 := by exact prefixLift 928661
  have htrace : WordTrace (prefixWord ++ tailWord_928661) baseStart_928661 baseEnd_928661 := by
    simpa [prefixWord, tailWord_928661, baseEnd_928661] using wordTrace_append hprefix tailTrace_928661
  have hstable : (prefixWord ++ tailWord_928661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928661).length < 2 ^ (prefixWord ++ tailWord_928661).sum := by decide
  have hdescent : baseEnd_928661 < baseStart_928661 := by decide
  rcases family_descends (prefixWord ++ tailWord_928661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928663 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 1, 4]
def baseStart_928663 : Nat := 118140960795 + 928663 * 2 ^ 59
def prefixEnd_928663 : Nat := 4983230072969 + 3 ^ 40 * 928663 * 2
def baseEnd_928663 : Nat := 317900323364270223627775

theorem tailTrace_928663 : CollatzResearch.WordTrace tailWord_928663 prefixEnd_928663 317900323364270223627775 := by
  unfold tailWord_928663
  simp only [CollatzResearch.WordTrace]
  refine ⟨33871122234620028858478643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22580748156413352572319095 33871122234620028858478643)
  ·
    refine ⟨50806683351930043287717965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33871122234620028858478643 50806683351930043287717965)
    ·
      refine ⟨19052506256973766232894237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50806683351930043287717965 19052506256973766232894237)
      ·
        refine ⟨7144689846365162337335339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19052506256973766232894237 7144689846365162337335339)
        ·
          refine ⟨10717034769547743506003009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7144689846365162337335339 10717034769547743506003009)
          ·
            refine ⟨8037776077160807629502257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10717034769547743506003009 8037776077160807629502257)
            ·
              refine ⟨6028332057870605722126693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8037776077160807629502257 6028332057870605722126693)
              ·
                refine ⟨1130312260850738572898755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6028332057870605722126693 1130312260850738572898755)
                ·
                  refine ⟨1695468391276107859348133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130312260850738572898755 1695468391276107859348133)
                  ·
                    refine ⟨317900323364270223627775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1695468391276107859348133 317900323364270223627775)
                    ·
                      rfl

theorem cell22_928663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_928663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928663 prefixEnd_928663 := by exact prefixLift 928663
  have htrace : WordTrace (prefixWord ++ tailWord_928663) baseStart_928663 baseEnd_928663 := by
    simpa [prefixWord, tailWord_928663, baseEnd_928663] using wordTrace_append hprefix tailTrace_928663
  have hstable : (prefixWord ++ tailWord_928663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928663).length < 2 ^ (prefixWord ++ tailWord_928663).sum := by decide
  have hdescent : baseEnd_928663 < baseStart_928663 := by decide
  rcases family_descends (prefixWord ++ tailWord_928663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928721 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_928721 : Nat := 118140960795 + 928721 * 2 ^ 59
def prefixEnd_928721 : Nat := 4983230072969 + 3 ^ 40 * 928721 * 2
def baseEnd_928721 : Nat := 317920177949577405677597

theorem tailTrace_928721 : CollatzResearch.WordTrace tailWord_928721 prefixEnd_928721 317920177949577405677597 := by
  unfold tailWord_928721
  simp only [CollatzResearch.WordTrace]
  refine ⟨33873237668409904764090017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22582158445606603176060011 33873237668409904764090017)
  ·
    refine ⟨25404928251307428573067513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33873237668409904764090017 25404928251307428573067513)
    ·
      refine ⟨19053696188480571429800635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25404928251307428573067513 19053696188480571429800635)
      ·
        refine ⟨28580544282720857144700953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19053696188480571429800635 28580544282720857144700953)
        ·
          refine ⟨21435408212040642858525715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28580544282720857144700953 21435408212040642858525715)
          ·
            refine ⟨32153112318060964287788573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21435408212040642858525715 32153112318060964287788573)
            ·
              refine ⟨12057417119272861607920715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32153112318060964287788573 12057417119272861607920715)
              ·
                refine ⟨18086125678909292411881073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12057417119272861607920715 18086125678909292411881073)
                ·
                  refine ⟨13564594259181969308910805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18086125678909292411881073 13564594259181969308910805)
                  ·
                    refine ⟨317920177949577405677597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13564594259181969308910805 317920177949577405677597)
                    ·
                      rfl

theorem cell22_928721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_928721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928721 prefixEnd_928721 := by exact prefixLift 928721
  have htrace : WordTrace (prefixWord ++ tailWord_928721) baseStart_928721 baseEnd_928721 := by
    simpa [prefixWord, tailWord_928721, baseEnd_928721] using wordTrace_append hprefix tailTrace_928721
  have hstable : (prefixWord ++ tailWord_928721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928721).length < 2 ^ (prefixWord ++ tailWord_928721).sum := by decide
  have hdescent : baseEnd_928721 < baseStart_928721 := by decide
  rcases family_descends (prefixWord ++ tailWord_928721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928736 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_928736 : Nat := 118140960795 + 928736 * 2 ^ 59
def prefixEnd_928736 : Nat := 4983230072969 + 3 ^ 40 * 928736 * 2
def baseEnd_928736 : Nat := 317925312756122366552551

theorem tailTrace_928736 : CollatzResearch.WordTrace tailWord_928736 prefixEnd_928736 317925312756122366552551 := by
  unfold tailWord_928736
  simp only [CollatzResearch.WordTrace]
  refine ⟨16936892381677781162943031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22582523175570374883924041 16936892381677781162943031)
  ·
    refine ⟨25405338572516671744414547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16936892381677781162943031 25405338572516671744414547)
    ·
      refine ⟨38108007858775007616621821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25405338572516671744414547 38108007858775007616621821)
      ·
        refine ⟨14290502947040627856233183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38108007858775007616621821 14290502947040627856233183)
        ·
          refine ⟨21435754420560941784349775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14290502947040627856233183 21435754420560941784349775)
          ·
            refine ⟨32153631630841412676524663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21435754420560941784349775 32153631630841412676524663)
            ·
              refine ⟨48230447446262119014786995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32153631630841412676524663 48230447446262119014786995)
              ·
                refine ⟨72345671169393178522180493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48230447446262119014786995 72345671169393178522180493)
                ·
                  refine ⟨27129626688522441945817685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72345671169393178522180493 27129626688522441945817685)
                  ·
                    refine ⟨317925312756122366552551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27129626688522441945817685 317925312756122366552551)
                    ·
                      rfl

theorem cell22_928736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_928736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928736 prefixEnd_928736 := by exact prefixLift 928736
  have htrace : WordTrace (prefixWord ++ tailWord_928736) baseStart_928736 baseEnd_928736 := by
    simpa [prefixWord, tailWord_928736, baseEnd_928736] using wordTrace_append hprefix tailTrace_928736
  have hstable : (prefixWord ++ tailWord_928736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928736).length < 2 ^ (prefixWord ++ tailWord_928736).sum := by decide
  have hdescent : baseEnd_928736 < baseStart_928736 := by decide
  rcases family_descends (prefixWord ++ tailWord_928736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928757 : List Nat := [1, 3, 5, 2, 1, 1, 2, 7]
def baseStart_928757 : Nat := 118140960795 + 928757 * 2 ^ 59
def prefixEnd_928757 : Nat := 4983230072969 + 3 ^ 40 * 928757 * 2
def baseEnd_928757 : Nat := 35325833498365034641943

theorem tailTrace_928757 : CollatzResearch.WordTrace tailWord_928757 prefixEnd_928757 35325833498365034641943 := by
  unfold tailWord_928757
  simp only [CollatzResearch.WordTrace]
  refine ⟨33874550696279482912400525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22583033797519655274933683 33874550696279482912400525)
  ·
    refine ⟨12702956511104806092150197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33874550696279482912400525 12702956511104806092150197)
    ·
      refine ⟨1190902172916075571139081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12702956511104806092150197 1190902172916075571139081)
      ·
        refine ⟨893176629687056678354311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190902172916075571139081 893176629687056678354311)
        ·
          refine ⟨1339764944530585017531467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893176629687056678354311 1339764944530585017531467)
          ·
            refine ⟨2009647416795877526297201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339764944530585017531467 2009647416795877526297201)
            ·
              refine ⟨1507235562596908144722901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009647416795877526297201 1507235562596908144722901)
              ·
                refine ⟨35325833498365034641943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1507235562596908144722901 35325833498365034641943)
                ·
                  rfl

theorem cell22_928757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 7].length) (baseStart_928757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928757 prefixEnd_928757 := by exact prefixLift 928757
  have htrace : WordTrace (prefixWord ++ tailWord_928757) baseStart_928757 baseEnd_928757 := by
    simpa [prefixWord, tailWord_928757, baseEnd_928757] using wordTrace_append hprefix tailTrace_928757
  have hstable : (prefixWord ++ tailWord_928757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928757).length < 2 ^ (prefixWord ++ tailWord_928757).sum := by decide
  have hdescent : baseEnd_928757 < baseStart_928757 := by decide
  rcases family_descends (prefixWord ++ tailWord_928757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928830 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_928830 : Nat := 118140960795 + 928830 * 2 ^ 59
def prefixEnd_928830 : Nat := 4983230072969 + 3 ^ 40 * 928830 * 2
def baseEnd_928830 : Nat := 105985830292379151567421

theorem tailTrace_928830 : CollatzResearch.WordTrace tailWord_928830 prefixEnd_928830 105985830292379151567421 := by
  unfold tailWord_928830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234651653126877047475993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22584808816676677586538629 4234651653126877047475993)
  ·
    refine ⟨3175988739845157785606995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4234651653126877047475993 3175988739845157785606995)
    ·
      refine ⟨4763983109767736678410493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3175988739845157785606995 4763983109767736678410493)
      ·
        refine ⟨1786493666162901254403935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4763983109767736678410493 1786493666162901254403935)
        ·
          refine ⟨2679740499244351881605903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786493666162901254403935 2679740499244351881605903)
          ·
            refine ⟨4019610748866527822408855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2679740499244351881605903 4019610748866527822408855)
            ·
              refine ⟨6029416123299791733613283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019610748866527822408855 6029416123299791733613283)
              ·
                refine ⟨9044124184949687600419925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029416123299791733613283 9044124184949687600419925)
                ·
                  refine ⟨105985830292379151567421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9044124184949687600419925 105985830292379151567421)
                  ·
                    rfl

theorem cell22_928830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_928830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928830 prefixEnd_928830 := by exact prefixLift 928830
  have htrace : WordTrace (prefixWord ++ tailWord_928830) baseStart_928830 baseEnd_928830 := by
    simpa [prefixWord, tailWord_928830, baseEnd_928830] using wordTrace_append hprefix tailTrace_928830
  have hstable : (prefixWord ++ tailWord_928830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928830).length < 2 ^ (prefixWord ++ tailWord_928830).sum := by decide
  have hdescent : baseEnd_928830 < baseStart_928830 := by decide
  rcases family_descends (prefixWord ++ tailWord_928830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928860 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_928860 : Nat := 118140960795 + 928860 * 2 ^ 59
def prefixEnd_928860 : Nat := 4983230072969 + 3 ^ 40 * 928860 * 2
def baseEnd_928860 : Nat := 317967760490227376452171

theorem tailTrace_928860 : CollatzResearch.WordTrace tailWord_928860 prefixEnd_928860 317967760490227376452171 := by
  unfold tailWord_928860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16939153707453165751700017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22585538276604221002266689 16939153707453165751700017)
  ·
    refine ⟨12704365280589874313775013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16939153707453165751700017 12704365280589874313775013)
    ·
      refine ⟨2382068490110601433832815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12704365280589874313775013 2382068490110601433832815)
      ·
        refine ⟨3573102735165902150749223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2382068490110601433832815 3573102735165902150749223)
        ·
          refine ⟨5359654102748853226123835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573102735165902150749223 5359654102748853226123835)
          ·
            refine ⟨8039481154123279839185753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359654102748853226123835 8039481154123279839185753)
            ·
              refine ⟨6029610865592459879389315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8039481154123279839185753 6029610865592459879389315)
              ·
                refine ⟨9044416298388689819083973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029610865592459879389315 9044416298388689819083973)
                ·
                  refine ⟨1695828055947879341078245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9044416298388689819083973 1695828055947879341078245)
                  ·
                    refine ⟨317967760490227376452171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1695828055947879341078245 317967760490227376452171)
                    ·
                      rfl

theorem cell22_928860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_928860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928860 prefixEnd_928860 := by exact prefixLift 928860
  have htrace : WordTrace (prefixWord ++ tailWord_928860) baseStart_928860 baseEnd_928860 := by
    simpa [prefixWord, tailWord_928860, baseEnd_928860] using wordTrace_append hprefix tailTrace_928860
  have hstable : (prefixWord ++ tailWord_928860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928860).length < 2 ^ (prefixWord ++ tailWord_928860).sum := by decide
  have hdescent : baseEnd_928860 < baseStart_928860 := by decide
  rcases family_descends (prefixWord ++ tailWord_928860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928888 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_928888 : Nat := 118140960795 + 928888 * 2 ^ 59
def prefixEnd_928888 : Nat := 4983230072969 + 3 ^ 40 * 928888 * 2
def baseEnd_928888 : Nat := 317977345462444636752085

theorem tailTrace_928888 : CollatzResearch.WordTrace tailWord_928888 prefixEnd_928888 317977345462444636752085 := by
  unfold tailWord_928888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16939664329402446142709659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22586219105869928190279545 16939664329402446142709659)
  ·
    refine ⟨25409496494103669214064489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16939664329402446142709659 25409496494103669214064489)
    ·
      refine ⟨19057122370577751910548367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25409496494103669214064489 19057122370577751910548367)
      ·
        refine ⟨28585683555866627865822551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19057122370577751910548367 28585683555866627865822551)
        ·
          refine ⟨42878525333799941798733827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28585683555866627865822551 42878525333799941798733827)
          ·
            refine ⟨64317788000699912698100741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42878525333799941798733827 64317788000699912698100741)
            ·
              refine ⟨12059585250131233630893889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64317788000699912698100741 12059585250131233630893889)
              ·
                refine ⟨9044688937598425223170417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12059585250131233630893889 9044688937598425223170417)
                ·
                  refine ⟨6783516703198818917377813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9044688937598425223170417 6783516703198818917377813)
                  ·
                    refine ⟨317977345462444636752085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6783516703198818917377813 317977345462444636752085)
                    ·
                      rfl

theorem cell22_928888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_928888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928888 prefixEnd_928888 := by exact prefixLift 928888
  have htrace : WordTrace (prefixWord ++ tailWord_928888) baseStart_928888 baseEnd_928888 := by
    simpa [prefixWord, tailWord_928888, baseEnd_928888] using wordTrace_append hprefix tailTrace_928888
  have hstable : (prefixWord ++ tailWord_928888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928888).length < 2 ^ (prefixWord ++ tailWord_928888).sum := by decide
  have hdescent : baseEnd_928888 < baseStart_928888 := by decide
  rcases family_descends (prefixWord ++ tailWord_928888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928920 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 7]
def baseStart_928920 : Nat := 118140960795 + 928920 * 2 ^ 59
def prefixEnd_928920 : Nat := 4983230072969 + 3 ^ 40 * 928920 * 2
def baseEnd_928920 : Nat := 105996099905469073317329

theorem tailTrace_928920 : CollatzResearch.WordTrace tailWord_928920 prefixEnd_928920 105996099905469073317329 := by
  unfold tailWord_928920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16940247897344480875292107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22586997196459307833722809 16940247897344480875292107)
  ·
    refine ⟨25410371846016721312938161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16940247897344480875292107 25410371846016721312938161)
    ·
      refine ⟨19057778884512540984703621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25410371846016721312938161 19057778884512540984703621)
      ·
        refine ⟨3573333540846101434631929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19057778884512540984703621 3573333540846101434631929)
        ·
          refine ⟨2680000155634576075973947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3573333540846101434631929 2680000155634576075973947)
          ·
            refine ⟨4020000233451864113960921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2680000155634576075973947 4020000233451864113960921)
            ·
              refine ⟨3015000175088898085470691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4020000233451864113960921 3015000175088898085470691)
              ·
                refine ⟨4522500262633347128206037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015000175088898085470691 4522500262633347128206037)
                ·
                  refine ⟨105996099905469073317329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4522500262633347128206037 105996099905469073317329)
                  ·
                    rfl

theorem cell22_928920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_928920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928920 prefixEnd_928920 := by exact prefixLift 928920
  have htrace : WordTrace (prefixWord ++ tailWord_928920) baseStart_928920 baseEnd_928920 := by
    simpa [prefixWord, tailWord_928920, baseEnd_928920] using wordTrace_append hprefix tailTrace_928920
  have hstable : (prefixWord ++ tailWord_928920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928920).length < 2 ^ (prefixWord ++ tailWord_928920).sum := by decide
  have hdescent : baseEnd_928920 < baseStart_928920 := by decide
  rcases family_descends (prefixWord ++ tailWord_928920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928924 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_928924 : Nat := 118140960795 + 928924 * 2 ^ 59
def prefixEnd_928924 : Nat := 4983230072969 + 3 ^ 40 * 928924 * 2
def baseEnd_928924 : Nat := 317989668998152542851975

theorem tailTrace_928924 : CollatzResearch.WordTrace tailWord_928924 prefixEnd_928924 317989668998152542851975 := by
  unfold tailWord_928924
  simp only [CollatzResearch.WordTrace]
  refine ⟨16940320843337235216864913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22587094457782980289153217 16940320843337235216864913)
  ·
    refine ⟨12705240632502926412648685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16940320843337235216864913 12705240632502926412648685)
    ·
      refine ⟨4764465237188597404743257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12705240632502926412648685 4764465237188597404743257)
      ·
        refine ⟨3573348927891448053557443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4764465237188597404743257 3573348927891448053557443)
        ·
          refine ⟨5360023391837172080336165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573348927891448053557443 5360023391837172080336165)
          ·
            refine ⟨1005004385969469765063031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5360023391837172080336165 1005004385969469765063031)
            ·
              refine ⟨1507506578954204647594547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005004385969469765063031 1507506578954204647594547)
              ·
                refine ⟨2261259868431306971391821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507506578954204647594547 2261259868431306971391821)
                ·
                  refine ⟨847972450661740114271933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2261259868431306971391821 847972450661740114271933)
                  ·
                    refine ⟨317989668998152542851975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 847972450661740114271933 317989668998152542851975)
                    ·
                      rfl

theorem cell22_928924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_928924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_928924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_928924 prefixEnd_928924 := by exact prefixLift 928924
  have htrace : WordTrace (prefixWord ++ tailWord_928924) baseStart_928924 baseEnd_928924 := by
    simpa [prefixWord, tailWord_928924, baseEnd_928924] using wordTrace_append hprefix tailTrace_928924
  have hstable : (prefixWord ++ tailWord_928924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928924).length < 2 ^ (prefixWord ++ tailWord_928924).sum := by decide
  have hdescent : baseEnd_928924 < baseStart_928924 := by decide
  rcases family_descends (prefixWord ++ tailWord_928924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929102 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_929102 : Nat := 118140960795 + 929102 * 2 ^ 59
def prefixEnd_929102 : Nat := 4983230072969 + 3 ^ 40 * 929102 * 2
def baseEnd_929102 : Nat := 318050602035819411901429

theorem tailTrace_929102 : CollatzResearch.WordTrace tailWord_929102 prefixEnd_929102 318050602035819411901429 := by
  unfold tailWord_929102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4235891735003700854213695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22591422586686404555806373 4235891735003700854213695)
  ·
    refine ⟨6353837602505551281320543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4235891735003700854213695 6353837602505551281320543)
    ·
      refine ⟨9530756403758326921980815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353837602505551281320543 9530756403758326921980815)
      ·
        refine ⟨14296134605637490382971223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9530756403758326921980815 14296134605637490382971223)
        ·
          refine ⟨21444201908456235574456835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14296134605637490382971223 21444201908456235574456835)
          ·
            refine ⟨32166302862684353361685253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21444201908456235574456835 32166302862684353361685253)
            ·
              refine ⟨6031181786753316255315985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32166302862684353361685253 6031181786753316255315985)
              ·
                refine ⟨4523386340064987191486989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6031181786753316255315985 4523386340064987191486989)
                ·
                  refine ⟨1696269877524370196807621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4523386340064987191486989 1696269877524370196807621)
                  ·
                    refine ⟨318050602035819411901429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696269877524370196807621 318050602035819411901429)
                    ·
                      rfl

theorem cell22_929102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_929102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929102 prefixEnd_929102 := by exact prefixLift 929102
  have htrace : WordTrace (prefixWord ++ tailWord_929102) baseStart_929102 baseEnd_929102 := by
    simpa [prefixWord, tailWord_929102, baseEnd_929102] using wordTrace_append hprefix tailTrace_929102
  have hstable : (prefixWord ++ tailWord_929102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929102).length < 2 ^ (prefixWord ++ tailWord_929102).sum := by decide
  have hdescent : baseEnd_929102 < baseStart_929102 := by decide
  rcases family_descends (prefixWord ++ tailWord_929102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929132 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_929132 : Nat := 118140960795 + 929132 * 2 ^ 59
def prefixEnd_929132 : Nat := 4983230072969 + 3 ^ 40 * 929132 * 2
def baseEnd_929132 : Nat := 318060871648909333651337

theorem tailTrace_929132 : CollatzResearch.WordTrace tailWord_929132 prefixEnd_929132 318060871648909333651337 := by
  unfold tailWord_929132
  simp only [CollatzResearch.WordTrace]
  refine ⟨16944114034960460978650825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22592152046613947971534433 16944114034960460978650825)
  ·
    refine ⟨12708085526220345733988119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16944114034960460978650825 12708085526220345733988119)
    ·
      refine ⟨19062128289330518600982179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12708085526220345733988119 19062128289330518600982179)
      ·
        refine ⟨28593192433995777901473269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19062128289330518600982179 28593192433995777901473269)
        ·
          refine ⟨2680611790687104178263119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28593192433995777901473269 2680611790687104178263119)
          ·
            refine ⟨4020917686030656267394679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2680611790687104178263119 4020917686030656267394679)
            ·
              refine ⟨6031376529045984401092019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020917686030656267394679 6031376529045984401092019)
              ·
                refine ⟨9047064793568976601638029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031376529045984401092019 9047064793568976601638029)
                ·
                  refine ⟨3392649297588366225614261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9047064793568976601638029 3392649297588366225614261)
                  ·
                    refine ⟨318060871648909333651337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3392649297588366225614261 318060871648909333651337)
                    ·
                      rfl

theorem cell22_929132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_929132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929132 prefixEnd_929132 := by exact prefixLift 929132
  have htrace : WordTrace (prefixWord ++ tailWord_929132) baseStart_929132 baseEnd_929132 := by
    simpa [prefixWord, tailWord_929132, baseEnd_929132] using wordTrace_append hprefix tailTrace_929132
  have hstable : (prefixWord ++ tailWord_929132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929132).length < 2 ^ (prefixWord ++ tailWord_929132).sum := by decide
  have hdescent : baseEnd_929132 < baseStart_929132 := by decide
  rcases family_descends (prefixWord ++ tailWord_929132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929147 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 2, 4]
def baseStart_929147 : Nat := 118140960795 + 929147 * 2 ^ 59
def prefixEnd_929147 : Nat := 4983230072969 + 3 ^ 40 * 929147 * 2
def baseEnd_929147 : Nat := 318066006455454294526291

theorem tailTrace_929147 : CollatzResearch.WordTrace tailWord_929147 prefixEnd_929147 318066006455454294526291 := by
  unfold tailWord_929147
  simp only [CollatzResearch.WordTrace]
  refine ⟨33888775164866579519097695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22592516776577719679398463 33888775164866579519097695)
  ·
    refine ⟨50833162747299869278646543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33888775164866579519097695 50833162747299869278646543)
    ·
      refine ⟨76249744120949803917969815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50833162747299869278646543 76249744120949803917969815)
      ·
        refine ⟨114374616181424705876954723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76249744120949803917969815 114374616181424705876954723)
        ·
          refine ⟨171561924272137058815432085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114374616181424705876954723 171561924272137058815432085)
          ·
            refine ⟨8041965200256424631973379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171561924272137058815432085 8041965200256424631973379)
            ·
              refine ⟨12062947800384636947960069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041965200256424631973379 12062947800384636947960069)
              ·
                refine ⟨2261802712572119427742513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12062947800384636947960069 2261802712572119427742513)
                ·
                  refine ⟨1696352034429089570806885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2261802712572119427742513 1696352034429089570806885)
                  ·
                    refine ⟨318066006455454294526291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696352034429089570806885 318066006455454294526291)
                    ·
                      rfl

theorem cell22_929147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 4].length) (baseStart_929147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929147 prefixEnd_929147 := by exact prefixLift 929147
  have htrace : WordTrace (prefixWord ++ tailWord_929147) baseStart_929147 baseEnd_929147 := by
    simpa [prefixWord, tailWord_929147, baseEnd_929147] using wordTrace_append hprefix tailTrace_929147
  have hstable : (prefixWord ++ tailWord_929147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929147).length < 2 ^ (prefixWord ++ tailWord_929147).sum := by decide
  have hdescent : baseEnd_929147 < baseStart_929147 := by decide
  rcases family_descends (prefixWord ++ tailWord_929147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929166 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_929166 : Nat := 118140960795 + 929166 * 2 ^ 59
def prefixEnd_929166 : Nat := 4983230072969 + 3 ^ 40 * 929166 * 2
def baseEnd_929166 : Nat := 318072510543744578301233

theorem tailTrace_929166 : CollatzResearch.WordTrace tailWord_929166 prefixEnd_929166 318072510543744578301233 := by
  unfold tailWord_929166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236183518974718220504919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22592978767865163842692901 4236183518974718220504919)
  ·
    refine ⟨6354275278462077330757379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4236183518974718220504919 6354275278462077330757379)
    ·
      refine ⟨9531412917693115996136069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6354275278462077330757379 9531412917693115996136069)
      ·
        refine ⟨1787139922067459249275513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9531412917693115996136069 1787139922067459249275513)
        ·
          refine ⟨1340354941550594436956635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1787139922067459249275513 1340354941550594436956635)
          ·
            refine ⟨2010532412325891655434953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340354941550594436956635 2010532412325891655434953)
            ·
              refine ⟨1507899309244418741576215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2010532412325891655434953 1507899309244418741576215)
              ·
                refine ⟨2261848963866628112364323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507899309244418741576215 2261848963866628112364323)
                ·
                  refine ⟨3392773445799942168546485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261848963866628112364323 3392773445799942168546485)
                  ·
                    refine ⟨318072510543744578301233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3392773445799942168546485 318072510543744578301233)
                    ·
                      rfl

theorem cell22_929166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_929166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929166 prefixEnd_929166 := by exact prefixLift 929166
  have htrace : WordTrace (prefixWord ++ tailWord_929166) baseStart_929166 baseEnd_929166 := by
    simpa [prefixWord, tailWord_929166, baseEnd_929166] using wordTrace_append hprefix tailTrace_929166
  have hstable : (prefixWord ++ tailWord_929166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929166).length < 2 ^ (prefixWord ++ tailWord_929166).sum := by decide
  have hdescent : baseEnd_929166 < baseStart_929166 := by decide
  rcases family_descends (prefixWord ++ tailWord_929166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929181 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_929181 : Nat := 118140960795 + 929181 * 2 ^ 59
def prefixEnd_929181 : Nat := 4983230072969 + 3 ^ 40 * 929181 * 2
def baseEnd_929181 : Nat := 318077645350289539176187

theorem tailTrace_929181 : CollatzResearch.WordTrace tailWord_929181 prefixEnd_929181 318077645350289539176187 := by
  unfold tailWord_929181
  simp only [CollatzResearch.WordTrace]
  refine ⟨33890015246743403325835397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22593343497828935550556931 33890015246743403325835397)
  ·
    refine ⟨6354377858764388123594137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33890015246743403325835397 6354377858764388123594137)
    ·
      refine ⟨4765783394073291092695603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6354377858764388123594137 4765783394073291092695603)
      ·
        refine ⟨7148675091109936639043405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765783394073291092695603 7148675091109936639043405)
        ·
          refine ⟨2680753159166226239641277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7148675091109936639043405 2680753159166226239641277)
          ·
            refine ⟨1005282434687334839865479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2680753159166226239641277 1005282434687334839865479)
            ·
              refine ⟨1507923652031002259798219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005282434687334839865479 1507923652031002259798219)
              ·
                refine ⟨2261885478046503389697329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507923652031002259798219 2261885478046503389697329)
                ·
                  refine ⟨1696414108534877542272997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2261885478046503389697329 1696414108534877542272997)
                  ·
                    refine ⟨318077645350289539176187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696414108534877542272997 318077645350289539176187)
                    ·
                      rfl

theorem cell22_929181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_929181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929181 prefixEnd_929181 := by exact prefixLift 929181
  have htrace : WordTrace (prefixWord ++ tailWord_929181) baseStart_929181 baseEnd_929181 := by
    simpa [prefixWord, tailWord_929181, baseEnd_929181] using wordTrace_append hprefix tailTrace_929181
  have hstable : (prefixWord ++ tailWord_929181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929181).length < 2 ^ (prefixWord ++ tailWord_929181).sum := by decide
  have hdescent : baseEnd_929181 < baseStart_929181 := by decide
  rcases family_descends (prefixWord ++ tailWord_929181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929207 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 7]
def baseStart_929207 : Nat := 118140960795 + 929207 * 2 ^ 59
def prefixEnd_929207 : Nat := 4983230072969 + 3 ^ 40 * 929207 * 2
def baseEnd_929207 : Nat := 106028848560544712675369

theorem tailTrace_929207 : CollatzResearch.WordTrace tailWord_929207 prefixEnd_929207 106028848560544712675369 := by
  unfold tailWord_929207
  simp only [CollatzResearch.WordTrace]
  refine ⟨33890963544649209766281875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22593975696432806510854583 33890963544649209766281875)
  ·
    refine ⟨50836445316973814649422813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33890963544649209766281875 50836445316973814649422813)
    ·
      refine ⟨19063666993865180493533555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50836445316973814649422813 19063666993865180493533555)
      ·
        refine ⟨28595500490797770740300333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19063666993865180493533555 28595500490797770740300333)
        ·
          refine ⟨10723312684049164027612625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28595500490797770740300333 10723312684049164027612625)
          ·
            refine ⟨8042484513036873020709469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10723312684049164027612625 8042484513036873020709469)
            ·
              refine ⟨3015931692388827382766051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8042484513036873020709469 3015931692388827382766051)
              ·
                refine ⟨4523897538583241074149077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015931692388827382766051 4523897538583241074149077)
                ·
                  refine ⟨106028848560544712675369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4523897538583241074149077 106028848560544712675369)
                  ·
                    rfl

theorem cell22_929207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 7].length) (baseStart_929207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929207 prefixEnd_929207 := by exact prefixLift 929207
  have htrace : WordTrace (prefixWord ++ tailWord_929207) baseStart_929207 baseEnd_929207 := by
    simpa [prefixWord, tailWord_929207, baseEnd_929207] using wordTrace_append hprefix tailTrace_929207
  have hstable : (prefixWord ++ tailWord_929207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929207).length < 2 ^ (prefixWord ++ tailWord_929207).sum := by decide
  have hdescent : baseEnd_929207 < baseStart_929207 := by decide
  rcases family_descends (prefixWord ++ tailWord_929207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929245 : List Nat := [1, 4, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_929245 : Nat := 118140960795 + 929245 * 2 ^ 59
def prefixEnd_929245 : Nat := 4983230072969 + 3 ^ 40 * 929245 * 2
def baseEnd_929245 : Nat := 318099553858214705575991

theorem tailTrace_929245 : CollatzResearch.WordTrace tailWord_929245 prefixEnd_929245 318099553858214705575991 := by
  unfold tailWord_929245
  simp only [CollatzResearch.WordTrace]
  refine ⟨33892349518511542256165189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22594899679007694837443459 33892349518511542256165189)
  ·
    refine ⟨6354815534720914173030973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33892349518511542256165189 6354815534720914173030973)
    ·
      refine ⟨2383055825520342814886615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6354815534720914173030973 2383055825520342814886615)
      ·
        refine ⟨3574583738280514222329923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383055825520342814886615 3574583738280514222329923)
        ·
          refine ⟨5361875607420771333494885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574583738280514222329923 5361875607420771333494885)
          ·
            refine ⟨1005351676391394625030291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5361875607420771333494885 1005351676391394625030291)
            ·
              refine ⟨1508027514587091937545437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005351676391394625030291 1508027514587091937545437)
              ·
                refine ⟨565510317970159476579539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1508027514587091937545437 565510317970159476579539)
                ·
                  refine ⟨848265476955239214869309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565510317970159476579539 848265476955239214869309)
                  ·
                    refine ⟨318099553858214705575991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 848265476955239214869309 318099553858214705575991)
                    ·
                      rfl

theorem cell22_929245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_929245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929245 prefixEnd_929245 := by exact prefixLift 929245
  have htrace : WordTrace (prefixWord ++ tailWord_929245) baseStart_929245 baseEnd_929245 := by
    simpa [prefixWord, tailWord_929245, baseEnd_929245] using wordTrace_append hprefix tailTrace_929245
  have hstable : (prefixWord ++ tailWord_929245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929245).length < 2 ^ (prefixWord ++ tailWord_929245).sum := by decide
  have hdescent : baseEnd_929245 < baseStart_929245 := by decide
  rcases family_descends (prefixWord ++ tailWord_929245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929252 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 8]
def baseStart_929252 : Nat := 118140960795 + 929252 * 2 ^ 59
def prefixEnd_929252 : Nat := 4983230072969 + 3 ^ 40 * 929252 * 2
def baseEnd_929252 : Nat := 106033983367089673550323

theorem tailTrace_929252 : CollatzResearch.WordTrace tailWord_929252 prefixEnd_929252 106033983367089673550323 := by
  unfold tailWord_929252
  simp only [CollatzResearch.WordTrace]
  refine ⟨16946302414743091225835005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22595069886324121634446673 16946302414743091225835005)
  ·
    refine ⟨6354863405528659209688127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16946302414743091225835005 6354863405528659209688127)
    ·
      refine ⟨9532295108292988814532191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6354863405528659209688127 9532295108292988814532191)
      ·
        refine ⟨14298442662439483221798287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9532295108292988814532191 14298442662439483221798287)
        ·
          refine ⟨21447663993659224832697431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14298442662439483221798287 21447663993659224832697431)
          ·
            refine ⟨32171495990488837249046147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21447663993659224832697431 32171495990488837249046147)
            ·
              refine ⟨48257243985733255873569221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32171495990488837249046147 48257243985733255873569221)
              ·
                refine ⟨9048233247324985476294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48257243985733255873569221 9048233247324985476294229)
                ·
                  refine ⟨106033983367089673550323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9048233247324985476294229 106033983367089673550323)
                  ·
                    rfl

theorem cell22_929252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_929252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929252 prefixEnd_929252 := by exact prefixLift 929252
  have htrace : WordTrace (prefixWord ++ tailWord_929252) baseStart_929252 baseEnd_929252 := by
    simpa [prefixWord, tailWord_929252, baseEnd_929252] using wordTrace_append hprefix tailTrace_929252
  have hstable : (prefixWord ++ tailWord_929252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929252).length < 2 ^ (prefixWord ++ tailWord_929252).sum := by decide
  have hdescent : baseEnd_929252 < baseStart_929252 := by decide
  rcases family_descends (prefixWord ++ tailWord_929252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929267 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 5, 5]
def baseStart_929267 : Nat := 118140960795 + 929267 * 2 ^ 59
def prefixEnd_929267 : Nat := 4983230072969 + 3 ^ 40 * 929267 * 2
def baseEnd_929267 : Nat := 318107084907813981525923

theorem tailTrace_929267 : CollatzResearch.WordTrace tailWord_929267 prefixEnd_929267 318107084907813981525923 := by
  unfold tailWord_929267
  simp only [CollatzResearch.WordTrace]
  refine ⟨33893151924431840013466055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22595434616287893342310703 33893151924431840013466055)
  ·
    refine ⟨50839727886647760020199083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33893151924431840013466055 50839727886647760020199083)
    ·
      refine ⟨76259591829971640030298625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50839727886647760020199083 76259591829971640030298625)
      ·
        refine ⟨57194693872478730022723969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76259591829971640030298625 57194693872478730022723969)
        ·
          refine ⟨42896020404359047517042977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57194693872478730022723969 42896020404359047517042977)
          ·
            refine ⟨32172015303269285637782233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42896020404359047517042977 32172015303269285637782233)
            ·
              refine ⟨24129011477451964228336675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32172015303269285637782233 24129011477451964228336675)
              ·
                refine ⟨36193517216177946342505013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24129011477451964228336675 36193517216177946342505013)
                ·
                  refine ⟨3393142239016682469609845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36193517216177946342505013 3393142239016682469609845)
                  ·
                    refine ⟨318107084907813981525923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3393142239016682469609845 318107084907813981525923)
                    ·
                      rfl

theorem cell22_929267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_929267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929267 prefixEnd_929267 := by exact prefixLift 929267
  have htrace : WordTrace (prefixWord ++ tailWord_929267) baseStart_929267 baseEnd_929267 := by
    simpa [prefixWord, tailWord_929267, baseEnd_929267] using wordTrace_append hprefix tailTrace_929267
  have hstable : (prefixWord ++ tailWord_929267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929267).length < 2 ^ (prefixWord ++ tailWord_929267).sum := by decide
  have hdescent : baseEnd_929267 < baseStart_929267 := by decide
  rcases family_descends (prefixWord ++ tailWord_929267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929297 : List Nat := [1, 2, 2, 1, 1, 2, 3, 10]
def baseStart_929297 : Nat := 118140960795 + 929297 * 2 ^ 59
def prefixEnd_929297 : Nat := 4983230072969 + 3 ^ 40 * 929297 * 2
def baseEnd_929297 : Nat := 35346372724544878141759

theorem tailTrace_929297 : CollatzResearch.WordTrace tailWord_929297 prefixEnd_929297 35346372724544878141759 := by
  unfold tailWord_929297
  simp only [CollatzResearch.WordTrace]
  refine ⟨33894246114323155137058145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22596164076215436758038763 33894246114323155137058145)
  ·
    refine ⟨25420684585742366352793609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33894246114323155137058145 25420684585742366352793609)
    ·
      refine ⟨19065513439306774764595207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25420684585742366352793609 19065513439306774764595207)
      ·
        refine ⟨28598270158960162146892811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19065513439306774764595207 28598270158960162146892811)
        ·
          refine ⟨42897405238440243220339217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28598270158960162146892811 42897405238440243220339217)
          ·
            refine ⟨32173053928830182415254413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42897405238440243220339217 32173053928830182415254413)
            ·
              refine ⟨12064895223311318405720405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32173053928830182415254413 12064895223311318405720405)
              ·
                refine ⟨35346372724544878141759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12064895223311318405720405 35346372724544878141759)
                ·
                  rfl

theorem cell22_929297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 10].length) (baseStart_929297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929297 prefixEnd_929297 := by exact prefixLift 929297
  have htrace : WordTrace (prefixWord ++ tailWord_929297) baseStart_929297 baseEnd_929297 := by
    simpa [prefixWord, tailWord_929297, baseEnd_929297] using wordTrace_append hprefix tailTrace_929297
  have hstable : (prefixWord ++ tailWord_929297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929297).length < 2 ^ (prefixWord ++ tailWord_929297).sum := by decide
  have hdescent : baseEnd_929297 < baseStart_929297 := by decide
  rcases family_descends (prefixWord ++ tailWord_929297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929299 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 2, 4]
def baseStart_929299 : Nat := 118140960795 + 929299 * 2 ^ 59
def prefixEnd_929299 : Nat := 4983230072969 + 3 ^ 40 * 929299 * 2
def baseEnd_929299 : Nat := 318118039161776564725825

theorem tailTrace_929299 : CollatzResearch.WordTrace tailWord_929299 prefixEnd_929299 318118039161776564725825 := by
  unfold tailWord_929299
  simp only [CollatzResearch.WordTrace]
  refine ⟨33894319060315909478630951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22596212706877272985753967 33894319060315909478630951)
  ·
    refine ⟨50841478590473864217946427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33894319060315909478630951 50841478590473864217946427)
    ·
      refine ⟨76262217885710796326919641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50841478590473864217946427 76262217885710796326919641)
      ·
        refine ⟨57196663414283097245189731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76262217885710796326919641 57196663414283097245189731)
        ·
          refine ⟨85794995121424645867784597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57196663414283097245189731 85794995121424645867784597)
          ·
            refine ⟨4021640396316780275052403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85794995121424645867784597 4021640396316780275052403)
            ·
              refine ⟨6032460594475170412578605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021640396316780275052403 6032460594475170412578605)
              ·
                refine ⟨2262172722928188904716977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6032460594475170412578605 2262172722928188904716977)
                ·
                  refine ⟨1696629542196141678537733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262172722928188904716977 1696629542196141678537733)
                  ·
                    refine ⟨318118039161776564725825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696629542196141678537733 318118039161776564725825)
                    ·
                      rfl

theorem cell22_929299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 4].length) (baseStart_929299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929299 prefixEnd_929299 := by exact prefixLift 929299
  have htrace : WordTrace (prefixWord ++ tailWord_929299) baseStart_929299 baseEnd_929299 := by
    simpa [prefixWord, tailWord_929299, baseEnd_929299] using wordTrace_append hprefix tailTrace_929299
  have hstable : (prefixWord ++ tailWord_929299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929299).length < 2 ^ (prefixWord ++ tailWord_929299).sum := by decide
  have hdescent : baseEnd_929299 < baseStart_929299 := by decide
  rcases family_descends (prefixWord ++ tailWord_929299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929419 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 3, 5]
def baseStart_929419 : Nat := 118140960795 + 929419 * 2 ^ 59
def prefixEnd_929419 : Nat := 4983230072969 + 3 ^ 40 * 929419 * 2
def baseEnd_929419 : Nat := 318159117614136251725457

theorem tailTrace_929419 : CollatzResearch.WordTrace tailWord_929419 prefixEnd_929419 318159117614136251725457 := by
  unfold tailWord_929419
  simp only [CollatzResearch.WordTrace]
  refine ⟨33898695819881169972999311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22599130546587446648666207 33898695819881169972999311)
  ·
    refine ⟨50848043729821754959498967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33898695819881169972999311 50848043729821754959498967)
    ·
      refine ⟨76272065594732632439248451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50848043729821754959498967 76272065594732632439248451)
      ·
        refine ⟨114408098392098948658872677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76272065594732632439248451 114408098392098948658872677)
        ·
          refine ⟨21451518448518552873538627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114408098392098948658872677 21451518448518552873538627)
          ·
            refine ⟨32177277672777829310307941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21451518448518552873538627 32177277672777829310307941)
            ·
              refine ⟨6033239563645842995682739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32177277672777829310307941 6033239563645842995682739)
              ·
                refine ⟨9049859345468764493524109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6033239563645842995682739 9049859345468764493524109)
                ·
                  refine ⟨3393697254550786685071541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9049859345468764493524109 3393697254550786685071541)
                  ·
                    refine ⟨318159117614136251725457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3393697254550786685071541 318159117614136251725457)
                    ·
                      rfl

theorem cell22_929419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_929419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929419 prefixEnd_929419 := by exact prefixLift 929419
  have htrace : WordTrace (prefixWord ++ tailWord_929419) baseStart_929419 baseEnd_929419 := by
    simpa [prefixWord, tailWord_929419, baseEnd_929419] using wordTrace_append hprefix tailTrace_929419
  have hstable : (prefixWord ++ tailWord_929419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929419).length < 2 ^ (prefixWord ++ tailWord_929419).sum := by decide
  have hdescent : baseEnd_929419 < baseStart_929419 := by decide
  rcases family_descends (prefixWord ++ tailWord_929419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929438 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_929438 : Nat := 118140960795 + 929438 * 2 ^ 59
def prefixEnd_929438 : Nat := 4983230072969 + 3 ^ 40 * 929438 * 2
def baseEnd_929438 : Nat := 106055207234142178500133

theorem tailTrace_929438 : CollatzResearch.WordTrace tailWord_929438 prefixEnd_929438 106055207234142178500133 := by
  unfold tailWord_929438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4237423600851542027242621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22599592537874890811960645 4237423600851542027242621)
  ·
    refine ⟨1589033850319328260215983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4237423600851542027242621 1589033850319328260215983)
    ·
      refine ⟨2383550775478992390323975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589033850319328260215983 2383550775478992390323975)
      ·
        refine ⟨3575326163218488585485963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383550775478992390323975 3575326163218488585485963)
        ·
          refine ⟨5362989244827732878228945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575326163218488585485963 5362989244827732878228945)
          ·
            refine ⟨4022241933620799658671709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5362989244827732878228945 4022241933620799658671709)
            ·
              refine ⟨1508340725107799872001891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4022241933620799658671709 1508340725107799872001891)
              ·
                refine ⟨2262511087661699808002837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508340725107799872001891 2262511087661699808002837)
                ·
                  refine ⟨106055207234142178500133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2262511087661699808002837 106055207234142178500133)
                  ·
                    rfl

theorem cell22_929438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_929438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929438 prefixEnd_929438 := by exact prefixLift 929438
  have htrace : WordTrace (prefixWord ++ tailWord_929438) baseStart_929438 baseEnd_929438 := by
    simpa [prefixWord, tailWord_929438, baseEnd_929438] using wordTrace_append hprefix tailTrace_929438
  have hstable : (prefixWord ++ tailWord_929438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929438).length < 2 ^ (prefixWord ++ tailWord_929438).sum := by decide
  have hdescent : baseEnd_929438 < baseStart_929438 := by decide
  rcases family_descends (prefixWord ++ tailWord_929438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929464 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_929464 : Nat := 118140960795 + 929464 * 2 ^ 59
def prefixEnd_929464 : Nat := 4983230072969 + 3 ^ 40 * 929464 * 2
def baseEnd_929464 : Nat := 318174522033771134350319

theorem tailTrace_929464 : CollatzResearch.WordTrace tailWord_929464 prefixEnd_929464 318174522033771134350319 := by
  unfold tailWord_929464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16950168552359071329193723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22600224736478761772258297 16950168552359071329193723)
  ·
    refine ⟨25425252828538606993790585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16950168552359071329193723 25425252828538606993790585)
    ·
      refine ⟨19068939621403955245342939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25425252828538606993790585 19068939621403955245342939)
      ·
        refine ⟨28603409432105932868014409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19068939621403955245342939 28603409432105932868014409)
        ·
          refine ⟨21452557074079449651010807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28603409432105932868014409 21452557074079449651010807)
          ·
            refine ⟨32178835611119174476516211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21452557074079449651010807 32178835611119174476516211)
            ·
              refine ⟨48268253416678761714774317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32178835611119174476516211 48268253416678761714774317)
              ·
                refine ⟨18100595031254535643040369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48268253416678761714774317 18100595031254535643040369)
                ·
                  refine ⟨13575446273440901732280277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18100595031254535643040369 13575446273440901732280277)
                  ·
                    refine ⟨318174522033771134350319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13575446273440901732280277 318174522033771134350319)
                    ·
                      rfl

theorem cell22_929464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_929464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929464 prefixEnd_929464 := by exact prefixLift 929464
  have htrace : WordTrace (prefixWord ++ tailWord_929464) baseStart_929464 baseEnd_929464 := by
    simpa [prefixWord, tailWord_929464, baseEnd_929464] using wordTrace_append hprefix tailTrace_929464
  have hstable : (prefixWord ++ tailWord_929464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929464).length < 2 ^ (prefixWord ++ tailWord_929464).sum := by decide
  have hdescent : baseEnd_929464 < baseStart_929464 := by decide
  rcases family_descends (prefixWord ++ tailWord_929464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929468 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_929468 : Nat := 118140960795 + 929468 * 2 ^ 59
def prefixEnd_929468 : Nat := 4983230072969 + 3 ^ 40 * 929468 * 2
def baseEnd_929468 : Nat := 318175891315516457250307

theorem tailTrace_929468 : CollatzResearch.WordTrace tailWord_929468 prefixEnd_929468 318175891315516457250307 := by
  unfold tailWord_929468
  simp only [CollatzResearch.WordTrace]
  refine ⟨16950241498351825670766529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22600321997802434227688705 16950241498351825670766529)
  ·
    refine ⟨12712681123763869253074897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16950241498351825670766529 12712681123763869253074897)
    ·
      refine ⟨9534510842822901939806173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12712681123763869253074897 9534510842822901939806173)
      ·
        refine ⟨3575441566058588227427315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9534510842822901939806173 3575441566058588227427315)
        ·
          refine ⟨5363162349087882341140973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575441566058588227427315 5363162349087882341140973)
          ·
            refine ⟨2011185880907955877927865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5363162349087882341140973 2011185880907955877927865)
            ·
              refine ⟨1508389410680966908445899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011185880907955877927865 1508389410680966908445899)
              ·
                refine ⟨2262584116021450362668849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508389410680966908445899 2262584116021450362668849)
                ·
                  refine ⟨1696938087016087772001637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262584116021450362668849 1696938087016087772001637)
                  ·
                    refine ⟨318175891315516457250307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696938087016087772001637 318175891315516457250307)
                    ·
                      rfl

theorem cell22_929468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_929468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929468 prefixEnd_929468 := by exact prefixLift 929468
  have htrace : WordTrace (prefixWord ++ tailWord_929468) baseStart_929468 baseEnd_929468 := by
    simpa [prefixWord, tailWord_929468, baseEnd_929468] using wordTrace_append hprefix tailTrace_929468
  have hstable : (prefixWord ++ tailWord_929468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929468).length < 2 ^ (prefixWord ++ tailWord_929468).sum := by decide
  have hdescent : baseEnd_929468 < baseStart_929468 := by decide
  rcases family_descends (prefixWord ++ tailWord_929468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929485 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_929485 : Nat := 118140960795 + 929485 * 2 ^ 59
def prefixEnd_929485 : Nat := 4983230072969 + 3 ^ 40 * 929485 * 2
def baseEnd_929485 : Nat := 318181710762934079575255

theorem tailTrace_929485 : CollatzResearch.WordTrace tailWord_929485 prefixEnd_929485 318181710762934079575255 := by
  unfold tailWord_929485
  simp only [CollatzResearch.WordTrace]
  refine ⟨33901103037642063244901909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22600735358428042163267939 33901103037642063244901909)
  ·
    refine ⟨1589114204889471714604777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33901103037642063244901909 1589114204889471714604777)
    ·
      refine ⟨1191835653667103785953583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1589114204889471714604777 1191835653667103785953583)
      ·
        refine ⟨1787753480500655678930375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191835653667103785953583 1787753480500655678930375)
        ·
          refine ⟨2681630220750983518395563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787753480500655678930375 2681630220750983518395563)
          ·
            refine ⟨4022445331126475277593345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681630220750983518395563 4022445331126475277593345)
            ·
              refine ⟨3016833998344856458195009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4022445331126475277593345 3016833998344856458195009)
              ·
                refine ⟨2262625498758642343646257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016833998344856458195009 2262625498758642343646257)
                ·
                  refine ⟨1696969124068981757734693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262625498758642343646257 1696969124068981757734693)
                  ·
                    refine ⟨318181710762934079575255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1696969124068981757734693 318181710762934079575255)
                    ·
                      rfl

theorem cell22_929485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_929485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929485 prefixEnd_929485 := by exact prefixLift 929485
  have htrace : WordTrace (prefixWord ++ tailWord_929485) baseStart_929485 baseEnd_929485 := by
    simpa [prefixWord, tailWord_929485, baseEnd_929485] using wordTrace_append hprefix tailTrace_929485
  have hstable : (prefixWord ++ tailWord_929485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929485).length < 2 ^ (prefixWord ++ tailWord_929485).sum := by decide
  have hdescent : baseEnd_929485 < baseStart_929485 := by decide
  rcases family_descends (prefixWord ++ tailWord_929485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929500 : List Nat := [2, 2, 5, 1, 2, 2, 1, 7]
def baseStart_929500 : Nat := 118140960795 + 929500 * 2 ^ 59
def prefixEnd_929500 : Nat := 4983230072969 + 3 ^ 40 * 929500 * 2
def baseEnd_929500 : Nat := 35354093952164337827801

theorem tailTrace_929500 : CollatzResearch.WordTrace tailWord_929500 prefixEnd_929500 35354093952164337827801 := by
  unfold tailWord_929500
  simp only [CollatzResearch.WordTrace]
  refine ⟨16950825066293860403348977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22601100088391813871131969 16950825066293860403348977)
  ·
    refine ⟨12713118799720395302511733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16950825066293860403348977 12713118799720395302511733)
    ·
      refine ⟨1191854887473787059610475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12713118799720395302511733 1191854887473787059610475)
      ·
        refine ⟨1787782331210680589415713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191854887473787059610475 1787782331210680589415713)
        ·
          refine ⟨1340836748408010442061785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1787782331210680589415713 1340836748408010442061785)
          ·
            refine ⟨1005627561306007831546339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340836748408010442061785 1005627561306007831546339)
            ·
              refine ⟨1508441341959011747319509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005627561306007831546339 1508441341959011747319509)
              ·
                refine ⟨35354093952164337827801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1508441341959011747319509 35354093952164337827801)
                ·
                  rfl

theorem cell22_929500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 7].length) (baseStart_929500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929500 prefixEnd_929500 := by exact prefixLift 929500
  have htrace : WordTrace (prefixWord ++ tailWord_929500) baseStart_929500 baseEnd_929500 := by
    simpa [prefixWord, tailWord_929500, baseEnd_929500] using wordTrace_append hprefix tailTrace_929500
  have hstable : (prefixWord ++ tailWord_929500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929500).length < 2 ^ (prefixWord ++ tailWord_929500).sum := by decide
  have hdescent : baseEnd_929500 < baseStart_929500 := by decide
  rcases family_descends (prefixWord ++ tailWord_929500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929603 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 2, 4]
def baseStart_929603 : Nat := 118140960795 + 929603 * 2 ^ 59
def prefixEnd_929603 : Nat := 4983230072969 + 3 ^ 40 * 929603 * 2
def baseEnd_929603 : Nat := 318222104574421105124893

theorem tailTrace_929603 : CollatzResearch.WordTrace tailWord_929603 prefixEnd_929603 318222104574421105124893 := by
  unfold tailWord_929603
  simp only [CollatzResearch.WordTrace]
  refine ⟨33905406851214569397697463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22603604567476379598464975 33905406851214569397697463)
  ·
    refine ⟨50858110276821854096546195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33905406851214569397697463 50858110276821854096546195)
    ·
      refine ⟨76287165415232781144819293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50858110276821854096546195 76287165415232781144819293)
      ·
        refine ⟨28607687030712292929307235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76287165415232781144819293 28607687030712292929307235)
        ·
          refine ⟨42911530546068439393960853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28607687030712292929307235 42911530546068439393960853)
          ·
            refine ⟨2011477994346958096591915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42911530546068439393960853 2011477994346958096591915)
            ·
              refine ⟨3017216991520437144887873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011477994346958096591915 3017216991520437144887873)
              ·
                refine ⟨2262912743640327858665905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3017216991520437144887873 2262912743640327858665905)
                ·
                  refine ⟨1697184557730245893999429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262912743640327858665905 1697184557730245893999429)
                  ·
                    refine ⟨318222104574421105124893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1697184557730245893999429 318222104574421105124893)
                    ·
                      rfl

theorem cell22_929603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 4].length) (baseStart_929603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929603 prefixEnd_929603 := by exact prefixLift 929603
  have htrace : WordTrace (prefixWord ++ tailWord_929603) baseStart_929603 baseEnd_929603 := by
    simpa [prefixWord, tailWord_929603, baseEnd_929603] using wordTrace_append hprefix tailTrace_929603
  have hstable : (prefixWord ++ tailWord_929603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929603).length < 2 ^ (prefixWord ++ tailWord_929603).sum := by decide
  have hdescent : baseEnd_929603 < baseStart_929603 := by decide
  rcases family_descends (prefixWord ++ tailWord_929603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929618 : List Nat := [3, 2, 2, 1, 1, 4, 2, 7]
def baseStart_929618 : Nat := 118140960795 + 929618 * 2 ^ 59
def prefixEnd_929618 : Nat := 4983230072969 + 3 ^ 40 * 929618 * 2
def baseEnd_929618 : Nat := 35358582153440673999983

theorem tailTrace_929618 : CollatzResearch.WordTrace tailWord_929618 prefixEnd_929618 35358582153440673999983 := by
  unfold tailWord_929618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8476488486540056739873377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22603969297440151306329005 8476488486540056739873377)
  ·
    refine ⟨6357366364905042554905033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8476488486540056739873377 6357366364905042554905033)
    ·
      refine ⟨4768024773678781916178775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6357366364905042554905033 4768024773678781916178775)
      ·
        refine ⟨7152037160518172874268163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4768024773678781916178775 7152037160518172874268163)
        ·
          refine ⟨10728055740777259311402245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7152037160518172874268163 10728055740777259311402245)
          ·
            refine ⟨2011510451395736120887921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10728055740777259311402245 2011510451395736120887921)
            ·
              refine ⟨1508632838546802090665941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011510451395736120887921 1508632838546802090665941)
              ·
                refine ⟨35358582153440673999983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1508632838546802090665941 35358582153440673999983)
                ·
                  rfl

theorem cell22_929618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_929618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929618 prefixEnd_929618 := by exact prefixLift 929618
  have htrace : WordTrace (prefixWord ++ tailWord_929618) baseStart_929618 baseEnd_929618 := by
    simpa [prefixWord, tailWord_929618, baseEnd_929618] using wordTrace_append hprefix tailTrace_929618
  have hstable : (prefixWord ++ tailWord_929618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929618).length < 2 ^ (prefixWord ++ tailWord_929618).sum := by decide
  have hdescent : baseEnd_929618 < baseStart_929618 := by decide
  rcases family_descends (prefixWord ++ tailWord_929618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929633 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 5, 3]
def baseStart_929633 : Nat := 118140960795 + 929633 * 2 ^ 59
def prefixEnd_929633 : Nat := 4983230072969 + 3 ^ 40 * 929633 * 2
def baseEnd_929633 : Nat := 318232374187511026874801

theorem tailTrace_929633 : CollatzResearch.WordTrace tailWord_929633 prefixEnd_929633 318232374187511026874801 := by
  unfold tailWord_929633
  simp only [CollatzResearch.WordTrace]
  refine ⟨33906501041105884521289553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22604334027403923014193035 33906501041105884521289553)
  ·
    refine ⟨25429875780829413390967165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33906501041105884521289553 25429875780829413390967165)
    ·
      refine ⟨9536203417811030021612687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25429875780829413390967165 9536203417811030021612687)
      ·
        refine ⟨14304305126716545032419031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536203417811030021612687 14304305126716545032419031)
        ·
          refine ⟨21456457690074817548628547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14304305126716545032419031 21456457690074817548628547)
          ·
            refine ⟨32184686535112226322942821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21456457690074817548628547 32184686535112226322942821)
            ·
              refine ⟨6034628725333542435551779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32184686535112226322942821 6034628725333542435551779)
              ·
                refine ⟨9051943088000313653327669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6034628725333542435551779 9051943088000313653327669)
                ·
                  refine ⟨848619664500029404999469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9051943088000313653327669 848619664500029404999469)
                  ·
                    refine ⟨318232374187511026874801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 848619664500029404999469 318232374187511026874801)
                    ·
                      rfl

theorem cell22_929633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_929633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929633 prefixEnd_929633 := by exact prefixLift 929633
  have htrace : WordTrace (prefixWord ++ tailWord_929633) baseStart_929633 baseEnd_929633 := by
    simpa [prefixWord, tailWord_929633, baseEnd_929633] using wordTrace_append hprefix tailTrace_929633
  have hstable : (prefixWord ++ tailWord_929633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929633).length < 2 ^ (prefixWord ++ tailWord_929633).sum := by decide
  have hdescent : baseEnd_929633 < baseStart_929633 := by decide
  rcases family_descends (prefixWord ++ tailWord_929633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929667 : List Nat := [1, 1, 1, 3, 4, 3, 1, 4, 1, 3]
def baseStart_929667 : Nat := 118140960795 + 929667 * 2 ^ 59
def prefixEnd_929667 : Nat := 4983230072969 + 3 ^ 40 * 929667 * 2
def baseEnd_929667 : Nat := 318244013082346271524697

theorem tailTrace_929667 : CollatzResearch.WordTrace tailWord_929667 prefixEnd_929667 318244013082346271524697 := by
  unfold tailWord_929667
  simp only [CollatzResearch.WordTrace]
  refine ⟨33907741122982708328027255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22605160748655138885351503 33907741122982708328027255)
  ·
    refine ⟨50861611684474062492040883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33907741122982708328027255 50861611684474062492040883)
    ·
      refine ⟨76292417526711093738061325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50861611684474062492040883 76292417526711093738061325)
      ·
        refine ⟨28609656572516660151772997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76292417526711093738061325 28609656572516660151772997)
        ·
          refine ⟨5364310607346873778457437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28609656572516660151772997 5364310607346873778457437)
          ·
            refine ⟨2011616477755077666921539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5364310607346873778457437 2011616477755077666921539)
            ·
              refine ⟨3017424716632616500382309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011616477755077666921539 3017424716632616500382309)
              ·
                refine ⟨565767134368615593821683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3017424716632616500382309 565767134368615593821683)
                ·
                  refine ⟨848650701552923390732525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565767134368615593821683 848650701552923390732525)
                  ·
                    refine ⟨318244013082346271524697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 848650701552923390732525 318244013082346271524697)
                    ·
                      rfl

theorem cell22_929667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 3].length) (baseStart_929667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929667 prefixEnd_929667 := by exact prefixLift 929667
  have htrace : WordTrace (prefixWord ++ tailWord_929667) baseStart_929667 baseEnd_929667 := by
    simpa [prefixWord, tailWord_929667, baseEnd_929667] using wordTrace_append hprefix tailTrace_929667
  have hstable : (prefixWord ++ tailWord_929667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929667).length < 2 ^ (prefixWord ++ tailWord_929667).sum := by decide
  have hdescent : baseEnd_929667 < baseStart_929667 := by decide
  rcases family_descends (prefixWord ++ tailWord_929667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929725 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 6]
def baseStart_929725 : Nat := 118140960795 + 929725 * 2 ^ 59
def prefixEnd_929725 : Nat := 4983230072969 + 3 ^ 40 * 929725 * 2
def baseEnd_929725 : Nat := 106087955889217817858173

theorem tailTrace_929725 : CollatzResearch.WordTrace tailWord_929725 prefixEnd_929725 106087955889217817858173 := by
  unfold tailWord_929725
  simp only [CollatzResearch.WordTrace]
  refine ⟨33909856556772584233638629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22606571037848389489092419 33909856556772584233638629)
  ·
    refine ⟨6358098104394859543807243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33909856556772584233638629 6358098104394859543807243)
    ·
      refine ⟨9537147156592289315710865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6358098104394859543807243 9537147156592289315710865)
      ·
        refine ⟨7152860367444216986783149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9537147156592289315710865 7152860367444216986783149)
        ·
          refine ⟨2682322637791581370043681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7152860367444216986783149 2682322637791581370043681)
          ·
            refine ⟨2011741978343686027532761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2682322637791581370043681 2011741978343686027532761)
            ·
              refine ⟨1508806483757764520649571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011741978343686027532761 1508806483757764520649571)
              ·
                refine ⟨2263209725636646780974357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508806483757764520649571 2263209725636646780974357)
                ·
                  refine ⟨106087955889217817858173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2263209725636646780974357 106087955889217817858173)
                  ·
                    rfl

theorem cell22_929725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_929725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929725 prefixEnd_929725 := by exact prefixLift 929725
  have htrace : WordTrace (prefixWord ++ tailWord_929725) baseStart_929725 baseEnd_929725 := by
    simpa [prefixWord, tailWord_929725, baseEnd_929725] using wordTrace_append hprefix tailTrace_929725
  have hstable : (prefixWord ++ tailWord_929725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929725).length < 2 ^ (prefixWord ++ tailWord_929725).sum := by decide
  have hdescent : baseEnd_929725 < baseStart_929725 := by decide
  rcases family_descends (prefixWord ++ tailWord_929725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929738 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_929738 : Nat := 118140960795 + 929738 * 2 ^ 59
def prefixEnd_929738 : Nat := 4983230072969 + 3 ^ 40 * 929738 * 2
def baseEnd_929738 : Nat := 318268317833325752999479

theorem tailTrace_929738 : CollatzResearch.WordTrace tailWord_929738 prefixEnd_929738 318268317833325752999479 := by
  unfold tailWord_929738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8477582676431371863465467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22606887137150324969241245 8477582676431371863465467)
  ·
    refine ⟨12716374014647057795198201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8477582676431371863465467 12716374014647057795198201)
    ·
      refine ⟨9537280510985293346398651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12716374014647057795198201 9537280510985293346398651)
      ·
        refine ⟨14305920766477940019597977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9537280510985293346398651 14305920766477940019597977)
        ·
          refine ⟨10729440574858455014698483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14305920766477940019597977 10729440574858455014698483)
          ·
            refine ⟨16094160862287682522047725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10729440574858455014698483 16094160862287682522047725)
            ·
              refine ⟨6035310323357880945767897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16094160862287682522047725 6035310323357880945767897)
              ·
                refine ⟨4526482742518410709325923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6035310323357880945767897 4526482742518410709325923)
                ·
                  refine ⟨6789724113777616063988885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526482742518410709325923 6789724113777616063988885)
                  ·
                    refine ⟨318268317833325752999479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6789724113777616063988885 318268317833325752999479)
                    ·
                      rfl

theorem cell22_929738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_929738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929738 prefixEnd_929738 := by exact prefixLift 929738
  have htrace : WordTrace (prefixWord ++ tailWord_929738) baseStart_929738 baseEnd_929738 := by
    simpa [prefixWord, tailWord_929738, baseEnd_929738] using wordTrace_append hprefix tailTrace_929738
  have hstable : (prefixWord ++ tailWord_929738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929738).length < 2 ^ (prefixWord ++ tailWord_929738).sum := by decide
  have hdescent : baseEnd_929738 < baseStart_929738 := by decide
  rcases family_descends (prefixWord ++ tailWord_929738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929740 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_929740 : Nat := 118140960795 + 929740 * 2 ^ 59
def prefixEnd_929740 : Nat := 4983230072969 + 3 ^ 40 * 929740 * 2
def baseEnd_929740 : Nat := 318269002474198414449473

theorem tailTrace_929740 : CollatzResearch.WordTrace tailWord_929740 prefixEnd_929740 318269002474198414449473 := by
  unfold tailWord_929740
  simp only [CollatzResearch.WordTrace]
  refine ⟨16955201825859120897717337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22606935767812161196956449 16955201825859120897717337)
  ·
    refine ⟨12716401369394340673288003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16955201825859120897717337 12716401369394340673288003)
    ·
      refine ⟨19074602054091511009932005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12716401369394340673288003 19074602054091511009932005)
      ·
        refine ⟨3576487885142158314362251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19074602054091511009932005 3576487885142158314362251)
        ·
          refine ⟨5364731827713237471543377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3576487885142158314362251 5364731827713237471543377)
          ·
            refine ⟨4023548870784928103657533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5364731827713237471543377 4023548870784928103657533)
            ·
              refine ⟨1508830826544348038871575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4023548870784928103657533 1508830826544348038871575)
              ·
                refine ⟨2263246239816522058307363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508830826544348038871575 2263246239816522058307363)
                ·
                  refine ⟨3394869359724783087461045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263246239816522058307363 3394869359724783087461045)
                  ·
                    refine ⟨318269002474198414449473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3394869359724783087461045 318269002474198414449473)
                    ·
                      rfl

theorem cell22_929740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_929740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929740 prefixEnd_929740 := by exact prefixLift 929740
  have htrace : WordTrace (prefixWord ++ tailWord_929740) baseStart_929740 baseEnd_929740 := by
    simpa [prefixWord, tailWord_929740, baseEnd_929740] using wordTrace_append hprefix tailTrace_929740
  have hstable : (prefixWord ++ tailWord_929740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929740).length < 2 ^ (prefixWord ++ tailWord_929740).sum := by decide
  have hdescent : baseEnd_929740 < baseStart_929740 := by decide
  rcases family_descends (prefixWord ++ tailWord_929740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929845 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_929845 : Nat := 118140960795 + 929845 * 2 ^ 59
def prefixEnd_929845 : Nat := 4983230072969 + 3 ^ 40 * 929845 * 2
def baseEnd_929845 : Nat := 318304946120013140574151

theorem tailTrace_929845 : CollatzResearch.WordTrace tailWord_929845 prefixEnd_929845 318304946120013140574151 := by
  unfold tailWord_929845
  simp only [CollatzResearch.WordTrace]
  refine ⟨33914233316337844728006989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22609488877558563152004659 33914233316337844728006989)
  ·
    refine ⟨12717837493626691773002621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33914233316337844728006989 12717837493626691773002621)
    ·
      refine ⟨4769189060110009414875983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12717837493626691773002621 4769189060110009414875983)
      ·
        refine ⟨7153783590165014122313975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4769189060110009414875983 7153783590165014122313975)
        ·
          refine ⟨10730675385247521183470963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7153783590165014122313975 10730675385247521183470963)
          ·
            refine ⟨16096013077871281775206445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10730675385247521183470963 16096013077871281775206445)
            ·
              refine ⟨6036004904201730665702417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16096013077871281775206445 6036004904201730665702417)
              ·
                refine ⟨4527003678151297999276813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6036004904201730665702417 4527003678151297999276813)
                ·
                  refine ⟨1697626379306736749728805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4527003678151297999276813 1697626379306736749728805)
                  ·
                    refine ⟨318304946120013140574151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1697626379306736749728805 318304946120013140574151)
                    ·
                      rfl

theorem cell22_929845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_929845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929845 prefixEnd_929845 := by exact prefixLift 929845
  have htrace : WordTrace (prefixWord ++ tailWord_929845) baseStart_929845 baseEnd_929845 := by
    simpa [prefixWord, tailWord_929845, baseEnd_929845] using wordTrace_append hprefix tailTrace_929845
  have hstable : (prefixWord ++ tailWord_929845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929845).length < 2 ^ (prefixWord ++ tailWord_929845).sum := by decide
  have hdescent : baseEnd_929845 < baseStart_929845 := by decide
  rcases family_descends (prefixWord ++ tailWord_929845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929877 : List Nat := [1, 3, 2, 2, 1, 3, 1, 5, 4]
def baseStart_929877 : Nat := 118140960795 + 929877 * 2 ^ 59
def prefixEnd_929877 : Nat := 4983230072969 + 3 ^ 40 * 929877 * 2
def baseEnd_929877 : Nat := 106105300124658574591351

theorem tailTrace_929877 : CollatzResearch.WordTrace tailWord_929877 prefixEnd_929877 106105300124658574591351 := by
  unfold tailWord_929877
  simp only [CollatzResearch.WordTrace]
  refine ⟨33915400452221914193171885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22610266968147942795447923 33915400452221914193171885)
  ·
    refine ⟨12718275169583217822439457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33915400452221914193171885 12718275169583217822439457)
    ·
      refine ⟨9538706377187413366829593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12718275169583217822439457 9538706377187413366829593)
      ·
        refine ⟨7154029782890560025122195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9538706377187413366829593 7154029782890560025122195)
        ·
          refine ⟨10731044674335840037683293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154029782890560025122195 10731044674335840037683293)
          ·
            refine ⟨4024141752875940014131235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10731044674335840037683293 4024141752875940014131235)
            ·
              refine ⟨6036212629313910021196853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024141752875940014131235 6036212629313910021196853)
              ·
                refine ⟨565894933998179064487205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6036212629313910021196853 565894933998179064487205)
                ·
                  refine ⟨106105300124658574591351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565894933998179064487205 106105300124658574591351)
                  ·
                    rfl

theorem cell22_929877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_929877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_929877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_929877 prefixEnd_929877 := by exact prefixLift 929877
  have htrace : WordTrace (prefixWord ++ tailWord_929877) baseStart_929877 baseEnd_929877 := by
    simpa [prefixWord, tailWord_929877, baseEnd_929877] using wordTrace_append hprefix tailTrace_929877
  have hstable : (prefixWord ++ tailWord_929877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929877).length < 2 ^ (prefixWord ++ tailWord_929877).sum := by decide
  have hdescent : baseEnd_929877 < baseStart_929877 := by decide
  rcases family_descends (prefixWord ++ tailWord_929877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930005 : List Nat := [1, 3, 2, 4, 2, 2, 2, 2, 1, 3]
def baseStart_930005 : Nat := 118140960795 + 930005 * 2 ^ 59
def prefixEnd_930005 : Nat := 4983230072969 + 3 ^ 40 * 930005 * 2
def baseEnd_930005 : Nat := 318359717389826056573661

theorem tailTrace_930005 : CollatzResearch.WordTrace tailWord_930005 prefixEnd_930005 318359717389826056573661 := by
  unfold tailWord_930005
  simp only [CollatzResearch.WordTrace]
  refine ⟨33920068995758192053831469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22613379330505461369220979 33920068995758192053831469)
  ·
    refine ⟨12720025873409322020186801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33920068995758192053831469 12720025873409322020186801)
    ·
      refine ⟨9540019405056991515140101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12720025873409322020186801 9540019405056991515140101)
      ·
        refine ⟨1788753638448185909088769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9540019405056991515140101 1788753638448185909088769)
        ·
          refine ⟨1341565228836139431816577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1788753638448185909088769 1341565228836139431816577)
          ·
            refine ⟨1006173921627104573862433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341565228836139431816577 1006173921627104573862433)
            ·
              refine ⟨754630441220328430396825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006173921627104573862433 754630441220328430396825)
              ·
                refine ⟨565972830915246322797619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754630441220328430396825 565972830915246322797619)
                ·
                  refine ⟨848959246372869484196429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565972830915246322797619 848959246372869484196429)
                  ·
                    refine ⟨318359717389826056573661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 848959246372869484196429 318359717389826056573661)
                    ·
                      rfl

theorem cell22_930005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_930005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930005 prefixEnd_930005 := by exact prefixLift 930005
  have htrace : WordTrace (prefixWord ++ tailWord_930005) baseStart_930005 baseEnd_930005 := by
    simpa [prefixWord, tailWord_930005, baseEnd_930005] using wordTrace_append hprefix tailTrace_930005
  have hstable : (prefixWord ++ tailWord_930005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930005).length < 2 ^ (prefixWord ++ tailWord_930005).sum := by decide
  have hdescent : baseEnd_930005 < baseStart_930005 := by decide
  rcases family_descends (prefixWord ++ tailWord_930005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930025 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_930025 : Nat := 118140960795 + 930025 * 2 ^ 59
def prefixEnd_930025 : Nat := 4983230072969 + 3 ^ 40 * 930025 * 2
def baseEnd_930025 : Nat := 318366563798552671073599

theorem tailTrace_930025 : CollatzResearch.WordTrace tailWord_930025 prefixEnd_930025 318366563798552671073599 := by
  unfold tailWord_930025
  simp only [CollatzResearch.WordTrace]
  refine ⟨33920798455685735469559529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22613865637123823646373019 33920798455685735469559529)
  ·
    refine ⟨25440598841764301602169647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33920798455685735469559529 25440598841764301602169647)
    ·
      refine ⟨38160898262646452403254471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25440598841764301602169647 38160898262646452403254471)
      ·
        refine ⟨57241347393969678604881707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38160898262646452403254471 57241347393969678604881707)
        ·
          refine ⟨85862021090954517907322561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57241347393969678604881707 85862021090954517907322561)
          ·
            refine ⟨64396515818215888430491921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85862021090954517907322561 64396515818215888430491921)
            ·
              refine ⟨48297386863661916322868941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64396515818215888430491921 48297386863661916322868941)
              ·
                refine ⟨18111520073873218621075853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48297386863661916322868941 18111520073873218621075853)
                ·
                  refine ⟨6791820027702456982903445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18111520073873218621075853 6791820027702456982903445)
                  ·
                    refine ⟨318366563798552671073599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6791820027702456982903445 318366563798552671073599)
                    ·
                      rfl

theorem cell22_930025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_930025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930025 prefixEnd_930025 := by exact prefixLift 930025
  have htrace : WordTrace (prefixWord ++ tailWord_930025) baseStart_930025 baseEnd_930025 := by
    simpa [prefixWord, tailWord_930025, baseEnd_930025] using wordTrace_append hprefix tailTrace_930025
  have hstable : (prefixWord ++ tailWord_930025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930025).length < 2 ^ (prefixWord ++ tailWord_930025).sum := by decide
  have hdescent : baseEnd_930025 < baseStart_930025 := by decide
  rcases family_descends (prefixWord ++ tailWord_930025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930027 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 1, 5]
def baseStart_930027 : Nat := 118140960795 + 930027 * 2 ^ 59
def prefixEnd_930027 : Nat := 4983230072969 + 3 ^ 40 * 930027 * 2
def baseEnd_930027 : Nat := 318367248439425332523593

theorem tailTrace_930027 : CollatzResearch.WordTrace tailWord_930027 prefixEnd_930027 318367248439425332523593 := by
  unfold tailWord_930027
  simp only [CollatzResearch.WordTrace]
  refine ⟨33920871401678489811132335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22613914267785659874088223 33920871401678489811132335)
  ·
    refine ⟨50881307102517734716698503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33920871401678489811132335 50881307102517734716698503)
    ·
      refine ⟨76321960653776602075047755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50881307102517734716698503 76321960653776602075047755)
      ·
        refine ⟨114482940980664903112571633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76321960653776602075047755 114482940980664903112571633)
        ·
          refine ⟨85862205735498677334428725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114482940980664903112571633 85862205735498677334428725)
          ·
            refine ⟨8049581787703001000102693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85862205735498677334428725 8049581787703001000102693)
            ·
              refine ⟨1509296585194312687519255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8049581787703001000102693 1509296585194312687519255)
              ·
                refine ⟨2263944877791469031278883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509296585194312687519255 2263944877791469031278883)
                ·
                  refine ⟨3395917316687203546918325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263944877791469031278883 3395917316687203546918325)
                  ·
                    refine ⟨318367248439425332523593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3395917316687203546918325 318367248439425332523593)
                    ·
                      rfl

theorem cell22_930027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 5].length) (baseStart_930027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930027 prefixEnd_930027 := by exact prefixLift 930027
  have htrace : WordTrace (prefixWord ++ tailWord_930027) baseStart_930027 baseEnd_930027 := by
    simpa [prefixWord, tailWord_930027, baseEnd_930027] using wordTrace_append hprefix tailTrace_930027
  have hstable : (prefixWord ++ tailWord_930027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930027).length < 2 ^ (prefixWord ++ tailWord_930027).sum := by decide
  have hdescent : baseEnd_930027 < baseStart_930027 := by decide
  rcases family_descends (prefixWord ++ tailWord_930027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930029 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 6]
def baseStart_930029 : Nat := 118140960795 + 930029 * 2 ^ 59
def prefixEnd_930029 : Nat := 4983230072969 + 3 ^ 40 * 930029 * 2
def baseEnd_930029 : Nat := 106122644360099331324529

theorem tailTrace_930029 : CollatzResearch.WordTrace tailWord_930029 prefixEnd_930029 106122644360099331324529 := by
  unfold tailWord_930029
  simp only [CollatzResearch.WordTrace]
  refine ⟨33920944347671244152705141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22613962898447496101803427 33920944347671244152705141)
  ·
    refine ⟨3180088532594179139316107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33920944347671244152705141 3180088532594179139316107)
    ·
      refine ⟨4770132798891268708974161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180088532594179139316107 4770132798891268708974161)
      ·
        refine ⟨3577599599168451531730621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4770132798891268708974161 3577599599168451531730621)
        ·
          refine ⟨1341599849688169324398983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3577599599168451531730621 1341599849688169324398983)
          ·
            refine ⟨2012399774532253986598475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341599849688169324398983 2012399774532253986598475)
            ·
              refine ⟨3018599661798380979897713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012399774532253986598475 3018599661798380979897713)
              ·
                refine ⟨2263949746348785734923285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018599661798380979897713 2263949746348785734923285)
                ·
                  refine ⟨106122644360099331324529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2263949746348785734923285 106122644360099331324529)
                  ·
                    rfl

theorem cell22_930029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_930029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930029 prefixEnd_930029 := by exact prefixLift 930029
  have htrace : WordTrace (prefixWord ++ tailWord_930029) baseStart_930029 baseEnd_930029 := by
    simpa [prefixWord, tailWord_930029, baseEnd_930029] using wordTrace_append hprefix tailTrace_930029
  have hstable : (prefixWord ++ tailWord_930029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930029).length < 2 ^ (prefixWord ++ tailWord_930029).sum := by decide
  have hdescent : baseEnd_930029 < baseStart_930029 := by decide
  rcases family_descends (prefixWord ++ tailWord_930029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930040 : List Nat := [2, 1, 2, 1, 1, 2, 1, 12]
def baseStart_930040 : Nat := 118140960795 + 930040 * 2 ^ 59
def prefixEnd_930040 : Nat := 4983230072969 + 3 ^ 40 * 930040 * 2
def baseEnd_930040 : Nat := 35374633178344181327617

theorem tailTrace_930040 : CollatzResearch.WordTrace tailWord_930040 prefixEnd_930040 35374633178344181327617 := by
  unfold tailWord_930040
  simp only [CollatzResearch.WordTrace]
  refine ⟨16960672775315696515677787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22614230367087595354237049 16960672775315696515677787)
  ·
    refine ⟨25441009162973544773516681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16960672775315696515677787 25441009162973544773516681)
    ·
      refine ⟨19080756872230158580137511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25441009162973544773516681 19080756872230158580137511)
      ·
        refine ⟨28621135308345237870206267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19080756872230158580137511 28621135308345237870206267)
        ·
          refine ⟨42931702962517856805309401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28621135308345237870206267 42931702962517856805309401)
          ·
            refine ⟨32198777221888392603982051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42931702962517856805309401 32198777221888392603982051)
            ·
              refine ⟨48298165832832588905973077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32198777221888392603982051 48298165832832588905973077)
              ·
                refine ⟨35374633178344181327617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 48298165832832588905973077 35374633178344181327617)
                ·
                  rfl

theorem cell22_930040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 12].length) (baseStart_930040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930040 prefixEnd_930040 := by exact prefixLift 930040
  have htrace : WordTrace (prefixWord ++ tailWord_930040) baseStart_930040 baseEnd_930040 := by
    simpa [prefixWord, tailWord_930040, baseEnd_930040] using wordTrace_append hprefix tailTrace_930040
  have hstable : (prefixWord ++ tailWord_930040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930040).length < 2 ^ (prefixWord ++ tailWord_930040).sum := by decide
  have hdescent : baseEnd_930040 < baseStart_930040 := by decide
  rcases family_descends (prefixWord ++ tailWord_930040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930042 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_930042 : Nat := 118140960795 + 930042 * 2 ^ 59
def prefixEnd_930042 : Nat := 4983230072969 + 3 ^ 40 * 930042 * 2
def baseEnd_930042 : Nat := 318372383245970293398547

theorem tailTrace_930042 : CollatzResearch.WordTrace tailWord_930042 prefixEnd_930042 318372383245970293398547 := by
  unfold tailWord_930042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8480354624156036843232095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22614278997749431581952253 8480354624156036843232095)
  ·
    refine ⟨12720531936234055264848143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8480354624156036843232095 12720531936234055264848143)
    ·
      refine ⟨19080797904351082897272215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12720531936234055264848143 19080797904351082897272215)
      ·
        refine ⟨28621196856526624345908323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19080797904351082897272215 28621196856526624345908323)
        ·
          refine ⟨42931795284789936518862485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28621196856526624345908323 42931795284789936518862485)
          ·
            refine ⟨2012427903974528274321679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42931795284789936518862485 2012427903974528274321679)
            ·
              refine ⟨3018641855961792411482519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012427903974528274321679 3018641855961792411482519)
              ·
                refine ⟨4527962783942688617223779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3018641855961792411482519 4527962783942688617223779)
                ·
                  refine ⟨6791944175914032925835669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4527962783942688617223779 6791944175914032925835669)
                  ·
                    refine ⟨318372383245970293398547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6791944175914032925835669 318372383245970293398547)
                    ·
                      rfl

theorem cell22_930042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_930042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930042 prefixEnd_930042 := by exact prefixLift 930042
  have htrace : WordTrace (prefixWord ++ tailWord_930042) baseStart_930042 baseEnd_930042 := by
    simpa [prefixWord, tailWord_930042, baseEnd_930042] using wordTrace_append hprefix tailTrace_930042
  have hstable : (prefixWord ++ tailWord_930042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930042).length < 2 ^ (prefixWord ++ tailWord_930042).sum := by decide
  have hdescent : baseEnd_930042 < baseStart_930042 := by decide
  rcases family_descends (prefixWord ++ tailWord_930042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930046 : List Nat := [4, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_930046 : Nat := 118140960795 + 930046 * 2 ^ 59
def prefixEnd_930046 : Nat := 4983230072969 + 3 ^ 40 * 930046 * 2
def baseEnd_930046 : Nat := 106124584175905205432845

theorem tailTrace_930046 : CollatzResearch.WordTrace tailWord_930046 prefixEnd_930046 106124584175905205432845 := by
  unfold tailWord_930046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240195548576207007009249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22614376259073104037382661 4240195548576207007009249)
  ·
    refine ⟨3180146661432155255256937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4240195548576207007009249 3180146661432155255256937)
    ·
      refine ⟨2385109996074116441442703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3180146661432155255256937 2385109996074116441442703)
      ·
        refine ⟨3577664994111174662164055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385109996074116441442703 3577664994111174662164055)
        ·
          refine ⟨5366497491166761993246083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577664994111174662164055 5366497491166761993246083)
          ·
            refine ⟨8049746236750142989869125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366497491166761993246083 8049746236750142989869125)
            ·
              refine ⟨1509327419390651810600461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8049746236750142989869125 1509327419390651810600461)
              ·
                refine ⟨565997782271494428975173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1509327419390651810600461 565997782271494428975173)
                ·
                  refine ⟨106124584175905205432845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565997782271494428975173 106124584175905205432845)
                  ·
                    rfl

theorem cell22_930046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_930046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930046 prefixEnd_930046 := by exact prefixLift 930046
  have htrace : WordTrace (prefixWord ++ tailWord_930046) baseStart_930046 baseEnd_930046 := by
    simpa [prefixWord, tailWord_930046, baseEnd_930046] using wordTrace_append hprefix tailTrace_930046
  have hstable : (prefixWord ++ tailWord_930046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930046).length < 2 ^ (prefixWord ++ tailWord_930046).sum := by decide
  have hdescent : baseEnd_930046 < baseStart_930046 := by decide
  rcases family_descends (prefixWord ++ tailWord_930046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930078 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_930078 : Nat := 118140960795 + 930078 * 2 ^ 59
def prefixEnd_930078 : Nat := 4983230072969 + 3 ^ 40 * 930078 * 2
def baseEnd_930078 : Nat := 318384706781678199498437

theorem tailTrace_930078 : CollatzResearch.WordTrace tailWord_930078 prefixEnd_930078 318384706781678199498437 := by
  unfold tailWord_930078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240341440561715690154861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22615154349662483680825925 4240341440561715690154861)
  ·
    refine ⟨1590128040210643383808073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4240341440561715690154861 1590128040210643383808073)
    ·
      refine ⟨1192596030157982537856055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1590128040210643383808073 1192596030157982537856055)
      ·
        refine ⟨1788894045236973806784083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192596030157982537856055 1788894045236973806784083)
        ·
          refine ⟨2683341067855460710176125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788894045236973806784083 2683341067855460710176125)
          ·
            refine ⟨1006252900445797766316047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2683341067855460710176125 1006252900445797766316047)
            ·
              refine ⟨1509379350668696649474071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006252900445797766316047 1509379350668696649474071)
              ·
                refine ⟨2264069026003044974211107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509379350668696649474071 2264069026003044974211107)
                ·
                  refine ⟨3396103539004567461316661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264069026003044974211107 3396103539004567461316661)
                  ·
                    refine ⟨318384706781678199498437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3396103539004567461316661 318384706781678199498437)
                    ·
                      rfl

theorem cell22_930078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_930078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930078 prefixEnd_930078 := by exact prefixLift 930078
  have htrace : WordTrace (prefixWord ++ tailWord_930078) baseStart_930078 baseEnd_930078 := by
    simpa [prefixWord, tailWord_930078, baseEnd_930078] using wordTrace_append hprefix tailTrace_930078
  have hstable : (prefixWord ++ tailWord_930078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930078).length < 2 ^ (prefixWord ++ tailWord_930078).sum := by decide
  have hdescent : baseEnd_930078 < baseStart_930078 := by decide
  rcases family_descends (prefixWord ++ tailWord_930078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930147 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 8]
def baseStart_930147 : Nat := 118140960795 + 930147 * 2 ^ 59
def prefixEnd_930147 : Nat := 4983230072969 + 3 ^ 40 * 930147 * 2
def baseEnd_930147 : Nat := 106136108963928339841075

theorem tailTrace_930147 : CollatzResearch.WordTrace tailWord_930147 prefixEnd_930147 106136108963928339841075 := by
  unfold tailWord_930147
  simp only [CollatzResearch.WordTrace]
  refine ⟨33925248161243750305500695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22616832107495833537000463 33925248161243750305500695)
  ·
    refine ⟨50887872241865625458251043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33925248161243750305500695 50887872241865625458251043)
    ·
      refine ⟨76331808362798438187376565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50887872241865625458251043 76331808362798438187376565)
      ·
        refine ⟨7156107034012353580066553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76331808362798438187376565 7156107034012353580066553)
        ·
          refine ⟨5367080275509265185049915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7156107034012353580066553 5367080275509265185049915)
          ·
            refine ⟨8050620413263897777574873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367080275509265185049915 8050620413263897777574873)
            ·
              refine ⟨6037965309947923333181155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8050620413263897777574873 6037965309947923333181155)
              ·
                refine ⟨9056947964921884999771733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037965309947923333181155 9056947964921884999771733)
                ·
                  refine ⟨106136108963928339841075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9056947964921884999771733 106136108963928339841075)
                  ·
                    rfl

theorem cell22_930147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 8].length) (baseStart_930147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930147 prefixEnd_930147 := by exact prefixLift 930147
  have htrace : WordTrace (prefixWord ++ tailWord_930147) baseStart_930147 baseEnd_930147 := by
    simpa [prefixWord, tailWord_930147, baseEnd_930147] using wordTrace_append hprefix tailTrace_930147
  have hstable : (prefixWord ++ tailWord_930147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930147).length < 2 ^ (prefixWord ++ tailWord_930147).sum := by decide
  have hdescent : baseEnd_930147 < baseStart_930147 := by decide
  rcases family_descends (prefixWord ++ tailWord_930147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930149 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_930149 : Nat := 118140960795 + 930149 * 2 ^ 59
def prefixEnd_930149 : Nat := 4983230072969 + 3 ^ 40 * 930149 * 2
def baseEnd_930149 : Nat := 318409011532657680973219

theorem tailTrace_930149 : CollatzResearch.WordTrace tailWord_930149 prefixEnd_930149 318409011532657680973219 := by
  unfold tailWord_930149
  simp only [CollatzResearch.WordTrace]
  refine ⟨33925321107236504647073501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22616880738157669764715667 33925321107236504647073501)
  ·
    refine ⟨12721995415213689242652563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33925321107236504647073501 12721995415213689242652563)
    ·
      refine ⟨19082993122820533863978845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12721995415213689242652563 19082993122820533863978845)
      ·
        refine ⟨7156122421057700198992067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19082993122820533863978845 7156122421057700198992067)
        ·
          refine ⟨10734183631586550298488101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156122421057700198992067 10734183631586550298488101)
          ·
            refine ⟨2012659430922478180966519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10734183631586550298488101 2012659430922478180966519)
            ·
              refine ⟨3018989146383717271449779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012659430922478180966519 3018989146383717271449779)
              ·
                refine ⟨4528483719575575907174669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3018989146383717271449779 4528483719575575907174669)
                ·
                  refine ⟨1698181394840840965190501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4528483719575575907174669 1698181394840840965190501)
                  ·
                    refine ⟨318409011532657680973219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698181394840840965190501 318409011532657680973219)
                    ·
                      rfl

theorem cell22_930149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_930149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930149 prefixEnd_930149 := by exact prefixLift 930149
  have htrace : WordTrace (prefixWord ++ tailWord_930149) baseStart_930149 baseEnd_930149 := by
    simpa [prefixWord, tailWord_930149, baseEnd_930149] using wordTrace_append hprefix tailTrace_930149
  have hstable : (prefixWord ++ tailWord_930149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930149).length < 2 ^ (prefixWord ++ tailWord_930149).sum := by decide
  have hdescent : baseEnd_930149 < baseStart_930149 := by decide
  rcases family_descends (prefixWord ++ tailWord_930149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930211 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 2, 4]
def baseStart_930211 : Nat := 118140960795 + 930211 * 2 ^ 59
def prefixEnd_930211 : Nat := 4983230072969 + 3 ^ 40 * 930211 * 2
def baseEnd_930211 : Nat := 318430235399710185923029

theorem tailTrace_930211 : CollatzResearch.WordTrace tailWord_930211 prefixEnd_930211 318430235399710185923029 := by
  unfold tailWord_930211
  simp only [CollatzResearch.WordTrace]
  refine ⟨33927582433011889235830487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22618388288674592823886991 33927582433011889235830487)
  ·
    refine ⟨50891373649517833853745731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33927582433011889235830487 50891373649517833853745731)
    ·
      refine ⟨76337060474276750780618597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50891373649517833853745731 76337060474276750780618597)
      ·
        refine ⟨14313198838926890771365987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76337060474276750780618597 14313198838926890771365987)
        ·
          refine ⟨21469798258390336157048981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14313198838926890771365987 21469798258390336157048981)
          ·
            refine ⟨1006396793362047007361671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21469798258390336157048981 1006396793362047007361671)
            ·
              refine ⟨1509595190043070511042507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006396793362047007361671 1509595190043070511042507)
              ·
                refine ⟨2264392785064605766563761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509595190043070511042507 2264392785064605766563761)
                ·
                  refine ⟨1698294588798454324922821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2264392785064605766563761 1698294588798454324922821)
                  ·
                    refine ⟨318430235399710185923029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698294588798454324922821 318430235399710185923029)
                    ·
                      rfl

theorem cell22_930211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 4].length) (baseStart_930211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930211 prefixEnd_930211 := by exact prefixLift 930211
  have htrace : WordTrace (prefixWord ++ tailWord_930211) baseStart_930211 baseEnd_930211 := by
    simpa [prefixWord, tailWord_930211, baseEnd_930211] using wordTrace_append hprefix tailTrace_930211
  have hstable : (prefixWord ++ tailWord_930211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930211).length < 2 ^ (prefixWord ++ tailWord_930211).sum := by decide
  have hdescent : baseEnd_930211 < baseStart_930211 := by decide
  rcases family_descends (prefixWord ++ tailWord_930211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930318 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_930318 : Nat := 118140960795 + 930318 * 2 ^ 59
def prefixEnd_930318 : Nat := 4983230072969 + 3 ^ 40 * 930318 * 2
def baseEnd_930318 : Nat := 318466863686397573497701

theorem tailTrace_930318 : CollatzResearch.WordTrace tailWord_930318 prefixEnd_930318 318466863686397573497701 := by
  unfold tailWord_930318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241435630453030813746951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22620990029082831006650405 4241435630453030813746951)
  ·
    refine ⟨6362153445679546220620427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4241435630453030813746951 6362153445679546220620427)
    ·
      refine ⟨9543230168519319330930641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6362153445679546220620427 9543230168519319330930641)
      ·
        refine ⟨7157422626389489498197981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9543230168519319330930641 7157422626389489498197981)
        ·
          refine ⟨2684033484896058561824243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7157422626389489498197981 2684033484896058561824243)
          ·
            refine ⟨4026050227344087842736365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684033484896058561824243 4026050227344087842736365)
            ·
              refine ⟨1509768835254032941026137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4026050227344087842736365 1509768835254032941026137)
              ·
                refine ⟨1132326626440524705769603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509768835254032941026137 1132326626440524705769603)
                ·
                  refine ⟨1698489939660787058654405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132326626440524705769603 1698489939660787058654405)
                  ·
                    refine ⟨318466863686397573497701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698489939660787058654405 318466863686397573497701)
                    ·
                      rfl

theorem cell22_930318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_930318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930318 prefixEnd_930318 := by exact prefixLift 930318
  have htrace : WordTrace (prefixWord ++ tailWord_930318) baseStart_930318 baseEnd_930318 := by
    simpa [prefixWord, tailWord_930318, baseEnd_930318] using wordTrace_append hprefix tailTrace_930318
  have hstable : (prefixWord ++ tailWord_930318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930318).length < 2 ^ (prefixWord ++ tailWord_930318).sum := by decide
  have hdescent : baseEnd_930318 < baseStart_930318 := by decide
  rcases family_descends (prefixWord ++ tailWord_930318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930329 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_930329 : Nat := 118140960795 + 930329 * 2 ^ 59
def prefixEnd_930329 : Nat := 4983230072969 + 3 ^ 40 * 930329 * 2
def baseEnd_930329 : Nat := 318470629211197211472667

theorem tailTrace_930329 : CollatzResearch.WordTrace tailWord_930329 prefixEnd_930329 318470629211197211472667 := by
  unfold tailWord_930329
  simp only [CollatzResearch.WordTrace]
  refine ⟨33931886246584395388626041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22621257497722930259084027 33931886246584395388626041)
  ·
    refine ⟨25448914684938296541469531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33931886246584395388626041 25448914684938296541469531)
    ·
      refine ⟨38173372027407444812204297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25448914684938296541469531 38173372027407444812204297)
      ·
        refine ⟨28630029020555583609153223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38173372027407444812204297 28630029020555583609153223)
        ·
          refine ⟨42945043530833375413729835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28630029020555583609153223 42945043530833375413729835)
          ·
            refine ⟨64417565296250063120594753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42945043530833375413729835 64417565296250063120594753)
            ·
              refine ⟨48313173972187547340446065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64417565296250063120594753 48313173972187547340446065)
              ·
                refine ⟨36234880479140660505334549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48313173972187547340446065 36234880479140660505334549)
                ·
                  refine ⟨1698510022459718461187557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36234880479140660505334549 1698510022459718461187557)
                  ·
                    refine ⟨318470629211197211472667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698510022459718461187557 318470629211197211472667)
                    ·
                      rfl

theorem cell22_930329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_930329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930329 prefixEnd_930329 := by exact prefixLift 930329
  have htrace : WordTrace (prefixWord ++ tailWord_930329) baseStart_930329 baseEnd_930329 := by
    simpa [prefixWord, tailWord_930329, baseEnd_930329] using wordTrace_append hprefix tailTrace_930329
  have hstable : (prefixWord ++ tailWord_930329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930329).length < 2 ^ (prefixWord ++ tailWord_930329).sum := by decide
  have hdescent : baseEnd_930329 < baseStart_930329 := by decide
  rcases family_descends (prefixWord ++ tailWord_930329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930350 : List Nat := [4, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_930350 : Nat := 118140960795 + 930350 * 2 ^ 59
def prefixEnd_930350 : Nat := 4983230072969 + 3 ^ 40 * 930350 * 2
def baseEnd_930350 : Nat := 106159272646786718899201

theorem tailTrace_930350 : CollatzResearch.WordTrace tailWord_930350 prefixEnd_930350 106159272646786718899201 := by
  unfold tailWord_930350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241581522438539496892563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22621768119672210650093669 4241581522438539496892563)
  ·
    refine ⟨6362372283657809245338845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4241581522438539496892563 6362372283657809245338845)
    ·
      refine ⟨2385889606371678467002067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6362372283657809245338845 2385889606371678467002067)
      ·
        refine ⟨3578834409557517700503101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385889606371678467002067 3578834409557517700503101)
        ·
          refine ⟨1342062903584069137688663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3578834409557517700503101 1342062903584069137688663)
          ·
            refine ⟨2013094355376103706532995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342062903584069137688663 2013094355376103706532995)
            ·
              refine ⟨3019641533064155559799493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013094355376103706532995 3019641533064155559799493)
              ·
                refine ⟨566182787449529167462405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3019641533064155559799493 566182787449529167462405)
                ·
                  refine ⟨106159272646786718899201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566182787449529167462405 106159272646786718899201)
                  ·
                    rfl

theorem cell22_930350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_930350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930350 prefixEnd_930350 := by exact prefixLift 930350
  have htrace : WordTrace (prefixWord ++ tailWord_930350) baseStart_930350 baseEnd_930350 := by
    simpa [prefixWord, tailWord_930350, baseEnd_930350] using wordTrace_append hprefix tailTrace_930350
  have hstable : (prefixWord ++ tailWord_930350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930350).length < 2 ^ (prefixWord ++ tailWord_930350).sum := by decide
  have hdescent : baseEnd_930350 < baseStart_930350 := by decide
  rcases family_descends (prefixWord ++ tailWord_930350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930410 : List Nat := [3, 1, 3, 2, 1, 1, 1, 6, 1, 3]
def baseStart_930410 : Nat := 118140960795 + 930410 * 2 ^ 59
def prefixEnd_930410 : Nat := 4983230072969 + 3 ^ 40 * 930410 * 2
def baseEnd_930410 : Nat := 318498357166540000197419

theorem tailTrace_930410 : CollatzResearch.WordTrace tailWord_930410 prefixEnd_930410 318498357166540000197419 := by
  unfold tailWord_930410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8483710139822736555581171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22623227039527297481549789 8483710139822736555581171)
  ·
    refine ⟨12725565209734104833371757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8483710139822736555581171 12725565209734104833371757)
    ·
      refine ⟨4772086953650289312514409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12725565209734104833371757 4772086953650289312514409)
      ·
        refine ⟨3579065215237716984385807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4772086953650289312514409 3579065215237716984385807)
        ·
          refine ⟨5368597822856575476578711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3579065215237716984385807 5368597822856575476578711)
          ·
            refine ⟨8052896734284863214868067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5368597822856575476578711 8052896734284863214868067)
            ·
              refine ⟨12079345101427294822302101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8052896734284863214868067 12079345101427294822302101)
              ·
                refine ⟨566219301629404444795411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12079345101427294822302101 566219301629404444795411)
                ·
                  refine ⟨849328952444106667193117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566219301629404444795411 849328952444106667193117)
                  ·
                    refine ⟨318498357166540000197419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 849328952444106667193117 318498357166540000197419)
                    ·
                      rfl

theorem cell22_930410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_930410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930410 prefixEnd_930410 := by exact prefixLift 930410
  have htrace : WordTrace (prefixWord ++ tailWord_930410) baseStart_930410 baseEnd_930410 := by
    simpa [prefixWord, tailWord_930410, baseEnd_930410] using wordTrace_append hprefix tailTrace_930410
  have hstable : (prefixWord ++ tailWord_930410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930410).length < 2 ^ (prefixWord ++ tailWord_930410).sum := by decide
  have hdescent : baseEnd_930410 < baseStart_930410 := by decide
  rcases family_descends (prefixWord ++ tailWord_930410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930419 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 2, 8]
def baseStart_930419 : Nat := 118140960795 + 930419 * 2 ^ 59
def prefixEnd_930419 : Nat := 4983230072969 + 3 ^ 40 * 930419 * 2
def baseEnd_930419 : Nat := 318501438050466976722391

theorem tailTrace_930419 : CollatzResearch.WordTrace tailWord_930419 prefixEnd_930419 318501438050466976722391 := by
  unfold tailWord_930419
  simp only [CollatzResearch.WordTrace]
  refine ⟨33935168816258340759402311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22623445877505560506268207 33935168816258340759402311)
  ·
    refine ⟨50902753224387511139103467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33935168816258340759402311 50902753224387511139103467)
    ·
      refine ⟨76354129836581266708655201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50902753224387511139103467 76354129836581266708655201)
      ·
        refine ⟨57265597377435950031491401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76354129836581266708655201 57265597377435950031491401)
        ·
          refine ⟨42949198033076962523618551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57265597377435950031491401 42949198033076962523618551)
          ·
            refine ⟨64423797049615443785427827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42949198033076962523618551 64423797049615443785427827)
            ·
              refine ⟨96635695574423165678141741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64423797049615443785427827 96635695574423165678141741)
              ·
                refine ⟨36238385840408687129303153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96635695574423165678141741 36238385840408687129303153)
                ·
                  refine ⟨27178789380306515346977365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36238385840408687129303153 27178789380306515346977365)
                  ·
                    refine ⟨318501438050466976722391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27178789380306515346977365 318501438050466976722391)
                    ·
                      rfl

theorem cell22_930419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_930419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930419 prefixEnd_930419 := by exact prefixLift 930419
  have htrace : WordTrace (prefixWord ++ tailWord_930419) baseStart_930419 baseEnd_930419 := by
    simpa [prefixWord, tailWord_930419, baseEnd_930419] using wordTrace_append hprefix tailTrace_930419
  have hstable : (prefixWord ++ tailWord_930419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930419).length < 2 ^ (prefixWord ++ tailWord_930419).sum := by decide
  have hdescent : baseEnd_930419 < baseStart_930419 := by decide
  rcases family_descends (prefixWord ++ tailWord_930419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930474 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_930474 : Nat := 118140960795 + 930474 * 2 ^ 59
def prefixEnd_930474 : Nat := 4983230072969 + 3 ^ 40 * 930474 * 2
def baseEnd_930474 : Nat := 106173421891488388865741

theorem tailTrace_930474 : CollatzResearch.WordTrace tailWord_930474 prefixEnd_930474 106173421891488388865741 := by
  unfold tailWord_930474
  simp only [CollatzResearch.WordTrace]
  refine ⟨8484293707764771288163619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22624783220706056768436317 8484293707764771288163619)
  ·
    refine ⟨12726440561647156932245429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8484293707764771288163619 12726440561647156932245429)
    ·
      refine ⟨1193103802654420962398009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12726440561647156932245429 1193103802654420962398009)
      ·
        refine ⟨894827851990815721798507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1193103802654420962398009 894827851990815721798507)
        ·
          refine ⟨1342241777986223582697761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894827851990815721798507 1342241777986223582697761)
          ·
            refine ⟨1006681333489667687023321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1342241777986223582697761 1006681333489667687023321)
            ·
              refine ⟨755011000117250765267491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006681333489667687023321 755011000117250765267491)
              ·
                refine ⟨1132516500175876147901237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755011000117250765267491 1132516500175876147901237)
                ·
                  refine ⟨106173421891488388865741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1132516500175876147901237 106173421891488388865741)
                  ·
                    rfl

theorem cell22_930474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_930474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930474 prefixEnd_930474 := by exact prefixLift 930474
  have htrace : WordTrace (prefixWord ++ tailWord_930474) baseStart_930474 baseEnd_930474 := by
    simpa [prefixWord, tailWord_930474, baseEnd_930474] using wordTrace_append hprefix tailTrace_930474
  have hstable : (prefixWord ++ tailWord_930474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930474).length < 2 ^ (prefixWord ++ tailWord_930474).sum := by decide
  have hdescent : baseEnd_930474 < baseStart_930474 := by decide
  rcases family_descends (prefixWord ++ tailWord_930474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930487 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 1, 4]
def baseStart_930487 : Nat := 118140960795 + 930487 * 2 ^ 59
def prefixEnd_930487 : Nat := 4983230072969 + 3 ^ 40 * 930487 * 2
def baseEnd_930487 : Nat := 318524715840137466022183

theorem tailTrace_930487 : CollatzResearch.WordTrace tailWord_930487 prefixEnd_930487 318524715840137466022183 := by
  unfold tailWord_930487
  simp only [CollatzResearch.WordTrace]
  refine ⟨33937648980011988372877715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22625099320007992248585143 33937648980011988372877715)
  ·
    refine ⟨50906473470017982559316573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33937648980011988372877715 50906473470017982559316573)
    ·
      refine ⟨19089927551256743459743715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50906473470017982559316573 19089927551256743459743715)
      ·
        refine ⟨28634891326885115189615573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19089927551256743459743715 28634891326885115189615573)
        ·
          refine ⟨671130265473869887256615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28634891326885115189615573 671130265473869887256615)
          ·
            refine ⟨1006695398210804830884923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671130265473869887256615 1006695398210804830884923)
            ·
              refine ⟨1510043097316207246327385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006695398210804830884923 1510043097316207246327385)
              ·
                refine ⟨1132532322987155434745539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510043097316207246327385 1132532322987155434745539)
                ·
                  refine ⟨1698798484480733152118309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132532322987155434745539 1698798484480733152118309)
                  ·
                    refine ⟨318524715840137466022183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698798484480733152118309 318524715840137466022183)
                    ·
                      rfl

theorem cell22_930487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_930487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930487 prefixEnd_930487 := by exact prefixLift 930487
  have htrace : WordTrace (prefixWord ++ tailWord_930487) baseStart_930487 baseEnd_930487 := by
    simpa [prefixWord, tailWord_930487, baseEnd_930487] using wordTrace_append hprefix tailTrace_930487
  have hstable : (prefixWord ++ tailWord_930487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930487).length < 2 ^ (prefixWord ++ tailWord_930487).sum := by decide
  have hdescent : baseEnd_930487 < baseStart_930487 := by decide
  rcases family_descends (prefixWord ++ tailWord_930487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930496 : List Nat := [2, 1, 1, 2, 4, 2, 2, 8]
def baseStart_930496 : Nat := 118140960795 + 930496 * 2 ^ 59
def prefixEnd_930496 : Nat := 4983230072969 + 3 ^ 40 * 930496 * 2
def baseEnd_930496 : Nat := 35391977413784938060795

theorem tailTrace_930496 : CollatzResearch.WordTrace tailWord_930496 prefixEnd_930496 35391977413784938060795 := by
  unfold tailWord_930496
  simp only [CollatzResearch.WordTrace]
  refine ⟨16968988618489691454977671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22625318157986255273303561 16968988618489691454977671)
  ·
    refine ⟨25453482927734537182466507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16968988618489691454977671 25453482927734537182466507)
    ·
      refine ⟨38180224391601805773699761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25453482927734537182466507 38180224391601805773699761)
      ·
        refine ⟨28635168293701354330274821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38180224391601805773699761 28635168293701354330274821)
        ·
          refine ⟨5369094055069003936926529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28635168293701354330274821 5369094055069003936926529)
          ·
            refine ⟨4026820541301752952694897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5369094055069003936926529 4026820541301752952694897)
            ·
              refine ⟨3020115405976314714521173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4026820541301752952694897 3020115405976314714521173)
              ·
                refine ⟨35391977413784938060795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3020115405976314714521173 35391977413784938060795)
                ·
                  rfl

theorem cell22_930496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 8].length) (baseStart_930496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930496 prefixEnd_930496 := by exact prefixLift 930496
  have htrace : WordTrace (prefixWord ++ tailWord_930496) baseStart_930496 baseEnd_930496 := by
    simpa [prefixWord, tailWord_930496, baseEnd_930496] using wordTrace_append hprefix tailTrace_930496
  have hstable : (prefixWord ++ tailWord_930496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930496).length < 2 ^ (prefixWord ++ tailWord_930496).sum := by decide
  have hdescent : baseEnd_930496 < baseStart_930496 := by decide
  rcases family_descends (prefixWord ++ tailWord_930496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930528 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 3, 3]
def baseStart_930528 : Nat := 118140960795 + 930528 * 2 ^ 59
def prefixEnd_930528 : Nat := 4983230072969 + 3 ^ 40 * 930528 * 2
def baseEnd_930528 : Nat := 318538750978027025747057

theorem tailTrace_930528 : CollatzResearch.WordTrace tailWord_930528 prefixEnd_930528 318538750978027025747057 := by
  unfold tailWord_930528
  simp only [CollatzResearch.WordTrace]
  refine ⟨16969572186431726187560119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22626096248575634916746825 16969572186431726187560119)
  ·
    refine ⟨25454358279647589281340179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16969572186431726187560119 25454358279647589281340179)
    ·
      refine ⟨38181537419471383922010269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25454358279647589281340179 38181537419471383922010269)
      ·
        refine ⟨14318076532301768970753851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38181537419471383922010269 14318076532301768970753851)
        ·
          refine ⟨21477114798452653456130777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14318076532301768970753851 21477114798452653456130777)
          ·
            refine ⟨16107836098839490092098083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21477114798452653456130777 16107836098839490092098083)
            ·
              refine ⟨24161754148259235138147125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16107836098839490092098083 24161754148259235138147125)
              ·
                refine ⟨2265164451399303294201293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24161754148259235138147125 2265164451399303294201293)
                ·
                  refine ⟨849436669274738735325485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2265164451399303294201293 849436669274738735325485)
                  ·
                    refine ⟨318538750978027025747057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 849436669274738735325485 318538750978027025747057)
                    ·
                      rfl

theorem cell22_930528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_930528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930528 prefixEnd_930528 := by exact prefixLift 930528
  have htrace : WordTrace (prefixWord ++ tailWord_930528) baseStart_930528 baseEnd_930528 := by
    simpa [prefixWord, tailWord_930528, baseEnd_930528] using wordTrace_append hprefix tailTrace_930528
  have hstable : (prefixWord ++ tailWord_930528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930528).length < 2 ^ (prefixWord ++ tailWord_930528).sum := by decide
  have hdescent : baseEnd_930528 < baseStart_930528 := by decide
  rcases family_descends (prefixWord ++ tailWord_930528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930633 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_930633 : Nat := 118140960795 + 930633 * 2 ^ 59
def prefixEnd_930633 : Nat := 4983230072969 + 3 ^ 40 * 930633 * 2
def baseEnd_930633 : Nat := 318574694623841751871735

theorem tailTrace_930633 : CollatzResearch.WordTrace tailWord_930633 prefixEnd_930633 318574694623841751871735 := by
  unfold tailWord_930633
  simp only [CollatzResearch.WordTrace]
  refine ⟨33942974037483055307692553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22628649358322036871795035 33942974037483055307692553)
  ·
    refine ⟨25457230528112291480769415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33942974037483055307692553 25457230528112291480769415)
    ·
      refine ⟨38185845792168437221154123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25457230528112291480769415 38185845792168437221154123)
      ·
        refine ⟨57278768688252655831731185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38185845792168437221154123 57278768688252655831731185)
        ·
          refine ⟨42959076516189491873798389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57278768688252655831731185 42959076516189491873798389)
          ·
            refine ⟨4027413423392764863168599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42959076516189491873798389 4027413423392764863168599)
            ·
              refine ⟨6041120135089147294752899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027413423392764863168599 6041120135089147294752899)
              ·
                refine ⟨9061680202633720942129349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041120135089147294752899 9061680202633720942129349)
                ·
                  refine ⟨1699065037993822676649253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9061680202633720942129349 1699065037993822676649253)
                  ·
                    refine ⟨318574694623841751871735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1699065037993822676649253 318574694623841751871735)
                    ·
                      rfl

theorem cell22_930633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_930633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930633 prefixEnd_930633 := by exact prefixLift 930633
  have htrace : WordTrace (prefixWord ++ tailWord_930633) baseStart_930633 baseEnd_930633 := by
    simpa [prefixWord, tailWord_930633, baseEnd_930633] using wordTrace_append hprefix tailTrace_930633
  have hstable : (prefixWord ++ tailWord_930633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930633).length < 2 ^ (prefixWord ++ tailWord_930633).sum := by decide
  have hdescent : baseEnd_930633 < baseStart_930633 := by decide
  rcases family_descends (prefixWord ++ tailWord_930633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930686 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_930686 : Nat := 118140960795 + 930686 * 2 ^ 59
def prefixEnd_930686 : Nat := 4983230072969 + 3 ^ 40 * 930686 * 2
def baseEnd_930686 : Nat := 318592837606967280296573

theorem tailTrace_930686 : CollatzResearch.WordTrace tailWord_930686 prefixEnd_930686 318592837606967280296573 := by
  unfold tailWord_930686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243113388286380669921489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22629938070860696906247941 4243113388286380669921489)
  ·
    refine ⟨3182335041214785502441117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4243113388286380669921489 3182335041214785502441117)
    ·
      refine ⟨1193375640455544563415419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3182335041214785502441117 1193375640455544563415419)
      ·
        refine ⟨1790063460683316845123129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193375640455544563415419 1790063460683316845123129)
        ·
          refine ⟨1342547595512487633842347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1790063460683316845123129 1342547595512487633842347)
          ·
            refine ⟨2013821393268731450763521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342547595512487633842347 2013821393268731450763521)
            ·
              refine ⟨1510366044951548588072641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2013821393268731450763521 1510366044951548588072641)
              ·
                refine ⟨1132774533713661441054481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510366044951548588072641 1132774533713661441054481)
                ·
                  refine ⟨849580900285246080790861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1132774533713661441054481 849580900285246080790861)
                  ·
                    refine ⟨318592837606967280296573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 849580900285246080790861 318592837606967280296573)
                    ·
                      rfl

theorem cell22_930686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_930686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930686 prefixEnd_930686 := by exact prefixLift 930686
  have htrace : WordTrace (prefixWord ++ tailWord_930686) baseStart_930686 baseEnd_930686 := by
    simpa [prefixWord, tailWord_930686, baseEnd_930686] using wordTrace_append hprefix tailTrace_930686
  have hstable : (prefixWord ++ tailWord_930686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930686).length < 2 ^ (prefixWord ++ tailWord_930686).sum := by decide
  have hdescent : baseEnd_930686 < baseStart_930686 := by decide
  rcases family_descends (prefixWord ++ tailWord_930686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930774 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_930774 : Nat := 118140960795 + 930774 * 2 ^ 59
def prefixEnd_930774 : Nat := 4983230072969 + 3 ^ 40 * 930774 * 2
def baseEnd_930774 : Nat := 318622961805364384096303

theorem tailTrace_930774 : CollatzResearch.WordTrace tailWord_930774 prefixEnd_930774 318622961805364384096303 := by
  unfold tailWord_930774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121757295623264774285961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22632077819981490925716917 2121757295623264774285961)
  ·
    refine ⟨1591317971717448580714471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2121757295623264774285961 1591317971717448580714471)
    ·
      refine ⟨2386976957576172871071707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591317971717448580714471 2386976957576172871071707)
      ·
        refine ⟨3580465436364259306607561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386976957576172871071707 3580465436364259306607561)
        ·
          refine ⟨2685349077273194479955671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3580465436364259306607561 2685349077273194479955671)
          ·
            refine ⟨4028023615909791719933507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685349077273194479955671 4028023615909791719933507)
            ·
              refine ⟨6042035423864687579900261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028023615909791719933507 6042035423864687579900261)
              ·
                refine ⟨1132881641974628921231299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6042035423864687579900261 1132881641974628921231299)
                ·
                  refine ⟨1699322462961943381846949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132881641974628921231299 1699322462961943381846949)
                  ·
                    refine ⟨318622961805364384096303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1699322462961943381846949 318622961805364384096303)
                    ·
                      rfl

theorem cell22_930774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_930774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930774 prefixEnd_930774 := by exact prefixLift 930774
  have htrace : WordTrace (prefixWord ++ tailWord_930774) baseStart_930774 baseEnd_930774 := by
    simpa [prefixWord, tailWord_930774, baseEnd_930774] using wordTrace_append hprefix tailTrace_930774
  have hstable : (prefixWord ++ tailWord_930774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930774).length < 2 ^ (prefixWord ++ tailWord_930774).sum := by decide
  have hdescent : baseEnd_930774 < baseStart_930774 := by decide
  rcases family_descends (prefixWord ++ tailWord_930774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930785 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_930785 : Nat := 118140960795 + 930785 * 2 ^ 59
def prefixEnd_930785 : Nat := 4983230072969 + 3 ^ 40 * 930785 * 2
def baseEnd_930785 : Nat := 318626727330164022071269

theorem tailTrace_930785 : CollatzResearch.WordTrace tailWord_930785 prefixEnd_930785 318626727330164022071269 := by
  unfold tailWord_930785
  simp only [CollatzResearch.WordTrace]
  refine ⟨33948517932932385267225809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22632345288621590178150539 33948517932932385267225809)
  ·
    refine ⟨25461388449699288950419357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33948517932932385267225809 25461388449699288950419357)
    ·
      refine ⟨9548020668637233356407259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25461388449699288950419357 9548020668637233356407259)
      ·
        refine ⟨14322031002955850034610889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9548020668637233356407259 14322031002955850034610889)
        ·
          refine ⟨10741523252216887525958167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14322031002955850034610889 10741523252216887525958167)
          ·
            refine ⟨16112284878325331288937251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10741523252216887525958167 16112284878325331288937251)
            ·
              refine ⟨24168427317487996933405877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16112284878325331288937251 24168427317487996933405877)
              ·
                refine ⟨2265790061014499712506801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24168427317487996933405877 2265790061014499712506801)
                ·
                  refine ⟨1699342545760874784380101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2265790061014499712506801 1699342545760874784380101)
                  ·
                    refine ⟨318626727330164022071269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1699342545760874784380101 318626727330164022071269)
                    ·
                      rfl

theorem cell22_930785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_930785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930785 prefixEnd_930785 := by exact prefixLift 930785
  have htrace : WordTrace (prefixWord ++ tailWord_930785) baseStart_930785 baseEnd_930785 := by
    simpa [prefixWord, tailWord_930785, baseEnd_930785] using wordTrace_append hprefix tailTrace_930785
  have hstable : (prefixWord ++ tailWord_930785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930785).length < 2 ^ (prefixWord ++ tailWord_930785).sum := by decide
  have hdescent : baseEnd_930785 < baseStart_930785 := by decide
  rcases family_descends (prefixWord ++ tailWord_930785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930806 : List Nat := [5, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_930806 : Nat := 118140960795 + 930806 * 2 ^ 59
def prefixEnd_930806 : Nat := 4983230072969 + 3 ^ 40 * 930806 * 2
def baseEnd_930806 : Nat := 106211305353108989098735

theorem tailTrace_930806 : CollatzResearch.WordTrace tailWord_930806 prefixEnd_930806 106211305353108989098735 := by
  unfold tailWord_930806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121830241616019115858767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22632855910570870569160181 2121830241616019115858767)
  ·
    refine ⟨3182745362424028673788151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2121830241616019115858767 3182745362424028673788151)
    ·
      refine ⟨4774118043636043010682227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3182745362424028673788151 4774118043636043010682227)
      ·
        refine ⟨7161177065454064516023341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774118043636043010682227 7161177065454064516023341)
        ·
          refine ⟨2685441399545274193508753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7161177065454064516023341 2685441399545274193508753)
          ·
            refine ⟨2014081049658955645131565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2685441399545274193508753 2014081049658955645131565)
            ·
              refine ⟨755280393622108366924337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2014081049658955645131565 755280393622108366924337)
              ·
                refine ⟨566460295216581275193253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755280393622108366924337 566460295216581275193253)
                ·
                  refine ⟨106211305353108989098735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566460295216581275193253 106211305353108989098735)
                  ·
                    rfl

theorem cell22_930806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_930806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930806 prefixEnd_930806 := by exact prefixLift 930806
  have htrace : WordTrace (prefixWord ++ tailWord_930806) baseStart_930806 baseEnd_930806 := by
    simpa [prefixWord, tailWord_930806, baseEnd_930806] using wordTrace_append hprefix tailTrace_930806
  have hstable : (prefixWord ++ tailWord_930806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930806).length < 2 ^ (prefixWord ++ tailWord_930806).sum := by decide
  have hdescent : baseEnd_930806 < baseStart_930806 := by decide
  rcases family_descends (prefixWord ++ tailWord_930806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930860 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_930860 : Nat := 118140960795 + 930860 * 2 ^ 59
def prefixEnd_930860 : Nat := 4983230072969 + 3 ^ 40 * 930860 * 2
def baseEnd_930860 : Nat := 318652401362888826446039

theorem tailTrace_930860 : CollatzResearch.WordTrace tailWord_930860 prefixEnd_930860 318652401362888826446039 := by
  unfold tailWord_930860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16975626703830336538103017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22634168938440448717470689 16975626703830336538103017)
  ·
    refine ⟨12731720027872752403577263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16975626703830336538103017 12731720027872752403577263)
    ·
      refine ⟨19097580041809128605365895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12731720027872752403577263 19097580041809128605365895)
      ·
        refine ⟨28646370062713692908048843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097580041809128605365895 28646370062713692908048843)
        ·
          refine ⟨42969555094070539362073265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28646370062713692908048843 42969555094070539362073265)
          ·
            refine ⟨32227166320552904521554949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42969555094070539362073265 32227166320552904521554949)
            ·
              refine ⟨6042593685103669597791553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32227166320552904521554949 6042593685103669597791553)
              ·
                refine ⟨4531945263827752198343665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6042593685103669597791553 4531945263827752198343665)
                ·
                  refine ⟨3398958947870814148757749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4531945263827752198343665 3398958947870814148757749)
                  ·
                    refine ⟨318652401362888826446039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3398958947870814148757749 318652401362888826446039)
                    ·
                      rfl

theorem cell22_930860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_930860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930860 prefixEnd_930860 := by exact prefixLift 930860
  have htrace : WordTrace (prefixWord ++ tailWord_930860) baseStart_930860 baseEnd_930860 := by
    simpa [prefixWord, tailWord_930860, baseEnd_930860] using wordTrace_append hprefix tailTrace_930860
  have hstable : (prefixWord ++ tailWord_930860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930860).length < 2 ^ (prefixWord ++ tailWord_930860).sum := by decide
  have hdescent : baseEnd_930860 < baseStart_930860 := by decide
  rcases family_descends (prefixWord ++ tailWord_930860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930877 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_930877 : Nat := 118140960795 + 930877 * 2 ^ 59
def prefixEnd_930877 : Nat := 4983230072969 + 3 ^ 40 * 930877 * 2
def baseEnd_930877 : Nat := 318658220810306448770987

theorem tailTrace_930877 : CollatzResearch.WordTrace tailWord_930877 prefixEnd_930877 318658220810306448770987 := by
  unfold tailWord_930877
  simp only [CollatzResearch.WordTrace]
  refine ⟨33951873448599084979574885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22634582299066056653049923 33951873448599084979574885)
  ·
    refine ⟨6365976271612328433670291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33951873448599084979574885 6365976271612328433670291)
    ·
      refine ⟨9548964407418492650505437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6365976271612328433670291 9548964407418492650505437)
      ·
        refine ⟨3580861652781934743939539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9548964407418492650505437 3580861652781934743939539)
        ·
          refine ⟨5371292479172902115909309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580861652781934743939539 5371292479172902115909309)
          ·
            refine ⟨2014234679689838293465991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5371292479172902115909309 2014234679689838293465991)
            ·
              refine ⟨3021352019534757440198987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014234679689838293465991 3021352019534757440198987)
              ·
                refine ⟨4532028029302136160298481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021352019534757440198987 4532028029302136160298481)
                ·
                  refine ⟨3399021021976602120223861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4532028029302136160298481 3399021021976602120223861)
                  ·
                    refine ⟨318658220810306448770987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3399021021976602120223861 318658220810306448770987)
                    ·
                      rfl

theorem cell22_930877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_930877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930877 prefixEnd_930877 := by exact prefixLift 930877
  have htrace : WordTrace (prefixWord ++ tailWord_930877) baseStart_930877 baseEnd_930877 := by
    simpa [prefixWord, tailWord_930877, baseEnd_930877] using wordTrace_append hprefix tailTrace_930877
  have hstable : (prefixWord ++ tailWord_930877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930877).length < 2 ^ (prefixWord ++ tailWord_930877).sum := by decide
  have hdescent : baseEnd_930877 < baseStart_930877 := by decide
  rcases family_descends (prefixWord ++ tailWord_930877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930890 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_930890 : Nat := 118140960795 + 930890 * 2 ^ 59
def prefixEnd_930890 : Nat := 4983230072969 + 3 ^ 40 * 930890 * 2
def baseEnd_930890 : Nat := 106220890325326249398649

theorem tailTrace_930890 : CollatzResearch.WordTrace tailWord_930890 prefixEnd_930890 106220890325326249398649 := by
  unfold tailWord_930890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8488086899387997049949531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22634898398367992133198749 8488086899387997049949531)
  ·
    refine ⟨12732130349081995574924297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8488086899387997049949531 12732130349081995574924297)
    ·
      refine ⟨9549097761811496681193223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12732130349081995574924297 9549097761811496681193223)
      ·
        refine ⟨14323646642717245021789835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9549097761811496681193223 14323646642717245021789835)
        ·
          refine ⟨21485469964075867532684753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14323646642717245021789835 21485469964075867532684753)
          ·
            refine ⟨16114102473056900649513565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21485469964075867532684753 16114102473056900649513565)
            ·
              refine ⟨6042788427396337743567587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16114102473056900649513565 6042788427396337743567587)
              ·
                refine ⟨9064182641094506615351381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6042788427396337743567587 9064182641094506615351381)
                ·
                  refine ⟨106220890325326249398649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9064182641094506615351381 106220890325326249398649)
                  ·
                    rfl

theorem cell22_930890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_930890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930890 prefixEnd_930890 := by exact prefixLift 930890
  have htrace : WordTrace (prefixWord ++ tailWord_930890) baseStart_930890 baseEnd_930890 := by
    simpa [prefixWord, tailWord_930890, baseEnd_930890] using wordTrace_append hprefix tailTrace_930890
  have hstable : (prefixWord ++ tailWord_930890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930890).length < 2 ^ (prefixWord ++ tailWord_930890).sum := by decide
  have hdescent : baseEnd_930890 < baseStart_930890 := by decide
  rcases family_descends (prefixWord ++ tailWord_930890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930892 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_930892 : Nat := 118140960795 + 930892 * 2 ^ 59
def prefixEnd_930892 : Nat := 4983230072969 + 3 ^ 40 * 930892 * 2
def baseEnd_930892 : Nat := 318663355616851409645941

theorem tailTrace_930892 : CollatzResearch.WordTrace tailWord_930892 prefixEnd_930892 318663355616851409645941 := by
  unfold tailWord_930892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16976210271772371270685465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22634947029029828360913953 16976210271772371270685465)
  ·
    refine ⟨12732157703829278453014099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16976210271772371270685465 12732157703829278453014099)
    ·
      refine ⟨19098236555743917679521149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12732157703829278453014099 19098236555743917679521149)
      ·
        refine ⟨7161838708403969129820431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19098236555743917679521149 7161838708403969129820431)
        ·
          refine ⟨10742758062605953694730647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161838708403969129820431 10742758062605953694730647)
          ·
            refine ⟨16114137093908930542095971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742758062605953694730647 16114137093908930542095971)
            ·
              refine ⟨24171205640863395813143957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16114137093908930542095971 24171205640863395813143957)
              ·
                refine ⟨1133025264415471678741123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24171205640863395813143957 1133025264415471678741123)
                ·
                  refine ⟨1699537896623207518111685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133025264415471678741123 1699537896623207518111685)
                  ·
                    refine ⟨318663355616851409645941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1699537896623207518111685 318663355616851409645941)
                    ·
                      rfl

theorem cell22_930892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_930892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930892 prefixEnd_930892 := by exact prefixLift 930892
  have htrace : WordTrace (prefixWord ++ tailWord_930892) baseStart_930892 baseEnd_930892 := by
    simpa [prefixWord, tailWord_930892, baseEnd_930892] using wordTrace_append hprefix tailTrace_930892
  have hstable : (prefixWord ++ tailWord_930892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930892).length < 2 ^ (prefixWord ++ tailWord_930892).sum := by decide
  have hdescent : baseEnd_930892 < baseStart_930892 := by decide
  rcases family_descends (prefixWord ++ tailWord_930892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930905 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_930905 : Nat := 118140960795 + 930905 * 2 ^ 59
def prefixEnd_930905 : Nat := 4983230072969 + 3 ^ 40 * 930905 * 2
def baseEnd_930905 : Nat := 318667805782523709070901

theorem tailTrace_930905 : CollatzResearch.WordTrace tailWord_930905 prefixEnd_930905 318667805782523709070901 := by
  unfold tailWord_930905
  simp only [CollatzResearch.WordTrace]
  refine ⟨33952894692497645761594169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22635263128331763841062779 33952894692497645761594169)
  ·
    refine ⟨25464671019373234321195627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33952894692497645761594169 25464671019373234321195627)
    ·
      refine ⟨38197006529059851481793441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25464671019373234321195627 38197006529059851481793441)
      ·
        refine ⟨28647754896794888611345081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38197006529059851481793441 28647754896794888611345081)
        ·
          refine ⟨21485816172596166458508811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28647754896794888611345081 21485816172596166458508811)
          ·
            refine ⟨32228724258894249687763217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21485816172596166458508811 32228724258894249687763217)
            ·
              refine ⟨24171543194170687265822413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32228724258894249687763217 24171543194170687265822413)
              ·
                refine ⟨9064328697814007724683405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24171543194170687265822413 9064328697814007724683405)
                ·
                  refine ⟨3399123261680252896756277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9064328697814007724683405 3399123261680252896756277)
                  ·
                    refine ⟨318667805782523709070901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3399123261680252896756277 318667805782523709070901)
                    ·
                      rfl

theorem cell22_930905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_930905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930905 prefixEnd_930905 := by exact prefixLift 930905
  have htrace : WordTrace (prefixWord ++ tailWord_930905) baseStart_930905 baseEnd_930905 := by
    simpa [prefixWord, tailWord_930905, baseEnd_930905] using wordTrace_append hprefix tailTrace_930905
  have hstable : (prefixWord ++ tailWord_930905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930905).length < 2 ^ (prefixWord ++ tailWord_930905).sum := by decide
  have hdescent : baseEnd_930905 < baseStart_930905 := by decide
  rcases family_descends (prefixWord ++ tailWord_930905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930935 : List Nat := [1, 1, 3, 1, 1, 4, 2, 9]
def baseStart_930935 : Nat := 118140960795 + 930935 * 2 ^ 59
def prefixEnd_930935 : Nat := 4983230072969 + 3 ^ 40 * 930935 * 2
def baseEnd_930935 : Nat := 35408675043957070091201

theorem tailTrace_930935 : CollatzResearch.WordTrace tailWord_930935 prefixEnd_930935 35408675043957070091201 := by
  unfold tailWord_930935
  simp only [CollatzResearch.WordTrace]
  refine ⟨33953988882388960885186259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22635992588259307256790839 33953988882388960885186259)
  ·
    refine ⟨50930983323583441327779389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33953988882388960885186259 50930983323583441327779389)
    ·
      refine ⟨19099118746343790497917271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50930983323583441327779389 19099118746343790497917271)
      ·
        refine ⟨28648678119515685746875907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19099118746343790497917271 28648678119515685746875907)
        ·
          refine ⟨42973017179273528620313861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28648678119515685746875907 42973017179273528620313861)
          ·
            refine ⟨8057440721113786616308849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42973017179273528620313861 8057440721113786616308849)
            ·
              refine ⟨6043080540835339962231637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8057440721113786616308849 6043080540835339962231637)
              ·
                refine ⟨35408675043957070091201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6043080540835339962231637 35408675043957070091201)
                ·
                  rfl

theorem cell22_930935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 9].length) (baseStart_930935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_930935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_930935 prefixEnd_930935 := by exact prefixLift 930935
  have htrace : WordTrace (prefixWord ++ tailWord_930935) baseStart_930935 baseEnd_930935 := by
    simpa [prefixWord, tailWord_930935, baseEnd_930935] using wordTrace_append hprefix tailTrace_930935
  have hstable : (prefixWord ++ tailWord_930935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930935).length < 2 ^ (prefixWord ++ tailWord_930935).sum := by decide
  have hdescent : baseEnd_930935 < baseStart_930935 := by decide
  rcases family_descends (prefixWord ++ tailWord_930935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931076 : List Nat := [2, 3, 2, 2, 2, 1, 1, 5, 4]
def baseStart_931076 : Nat := 118140960795 + 931076 * 2 ^ 59
def prefixEnd_931076 : Nat := 4983230072969 + 3 ^ 40 * 931076 * 2
def baseEnd_931076 : Nat := 106242114192378754348459

theorem tailTrace_931076 : CollatzResearch.WordTrace tailWord_931076 prefixEnd_931076 106242114192378754348459 := by
  unfold tailWord_931076
  simp only [CollatzResearch.WordTrace]
  refine ⟨16979565787439070983034541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22639421049918761310712721 16979565787439070983034541)
  ·
    refine ⟨6367337170289651618637953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16979565787439070983034541 6367337170289651618637953)
    ·
      refine ⟨4775502877717238713978465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6367337170289651618637953 4775502877717238713978465)
      ·
        refine ⟨3581627158287929035483849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4775502877717238713978465 3581627158287929035483849)
        ·
          refine ⟨2686220368715946776612887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3581627158287929035483849 2686220368715946776612887)
          ·
            refine ⟨4029330553073920164919331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686220368715946776612887 4029330553073920164919331)
            ·
              refine ⟨6043995829610880247378997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4029330553073920164919331 6043995829610880247378997)
              ·
                refine ⟨566624609026020023191781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6043995829610880247378997 566624609026020023191781)
                ·
                  refine ⟨106242114192378754348459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566624609026020023191781 106242114192378754348459)
                  ·
                    rfl

theorem cell22_931076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_931076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931076 prefixEnd_931076 := by exact prefixLift 931076
  have htrace : WordTrace (prefixWord ++ tailWord_931076) baseStart_931076 baseEnd_931076 := by
    simpa [prefixWord, tailWord_931076, baseEnd_931076] using wordTrace_append hprefix tailTrace_931076
  have hstable : (prefixWord ++ tailWord_931076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931076).length < 2 ^ (prefixWord ++ tailWord_931076).sum := by decide
  have hdescent : baseEnd_931076 < baseStart_931076 := by decide
  rcases family_descends (prefixWord ++ tailWord_931076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931108 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_931108 : Nat := 118140960795 + 931108 * 2 ^ 59
def prefixEnd_931108 : Nat := 4983230072969 + 3 ^ 40 * 931108 * 2
def baseEnd_931108 : Nat := 318737296831098846245279

theorem tailTrace_931108 : CollatzResearch.WordTrace tailWord_931108 prefixEnd_931108 318737296831098846245279 := by
  unfold tailWord_931108
  simp only [CollatzResearch.WordTrace]
  refine ⟨16980149355381105715616989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22640199140508140954155985 16980149355381105715616989)
  ·
    refine ⟨6367556008267914643356371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16980149355381105715616989 6367556008267914643356371)
    ·
      refine ⟨9551334012401871965034557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6367556008267914643356371 9551334012401871965034557)
      ·
        refine ⟨3581750254650701986887959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9551334012401871965034557 3581750254650701986887959)
        ·
          refine ⟨5372625381976052980331939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581750254650701986887959 5372625381976052980331939)
          ·
            refine ⟨8058938072964079470497909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5372625381976052980331939 8058938072964079470497909)
            ·
              refine ⟨755525444340382450359179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8058938072964079470497909 755525444340382450359179)
              ·
                refine ⟨1133288166510573675538769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755525444340382450359179 1133288166510573675538769)
                ·
                  refine ⟨849966124882930256654077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1133288166510573675538769 849966124882930256654077)
                  ·
                    refine ⟨318737296831098846245279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 849966124882930256654077 318737296831098846245279)
                    ·
                      rfl

theorem cell22_931108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_931108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931108 prefixEnd_931108 := by exact prefixLift 931108
  have htrace : WordTrace (prefixWord ++ tailWord_931108) baseStart_931108 baseEnd_931108 := by
    simpa [prefixWord, tailWord_931108, baseEnd_931108] using wordTrace_append hprefix tailTrace_931108
  have hstable : (prefixWord ++ tailWord_931108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931108).length < 2 ^ (prefixWord ++ tailWord_931108).sum := by decide
  have hdescent : baseEnd_931108 < baseStart_931108 := by decide
  rcases family_descends (prefixWord ++ tailWord_931108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931121 : List Nat := [1, 2, 2, 3, 3, 3, 2, 6]
def baseStart_931121 : Nat := 118140960795 + 931121 * 2 ^ 59
def prefixEnd_931121 : Nat := 4983230072969 + 3 ^ 40 * 931121 * 2
def baseEnd_931121 : Nat := 35415749666307905074471

theorem tailTrace_931121 : CollatzResearch.WordTrace tailWord_931121 prefixEnd_931121 35415749666307905074471 := by
  unfold tailWord_931121
  simp only [CollatzResearch.WordTrace]
  refine ⟨33960772859715114651457217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22640515239810076434304811 33960772859715114651457217)
  ·
    refine ⟨25470579644786335988592913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33960772859715114651457217 25470579644786335988592913)
    ·
      refine ⟨19102934733589751991444685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25470579644786335988592913 19102934733589751991444685)
      ·
        refine ⟨7163600525096156996791757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19102934733589751991444685 7163600525096156996791757)
        ·
          refine ⟨2686350196911058873796909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7163600525096156996791757 2686350196911058873796909)
          ·
            refine ⟨1007381323841647077673841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2686350196911058873796909 1007381323841647077673841)
            ·
              refine ⟨755535992881235308255381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007381323841647077673841 755535992881235308255381)
              ·
                refine ⟨35415749666307905074471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 755535992881235308255381 35415749666307905074471)
                ·
                  rfl

theorem cell22_931121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 6].length) (baseStart_931121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931121 prefixEnd_931121 := by exact prefixLift 931121
  have htrace : WordTrace (prefixWord ++ tailWord_931121) baseStart_931121 baseEnd_931121 := by
    simpa [prefixWord, tailWord_931121, baseEnd_931121] using wordTrace_append hprefix tailTrace_931121
  have hstable : (prefixWord ++ tailWord_931121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931121).length < 2 ^ (prefixWord ++ tailWord_931121).sum := by decide
  have hdescent : baseEnd_931121 < baseStart_931121 := by decide
  rcases family_descends (prefixWord ++ tailWord_931121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931211 : List Nat := [1, 1, 1, 1, 4, 3, 3, 4, 4]
def baseStart_931211 : Nat := 118140960795 + 931211 * 2 ^ 59
def prefixEnd_931211 : Nat := 4983230072969 + 3 ^ 40 * 931211 * 2
def baseEnd_931211 : Nat := 106257518612013636973321

theorem tailTrace_931211 : CollatzResearch.WordTrace tailWord_931211 prefixEnd_931211 106257518612013636973321 := by
  unfold tailWord_931211
  simp only [CollatzResearch.WordTrace]
  refine ⟨33964055429389060022233487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22642703619592706681488991 33964055429389060022233487)
  ·
    refine ⟨50946083144083590033350231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33964055429389060022233487 50946083144083590033350231)
    ·
      refine ⟨76419124716125385050025347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50946083144083590033350231 76419124716125385050025347)
      ·
        refine ⟨114628687074188077575038021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76419124716125385050025347 114628687074188077575038021)
        ·
          refine ⟨21492878826410264545319629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114628687074188077575038021 21492878826410264545319629)
          ·
            refine ⟨8059829559903849204494861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21492878826410264545319629 8059829559903849204494861)
            ·
              refine ⟨3022436084963943451685573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8059829559903849204494861 3022436084963943451685573)
              ·
                refine ⟨566706765930739397191045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3022436084963943451685573 566706765930739397191045)
                ·
                  refine ⟨106257518612013636973321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566706765930739397191045 106257518612013636973321)
                  ·
                    rfl

theorem cell22_931211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 4].length) (baseStart_931211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931211 prefixEnd_931211 := by exact prefixLift 931211
  have htrace : WordTrace (prefixWord ++ tailWord_931211) baseStart_931211 baseEnd_931211 := by
    simpa [prefixWord, tailWord_931211, baseEnd_931211] using wordTrace_append hprefix tailTrace_931211
  have hstable : (prefixWord ++ tailWord_931211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931211).length < 2 ^ (prefixWord ++ tailWord_931211).sum := by decide
  have hdescent : baseEnd_931211 < baseStart_931211 := by decide
  rcases family_descends (prefixWord ++ tailWord_931211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931226 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_931226 : Nat := 118140960795 + 931226 * 2 ^ 59
def prefixEnd_931226 : Nat := 4983230072969 + 3 ^ 40 * 931226 * 2
def baseEnd_931226 : Nat := 318777690642585871794917

theorem tailTrace_931226 : CollatzResearch.WordTrace tailWord_931226 prefixEnd_931226 318777690642585871794917 := by
  unfold tailWord_931226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8491150631083679396007383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22643068349556478389353021 8491150631083679396007383)
  ·
    refine ⟨12736725946625519094011075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8491150631083679396007383 12736725946625519094011075)
    ·
      refine ⟨19105088919938278641016613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12736725946625519094011075 19105088919938278641016613)
      ·
        refine ⟨3582204172488427245190615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19105088919938278641016613 3582204172488427245190615)
        ·
          refine ⟨5373306258732640867785923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582204172488427245190615 5373306258732640867785923)
          ·
            refine ⟨8059959388098961301678885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5373306258732640867785923 8059959388098961301678885)
            ·
              refine ⟨1511242385268555244064791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8059959388098961301678885 1511242385268555244064791)
              ·
                refine ⟨2266863577902832866097187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511242385268555244064791 2266863577902832866097187)
                ·
                  refine ⟨3400295366854249299145781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266863577902832866097187 3400295366854249299145781)
                  ·
                    refine ⟨318777690642585871794917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3400295366854249299145781 318777690642585871794917)
                    ·
                      rfl

theorem cell22_931226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_931226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931226 prefixEnd_931226 := by exact prefixLift 931226
  have htrace : WordTrace (prefixWord ++ tailWord_931226) baseStart_931226 baseEnd_931226 := by
    simpa [prefixWord, tailWord_931226, baseEnd_931226] using wordTrace_append hprefix tailTrace_931226
  have hstable : (prefixWord ++ tailWord_931226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931226).length < 2 ^ (prefixWord ++ tailWord_931226).sum := by decide
  have hdescent : baseEnd_931226 < baseStart_931226 := by decide
  rcases family_descends (prefixWord ++ tailWord_931226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931228 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 6]
def baseStart_931228 : Nat := 118140960795 + 931228 * 2 ^ 59
def prefixEnd_931228 : Nat := 4983230072969 + 3 ^ 40 * 931228 * 2
def baseEnd_931228 : Nat := 106259458427819511081637

theorem tailTrace_931228 : CollatzResearch.WordTrace tailWord_931228 prefixEnd_931228 106259458427819511081637 := by
  unfold tailWord_931228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16982337735163735962801169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22643116980218314617068225 16982337735163735962801169)
  ·
    refine ⟨12736753301372801972100877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16982337735163735962801169 12736753301372801972100877)
    ·
      refine ⟨4776282488014800739537829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12736753301372801972100877 4776282488014800739537829)
      ·
        refine ⟨895552966502775138663343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4776282488014800739537829 895552966502775138663343)
        ·
          refine ⟨1343329449754162707995015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895552966502775138663343 1343329449754162707995015)
          ·
            refine ⟨2014994174631244061992523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343329449754162707995015 2014994174631244061992523)
            ·
              refine ⟨3022491261946866092988785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014994174631244061992523 3022491261946866092988785)
              ·
                refine ⟨2266868446460149569741589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022491261946866092988785 2266868446460149569741589)
                ·
                  refine ⟨106259458427819511081637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2266868446460149569741589 106259458427819511081637)
                  ·
                    rfl

theorem cell22_931228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_931228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931228 prefixEnd_931228 := by exact prefixLift 931228
  have htrace : WordTrace (prefixWord ++ tailWord_931228) baseStart_931228 baseEnd_931228 := by
    simpa [prefixWord, tailWord_931228, baseEnd_931228] using wordTrace_append hprefix tailTrace_931228
  have hstable : (prefixWord ++ tailWord_931228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931228).length < 2 ^ (prefixWord ++ tailWord_931228).sum := by decide
  have hdescent : baseEnd_931228 < baseStart_931228 := by decide
  rcases family_descends (prefixWord ++ tailWord_931228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931245 : List Nat := [1, 5, 2, 2, 1, 2, 2, 3, 4]
def baseStart_931245 : Nat := 118140960795 + 931245 * 2 ^ 59
def prefixEnd_931245 : Nat := 4983230072969 + 3 ^ 40 * 931245 * 2
def baseEnd_931245 : Nat := 106261398243625385189953

theorem tailTrace_931245 : CollatzResearch.WordTrace tailWord_931245 prefixEnd_931245 106261398243625385189953 := by
  unfold tailWord_931245
  simp only [CollatzResearch.WordTrace]
  refine ⟨33965295511265883828971189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22643530340843922552647459 33965295511265883828971189)
  ·
    refine ⟨3184246454181176608966049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33965295511265883828971189 3184246454181176608966049)
    ·
      refine ⟨2388184840635882456724537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3184246454181176608966049 2388184840635882456724537)
      ·
        refine ⟨1791138630476911842543403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2388184840635882456724537 1791138630476911842543403)
        ·
          refine ⟨2686707945715367763815105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791138630476911842543403 2686707945715367763815105)
          ·
            refine ⟨2015030959286525822861329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2686707945715367763815105 2015030959286525822861329)
            ·
              refine ⟨1511273219464894367145997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015030959286525822861329 1511273219464894367145997)
              ·
                refine ⟨566727457299335387679749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1511273219464894367145997 566727457299335387679749)
                ·
                  refine ⟨106261398243625385189953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566727457299335387679749 106261398243625385189953)
                  ·
                    rfl

theorem cell22_931245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_931245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931245 prefixEnd_931245 := by exact prefixLift 931245
  have htrace : WordTrace (prefixWord ++ tailWord_931245) baseStart_931245 baseEnd_931245 := by
    simpa [prefixWord, tailWord_931245, baseEnd_931245] using wordTrace_append hprefix tailTrace_931245
  have hstable : (prefixWord ++ tailWord_931245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931245).length < 2 ^ (prefixWord ++ tailWord_931245).sum := by decide
  have hdescent : baseEnd_931245 < baseStart_931245 := by decide
  rcases family_descends (prefixWord ++ tailWord_931245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931301 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 7]
def baseStart_931301 : Nat := 118140960795 + 931301 * 2 ^ 59
def prefixEnd_931301 : Nat := 4983230072969 + 3 ^ 40 * 931301 * 2
def baseEnd_931301 : Nat := 106267788225103558723229

theorem tailTrace_931301 : CollatzResearch.WordTrace tailWord_931301 prefixEnd_931301 106267788225103558723229 := by
  unfold tailWord_931301
  simp only [CollatzResearch.WordTrace]
  refine ⟨33967337999063005393009757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22644891999375336928673171 33967337999063005393009757)
  ·
    refine ⟨12737751749648627022378659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33967337999063005393009757 12737751749648627022378659)
    ·
      refine ⟨19106627624472940533567989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12737751749648627022378659 19106627624472940533567989)
      ·
        refine ⟨1791246339794338175021999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19106627624472940533567989 1791246339794338175021999)
        ·
          refine ⟨2686869509691507262532999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791246339794338175021999 2686869509691507262532999)
          ·
            refine ⟨4030304264537260893799499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686869509691507262532999 4030304264537260893799499)
            ·
              refine ⟨6045456396805891340699249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030304264537260893799499 6045456396805891340699249)
              ·
                refine ⟨4534092297604418505524437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6045456396805891340699249 4534092297604418505524437)
                ·
                  refine ⟨106267788225103558723229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4534092297604418505524437 106267788225103558723229)
                  ·
                    rfl

theorem cell22_931301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_931301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931301 prefixEnd_931301 := by exact prefixLift 931301
  have htrace : WordTrace (prefixWord ++ tailWord_931301) baseStart_931301 baseEnd_931301 := by
    simpa [prefixWord, tailWord_931301, baseEnd_931301] using wordTrace_append hprefix tailTrace_931301
  have hstable : (prefixWord ++ tailWord_931301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931301).length < 2 ^ (prefixWord ++ tailWord_931301).sum := by decide
  have hdescent : baseEnd_931301 < baseStart_931301 := by decide
  rcases family_descends (prefixWord ++ tailWord_931301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931335 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 5]
def baseStart_931335 : Nat := 118140960795 + 931335 * 2 ^ 59
def prefixEnd_931335 : Nat := 4983230072969 + 3 ^ 40 * 931335 * 2
def baseEnd_931335 : Nat := 106271667856715306939861

theorem tailTrace_931335 : CollatzResearch.WordTrace tailWord_931335 prefixEnd_931335 106271667856715306939861 := by
  unfold tailWord_931335
  simp only [CollatzResearch.WordTrace]
  refine ⟨33968578080939829199747459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22645718720626552799831639 33968578080939829199747459)
  ·
    refine ⟨50952867121409743799621189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33968578080939829199747459 50952867121409743799621189)
    ·
      refine ⟨9553662585264326962428973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50952867121409743799621189 9553662585264326962428973)
      ·
        refine ⟨3582623469474122610910865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9553662585264326962428973 3582623469474122610910865)
        ·
          refine ⟨2686967602105591958183149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3582623469474122610910865 2686967602105591958183149)
          ·
            refine ⟨1007612850789596984318681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2686967602105591958183149 1007612850789596984318681)
            ·
              refine ⟨755709638092197738239011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007612850789596984318681 755709638092197738239011)
              ·
                refine ⟨1133564457138296607358517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755709638092197738239011 1133564457138296607358517)
                ·
                  refine ⟨106271667856715306939861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1133564457138296607358517 106271667856715306939861)
                  ·
                    rfl

theorem cell22_931335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 5].length) (baseStart_931335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931335 prefixEnd_931335 := by exact prefixLift 931335
  have htrace : WordTrace (prefixWord ++ tailWord_931335) baseStart_931335 baseEnd_931335 := by
    simpa [prefixWord, tailWord_931335, baseEnd_931335] using wordTrace_append hprefix tailTrace_931335
  have hstable : (prefixWord ++ tailWord_931335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931335).length < 2 ^ (prefixWord ++ tailWord_931335).sum := by decide
  have hdescent : baseEnd_931335 < baseStart_931335 := by decide
  rcases family_descends (prefixWord ++ tailWord_931335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931344 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_931344 : Nat := 118140960795 + 931344 * 2 ^ 59
def prefixEnd_931344 : Nat := 4983230072969 + 3 ^ 40 * 931344 * 2
def baseEnd_931344 : Nat := 318818084454072897344555

theorem tailTrace_931344 : CollatzResearch.WordTrace tailWord_931344 prefixEnd_931344 318818084454072897344555 := by
  unfold tailWord_931344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16984453168953611868412543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22645937558604815824550057 16984453168953611868412543)
  ·
    refine ⟨25476679753430417802618815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16984453168953611868412543 25476679753430417802618815)
    ·
      refine ⟨38215019630145626703928223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25476679753430417802618815 38215019630145626703928223)
      ·
        refine ⟨57322529445218440055892335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38215019630145626703928223 57322529445218440055892335)
        ·
          refine ⟨85983794167827660083838503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57322529445218440055892335 85983794167827660083838503)
          ·
            refine ⟨128975691251741490125757755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85983794167827660083838503 128975691251741490125757755)
            ·
              refine ⟨193463536877612235188636633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128975691251741490125757755 193463536877612235188636633)
              ·
                refine ⟨145097652658209176391477475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193463536877612235188636633 145097652658209176391477475)
                ·
                  refine ⟨217646478987313764587216213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145097652658209176391477475 217646478987313764587216213)
                  ·
                    refine ⟨318818084454072897344555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 217646478987313764587216213 318818084454072897344555)
                    ·
                      rfl

theorem cell22_931344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_931344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931344 prefixEnd_931344 := by exact prefixLift 931344
  have htrace : WordTrace (prefixWord ++ tailWord_931344) baseStart_931344 baseEnd_931344 := by
    simpa [prefixWord, tailWord_931344, baseEnd_931344] using wordTrace_append hprefix tailTrace_931344
  have hstable : (prefixWord ++ tailWord_931344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931344).length < 2 ^ (prefixWord ++ tailWord_931344).sum := by decide
  have hdescent : baseEnd_931344 < baseStart_931344 := by decide
  rcases family_descends (prefixWord ++ tailWord_931344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931361 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_931361 : Nat := 118140960795 + 931361 * 2 ^ 59
def prefixEnd_931361 : Nat := 4983230072969 + 3 ^ 40 * 931361 * 2
def baseEnd_931361 : Nat := 318823903901490519669503

theorem tailTrace_931361 : CollatzResearch.WordTrace tailWord_931361 prefixEnd_931361 318823903901490519669503 := by
  unfold tailWord_931361
  simp only [CollatzResearch.WordTrace]
  refine ⟨33969526378845635640193937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22646350919230423760129291 33969526378845635640193937)
  ·
    refine ⟨25477144784134226730145453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33969526378845635640193937 25477144784134226730145453)
    ·
      refine ⟨9553929294050335023804545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25477144784134226730145453 9553929294050335023804545)
      ·
        refine ⟨7165446970537751267853409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9553929294050335023804545 7165446970537751267853409)
        ·
          refine ⟨5374085227903313450890057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7165446970537751267853409 5374085227903313450890057)
          ·
            refine ⟨4030563920927485088167543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5374085227903313450890057 4030563920927485088167543)
            ·
              refine ⟨6045845881391227632251315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030563920927485088167543 6045845881391227632251315)
              ·
                refine ⟨9068768822086841448376973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045845881391227632251315 9068768822086841448376973)
                ·
                  refine ⟨3400788308282565543141365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9068768822086841448376973 3400788308282565543141365)
                  ·
                    refine ⟨318823903901490519669503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3400788308282565543141365 318823903901490519669503)
                    ·
                      rfl

theorem cell22_931361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_931361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931361 prefixEnd_931361 := by exact prefixLift 931361
  have htrace : WordTrace (prefixWord ++ tailWord_931361) baseStart_931361 baseEnd_931361 := by
    simpa [prefixWord, tailWord_931361, baseEnd_931361] using wordTrace_append hprefix tailTrace_931361
  have hstable : (prefixWord ++ tailWord_931361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931361).length < 2 ^ (prefixWord ++ tailWord_931361).sum := by decide
  have hdescent : baseEnd_931361 < baseStart_931361 := by decide
  rcases family_descends (prefixWord ++ tailWord_931361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931391 : List Nat := [1, 1, 2, 2, 3, 3, 3, 7]
def baseStart_931391 : Nat := 118140960795 + 931391 * 2 ^ 59
def prefixEnd_931391 : Nat := 4983230072969 + 3 ^ 40 * 931391 * 2
def baseEnd_931391 : Nat := 35426019279397826824379

theorem tailTrace_931391 : CollatzResearch.WordTrace tailWord_931391 prefixEnd_931391 35426019279397826824379 := by
  unfold tailWord_931391
  simp only [CollatzResearch.WordTrace]
  refine ⟨33970620568736950763786027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22647080379157967175857351 33970620568736950763786027)
  ·
    refine ⟨50955930853105426145679041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33970620568736950763786027 50955930853105426145679041)
    ·
      refine ⟨38216948139829069609259281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50955930853105426145679041 38216948139829069609259281)
      ·
        refine ⟨28662711104871802206944461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38216948139829069609259281 28662711104871802206944461)
        ·
          refine ⟨10748516664326925827604173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28662711104871802206944461 10748516664326925827604173)
          ·
            refine ⟨4030693749122597185351565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10748516664326925827604173 4030693749122597185351565)
            ·
              refine ⟨1511510155920973944506837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4030693749122597185351565 1511510155920973944506837)
              ·
                refine ⟨35426019279397826824379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1511510155920973944506837 35426019279397826824379)
                ·
                  rfl

theorem cell22_931391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 7].length) (baseStart_931391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931391 prefixEnd_931391 := by exact prefixLift 931391
  have htrace : WordTrace (prefixWord ++ tailWord_931391) baseStart_931391 baseEnd_931391 := by
    simpa [prefixWord, tailWord_931391, baseEnd_931391] using wordTrace_append hprefix tailTrace_931391
  have hstable : (prefixWord ++ tailWord_931391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931391).length < 2 ^ (prefixWord ++ tailWord_931391).sum := by decide
  have hdescent : baseEnd_931391 < baseStart_931391 := by decide
  rcases family_descends (prefixWord ++ tailWord_931391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931410 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_931410 : Nat := 118140960795 + 931410 * 2 ^ 59
def prefixEnd_931410 : Nat := 4983230072969 + 3 ^ 40 * 931410 * 2
def baseEnd_931410 : Nat := 318840677602870725194353

theorem tailTrace_931410 : CollatzResearch.WordTrace tailWord_931410 prefixEnd_931410 318840677602870725194353 := by
  unfold tailWord_931410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492828388917029252181921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22647542370445411339151789 8492828388917029252181921)
  ·
    refine ⟨6369621291687771939136441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8492828388917029252181921 6369621291687771939136441)
    ·
      refine ⟨4777215968765828954352331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6369621291687771939136441 4777215968765828954352331)
      ·
        refine ⟨7165823953148743431528497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4777215968765828954352331 7165823953148743431528497)
        ·
          refine ⟨5374367964861557573646373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7165823953148743431528497 5374367964861557573646373)
          ·
            refine ⟨1007693993411542045058695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5374367964861557573646373 1007693993411542045058695)
            ·
              refine ⟨1511540990117313067588043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007693993411542045058695 1511540990117313067588043)
              ·
                refine ⟨2267311485175969601382065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511540990117313067588043 2267311485175969601382065)
                ·
                  refine ⟨1700483613881977201036549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2267311485175969601382065 1700483613881977201036549)
                  ·
                    refine ⟨318840677602870725194353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1700483613881977201036549 318840677602870725194353)
                    ·
                      rfl

theorem cell22_931410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_931410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931410 prefixEnd_931410 := by exact prefixLift 931410
  have htrace : WordTrace (prefixWord ++ tailWord_931410) baseStart_931410 baseEnd_931410 := by
    simpa [prefixWord, tailWord_931410, baseEnd_931410] using wordTrace_append hprefix tailTrace_931410
  have hstable : (prefixWord ++ tailWord_931410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931410).length < 2 ^ (prefixWord ++ tailWord_931410).sum := by decide
  have hdescent : baseEnd_931410 < baseStart_931410 := by decide
  rcases family_descends (prefixWord ++ tailWord_931410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931440 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 3, 3]
def baseStart_931440 : Nat := 118140960795 + 931440 * 2 ^ 59
def prefixEnd_931440 : Nat := 4983230072969 + 3 ^ 40 * 931440 * 2
def baseEnd_931440 : Nat := 318850947215960646944261

theorem tailTrace_931440 : CollatzResearch.WordTrace tailWord_931440 prefixEnd_931440 318850947215960646944261 := by
  unfold tailWord_931440
  simp only [CollatzResearch.WordTrace]
  refine ⟨16986203872779716066159887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22648271830372954754879849 16986203872779716066159887)
  ·
    refine ⟨25479305809169574099239831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16986203872779716066159887 25479305809169574099239831)
    ·
      refine ⟨38218958713754361148859747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25479305809169574099239831 38218958713754361148859747)
      ·
        refine ⟨57328438070631541723289621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38218958713754361148859747 57328438070631541723289621)
        ·
          refine ⟨2687270534560853518279201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57328438070631541723289621 2687270534560853518279201)
          ·
            refine ⟨2015452900920640138709401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2687270534560853518279201 2015452900920640138709401)
            ·
              refine ⟨1511589675690480104032051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015452900920640138709401 1511589675690480104032051)
              ·
                refine ⟨2267384513535720156048077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511589675690480104032051 2267384513535720156048077)
                ·
                  refine ⟨850269192575895058518029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2267384513535720156048077 850269192575895058518029)
                  ·
                    refine ⟨318850947215960646944261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 850269192575895058518029 318850947215960646944261)
                    ·
                      rfl

theorem cell22_931440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_931440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931440 prefixEnd_931440 := by exact prefixLift 931440
  have htrace : WordTrace (prefixWord ++ tailWord_931440) baseStart_931440 baseEnd_931440 := by
    simpa [prefixWord, tailWord_931440, baseEnd_931440] using wordTrace_append hprefix tailTrace_931440
  have hstable : (prefixWord ++ tailWord_931440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931440).length < 2 ^ (prefixWord ++ tailWord_931440).sum := by decide
  have hdescent : baseEnd_931440 < baseStart_931440 := by decide
  rcases family_descends (prefixWord ++ tailWord_931440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931451 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 2, 5]
def baseStart_931451 : Nat := 118140960795 + 931451 * 2 ^ 59
def prefixEnd_931451 : Nat := 4983230072969 + 3 ^ 40 * 931451 * 2
def baseEnd_931451 : Nat := 318854712740760284919227

theorem tailTrace_931451 : CollatzResearch.WordTrace tailWord_931451 prefixEnd_931451 318854712740760284919227 := by
  unfold tailWord_931451
  simp only [CollatzResearch.WordTrace]
  refine ⟨33972808948519581010970207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22648539299013054007313471 33972808948519581010970207)
  ·
    refine ⟨50959213422779371516455311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33972808948519581010970207 50959213422779371516455311)
    ·
      refine ⟨76438820134169057274682967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50959213422779371516455311 76438820134169057274682967)
      ·
        refine ⟨114658230201253585912024451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76438820134169057274682967 114658230201253585912024451)
        ·
          refine ⟨171987345301880378868036677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114658230201253585912024451 171987345301880378868036677)
          ·
            refine ⟨32247627244102571037756877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171987345301880378868036677 32247627244102571037756877)
            ·
              refine ⟨12092860216538464139158829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32247627244102571037756877 12092860216538464139158829)
              ·
                refine ⟨4534822581201924052184561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12092860216538464139158829 4534822581201924052184561)
                ·
                  refine ⟨3401116935901443039138421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4534822581201924052184561 3401116935901443039138421)
                  ·
                    refine ⟨318854712740760284919227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3401116935901443039138421 318854712740760284919227)
                    ·
                      rfl

theorem cell22_931451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_931451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931451 prefixEnd_931451 := by exact prefixLift 931451
  have htrace : WordTrace (prefixWord ++ tailWord_931451) baseStart_931451 baseEnd_931451 := by
    simpa [prefixWord, tailWord_931451, baseEnd_931451] using wordTrace_append hprefix tailTrace_931451
  have hstable : (prefixWord ++ tailWord_931451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931451).length < 2 ^ (prefixWord ++ tailWord_931451).sum := by decide
  have hdescent : baseEnd_931451 < baseStart_931451 := by decide
  rcases family_descends (prefixWord ++ tailWord_931451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931530 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_931530 : Nat := 118140960795 + 931530 * 2 ^ 59
def prefixEnd_931530 : Nat := 4983230072969 + 3 ^ 40 * 931530 * 2
def baseEnd_931530 : Nat := 318881756055230412193985

theorem tailTrace_931530 : CollatzResearch.WordTrace tailWord_931530 prefixEnd_931530 318881756055230412193985 := by
  unfold tailWord_931530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493922578808344375774011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22650460210155585002064029 8493922578808344375774011)
  ·
    refine ⟨12740883868212516563661017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8493922578808344375774011 12740883868212516563661017)
    ·
      refine ⟨9555662901159387422745763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12740883868212516563661017 9555662901159387422745763)
      ·
        refine ⟨14333494351739081134118645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9555662901159387422745763 14333494351739081134118645)
        ·
          refine ⟨1343765095475538856323623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14333494351739081134118645 1343765095475538856323623)
          ·
            refine ⟨2015647643213308284485435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343765095475538856323623 2015647643213308284485435)
            ·
              refine ⟨3023471464819962426728153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2015647643213308284485435 3023471464819962426728153)
              ·
                refine ⟨2267603598614971820046115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3023471464819962426728153 2267603598614971820046115)
                ·
                  refine ⟨3401405397922457730069173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267603598614971820046115 3401405397922457730069173)
                  ·
                    refine ⟨318881756055230412193985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3401405397922457730069173 318881756055230412193985)
                    ·
                      rfl

theorem cell22_931530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_931530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931530 prefixEnd_931530 := by exact prefixLift 931530
  have htrace : WordTrace (prefixWord ++ tailWord_931530) baseStart_931530 baseEnd_931530 := by
    simpa [prefixWord, tailWord_931530, baseEnd_931530] using wordTrace_append hprefix tailTrace_931530
  have hstable : (prefixWord ++ tailWord_931530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931530).length < 2 ^ (prefixWord ++ tailWord_931530).sum := by decide
  have hdescent : baseEnd_931530 < baseStart_931530 := by decide
  rcases family_descends (prefixWord ++ tailWord_931530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931549 : List Nat := [1, 4, 3, 3, 1, 1, 1, 4, 4]
def baseStart_931549 : Nat := 118140960795 + 931549 * 2 ^ 59
def prefixEnd_931549 : Nat := 4983230072969 + 3 ^ 40 * 931549 * 2
def baseEnd_931549 : Nat := 106296086714506898656309

theorem tailTrace_931549 : CollatzResearch.WordTrace tailWord_931549 prefixEnd_931549 106296086714506898656309 := by
  unfold tailWord_931549
  simp only [CollatzResearch.WordTrace]
  refine ⟨33976383302164543748037701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22650922201443029165358467 33976383302164543748037701)
  ·
    refine ⟨6370571869155851952757069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33976383302164543748037701 6370571869155851952757069)
    ·
      refine ⟨2388964450933444482283901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6370571869155851952757069 2388964450933444482283901)
      ·
        refine ⟨895861669100041680856463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2388964450933444482283901 895861669100041680856463)
        ·
          refine ⟨1343792503650062521284695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895861669100041680856463 1343792503650062521284695)
          ·
            refine ⟨2015688755475093781927043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343792503650062521284695 2015688755475093781927043)
            ·
              refine ⟨3023533133212640672890565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2015688755475093781927043 3023533133212640672890565)
              ·
                refine ⟨566912462477370126166981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3023533133212640672890565 566912462477370126166981)
                ·
                  refine ⟨106296086714506898656309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566912462477370126166981 106296086714506898656309)
                  ·
                    rfl

theorem cell22_931549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_931549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931549 prefixEnd_931549 := by exact prefixLift 931549
  have htrace : WordTrace (prefixWord ++ tailWord_931549) baseStart_931549 baseEnd_931549 := by
    simpa [prefixWord, tailWord_931549, baseEnd_931549] using wordTrace_append hprefix tailTrace_931549
  have hstable : (prefixWord ++ tailWord_931549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931549).length < 2 ^ (prefixWord ++ tailWord_931549).sum := by decide
  have hdescent : baseEnd_931549 < baseStart_931549 := by decide
  rcases family_descends (prefixWord ++ tailWord_931549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931560 : List Nat := [2, 1, 4, 1, 3, 3, 1, 7]
def baseStart_931560 : Nat := 118140960795 + 931560 * 2 ^ 59
def prefixEnd_931560 : Nat := 4983230072969 + 3 ^ 40 * 931560 * 2
def baseEnd_931560 : Nat := 35432447296480037104877

theorem tailTrace_931560 : CollatzResearch.WordTrace tailWord_931560 prefixEnd_931560 35432447296480037104877 := by
  unfold tailWord_931560
  simp only [CollatzResearch.WordTrace]
  refine ⟨16988392252562346313344067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22651189670083128417792089 16988392252562346313344067)
  ·
    refine ⟨25482588378843519470016101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16988392252562346313344067 25482588378843519470016101)
    ·
      refine ⟨4777985321033159900628019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25482588378843519470016101 4777985321033159900628019)
      ·
        refine ⟨7166977981549739850942029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4777985321033159900628019 7166977981549739850942029)
        ·
          refine ⟨2687616743081152444103261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7166977981549739850942029 2687616743081152444103261)
          ·
            refine ⟨1007856278655432166538723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2687616743081152444103261 1007856278655432166538723)
            ·
              refine ⟨1511784417983148249808085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007856278655432166538723 1511784417983148249808085)
              ·
                refine ⟨35432447296480037104877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1511784417983148249808085 35432447296480037104877)
                ·
                  rfl

theorem cell22_931560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 7].length) (baseStart_931560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931560 prefixEnd_931560 := by exact prefixLift 931560
  have htrace : WordTrace (prefixWord ++ tailWord_931560) baseStart_931560 baseEnd_931560 := by
    simpa [prefixWord, tailWord_931560, baseEnd_931560] using wordTrace_append hprefix tailTrace_931560
  have hstable : (prefixWord ++ tailWord_931560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931560).length < 2 ^ (prefixWord ++ tailWord_931560).sum := by decide
  have hdescent : baseEnd_931560 < baseStart_931560 := by decide
  rcases family_descends (prefixWord ++ tailWord_931560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931605 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 5]
def baseStart_931605 : Nat := 118140960795 + 931605 * 2 ^ 59
def prefixEnd_931605 : Nat := 4983230072969 + 3 ^ 40 * 931605 * 2
def baseEnd_931605 : Nat := 106302476695985072189585

theorem tailTrace_931605 : CollatzResearch.WordTrace tailWord_931605 prefixEnd_931605 106302476695985072189585 := by
  unfold tailWord_931605
  simp only [CollatzResearch.WordTrace]
  refine ⟨33978425789961665312076269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22652283859974443541384179 33978425789961665312076269)
  ·
    refine ⟨12741909671235624492028601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33978425789961665312076269 12741909671235624492028601)
    ·
      refine ⟨9556432253426718369021451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12741909671235624492028601 9556432253426718369021451)
      ·
        refine ⟨14334648380140077553532177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9556432253426718369021451 14334648380140077553532177)
        ·
          refine ⟨10750986285105058165149133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14334648380140077553532177 10750986285105058165149133)
          ·
            refine ⟨4031619856914396811930925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10750986285105058165149133 4031619856914396811930925)
            ·
              refine ⟨1511857446342898804474097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4031619856914396811930925 1511857446342898804474097)
              ·
                refine ⟨1133893084757174103355573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511857446342898804474097 1133893084757174103355573)
                ·
                  refine ⟨106302476695985072189585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1133893084757174103355573 106302476695985072189585)
                  ·
                    rfl

theorem cell22_931605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_931605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931605 prefixEnd_931605 := by exact prefixLift 931605
  have htrace : WordTrace (prefixWord ++ tailWord_931605) baseStart_931605 baseEnd_931605 := by
    simpa [prefixWord, tailWord_931605, baseEnd_931605] using wordTrace_append hprefix tailTrace_931605
  have hstable : (prefixWord ++ tailWord_931605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931605).length < 2 ^ (prefixWord ++ tailWord_931605).sum := by decide
  have hdescent : baseEnd_931605 < baseStart_931605 := by decide
  rcases family_descends (prefixWord ++ tailWord_931605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931620 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_931620 : Nat := 118140960795 + 931620 * 2 ^ 59
def prefixEnd_931620 : Nat := 4983230072969 + 3 ^ 40 * 931620 * 2
def baseEnd_931620 : Nat := 318912564894500177443709

theorem tailTrace_931620 : CollatzResearch.WordTrace tailWord_931620 prefixEnd_931620 318912564894500177443709 := by
  unfold tailWord_931620
  simp only [CollatzResearch.WordTrace]
  refine ⟨16989486442453661436936157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22652648589938215249248209 16989486442453661436936157)
  ·
    refine ⟨6371057415920123038851059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16989486442453661436936157 6371057415920123038851059)
    ·
      refine ⟨9556586123880184558276589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6371057415920123038851059 9556586123880184558276589)
      ·
        refine ⟨3583719796455069209353721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9556586123880184558276589 3583719796455069209353721)
        ·
          refine ⟨2687789847341301907015291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3583719796455069209353721 2687789847341301907015291)
          ·
            refine ⟨4031684771011952860522937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687789847341301907015291 4031684771011952860522937)
            ·
              refine ⟨3023763578258964645392203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4031684771011952860522937 3023763578258964645392203)
              ·
                refine ⟨4535645367388446968088305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023763578258964645392203 4535645367388446968088305)
                ·
                  refine ⟨3401734025541335226066229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4535645367388446968088305 3401734025541335226066229)
                  ·
                    refine ⟨318912564894500177443709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3401734025541335226066229 318912564894500177443709)
                    ·
                      rfl

theorem cell22_931620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_931620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931620 prefixEnd_931620 := by exact prefixLift 931620
  have htrace : WordTrace (prefixWord ++ tailWord_931620) baseStart_931620 baseEnd_931620 := by
    simpa [prefixWord, tailWord_931620, baseEnd_931620] using wordTrace_append hprefix tailTrace_931620
  have hstable : (prefixWord ++ tailWord_931620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931620).length < 2 ^ (prefixWord ++ tailWord_931620).sum := by decide
  have hdescent : baseEnd_931620 < baseStart_931620 := by decide
  rcases family_descends (prefixWord ++ tailWord_931620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931761 : List Nat := [1, 2, 2, 4, 2, 2, 2, 3, 1, 3]
def baseStart_931761 : Nat := 118140960795 + 931761 * 2 ^ 59
def prefixEnd_931761 : Nat := 4983230072969 + 3 ^ 40 * 931761 * 2
def baseEnd_931761 : Nat := 318960832076022809668277

theorem tailTrace_931761 : CollatzResearch.WordTrace tailWord_931761 prefixEnd_931761 318960832076022809668277 := by
  unfold tailWord_931761
  simp only [CollatzResearch.WordTrace]
  refine ⟨33984115577396503954755137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22656077051597669303170091 33984115577396503954755137)
  ·
    refine ⟨25488086683047377966066353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33984115577396503954755137 25488086683047377966066353)
    ·
      refine ⟨19116065012285533474549765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25488086683047377966066353 19116065012285533474549765)
      ·
        refine ⟨3584262189803537526478081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19116065012285533474549765 3584262189803537526478081)
        ·
          refine ⟨2688196642352653144858561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3584262189803537526478081 2688196642352653144858561)
          ·
            refine ⟨2016147481764489858643921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2688196642352653144858561 2016147481764489858643921)
            ·
              refine ⟨1512110611323367393982941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016147481764489858643921 1512110611323367393982941)
              ·
                refine ⟨567041479246262772743603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1512110611323367393982941 567041479246262772743603)
                ·
                  refine ⟨850562218869394159115405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567041479246262772743603 850562218869394159115405)
                  ·
                    refine ⟨318960832076022809668277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 850562218869394159115405 318960832076022809668277)
                    ·
                      rfl

theorem cell22_931761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_931761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931761 prefixEnd_931761 := by exact prefixLift 931761
  have htrace : WordTrace (prefixWord ++ tailWord_931761) baseStart_931761 baseEnd_931761 := by
    simpa [prefixWord, tailWord_931761, baseEnd_931761] using wordTrace_append hprefix tailTrace_931761
  have hstable : (prefixWord ++ tailWord_931761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931761).length < 2 ^ (prefixWord ++ tailWord_931761).sum := by decide
  have hdescent : baseEnd_931761 < baseStart_931761 := by decide
  rcases family_descends (prefixWord ++ tailWord_931761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931770 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_931770 : Nat := 118140960795 + 931770 * 2 ^ 59
def prefixEnd_931770 : Nat := 4983230072969 + 3 ^ 40 * 931770 * 2
def baseEnd_931770 : Nat := 318963912959949786193249

theorem tailTrace_931770 : CollatzResearch.WordTrace tailWord_931770 prefixEnd_931770 318963912959949786193249 := by
  unfold tailWord_931770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8496110958590974622958191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22656295889575932327888509 8496110958590974622958191)
  ·
    refine ⟨12744166437886461934437287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8496110958590974622958191 12744166437886461934437287)
    ·
      refine ⟨19116249656829692901655931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12744166437886461934437287 19116249656829692901655931)
      ·
        refine ⟨28674374485244539352483897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19116249656829692901655931 28674374485244539352483897)
        ·
          refine ⟨21505780863933404514362923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28674374485244539352483897 21505780863933404514362923)
          ·
            refine ⟨32258671295900106771544385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21505780863933404514362923 32258671295900106771544385)
            ·
              refine ⟨24194003471925080078658289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32258671295900106771544385 24194003471925080078658289)
              ·
                refine ⟨18145502603943810058993717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24194003471925080078658289 18145502603943810058993717)
                ·
                  refine ⟨1701140869119732193030661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18145502603943810058993717 1701140869119732193030661)
                  ·
                    refine ⟨318963912959949786193249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1701140869119732193030661 318963912959949786193249)
                    ·
                      rfl

theorem cell22_931770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_931770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931770 prefixEnd_931770 := by exact prefixLift 931770
  have htrace : WordTrace (prefixWord ++ tailWord_931770) baseStart_931770 baseEnd_931770 := by
    simpa [prefixWord, tailWord_931770, baseEnd_931770] using wordTrace_append hprefix tailTrace_931770
  have hstable : (prefixWord ++ tailWord_931770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931770).length < 2 ^ (prefixWord ++ tailWord_931770).sum := by decide
  have hdescent : baseEnd_931770 < baseStart_931770 := by decide
  rcases family_descends (prefixWord ++ tailWord_931770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931774 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_931774 : Nat := 118140960795 + 931774 * 2 ^ 59
def prefixEnd_931774 : Nat := 4983230072969 + 3 ^ 40 * 931774 * 2
def baseEnd_931774 : Nat := 106321760747231703031079

theorem tailTrace_931774 : CollatzResearch.WordTrace tailWord_931774 prefixEnd_931774 106321760747231703031079 := by
  unfold tailWord_931774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248073715793675896872297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22656393150899604783318917 4248073715793675896872297)
  ·
    refine ⟨3186055286845256922654223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4248073715793675896872297 3186055286845256922654223)
    ·
      refine ⟨4779082930267885383981335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3186055286845256922654223 4779082930267885383981335)
      ·
        refine ⟨7168624395401828075972003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779082930267885383981335 7168624395401828075972003)
        ·
          refine ⟨10752936593102742113958005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168624395401828075972003 10752936593102742113958005)
          ·
            refine ⟨1008087805603382073183563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10752936593102742113958005 1008087805603382073183563)
            ·
              refine ⟨1512131708405073109775345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008087805603382073183563 1512131708405073109775345)
              ·
                refine ⟨1134098781303804832331509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512131708405073109775345 1134098781303804832331509)
                ·
                  refine ⟨106321760747231703031079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1134098781303804832331509 106321760747231703031079)
                  ·
                    rfl

theorem cell22_931774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_931774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931774 prefixEnd_931774 := by exact prefixLift 931774
  have htrace : WordTrace (prefixWord ++ tailWord_931774) baseStart_931774 baseEnd_931774 := by
    simpa [prefixWord, tailWord_931774, baseEnd_931774] using wordTrace_append hprefix tailTrace_931774
  have hstable : (prefixWord ++ tailWord_931774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931774).length < 2 ^ (prefixWord ++ tailWord_931774).sum := by decide
  have hdescent : baseEnd_931774 < baseStart_931774 := by decide
  rcases family_descends (prefixWord ++ tailWord_931774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931847 : List Nat := [1, 1, 4, 3, 1, 3, 2, 7]
def baseStart_931847 : Nat := 118140960795 + 931847 * 2 ^ 59
def prefixEnd_931847 : Nat := 4983230072969 + 3 ^ 40 * 931847 * 2
def baseEnd_931847 : Nat := 35443363514838583557557

theorem tailTrace_931847 : CollatzResearch.WordTrace tailWord_931847 prefixEnd_931847 35443363514838583557557 := by
  unfold tailWord_931847
  simp only [CollatzResearch.WordTrace]
  refine ⟨33987252255084940642385795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22658168170056627094923863 33987252255084940642385795)
  ·
    refine ⟨50980878382627410963578693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33987252255084940642385795 50980878382627410963578693)
    ·
      refine ⟨9558914696742639555671005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50980878382627410963578693 9558914696742639555671005)
      ·
        refine ⟨3584593011278489833376627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9558914696742639555671005 3584593011278489833376627)
        ·
          refine ⟨5376889516917734750064941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584593011278489833376627 5376889516917734750064941)
          ·
            refine ⟨2016333568844150531274353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5376889516917734750064941 2016333568844150531274353)
            ·
              refine ⟨1512250176633112898455765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016333568844150531274353 1512250176633112898455765)
              ·
                refine ⟨35443363514838583557557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1512250176633112898455765 35443363514838583557557)
                ·
                  rfl

theorem cell22_931847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 7].length) (baseStart_931847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931847 prefixEnd_931847 := by exact prefixLift 931847
  have htrace : WordTrace (prefixWord ++ tailWord_931847) baseStart_931847 baseEnd_931847 := by
    simpa [prefixWord, tailWord_931847, baseEnd_931847] using wordTrace_append hprefix tailTrace_931847
  have hstable : (prefixWord ++ tailWord_931847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931847).length < 2 ^ (prefixWord ++ tailWord_931847).sum := by decide
  have hdescent : baseEnd_931847 < baseStart_931847 := by decide
  rcases family_descends (prefixWord ++ tailWord_931847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931954 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_931954 : Nat := 118140960795 + 931954 * 2 ^ 59
def prefixEnd_931954 : Nat := 4983230072969 + 3 ^ 40 * 931954 * 2
def baseEnd_931954 : Nat := 106342299973411546530895

theorem tailTrace_931954 : CollatzResearch.WordTrace tailWord_931954 prefixEnd_931954 106342299973411546530895 := by
  unfold tailWord_931954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8497788716424324479132729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22660769910464865277687277 8497788716424324479132729)
  ·
    refine ⟨6373341537318243359349547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8497788716424324479132729 6373341537318243359349547)
    ·
      refine ⟨9560012305977365039024321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6373341537318243359349547 9560012305977365039024321)
      ·
        refine ⟨7170009229483023779268241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9560012305977365039024321 7170009229483023779268241)
        ·
          refine ⟨5377506922112267834451181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7170009229483023779268241 5377506922112267834451181)
          ·
            refine ⟨2016565095792100437919193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5377506922112267834451181 2016565095792100437919193)
            ·
              refine ⟨1512423821844075328439395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016565095792100437919193 1512423821844075328439395)
              ·
                refine ⟨2268635732766112992659093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512423821844075328439395 2268635732766112992659093)
                ·
                  refine ⟨106342299973411546530895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2268635732766112992659093 106342299973411546530895)
                  ·
                    rfl

theorem cell22_931954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_931954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931954 prefixEnd_931954 := by exact prefixLift 931954
  have htrace : WordTrace (prefixWord ++ tailWord_931954) baseStart_931954 baseEnd_931954 := by
    simpa [prefixWord, tailWord_931954, baseEnd_931954] using wordTrace_append hprefix tailTrace_931954
  have hstable : (prefixWord ++ tailWord_931954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931954).length < 2 ^ (prefixWord ++ tailWord_931954).sum := by decide
  have hdescent : baseEnd_931954 < baseStart_931954 := by decide
  rcases family_descends (prefixWord ++ tailWord_931954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931999 : List Nat := [1, 1, 2, 6, 1, 3, 8]
def baseStart_931999 : Nat := 118140960795 + 931999 * 2 ^ 59
def prefixEnd_931999 : Nat := 4983230072969 + 3 ^ 40 * 931999 * 2
def baseEnd_931999 : Nat := 11816381642217389711761

theorem tailTrace_931999 : CollatzResearch.WordTrace tailWord_931999 prefixEnd_931999 11816381642217389711761 := by
  unfold tailWord_931999
  simp only [CollatzResearch.WordTrace]
  refine ⟨33992796150534270601919051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22661864100356180401279367 33992796150534270601919051)
  ·
    refine ⟨50989194225801405902878577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33992796150534270601919051 50989194225801405902878577)
    ·
      refine ⟨38241895669351054427158933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50989194225801405902878577 38241895669351054427158933)
      ·
        refine ⟨1792588859500830676273075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38241895669351054427158933 1792588859500830676273075)
        ·
          refine ⟨2688883289251246014409613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1792588859500830676273075 2688883289251246014409613)
          ·
            refine ⟨1008331233469217255403605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2688883289251246014409613 1008331233469217255403605)
            ·
              refine ⟨11816381642217389711761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1008331233469217255403605 11816381642217389711761)
              ·
                rfl

theorem cell22_931999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 8].length) (baseStart_931999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_931999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_931999 prefixEnd_931999 := by exact prefixLift 931999
  have htrace : WordTrace (prefixWord ++ tailWord_931999) baseStart_931999 baseEnd_931999 := by
    simpa [prefixWord, tailWord_931999, baseEnd_931999] using wordTrace_append hprefix tailTrace_931999
  have hstable : (prefixWord ++ tailWord_931999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931999).length < 2 ^ (prefixWord ++ tailWord_931999).sum := by decide
  have hdescent : baseEnd_931999 < baseStart_931999 := by decide
  rcases family_descends (prefixWord ++ tailWord_931999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932061 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 5]
def baseStart_932061 : Nat := 118140960795 + 932061 * 2 ^ 59
def prefixEnd_932061 : Nat := 4983230072969 + 3 ^ 40 * 932061 * 2
def baseEnd_932061 : Nat := 106354509402307342389119

theorem tailTrace_932061 : CollatzResearch.WordTrace tailWord_932061 prefixEnd_932061 106354509402307342389119 := by
  unfold tailWord_932061
  simp only [CollatzResearch.WordTrace]
  refine ⟨33995057476309655190676037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22663371650873103460450691 33995057476309655190676037)
  ·
    refine ⟨6374073276808060348251757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33995057476309655190676037 6374073276808060348251757)
    ·
      refine ⟨2390277478803022630594409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6374073276808060348251757 2390277478803022630594409)
      ·
        refine ⟨1792708109102266972945807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2390277478803022630594409 1792708109102266972945807)
        ·
          refine ⟨2689062163653400459418711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1792708109102266972945807 2689062163653400459418711)
          ·
            refine ⟨4033593245480100689128067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689062163653400459418711 4033593245480100689128067)
            ·
              refine ⟨6050389868220151033692101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033593245480100689128067 6050389868220151033692101)
              ·
                refine ⟨1134448100291278318817269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6050389868220151033692101 1134448100291278318817269)
                ·
                  refine ⟨106354509402307342389119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1134448100291278318817269 106354509402307342389119)
                  ·
                    rfl

theorem cell22_932061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_932061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932061 prefixEnd_932061 := by exact prefixLift 932061
  have htrace : WordTrace (prefixWord ++ tailWord_932061) baseStart_932061 baseEnd_932061 := by
    simpa [prefixWord, tailWord_932061, baseEnd_932061] using wordTrace_append hprefix tailTrace_932061
  have hstable : (prefixWord ++ tailWord_932061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932061).length < 2 ^ (prefixWord ++ tailWord_932061).sum := by decide
  have hdescent : baseEnd_932061 < baseStart_932061 := by decide
  rcases family_descends (prefixWord ++ tailWord_932061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932074 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_932074 : Nat := 118140960795 + 932074 * 2 ^ 59
def prefixEnd_932074 : Nat := 4983230072969 + 3 ^ 40 * 932074 * 2
def baseEnd_932074 : Nat := 319067978372594326592317

theorem tailTrace_932074 : CollatzResearch.WordTrace tailWord_932074 prefixEnd_932074 319067978372594326592317 := by
  unfold tailWord_932074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498882906315639602724819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22663687750175038940599517 8498882906315639602724819)
  ·
    refine ⟨12748324359473459404087229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8498882906315639602724819 12748324359473459404087229)
    ·
      refine ⟨4780621634802547276532711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12748324359473459404087229 4780621634802547276532711)
      ·
        refine ⟨7170932452203820914799067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4780621634802547276532711 7170932452203820914799067)
        ·
          refine ⟨10756398678305731372198601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170932452203820914799067 10756398678305731372198601)
          ·
            refine ⟨8067299008729298529148951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10756398678305731372198601 8067299008729298529148951)
            ·
              refine ⟨12100948513093947793723427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8067299008729298529148951 12100948513093947793723427)
              ·
                refine ⟨18151422769640921690585141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12100948513093947793723427 18151422769640921690585141)
                ·
                  refine ⟨1701695884653836408492357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18151422769640921690585141 1701695884653836408492357)
                  ·
                    refine ⟨319067978372594326592317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1701695884653836408492357 319067978372594326592317)
                    ·
                      rfl

theorem cell22_932074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_932074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932074 prefixEnd_932074 := by exact prefixLift 932074
  have htrace : WordTrace (prefixWord ++ tailWord_932074) baseStart_932074 baseEnd_932074 := by
    simpa [prefixWord, tailWord_932074, baseEnd_932074] using wordTrace_append hprefix tailTrace_932074
  have hstable : (prefixWord ++ tailWord_932074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932074).length < 2 ^ (prefixWord ++ tailWord_932074).sum := by decide
  have hdescent : baseEnd_932074 < baseStart_932074 := by decide
  rcases family_descends (prefixWord ++ tailWord_932074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932106 : List Nat := [3, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_932106 : Nat := 118140960795 + 932106 * 2 ^ 59
def prefixEnd_932106 : Nat := 4983230072969 + 3 ^ 40 * 932106 * 2
def baseEnd_932106 : Nat := 106359644208852303264073

theorem tailTrace_932106 : CollatzResearch.WordTrace tailWord_932106 prefixEnd_932106 106359644208852303264073 := by
  unfold tailWord_932106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8499174690286656969016043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22664465840764418584042781 8499174690286656969016043)
  ·
    refine ⟨12748762035429985453524065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8499174690286656969016043 12748762035429985453524065)
    ·
      refine ⟨9561571526572489090143049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12748762035429985453524065 9561571526572489090143049)
      ·
        refine ⟨7171178644929366817607287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9561571526572489090143049 7171178644929366817607287)
        ·
          refine ⟨10756767967394050226410931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7171178644929366817607287 10756767967394050226410931)
          ·
            refine ⟨16135151951091075339616397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756767967394050226410931 16135151951091075339616397)
            ·
              refine ⟨6050681981659153252356149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16135151951091075339616397 6050681981659153252356149)
              ·
                refine ⟨567251435780545617408389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6050681981659153252356149 567251435780545617408389)
                ·
                  refine ⟨106359644208852303264073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567251435780545617408389 106359644208852303264073)
                  ·
                    rfl

theorem cell22_932106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_932106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932106 prefixEnd_932106 := by exact prefixLift 932106
  have htrace : WordTrace (prefixWord ++ tailWord_932106) baseStart_932106 baseEnd_932106 := by
    simpa [prefixWord, tailWord_932106, baseEnd_932106] using wordTrace_append hprefix tailTrace_932106
  have hstable : (prefixWord ++ tailWord_932106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932106).length < 2 ^ (prefixWord ++ tailWord_932106).sum := by decide
  have hdescent : baseEnd_932106 < baseStart_932106 := by decide
  rcases family_descends (prefixWord ++ tailWord_932106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932149 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_932149 : Nat := 118140960795 + 932149 * 2 ^ 59
def prefixEnd_932149 : Nat := 4983230072969 + 3 ^ 40 * 932149 * 2
def baseEnd_932149 : Nat := 319093652405319130967087

theorem tailTrace_932149 : CollatzResearch.WordTrace tailWord_932149 prefixEnd_932149 319093652405319130967087 := by
  unfold tailWord_932149
  simp only [CollatzResearch.WordTrace]
  refine ⟨33998267099990846219879501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22665511399993897479919667 33998267099990846219879501)
  ·
    refine ⟨12749350162496567332454813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33998267099990846219879501 12749350162496567332454813)
    ·
      refine ⟨4781006310936212749670555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12749350162496567332454813 4781006310936212749670555)
      ·
        refine ⟨7171509466404319124505833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4781006310936212749670555 7171509466404319124505833)
        ·
          refine ⟨5378632099803239343379375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7171509466404319124505833 5378632099803239343379375)
          ·
            refine ⟨8067948149704859015069063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378632099803239343379375 8067948149704859015069063)
            ·
              refine ⟨12101922224557288522603595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8067948149704859015069063 12101922224557288522603595)
              ·
                refine ⟨18152883336835932783905393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12101922224557288522603595 18152883336835932783905393)
                ·
                  refine ⟨13614662502626949587929045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18152883336835932783905393 13614662502626949587929045)
                  ·
                    refine ⟨319093652405319130967087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13614662502626949587929045 319093652405319130967087)
                    ·
                      rfl

theorem cell22_932149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_932149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932149 prefixEnd_932149 := by exact prefixLift 932149
  have htrace : WordTrace (prefixWord ++ tailWord_932149) baseStart_932149 baseEnd_932149 := by
    simpa [prefixWord, tailWord_932149, baseEnd_932149] using wordTrace_append hprefix tailTrace_932149
  have hstable : (prefixWord ++ tailWord_932149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932149).length < 2 ^ (prefixWord ++ tailWord_932149).sum := by decide
  have hdescent : baseEnd_932149 < baseStart_932149 := by decide
  rcases family_descends (prefixWord ++ tailWord_932149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932196 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 5]
def baseStart_932196 : Nat := 118140960795 + 932196 * 2 ^ 59
def prefixEnd_932196 : Nat := 4983230072969 + 3 ^ 40 * 932196 * 2
def baseEnd_932196 : Nat := 106369913821942225013981

theorem tailTrace_932196 : CollatzResearch.WordTrace tailWord_932196 prefixEnd_932196 106369913821942225013981 := by
  unfold tailWord_932196
  simp only [CollatzResearch.WordTrace]
  refine ⟨16999990665410286623420221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22666654220547048831226961 16999990665410286623420221)
  ·
    refine ⟨6374996499528857483782583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16999990665410286623420221 6374996499528857483782583)
    ·
      refine ⟨9562494749293286225673875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6374996499528857483782583 9562494749293286225673875)
      ·
        refine ⟨14343742123939929338510813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9562494749293286225673875 14343742123939929338510813)
        ·
          refine ⟨5378903296477473501941555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14343742123939929338510813 5378903296477473501941555)
          ·
            refine ⟨8068354944716210252912333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378903296477473501941555 8068354944716210252912333)
            ·
              refine ⟨3025633104268578844842125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8068354944716210252912333 3025633104268578844842125)
              ·
                refine ⟨1134612414100717066815797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3025633104268578844842125 1134612414100717066815797)
                ·
                  refine ⟨106369913821942225013981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1134612414100717066815797 106369913821942225013981)
                  ·
                    rfl

theorem cell22_932196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_932196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932196 prefixEnd_932196 := by exact prefixLift 932196
  have htrace : WordTrace (prefixWord ++ tailWord_932196) baseStart_932196 baseEnd_932196 := by
    simpa [prefixWord, tailWord_932196, baseEnd_932196] using wordTrace_append hprefix tailTrace_932196
  have hstable : (prefixWord ++ tailWord_932196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932196).length < 2 ^ (prefixWord ++ tailWord_932196).sum := by decide
  have hdescent : baseEnd_932196 < baseStart_932196 := by decide
  rcases family_descends (prefixWord ++ tailWord_932196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932256 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_932256 : Nat := 118140960795 + 932256 * 2 ^ 59
def prefixEnd_932256 : Nat := 4983230072969 + 3 ^ 40 * 932256 * 2
def baseEnd_932256 : Nat := 319130280692006518541759

theorem tailTrace_932256 : CollatzResearch.WordTrace tailWord_932256 prefixEnd_932256 319130280692006518541759 := by
  unfold tailWord_932256
  simp only [CollatzResearch.WordTrace]
  refine ⟨17001084855301601747012311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22668113140402135662683081 17001084855301601747012311)
  ·
    refine ⟨25501627282952402620518467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17001084855301601747012311 25501627282952402620518467)
    ·
      refine ⟨38252440924428603930777701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25501627282952402620518467 38252440924428603930777701)
      ·
        refine ⟨7172332673330363237020819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38252440924428603930777701 7172332673330363237020819)
        ·
          refine ⟨10758499009995544855531229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7172332673330363237020819 10758499009995544855531229)
          ·
            refine ⟨4034437128748329320824211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10758499009995544855531229 4034437128748329320824211)
            ·
              refine ⟨6051655693122493981236317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034437128748329320824211 6051655693122493981236317)
              ·
                refine ⟨2269370884920935242963619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6051655693122493981236317 2269370884920935242963619)
                ·
                  refine ⟨3404056327381402864445429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269370884920935242963619 3404056327381402864445429)
                  ·
                    refine ⟨319130280692006518541759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3404056327381402864445429 319130280692006518541759)
                    ·
                      rfl

theorem cell22_932256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_932256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932256 prefixEnd_932256 := by exact prefixLift 932256
  have htrace : WordTrace (prefixWord ++ tailWord_932256) baseStart_932256 baseEnd_932256 := by
    simpa [prefixWord, tailWord_932256, baseEnd_932256] using wordTrace_append hprefix tailTrace_932256
  have hstable : (prefixWord ++ tailWord_932256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932256).length < 2 ^ (prefixWord ++ tailWord_932256).sum := by decide
  have hdescent : baseEnd_932256 < baseStart_932256 := by decide
  rcases family_descends (prefixWord ++ tailWord_932256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932277 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 1, 4]
def baseStart_932277 : Nat := 118140960795 + 932277 * 2 ^ 59
def prefixEnd_932277 : Nat := 4983230072969 + 3 ^ 40 * 932277 * 2
def baseEnd_932277 : Nat := 319137469421169463766695

theorem tailTrace_932277 : CollatzResearch.WordTrace tailWord_932277 prefixEnd_932277 319137469421169463766695 := by
  unfold tailWord_932277
  simp only [CollatzResearch.WordTrace]
  refine ⟨34002935643527124080539085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22668623762351416053692723 34002935643527124080539085)
  ·
    refine ⟨12751100866322671530202157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34002935643527124080539085 12751100866322671530202157)
    ·
      refine ⟨4781662824871001823825809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12751100866322671530202157 4781662824871001823825809)
      ·
        refine ⟨3586247118653251367869357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4781662824871001823825809 3586247118653251367869357)
        ·
          refine ⟨1344842669494969262951009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3586247118653251367869357 1344842669494969262951009)
          ·
            refine ⟨1008632002121226947213257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344842669494969262951009 1008632002121226947213257)
            ·
              refine ⟨756474001590920210409943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008632002121226947213257 756474001590920210409943)
              ·
                refine ⟨1134711002386380315614915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756474001590920210409943 1134711002386380315614915)
                ·
                  refine ⟨1702066503579570473422373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134711002386380315614915 1702066503579570473422373)
                  ·
                    refine ⟨319137469421169463766695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1702066503579570473422373 319137469421169463766695)
                    ·
                      rfl

theorem cell22_932277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_932277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932277 prefixEnd_932277 := by exact prefixLift 932277
  have htrace : WordTrace (prefixWord ++ tailWord_932277) baseStart_932277 baseEnd_932277 := by
    simpa [prefixWord, tailWord_932277, baseEnd_932277] using wordTrace_append hprefix tailTrace_932277
  have hstable : (prefixWord ++ tailWord_932277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932277).length < 2 ^ (prefixWord ++ tailWord_932277).sum := by decide
  have hdescent : baseEnd_932277 < baseStart_932277 := by decide
  rcases family_descends (prefixWord ++ tailWord_932277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932346 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_932346 : Nat := 118140960795 + 932346 * 2 ^ 59
def prefixEnd_932346 : Nat := 4983230072969 + 3 ^ 40 * 932346 * 2
def baseEnd_932346 : Nat := 319161089531276283791483

theorem tailTrace_932346 : CollatzResearch.WordTrace tailWord_932346 prefixEnd_932346 319161089531276283791483 := by
  unfold tailWord_932346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501363070069287216200223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22670301520184765909867261 8501363070069287216200223)
  ·
    refine ⟨12752044605103930824300335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8501363070069287216200223 12752044605103930824300335)
    ·
      refine ⟨19128066907655896236450503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12752044605103930824300335 19128066907655896236450503)
      ·
        refine ⟨28692100361483844354675755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19128066907655896236450503 28692100361483844354675755)
        ·
          refine ⟨43038150542225766532013633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28692100361483844354675755 43038150542225766532013633)
          ·
            refine ⟨32278612906669324899010225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43038150542225766532013633 32278612906669324899010225)
            ·
              refine ⟨24208959680001993674257669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32278612906669324899010225 24208959680001993674257669)
              ·
                refine ⟨4539179940000373813923313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24208959680001993674257669 4539179940000373813923313)
                ·
                  refine ⟨3404384955000280360442485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4539179940000373813923313 3404384955000280360442485)
                  ·
                    refine ⟨319161089531276283791483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3404384955000280360442485 319161089531276283791483)
                    ·
                      rfl

theorem cell22_932346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_932346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932346 prefixEnd_932346 := by exact prefixLift 932346
  have htrace : WordTrace (prefixWord ++ tailWord_932346) baseStart_932346 baseEnd_932346 := by
    simpa [prefixWord, tailWord_932346, baseEnd_932346] using wordTrace_append hprefix tailTrace_932346
  have hstable : (prefixWord ++ tailWord_932346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932346).length < 2 ^ (prefixWord ++ tailWord_932346).sum := by decide
  have hdescent : baseEnd_932346 < baseStart_932346 := by decide
  rcases family_descends (prefixWord ++ tailWord_932346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932358 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_932358 : Nat := 118140960795 + 932358 * 2 ^ 59
def prefixEnd_932358 : Nat := 4983230072969 + 3 ^ 40 * 932358 * 2
def baseEnd_932358 : Nat := 319165197376512252491447

theorem tailTrace_932358 : CollatzResearch.WordTrace tailWord_932358 prefixEnd_932358 319165197376512252491447 := by
  unfold tailWord_932358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1062684061132302341069929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22670593304155783276158485 1062684061132302341069929)
  ·
    refine ⟨797013045849226755802447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1062684061132302341069929 797013045849226755802447)
    ·
      refine ⟨1195519568773840133703671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 797013045849226755802447 1195519568773840133703671)
      ·
        refine ⟨1793279353160760200555507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195519568773840133703671 1793279353160760200555507)
        ·
          refine ⟨2689919029741140300833261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793279353160760200555507 2689919029741140300833261)
          ·
            refine ⟨1008719636152927612812473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2689919029741140300833261 1008719636152927612812473)
            ·
              refine ⟨756539727114695709609355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008719636152927612812473 756539727114695709609355)
              ·
                refine ⟨1134809590672043564414033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756539727114695709609355 1134809590672043564414033)
                ·
                  refine ⟨851107193004032673310525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1134809590672043564414033 851107193004032673310525)
                  ·
                    refine ⟨319165197376512252491447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 851107193004032673310525 319165197376512252491447)
                    ·
                      rfl

theorem cell22_932358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_932358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932358 prefixEnd_932358 := by exact prefixLift 932358
  have htrace : WordTrace (prefixWord ++ tailWord_932358) baseStart_932358 baseEnd_932358 := by
    simpa [prefixWord, tailWord_932358, baseEnd_932358] using wordTrace_append hprefix tailTrace_932358
  have hstable : (prefixWord ++ tailWord_932358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932358).length < 2 ^ (prefixWord ++ tailWord_932358).sum := by decide
  have hdescent : baseEnd_932358 < baseStart_932358 := by decide
  rcases family_descends (prefixWord ++ tailWord_932358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932410 : List Nat := [3, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_932410 : Nat := 118140960795 + 932410 * 2 ^ 59
def prefixEnd_932410 : Nat := 4983230072969 + 3 ^ 40 * 932410 * 2
def baseEnd_932410 : Nat := 106394332679733816730429

theorem tailTrace_932410 : CollatzResearch.WordTrace tailWord_932410 prefixEnd_932410 106394332679733816730429 := by
  unfold tailWord_932410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501946638011321948782671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22671857701363525196753789 8501946638011321948782671)
  ·
    refine ⟨12752919957016982923174007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8501946638011321948782671 12752919957016982923174007)
    ·
      refine ⟨19129379935525474384761011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12752919957016982923174007 19129379935525474384761011)
      ·
        refine ⟨28694069903288211577141517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19129379935525474384761011 28694069903288211577141517)
        ·
          refine ⟨10760276213733079341428069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28694069903288211577141517 10760276213733079341428069)
          ·
            refine ⟨2017551790074952376517763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10760276213733079341428069 2017551790074952376517763)
            ·
              refine ⟨3026327685112428564776645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017551790074952376517763 3026327685112428564776645)
              ·
                refine ⟨567436440958580355895621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3026327685112428564776645 567436440958580355895621)
                ·
                  refine ⟨106394332679733816730429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567436440958580355895621 106394332679733816730429)
                  ·
                    rfl

theorem cell22_932410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_932410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932410 prefixEnd_932410 := by exact prefixLift 932410
  have htrace : WordTrace (prefixWord ++ tailWord_932410) baseStart_932410 baseEnd_932410 := by
    simpa [prefixWord, tailWord_932410, baseEnd_932410] using wordTrace_append hprefix tailTrace_932410
  have hstable : (prefixWord ++ tailWord_932410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932410).length < 2 ^ (prefixWord ++ tailWord_932410).sum := by decide
  have hdescent : baseEnd_932410 < baseStart_932410 := by decide
  rcases family_descends (prefixWord ++ tailWord_932410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932446 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_932446 : Nat := 118140960795 + 932446 * 2 ^ 59
def prefixEnd_932446 : Nat := 4983230072969 + 3 ^ 40 * 932446 * 2
def baseEnd_932446 : Nat := 319195321574909356291177

theorem tailTrace_932446 : CollatzResearch.WordTrace tailWord_932446 prefixEnd_932446 319195321574909356291177 := by
  unfold tailWord_932446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4251137447489358242930149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22672733053276577295627461 4251137447489358242930149)
  ·
    refine ⟨797088271404254670549403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4251137447489358242930149 797088271404254670549403)
    ·
      refine ⟨1195632407106382005824105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 797088271404254670549403 1195632407106382005824105)
      ·
        refine ⟨896724305329786504368079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1195632407106382005824105 896724305329786504368079)
        ·
          refine ⟨1345086457994679756552119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896724305329786504368079 1345086457994679756552119)
          ·
            refine ⟨2017629686992019634828179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345086457994679756552119 2017629686992019634828179)
            ·
              refine ⟨3026444530488029452242269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017629686992019634828179 3026444530488029452242269)
              ·
                refine ⟨1134916698933011044590851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3026444530488029452242269 1134916698933011044590851)
                ·
                  refine ⟨1702375048399516566886277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134916698933011044590851 1702375048399516566886277)
                  ·
                    refine ⟨319195321574909356291177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1702375048399516566886277 319195321574909356291177)
                    ·
                      rfl

theorem cell22_932446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_932446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932446 prefixEnd_932446 := by exact prefixLift 932446
  have htrace : WordTrace (prefixWord ++ tailWord_932446) baseStart_932446 baseEnd_932446 := by
    simpa [prefixWord, tailWord_932446, baseEnd_932446] using wordTrace_append hprefix tailTrace_932446
  have hstable : (prefixWord ++ tailWord_932446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932446).length < 2 ^ (prefixWord ++ tailWord_932446).sum := by decide
  have hdescent : baseEnd_932446 < baseStart_932446 := by decide
  rcases family_descends (prefixWord ++ tailWord_932446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932483 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 5]
def baseStart_932483 : Nat := 118140960795 + 932483 * 2 ^ 59
def prefixEnd_932483 : Nat := 4983230072969 + 3 ^ 40 * 932483 * 2
def baseEnd_932483 : Nat := 106402662477017864372021

theorem tailTrace_932483 : CollatzResearch.WordTrace tailWord_932483 prefixEnd_932483 106402662477017864372021 := by
  unfold tailWord_932483
  simp only [CollatzResearch.WordTrace]
  refine ⟨34010449080780821262538103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22673632720520547508358735 34010449080780821262538103)
  ·
    refine ⟨51015673621171231893807155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34010449080780821262538103 51015673621171231893807155)
    ·
      refine ⟨76523510431756847840710733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51015673621171231893807155 76523510431756847840710733)
      ·
        refine ⟨28696316411908817940266525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76523510431756847840710733 28696316411908817940266525)
        ·
          refine ⟨10761118654465806727599947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28696316411908817940266525 10761118654465806727599947)
          ·
            refine ⟨16141677981698710091399921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10761118654465806727599947 16141677981698710091399921)
            ·
              refine ⟨12106258486274032568549941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16141677981698710091399921 12106258486274032568549941)
              ·
                refine ⟨1134961733088190553301557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12106258486274032568549941 1134961733088190553301557)
                ·
                  refine ⟨106402662477017864372021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1134961733088190553301557 106402662477017864372021)
                  ·
                    rfl

theorem cell22_932483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 5].length) (baseStart_932483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932483 prefixEnd_932483 := by exact prefixLift 932483
  have htrace : WordTrace (prefixWord ++ tailWord_932483) baseStart_932483 baseEnd_932483 := by
    simpa [prefixWord, tailWord_932483, baseEnd_932483] using wordTrace_append hprefix tailTrace_932483
  have hstable : (prefixWord ++ tailWord_932483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932483).length < 2 ^ (prefixWord ++ tailWord_932483).sum := by decide
  have hdescent : baseEnd_932483 < baseStart_932483 := by decide
  rcases family_descends (prefixWord ++ tailWord_932483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932500 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 7]
def baseStart_932500 : Nat := 118140960795 + 932500 * 2 ^ 59
def prefixEnd_932500 : Nat := 4983230072969 + 3 ^ 40 * 932500 * 2
def baseEnd_932500 : Nat := 106404602292823738480337

theorem tailTrace_932500 : CollatzResearch.WordTrace tailWord_932500 prefixEnd_932500 106404602292823738480337 := by
  unfold tailWord_932500
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005534560859616582953477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22674046081146155443937969 17005534560859616582953477)
  ·
    refine ⟨3188537730161178109303777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17005534560859616582953477 3188537730161178109303777)
    ·
      refine ⟨2391403297620883581977833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3188537730161178109303777 2391403297620883581977833)
      ·
        refine ⟨1793552473215662686483375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2391403297620883581977833 1793552473215662686483375)
        ·
          refine ⟨2690328709823494029725063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793552473215662686483375 2690328709823494029725063)
          ·
            refine ⟨4035493064735241044587595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690328709823494029725063 4035493064735241044587595)
            ·
              refine ⟨6053239597102861566881393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035493064735241044587595 6053239597102861566881393)
              ·
                refine ⟨4539929697827146175161045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6053239597102861566881393 4539929697827146175161045)
                ·
                  refine ⟨106404602292823738480337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4539929697827146175161045 106404602292823738480337)
                  ·
                    rfl

theorem cell22_932500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_932500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932500 prefixEnd_932500 := by exact prefixLift 932500
  have htrace : WordTrace (prefixWord ++ tailWord_932500) baseStart_932500 baseEnd_932500 := by
    simpa [prefixWord, tailWord_932500, baseEnd_932500] using wordTrace_append hprefix tailTrace_932500
  have hstable : (prefixWord ++ tailWord_932500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932500).length < 2 ^ (prefixWord ++ tailWord_932500).sum := by decide
  have hdescent : baseEnd_932500 < baseStart_932500 := by decide
  rcases family_descends (prefixWord ++ tailWord_932500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932534 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_932534 : Nat := 118140960795 + 932534 * 2 ^ 59
def prefixEnd_932534 : Nat := 4983230072969 + 3 ^ 40 * 932534 * 2
def baseEnd_932534 : Nat := 106408481924435486696969

theorem tailTrace_932534 : CollatzResearch.WordTrace tailWord_932534 prefixEnd_932534 106408481924435486696969 := by
  unfold tailWord_932534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2125769325224753560790291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22674872802397371315096437 2125769325224753560790291)
  ·
    refine ⟨3188653987837130341185437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2125769325224753560790291 3188653987837130341185437)
    ·
      refine ⟨1195745245438923877944539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3188653987837130341185437 1195745245438923877944539)
      ·
        refine ⟨1793617868158385816916809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195745245438923877944539 1793617868158385816916809)
        ·
          refine ⟨1345213401118789362687607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1793617868158385816916809 1345213401118789362687607)
          ·
            refine ⟨2017820101678184044031411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345213401118789362687607 2017820101678184044031411)
            ·
              refine ⟨3026730152517276066047117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017820101678184044031411 3026730152517276066047117)
              ·
                refine ⟨1135023807193978524767669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3026730152517276066047117 1135023807193978524767669)
                ·
                  refine ⟨106408481924435486696969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1135023807193978524767669 106408481924435486696969)
                  ·
                    rfl

theorem cell22_932534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_932534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932534 prefixEnd_932534 := by exact prefixLift 932534
  have htrace : WordTrace (prefixWord ++ tailWord_932534) baseStart_932534 baseEnd_932534 := by
    simpa [prefixWord, tailWord_932534, baseEnd_932534] using wordTrace_append hprefix tailTrace_932534
  have hstable : (prefixWord ++ tailWord_932534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932534).length < 2 ^ (prefixWord ++ tailWord_932534).sum := by decide
  have hdescent : baseEnd_932534 < baseStart_932534 := by decide
  rcases family_descends (prefixWord ++ tailWord_932534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932573 : List Nat := [1, 4, 3, 14]
def baseStart_932573 : Nat := 118140960795 + 932573 * 2 ^ 59
def prefixEnd_932573 : Nat := 4983230072969 + 3 ^ 40 * 932573 * 2
def baseEnd_932573 : Nat := 437913300782336568403

theorem tailTrace_932573 : CollatzResearch.WordTrace tailWord_932573 prefixEnd_932573 437913300782336568403 := by
  unfold tailWord_932573
  simp only [CollatzResearch.WordTrace]
  refine ⟨34013731650454766633314373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22675821100303177755542915 34013731650454766633314373)
  ·
    refine ⟨6377574684460268743746445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34013731650454766633314373 6377574684460268743746445)
    ·
      refine ⟨2391590506672600778904917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6377574684460268743746445 2391590506672600778904917)
      ·
        refine ⟨437913300782336568403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 2391590506672600778904917 437913300782336568403)
        ·
          rfl

theorem cell22_932573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 14].length) (baseStart_932573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932573 prefixEnd_932573 := by exact prefixLift 932573
  have htrace : WordTrace (prefixWord ++ tailWord_932573) baseStart_932573 baseEnd_932573 := by
    simpa [prefixWord, tailWord_932573, baseEnd_932573] using wordTrace_append hprefix tailTrace_932573
  have hstable : (prefixWord ++ tailWord_932573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932573).length < 2 ^ (prefixWord ++ tailWord_932573).sum := by decide
  have hdescent : baseEnd_932573 < baseStart_932573 := by decide
  rcases family_descends (prefixWord ++ tailWord_932573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932575 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 2, 4]
def baseStart_932575 : Nat := 118140960795 + 932575 * 2 ^ 59
def prefixEnd_932575 : Nat := 4983230072969 + 3 ^ 40 * 932575 * 2
def baseEnd_932575 : Nat := 319239480911196019815781

theorem tailTrace_932575 : CollatzResearch.WordTrace tailWord_932575 prefixEnd_932575 319239480911196019815781 := by
  unfold tailWord_932575
  simp only [CollatzResearch.WordTrace]
  refine ⟨34013804596447520974887179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22675869730965013983258119 34013804596447520974887179)
  ·
    refine ⟨51020706894671281462330769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34013804596447520974887179 51020706894671281462330769)
    ·
      refine ⟨38265530171003461096748077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51020706894671281462330769 38265530171003461096748077)
      ·
        refine ⟨14349573814126297911280529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38265530171003461096748077 14349573814126297911280529)
        ·
          refine ⟨10762180360594723433460397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14349573814126297911280529 10762180360594723433460397)
          ·
            refine ⟨4035817635223021287547649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10762180360594723433460397 4035817635223021287547649)
            ·
              refine ⟨3026863226417265965660737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4035817635223021287547649 3026863226417265965660737)
              ·
                refine ⟨2270147419812949474245553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026863226417265965660737 2270147419812949474245553)
                ·
                  refine ⟨1702610564859712105684165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2270147419812949474245553 1702610564859712105684165)
                  ·
                    refine ⟨319239480911196019815781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1702610564859712105684165 319239480911196019815781)
                    ·
                      rfl

theorem cell22_932575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_932575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932575 prefixEnd_932575 := by exact prefixLift 932575
  have htrace : WordTrace (prefixWord ++ tailWord_932575) baseStart_932575 baseEnd_932575 := by
    simpa [prefixWord, tailWord_932575, baseEnd_932575] using wordTrace_append hprefix tailTrace_932575
  have hstable : (prefixWord ++ tailWord_932575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932575).length < 2 ^ (prefixWord ++ tailWord_932575).sum := by decide
  have hdescent : baseEnd_932575 < baseStart_932575 := by decide
  rcases family_descends (prefixWord ++ tailWord_932575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932577 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 2, 3]
def baseStart_932577 : Nat := 118140960795 + 932577 * 2 ^ 59
def prefixEnd_932577 : Nat := 4983230072969 + 3 ^ 40 * 932577 * 2
def baseEnd_932577 : Nat := 319240165552068681265775

theorem tailTrace_932577 : CollatzResearch.WordTrace tailWord_932577 prefixEnd_932577 319240165552068681265775 := by
  unfold tailWord_932577
  simp only [CollatzResearch.WordTrace]
  refine ⟨34013877542440275316459985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22675918361626850210973323 34013877542440275316459985)
  ·
    refine ⟨25510408156830206487344989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34013877542440275316459985 25510408156830206487344989)
    ·
      refine ⟨9566403058811327432754371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25510408156830206487344989 9566403058811327432754371)
      ·
        refine ⟨14349604588216991149131557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9566403058811327432754371 14349604588216991149131557)
        ·
          refine ⟨2690550860290685840462167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14349604588216991149131557 2690550860290685840462167)
          ·
            refine ⟨4035826290436028760693251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690550860290685840462167 4035826290436028760693251)
            ·
              refine ⟨6053739435654043141039877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035826290436028760693251 6053739435654043141039877)
              ·
                refine ⟨1135076144185133088944977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6053739435654043141039877 1135076144185133088944977)
                ·
                  refine ⟨851307108138849816708733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1135076144185133088944977 851307108138849816708733)
                  ·
                    refine ⟨319240165552068681265775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 851307108138849816708733 319240165552068681265775)
                    ·
                      rfl

theorem cell22_932577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_932577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932577 prefixEnd_932577 := by exact prefixLift 932577
  have htrace : WordTrace (prefixWord ++ tailWord_932577) baseStart_932577 baseEnd_932577 := by
    simpa [prefixWord, tailWord_932577, baseEnd_932577] using wordTrace_append hprefix tailTrace_932577
  have hstable : (prefixWord ++ tailWord_932577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932577).length < 2 ^ (prefixWord ++ tailWord_932577).sum := by decide
  have hdescent : baseEnd_932577 < baseStart_932577 := by decide
  rcases family_descends (prefixWord ++ tailWord_932577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932579 : List Nat := [1, 1, 1, 7, 1, 1, 4, 2, 4]
def baseStart_932579 : Nat := 118140960795 + 932579 * 2 ^ 59
def prefixEnd_932579 : Nat := 4983230072969 + 3 ^ 40 * 932579 * 2
def baseEnd_932579 : Nat := 106413616730980447571923

theorem tailTrace_932579 : CollatzResearch.WordTrace tailWord_932579 prefixEnd_932579 106413616730980447571923 := by
  unfold tailWord_932579
  simp only [CollatzResearch.WordTrace]
  refine ⟨34013950488433029658032791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22675966992288686438688527 34013950488433029658032791)
  ·
    refine ⟨51020925732649544487049187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34013950488433029658032791 51020925732649544487049187)
    ·
      refine ⟨76531388598974316730573781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51020925732649544487049187 76531388598974316730573781)
      ·
        refine ⟨1793704420288460548372823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 76531388598974316730573781 1793704420288460548372823)
        ·
          refine ⟨2690556630432690822559235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793704420288460548372823 2690556630432690822559235)
          ·
            refine ⟨4035834945649036233838853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690556630432690822559235 4035834945649036233838853)
            ·
              refine ⟨756719052309194293844785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4035834945649036233838853 756719052309194293844785)
              ·
                refine ⟨567539289231895720383589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756719052309194293844785 567539289231895720383589)
                ·
                  refine ⟨106413616730980447571923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567539289231895720383589 106413616730980447571923)
                  ·
                    rfl

theorem cell22_932579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 4].length) (baseStart_932579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932579 prefixEnd_932579 := by exact prefixLift 932579
  have htrace : WordTrace (prefixWord ++ tailWord_932579) baseStart_932579 baseEnd_932579 := by
    simpa [prefixWord, tailWord_932579, baseEnd_932579] using wordTrace_append hprefix tailTrace_932579
  have hstable : (prefixWord ++ tailWord_932579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932579).length < 2 ^ (prefixWord ++ tailWord_932579).sum := by decide
  have hdescent : baseEnd_932579 < baseStart_932579 := by decide
  rcases family_descends (prefixWord ++ tailWord_932579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932588 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_932588 : Nat := 118140960795 + 932588 * 2 ^ 59
def prefixEnd_932588 : Nat := 4983230072969 + 3 ^ 40 * 932588 * 2
def baseEnd_932588 : Nat := 319243931076868319240741

theorem tailTrace_932588 : CollatzResearch.WordTrace tailWord_932588 prefixEnd_932588 319243931076868319240741 := by
  unfold tailWord_932588
  simp only [CollatzResearch.WordTrace]
  refine ⟨17007139372700212097555209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22676185830266949463406945 17007139372700212097555209)
  ·
    refine ⟨12755354529525159073166407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17007139372700212097555209 12755354529525159073166407)
    ·
      refine ⟨19133031794287738609749611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12755354529525159073166407 19133031794287738609749611)
      ·
        refine ⟨28699547691431607914624417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19133031794287738609749611 28699547691431607914624417)
        ·
          refine ⟨21524660768573705935968313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28699547691431607914624417 21524660768573705935968313)
          ·
            refine ⟨16143495576430279451976235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21524660768573705935968313 16143495576430279451976235)
            ·
              refine ⟨24215243364645419177964353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16143495576430279451976235 24215243364645419177964353)
              ·
                refine ⟨18161432523484064383473265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24215243364645419177964353 18161432523484064383473265)
                ·
                  refine ⟨13621074392613048287604949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18161432523484064383473265 13621074392613048287604949)
                  ·
                    refine ⟨319243931076868319240741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13621074392613048287604949 319243931076868319240741)
                    ·
                      rfl

theorem cell22_932588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_932588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932588 prefixEnd_932588 := by exact prefixLift 932588
  have htrace : WordTrace (prefixWord ++ tailWord_932588) baseStart_932588 baseEnd_932588 := by
    simpa [prefixWord, tailWord_932588, baseEnd_932588] using wordTrace_append hprefix tailTrace_932588
  have hstable : (prefixWord ++ tailWord_932588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932588).length < 2 ^ (prefixWord ++ tailWord_932588).sum := by decide
  have hdescent : baseEnd_932588 < baseStart_932588 := by decide
  rcases family_descends (prefixWord ++ tailWord_932588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932590 : List Nat := [4, 1, 2, 1, 1, 3, 3, 7]
def baseStart_932590 : Nat := 118140960795 + 932590 * 2 ^ 59
def prefixEnd_932590 : Nat := 4983230072969 + 3 ^ 40 * 932590 * 2
def baseEnd_932590 : Nat := 35471623968637886743415

theorem tailTrace_932590 : CollatzResearch.WordTrace tailWord_932590 prefixEnd_932590 35471623968637886743415 := by
  unfold tailWord_932590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4251793961424147317085403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22676234460928785691122149 4251793961424147317085403)
  ·
    refine ⟨6377690942136220975628105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4251793961424147317085403 6377690942136220975628105)
    ·
      refine ⟨4783268206602165731721079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6377690942136220975628105 4783268206602165731721079)
      ·
        refine ⟨7174902309903248597581619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4783268206602165731721079 7174902309903248597581619)
        ·
          refine ⟨10762353464854872896372429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174902309903248597581619 10762353464854872896372429)
          ·
            refine ⟨4035882549320577336139661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10762353464854872896372429 4035882549320577336139661)
            ·
              refine ⟨1513455955995216501052373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4035882549320577336139661 1513455955995216501052373)
              ·
                refine ⟨35471623968637886743415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1513455955995216501052373 35471623968637886743415)
                ·
                  rfl

theorem cell22_932590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_932590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932590 prefixEnd_932590 := by exact prefixLift 932590
  have htrace : WordTrace (prefixWord ++ tailWord_932590) baseStart_932590 baseEnd_932590 := by
    simpa [prefixWord, tailWord_932590, baseEnd_932590] using wordTrace_append hprefix tailTrace_932590
  have hstable : (prefixWord ++ tailWord_932590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932590).length < 2 ^ (prefixWord ++ tailWord_932590).sum := by decide
  have hdescent : baseEnd_932590 < baseStart_932590 := by decide
  rcases family_descends (prefixWord ++ tailWord_932590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932639 : List Nat := [1, 1, 2, 4, 2, 2, 2, 4, 1, 3]
def baseStart_932639 : Nat := 118140960795 + 932639 * 2 ^ 59
def prefixEnd_932639 : Nat := 4983230072969 + 3 ^ 40 * 932639 * 2
def baseEnd_932639 : Nat := 319261389419121186215585

theorem tailTrace_932639 : CollatzResearch.WordTrace tailWord_932639 prefixEnd_932639 319261389419121186215585 := by
  unfold tailWord_932639
  simp only [CollatzResearch.WordTrace]
  refine ⟨34016138868215659905216971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22677425912143773270144647 34016138868215659905216971)
  ·
    refine ⟨51024208302323489857825457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34016138868215659905216971 51024208302323489857825457)
    ·
      refine ⟨38268156226742617393369093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51024208302323489857825457 38268156226742617393369093)
      ·
        refine ⟨7175279292514240761256705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38268156226742617393369093 7175279292514240761256705)
        ·
          refine ⟨5381459469385680570942529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7175279292514240761256705 5381459469385680570942529)
          ·
            refine ⟨4036094602039260428206897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5381459469385680570942529 4036094602039260428206897)
            ·
              refine ⟨3027070951529445321155173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4036094602039260428206897 3027070951529445321155173)
              ·
                refine ⟨567575803411770997716595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3027070951529445321155173 567575803411770997716595)
                ·
                  refine ⟨851363705117656496574893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567575803411770997716595 851363705117656496574893)
                  ·
                    refine ⟨319261389419121186215585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 851363705117656496574893 319261389419121186215585)
                    ·
                      rfl

theorem cell22_932639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 3].length) (baseStart_932639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932639 prefixEnd_932639 := by exact prefixLift 932639
  have htrace : WordTrace (prefixWord ++ tailWord_932639) baseStart_932639 baseEnd_932639 := by
    simpa [prefixWord, tailWord_932639, baseEnd_932639] using wordTrace_append hprefix tailTrace_932639
  have hstable : (prefixWord ++ tailWord_932639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932639).length < 2 ^ (prefixWord ++ tailWord_932639).sum := by decide
  have hdescent : baseEnd_932639 < baseStart_932639 := by decide
  rcases family_descends (prefixWord ++ tailWord_932639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932652 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 5]
def baseStart_932652 : Nat := 118140960795 + 932652 * 2 ^ 59
def prefixEnd_932652 : Nat := 4983230072969 + 3 ^ 40 * 932652 * 2
def baseEnd_932652 : Nat := 106421946528264495213515

theorem tailTrace_932652 : CollatzResearch.WordTrace tailWord_932652 prefixEnd_932652 106421946528264495213515 := by
  unfold tailWord_932652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17008306508584281562720105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22677742011445708750293473 17008306508584281562720105)
  ·
    refine ⟨12756229881438211172040079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17008306508584281562720105 12756229881438211172040079)
    ·
      refine ⟨19134344822157316758060119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12756229881438211172040079 19134344822157316758060119)
      ·
        refine ⟨28701517233235975137090179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19134344822157316758060119 28701517233235975137090179)
        ·
          refine ⟨43052275849853962705635269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28701517233235975137090179 43052275849853962705635269)
          ·
            refine ⟨8072301721847618007306613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43052275849853962705635269 8072301721847618007306613)
            ·
              refine ⟨756778286423214188184995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8072301721847618007306613 756778286423214188184995)
              ·
                refine ⟨1135167429634821282277493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756778286423214188184995 1135167429634821282277493)
                ·
                  refine ⟨106421946528264495213515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1135167429634821282277493 106421946528264495213515)
                  ·
                    rfl

theorem cell22_932652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_932652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932652 prefixEnd_932652 := by exact prefixLift 932652
  have htrace : WordTrace (prefixWord ++ tailWord_932652) baseStart_932652 baseEnd_932652 := by
    simpa [prefixWord, tailWord_932652, baseEnd_932652] using wordTrace_append hprefix tailTrace_932652
  have hstable : (prefixWord ++ tailWord_932652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932652).length < 2 ^ (prefixWord ++ tailWord_932652).sum := by decide
  have hdescent : baseEnd_932652 < baseStart_932652 := by decide
  rcases family_descends (prefixWord ++ tailWord_932652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932697 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 6]
def baseStart_932697 : Nat := 118140960795 + 932697 * 2 ^ 59
def prefixEnd_932697 : Nat := 4983230072969 + 3 ^ 40 * 932697 * 2
def baseEnd_932697 : Nat := 106427081334809456088469

theorem tailTrace_932697 : CollatzResearch.WordTrace tailWord_932697 prefixEnd_932697 106427081334809456088469 := by
  unfold tailWord_932697
  simp only [CollatzResearch.WordTrace]
  refine ⟨34018254302005535810828345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22678836201337023873885563 34018254302005535810828345)
  ·
    refine ⟨25513690726504151858121259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34018254302005535810828345 25513690726504151858121259)
    ·
      refine ⟨38270536089756227787181889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25513690726504151858121259 38270536089756227787181889)
      ·
        refine ⟨28702902067317170840386417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38270536089756227787181889 28702902067317170840386417)
        ·
          refine ⟨21527176550487878130289813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28702902067317170840386417 21527176550487878130289813)
          ·
            refine ⟨1009086400804119287357335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21527176550487878130289813 1009086400804119287357335)
            ·
              refine ⟨1513629601206178931036003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009086400804119287357335 1513629601206178931036003)
              ·
                refine ⟨2270444401809268396554005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513629601206178931036003 2270444401809268396554005)
                ·
                  refine ⟨106427081334809456088469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2270444401809268396554005 106427081334809456088469)
                  ·
                    rfl

theorem cell22_932697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_932697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932697 prefixEnd_932697 := by exact prefixLift 932697
  have htrace : WordTrace (prefixWord ++ tailWord_932697) baseStart_932697 baseEnd_932697 := by
    simpa [prefixWord, tailWord_932697, baseEnd_932697] using wordTrace_append hprefix tailTrace_932697
  have hstable : (prefixWord ++ tailWord_932697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932697).length < 2 ^ (prefixWord ++ tailWord_932697).sum := by decide
  have hdescent : baseEnd_932697 < baseStart_932697 := by decide
  rcases family_descends (prefixWord ++ tailWord_932697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932746 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_932746 : Nat := 118140960795 + 932746 * 2 ^ 59
def prefixEnd_932746 : Nat := 4983230072969 + 3 ^ 40 * 932746 * 2
def baseEnd_932746 : Nat := 319298017705808573790257

theorem tailTrace_932746 : CollatzResearch.WordTrace tailWord_932746 prefixEnd_932746 319298017705808573790257 := by
  unfold tailWord_932746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505010369707004294840523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22680027652552011452908061 8505010369707004294840523)
  ·
    refine ⟨12757515554560506442260785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8505010369707004294840523 12757515554560506442260785)
    ·
      refine ⟨9568136665920379831695589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12757515554560506442260785 9568136665920379831695589)
      ·
        refine ⟨1794025624860071218442923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9568136665920379831695589 1794025624860071218442923)
        ·
          refine ⟨2691038437290106827664385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794025624860071218442923 2691038437290106827664385)
          ·
            refine ⟨2018278827967580120748289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2691038437290106827664385 2018278827967580120748289)
            ·
              refine ⟨1513709120975685090561217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2018278827967580120748289 1513709120975685090561217)
              ·
                refine ⟨1135281840731763817920913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513709120975685090561217 1135281840731763817920913)
                ·
                  refine ⟨851461380548822863440685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1135281840731763817920913 851461380548822863440685)
                  ·
                    refine ⟨319298017705808573790257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 851461380548822863440685 319298017705808573790257)
                    ·
                      rfl

theorem cell22_932746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_932746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932746 prefixEnd_932746 := by exact prefixLift 932746
  have htrace : WordTrace (prefixWord ++ tailWord_932746) baseStart_932746 baseEnd_932746 := by
    simpa [prefixWord, tailWord_932746, baseEnd_932746] using wordTrace_append hprefix tailTrace_932746
  have hstable : (prefixWord ++ tailWord_932746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932746).length < 2 ^ (prefixWord ++ tailWord_932746).sum := by decide
  have hdescent : baseEnd_932746 < baseStart_932746 := by decide
  rcases family_descends (prefixWord ++ tailWord_932746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932821 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 5]
def baseStart_932821 : Nat := 118140960795 + 932821 * 2 ^ 59
def prefixEnd_932821 : Nat := 4983230072969 + 3 ^ 40 * 932821 * 2
def baseEnd_932821 : Nat := 106441230579511126055009

theorem tailTrace_932821 : CollatzResearch.WordTrace tailWord_932821 prefixEnd_932821 106441230579511126055009 := by
  unfold tailWord_932821
  simp only [CollatzResearch.WordTrace]
  refine ⟨34022776953556304988342317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22681851302370869992228211 34022776953556304988342317)
  ·
    refine ⟨12758541357583614370628369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34022776953556304988342317 12758541357583614370628369)
    ·
      refine ⟨9568906018187710777971277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12758541357583614370628369 9568906018187710777971277)
      ·
        refine ⟨3588339756820391541739229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9568906018187710777971277 3588339756820391541739229)
        ·
          refine ⟨1345627408807646828152211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3588339756820391541739229 1345627408807646828152211)
          ·
            refine ⟨2018441113211470242228317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345627408807646828152211 2018441113211470242228317)
            ·
              refine ⟨756915417454301340835619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2018441113211470242228317 756915417454301340835619)
              ·
                refine ⟨1135373126181452011253429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756915417454301340835619 1135373126181452011253429)
                ·
                  refine ⟨106441230579511126055009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1135373126181452011253429 106441230579511126055009)
                  ·
                    rfl

theorem cell22_932821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_932821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932821 prefixEnd_932821 := by exact prefixLift 932821
  have htrace : WordTrace (prefixWord ++ tailWord_932821) baseStart_932821 baseEnd_932821 := by
    simpa [prefixWord, tailWord_932821, baseEnd_932821] using wordTrace_append hprefix tailTrace_932821
  have hstable : (prefixWord ++ tailWord_932821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932821).length < 2 ^ (prefixWord ++ tailWord_932821).sum := by decide
  have hdescent : baseEnd_932821 < baseStart_932821 := by decide
  rcases family_descends (prefixWord ++ tailWord_932821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932922 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_932922 : Nat := 118140960795 + 932922 * 2 ^ 59
def prefixEnd_932922 : Nat := 4983230072969 + 3 ^ 40 * 932922 * 2
def baseEnd_932922 : Nat := 106452755367534260463239

theorem tailTrace_932922 : CollatzResearch.WordTrace tailWord_932922 prefixEnd_932922 106452755367534260463239 := by
  unfold tailWord_932922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506615181547599809442255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22684307150793599491846013 8506615181547599809442255)
  ·
    refine ⟨12759922772321399714163383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8506615181547599809442255 12759922772321399714163383)
    ·
      refine ⟨19139884158482099571245075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12759922772321399714163383 19139884158482099571245075)
      ·
        refine ⟨28709826237723149356867613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19139884158482099571245075 28709826237723149356867613)
        ·
          refine ⟨10766184839146181008825355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28709826237723149356867613 10766184839146181008825355)
          ·
            refine ⟨16149277258719271513238033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10766184839146181008825355 16149277258719271513238033)
            ·
              refine ⟨12111957944039453634928525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16149277258719271513238033 12111957944039453634928525)
              ·
                refine ⟨4541984229014795113098197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12111957944039453634928525 4541984229014795113098197)
                ·
                  refine ⟨106452755367534260463239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4541984229014795113098197 106452755367534260463239)
                  ·
                    rfl

theorem cell22_932922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_932922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_932922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_932922 prefixEnd_932922 := by exact prefixLift 932922
  have htrace : WordTrace (prefixWord ++ tailWord_932922) baseStart_932922 baseEnd_932922 := by
    simpa [prefixWord, tailWord_932922, baseEnd_932922] using wordTrace_append hprefix tailTrace_932922
  have hstable : (prefixWord ++ tailWord_932922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932922).length < 2 ^ (prefixWord ++ tailWord_932922).sum := by decide
  have hdescent : baseEnd_932922 < baseStart_932922 := by decide
  rcases family_descends (prefixWord ++ tailWord_932922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933016 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 4, 3]
def baseStart_933016 : Nat := 118140960795 + 933016 * 2 ^ 59
def prefixEnd_933016 : Nat := 4983230072969 + 3 ^ 40 * 933016 * 2
def baseEnd_933016 : Nat := 319390444223617869539429

theorem tailTrace_933016 : CollatzResearch.WordTrace tailWord_933016 prefixEnd_933016 319390444223617869539429 := by
  unfold tailWord_933016
  simp only [CollatzResearch.WordTrace]
  refine ⟨17014944593924926645845451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22686592791899902194460601 17014944593924926645845451)
  ·
    refine ⟨25522416890887389968768177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17014944593924926645845451 25522416890887389968768177)
    ·
      refine ⟨19141812668165542476576133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25522416890887389968768177 19141812668165542476576133)
      ·
        refine ⟨3589089875281039214358025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19141812668165542476576133 3589089875281039214358025)
        ·
          refine ⟨2691817406460779410768519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3589089875281039214358025 2691817406460779410768519)
          ·
            refine ⟨4037726109691169116152779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691817406460779410768519 4037726109691169116152779)
            ·
              refine ⟨6056589164536753674229169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037726109691169116152779 6056589164536753674229169)
              ·
                refine ⟨4542441873402565255671877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056589164536753674229169 4542441873402565255671877)
                ·
                  refine ⟨851707851262980985438477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4542441873402565255671877 851707851262980985438477)
                  ·
                    refine ⟨319390444223617869539429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 851707851262980985438477 319390444223617869539429)
                    ·
                      rfl

theorem cell22_933016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_933016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933016 prefixEnd_933016 := by exact prefixLift 933016
  have htrace : WordTrace (prefixWord ++ tailWord_933016) baseStart_933016 baseEnd_933016 := by
    simpa [prefixWord, tailWord_933016, baseEnd_933016] using wordTrace_append hprefix tailTrace_933016
  have hstable : (prefixWord ++ tailWord_933016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933016).length < 2 ^ (prefixWord ++ tailWord_933016).sum := by decide
  have hdescent : baseEnd_933016 < baseStart_933016 := by decide
  rcases family_descends (prefixWord ++ tailWord_933016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933018 : List Nat := [3, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_933018 : Nat := 118140960795 + 933018 * 2 ^ 59
def prefixEnd_933018 : Nat := 4983230072969 + 3 ^ 40 * 933018 * 2
def baseEnd_933018 : Nat := 106463709621496843663141

theorem tailTrace_933018 : CollatzResearch.WordTrace tailWord_933018 prefixEnd_933018 106463709621496843663141 := by
  unfold tailWord_933018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8507490533460651908315927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22686641422561738422175805 8507490533460651908315927)
  ·
    refine ⟨12761235800190977862473891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8507490533460651908315927 12761235800190977862473891)
    ·
      refine ⟨19141853700286466793710837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12761235800190977862473891 19141853700286466793710837)
      ·
        refine ⟨1794548784401856261910391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19141853700286466793710837 1794548784401856261910391)
        ·
          refine ⟨2691823176602784392865587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794548784401856261910391 2691823176602784392865587)
          ·
            refine ⟨4037734764904176589298381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691823176602784392865587 4037734764904176589298381)
            ·
              refine ⟨1514150536839066220986893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4037734764904176589298381 1514150536839066220986893)
              ·
                refine ⟨567806451314649832870085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1514150536839066220986893 567806451314649832870085)
                ·
                  refine ⟨106463709621496843663141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567806451314649832870085 106463709621496843663141)
                  ·
                    rfl

theorem cell22_933018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_933018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933018 prefixEnd_933018 := by exact prefixLift 933018
  have htrace : WordTrace (prefixWord ++ tailWord_933018) baseStart_933018 baseEnd_933018 := by
    simpa [prefixWord, tailWord_933018, baseEnd_933018] using wordTrace_append hprefix tailTrace_933018
  have hstable : (prefixWord ++ tailWord_933018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933018).length < 2 ^ (prefixWord ++ tailWord_933018).sum := by decide
  have hdescent : baseEnd_933018 < baseStart_933018 := by decide
  rcases family_descends (prefixWord ++ tailWord_933018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933029 : List Nat := [1, 3, 1, 2, 1, 6, 8]
def baseStart_933029 : Nat := 118140960795 + 933029 * 2 ^ 59
def prefixEnd_933029 : Nat := 4983230072969 + 3 ^ 40 * 933029 * 2
def baseEnd_933029 : Nat := 11829440532936672924607

theorem tailTrace_933029 : CollatzResearch.WordTrace tailWord_933029 prefixEnd_933029 11829440532936672924607 := by
  unfold tailWord_933029
  simp only [CollatzResearch.WordTrace]
  refine ⟨34030363336802756511914141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22686908891201837674609427 34030363336802756511914141)
  ·
    refine ⟨12761386251301033691967803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34030363336802756511914141 12761386251301033691967803)
    ·
      refine ⟨19142079376951550537951705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12761386251301033691967803 19142079376951550537951705)
      ·
        refine ⟨14356559532713662903463779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19142079376951550537951705 14356559532713662903463779)
        ·
          refine ⟨21534839299070494355195669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14356559532713662903463779 21534839299070494355195669)
          ·
            refine ⟨1009445592143929422899797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21534839299070494355195669 1009445592143929422899797)
            ·
              refine ⟨11829440532936672924607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1009445592143929422899797 11829440532936672924607)
              ·
                rfl

theorem cell22_933029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 8].length) (baseStart_933029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933029 prefixEnd_933029 := by exact prefixLift 933029
  have htrace : WordTrace (prefixWord ++ tailWord_933029) baseStart_933029 baseEnd_933029 := by
    simpa [prefixWord, tailWord_933029, baseEnd_933029] using wordTrace_append hprefix tailTrace_933029
  have hstable : (prefixWord ++ tailWord_933029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933029).length < 2 ^ (prefixWord ++ tailWord_933029).sum := by decide
  have hdescent : baseEnd_933029 < baseStart_933029 := by decide
  rcases family_descends (prefixWord ++ tailWord_933029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933031 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 4, 4]
def baseStart_933031 : Nat := 118140960795 + 933031 * 2 ^ 59
def prefixEnd_933031 : Nat := 4983230072969 + 3 ^ 40 * 933031 * 2
def baseEnd_933031 : Nat := 319395579030162830414383

theorem tailTrace_933031 : CollatzResearch.WordTrace tailWord_933031 prefixEnd_933031 319395579030162830414383 := by
  unfold tailWord_933031
  simp only [CollatzResearch.WordTrace]
  refine ⟨34030436282795510853486947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22686957521863673902324631 34030436282795510853486947)
  ·
    refine ⟨51045654424193266280230421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34030436282795510853486947 51045654424193266280230421)
    ·
      refine ⟨2392765051134059356885801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51045654424193266280230421 2392765051134059356885801)
      ·
        refine ⟨1794573788350544517664351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2392765051134059356885801 1794573788350544517664351)
        ·
          refine ⟨2691860682525816776496527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794573788350544517664351 2691860682525816776496527)
          ·
            refine ⟨4037791023788725164744791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691860682525816776496527 4037791023788725164744791)
            ·
              refine ⟨6056686535683087747117187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037791023788725164744791 6056686535683087747117187)
              ·
                refine ⟨9085029803524631620675781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056686535683087747117187 9085029803524631620675781)
                ·
                  refine ⟨1703443088160868428876709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9085029803524631620675781 1703443088160868428876709)
                  ·
                    refine ⟨319395579030162830414383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1703443088160868428876709 319395579030162830414383)
                    ·
                      rfl

theorem cell22_933031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_933031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933031 prefixEnd_933031 := by exact prefixLift 933031
  have htrace : WordTrace (prefixWord ++ tailWord_933031) baseStart_933031 baseEnd_933031 := by
    simpa [prefixWord, tailWord_933031, baseEnd_933031] using wordTrace_append hprefix tailTrace_933031
  have hstable : (prefixWord ++ tailWord_933031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933031).length < 2 ^ (prefixWord ++ tailWord_933031).sum := by decide
  have hdescent : baseEnd_933031 < baseStart_933031 := by decide
  rcases family_descends (prefixWord ++ tailWord_933031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933119 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 8]
def baseStart_933119 : Nat := 118140960795 + 933119 * 2 ^ 59
def prefixEnd_933119 : Nat := 4983230072969 + 3 ^ 40 * 933119 * 2
def baseEnd_933119 : Nat := 106475234409519978071371

theorem tailTrace_933119 : CollatzResearch.WordTrace tailWord_933119 prefixEnd_933119 106475234409519978071371 := by
  unfold tailWord_933119
  simp only [CollatzResearch.WordTrace]
  refine ⟨34033645906476701882690411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22689097270984467921793607 34033645906476701882690411)
  ·
    refine ⟨51050468859715052824035617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34033645906476701882690411 51050468859715052824035617)
    ·
      refine ⟨38287851644786289618026713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51050468859715052824035617 38287851644786289618026713)
      ·
        refine ⟨28715888733589717213520035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38287851644786289618026713 28715888733589717213520035)
        ·
          refine ⟨43073833100384575820280053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28715888733589717213520035 43073833100384575820280053)
          ·
            refine ⟨4038171853161053983151255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43073833100384575820280053 4038171853161053983151255)
            ·
              refine ⟨6057257779741580974726883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4038171853161053983151255 6057257779741580974726883)
              ·
                refine ⟨9085886669612371462090325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6057257779741580974726883 9085886669612371462090325)
                ·
                  refine ⟨106475234409519978071371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9085886669612371462090325 106475234409519978071371)
                  ·
                    rfl

theorem cell22_933119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 8].length) (baseStart_933119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933119 prefixEnd_933119 := by exact prefixLift 933119
  have htrace : WordTrace (prefixWord ++ tailWord_933119) baseStart_933119 baseEnd_933119 := by
    simpa [prefixWord, tailWord_933119, baseEnd_933119] using wordTrace_append hprefix tailTrace_933119
  have hstable : (prefixWord ++ tailWord_933119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933119).length < 2 ^ (prefixWord ++ tailWord_933119).sum := by decide
  have hdescent : baseEnd_933119 < baseStart_933119 := by decide
  rcases family_descends (prefixWord ++ tailWord_933119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933121 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_933121 : Nat := 118140960795 + 933121 * 2 ^ 59
def prefixEnd_933121 : Nat := 4983230072969 + 3 ^ 40 * 933121 * 2
def baseEnd_933121 : Nat := 319426387869432595664107

theorem tailTrace_933121 : CollatzResearch.WordTrace tailWord_933121 prefixEnd_933121 319426387869432595664107 := by
  unfold tailWord_933121
  simp only [CollatzResearch.WordTrace]
  refine ⟨34033718852469456224263217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22689145901646304149508811 34033718852469456224263217)
  ·
    refine ⟨25525289139352092168197413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34033718852469456224263217 25525289139352092168197413)
    ·
      refine ⟨4785991713628517281537015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25525289139352092168197413 4785991713628517281537015)
      ·
        refine ⟨7178987570442775922305523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785991713628517281537015 7178987570442775922305523)
        ·
          refine ⟨10768481355664163883458285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7178987570442775922305523 10768481355664163883458285)
          ·
            refine ⟨4038180508374061456296857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10768481355664163883458285 4038180508374061456296857)
            ·
              refine ⟨3028635381280546092222643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038180508374061456296857 3028635381280546092222643)
              ·
                refine ⟨4542953071920819138333965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028635381280546092222643 4542953071920819138333965)
                ·
                  refine ⟨1703607401970307176875237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4542953071920819138333965 1703607401970307176875237)
                  ·
                    refine ⟨319426387869432595664107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1703607401970307176875237 319426387869432595664107)
                    ·
                      rfl

theorem cell22_933121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_933121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933121 prefixEnd_933121 := by exact prefixLift 933121
  have htrace : WordTrace (prefixWord ++ tailWord_933121) baseStart_933121 baseEnd_933121 := by
    simpa [prefixWord, tailWord_933121, baseEnd_933121] using wordTrace_append hprefix tailTrace_933121
  have hstable : (prefixWord ++ tailWord_933121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933121).length < 2 ^ (prefixWord ++ tailWord_933121).sum := by decide
  have hdescent : baseEnd_933121 < baseStart_933121 := by decide
  rcases family_descends (prefixWord ++ tailWord_933121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933164 : List Nat := [2, 2, 1, 1, 1, 3, 1, 11]
def baseStart_933164 : Nat := 118140960795 + 933164 * 2 ^ 59
def prefixEnd_933164 : Nat := 4983230072969 + 3 ^ 40 * 933164 * 2
def baseEnd_933164 : Nat := 35493456405354979648775

theorem tailTrace_933164 : CollatzResearch.WordTrace tailWord_933164 prefixEnd_933164 35493456405354979648775 := by
  unfold tailWord_933164
  simp only [CollatzResearch.WordTrace]
  refine ⟨17017643595656837284039273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22690191460875783045385697 17017643595656837284039273)
  ·
    refine ⟨12763232696742627963029455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17017643595656837284039273 12763232696742627963029455)
    ·
      refine ⟨19144849045113941944544183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12763232696742627963029455 19144849045113941944544183)
      ·
        refine ⟨28717273567670912916816275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19144849045113941944544183 28717273567670912916816275)
        ·
          refine ⟨43075910351506369375224413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28717273567670912916816275 43075910351506369375224413)
          ·
            refine ⟨16153466381814888515709155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43075910351506369375224413 16153466381814888515709155)
            ·
              refine ⟨24230199572722332773563733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16153466381814888515709155 24230199572722332773563733)
              ·
                refine ⟨35493456405354979648775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24230199572722332773563733 35493456405354979648775)
                ·
                  rfl

theorem cell22_933164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 11].length) (baseStart_933164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933164 prefixEnd_933164 := by exact prefixLift 933164
  have htrace : WordTrace (prefixWord ++ tailWord_933164) baseStart_933164 baseEnd_933164 := by
    simpa [prefixWord, tailWord_933164, baseEnd_933164] using wordTrace_append hprefix tailTrace_933164
  have hstable : (prefixWord ++ tailWord_933164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933164).length < 2 ^ (prefixWord ++ tailWord_933164).sum := by decide
  have hdescent : baseEnd_933164 < baseStart_933164 := by decide
  rcases family_descends (prefixWord ++ tailWord_933164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933271 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 6]
def baseStart_933271 : Nat := 118140960795 + 933271 * 2 ^ 59
def prefixEnd_933271 : Nat := 4983230072969 + 3 ^ 40 * 933271 * 2
def baseEnd_933271 : Nat := 106492578644960734804549

theorem tailTrace_933271 : CollatzResearch.WordTrace tailWord_933271 prefixEnd_933271 106492578644960734804549 := by
  unfold tailWord_933271
  simp only [CollatzResearch.WordTrace]
  refine ⟨34039189801926031842223667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22692793201284021228149111 34039189801926031842223667)
  ·
    refine ⟨51058784702889047763335501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34039189801926031842223667 51058784702889047763335501)
    ·
      refine ⟨19147044263583392911250813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51058784702889047763335501 19147044263583392911250813)
      ·
        refine ⟨7180141598843772341719055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19147044263583392911250813 7180141598843772341719055)
        ·
          refine ⟨10770212398265658512578583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7180141598843772341719055 10770212398265658512578583)
          ·
            refine ⟨16155318597398487768867875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10770212398265658512578583 16155318597398487768867875)
            ·
              refine ⟨24232977896097731653301813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16155318597398487768867875 24232977896097731653301813)
              ·
                refine ⟨2271841677759162342497045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24232977896097731653301813 2271841677759162342497045)
                ·
                  refine ⟨106492578644960734804549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2271841677759162342497045 106492578644960734804549)
                  ·
                    rfl

theorem cell22_933271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 6].length) (baseStart_933271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933271 prefixEnd_933271 := by exact prefixLift 933271
  have htrace : WordTrace (prefixWord ++ tailWord_933271) baseStart_933271 baseEnd_933271 := by
    simpa [prefixWord, tailWord_933271, baseEnd_933271] using wordTrace_append hprefix tailTrace_933271
  have hstable : (prefixWord ++ tailWord_933271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933271).length < 2 ^ (prefixWord ++ tailWord_933271).sum := by decide
  have hdescent : baseEnd_933271 < baseStart_933271 := by decide
  rcases family_descends (prefixWord ++ tailWord_933271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933303 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 4, 3]
def baseStart_933303 : Nat := 118140960795 + 933303 * 2 ^ 59
def prefixEnd_933303 : Nat := 4983230072969 + 3 ^ 40 * 933303 * 2
def baseEnd_933303 : Nat := 319488690188844787613549

theorem tailTrace_933303 : CollatzResearch.WordTrace tailWord_933303 prefixEnd_933303 319488690188844787613549 := by
  unfold tailWord_933303
  simp only [CollatzResearch.WordTrace]
  refine ⟨34040356937810101307388563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22693571291873400871592375 34040356937810101307388563)
  ·
    refine ⟨51060535406715151961082845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34040356937810101307388563 51060535406715151961082845)
    ·
      refine ⟨19147700777518181985406067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51060535406715151961082845 19147700777518181985406067)
      ·
        refine ⟨28721551166277272978109101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19147700777518181985406067 28721551166277272978109101)
        ·
          refine ⟨10770581687353977366790913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28721551166277272978109101 10770581687353977366790913)
          ·
            refine ⟨8077936265515483025093185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10770581687353977366790913 8077936265515483025093185)
            ·
              refine ⟨6058452199136612268819889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8077936265515483025093185 6058452199136612268819889)
              ·
                refine ⟨4543839149352459201614917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6058452199136612268819889 4543839149352459201614917)
                ·
                  refine ⟨851969840503586100302797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4543839149352459201614917 851969840503586100302797)
                  ·
                    refine ⟨319488690188844787613549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 851969840503586100302797 319488690188844787613549)
                    ·
                      rfl

theorem cell22_933303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_933303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933303 prefixEnd_933303 := by exact prefixLift 933303
  have htrace : WordTrace (prefixWord ++ tailWord_933303) baseStart_933303 baseEnd_933303 := by
    simpa [prefixWord, tailWord_933303, baseEnd_933303] using wordTrace_append hprefix tailTrace_933303
  have hstable : (prefixWord ++ tailWord_933303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933303).length < 2 ^ (prefixWord ++ tailWord_933303).sum := by decide
  have hdescent : baseEnd_933303 < baseStart_933303 := by decide
  rcases family_descends (prefixWord ++ tailWord_933303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933337 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 2, 3]
def baseStart_933337 : Nat := 118140960795 + 933337 * 2 ^ 59
def prefixEnd_933337 : Nat := 4983230072969 + 3 ^ 40 * 933337 * 2
def baseEnd_933337 : Nat := 319500329083680032263445

theorem tailTrace_933337 : CollatzResearch.WordTrace tailWord_933337 prefixEnd_933337 319500329083680032263445 := by
  unfold tailWord_933337
  simp only [CollatzResearch.WordTrace]
  refine ⟨34041597019686925114126265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22694398013124616742750843 34041597019686925114126265)
  ·
    refine ⟨25531197764765193835594699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34041597019686925114126265 25531197764765193835594699)
    ·
      refine ⟨38296796647147790753392049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25531197764765193835594699 38296796647147790753392049)
      ·
        refine ⟨28722597485360843065044037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38296796647147790753392049 28722597485360843065044037)
        ·
          refine ⟨5385487028505158074695757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28722597485360843065044037 5385487028505158074695757)
          ·
            refine ⟨2019557635689434278010909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5385487028505158074695757 2019557635689434278010909)
            ·
              refine ⟨757334113383537854254091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2019557635689434278010909 757334113383537854254091)
              ·
                refine ⟨1136001170075306781381137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757334113383537854254091 1136001170075306781381137)
                ·
                  refine ⟨852000877556480086035853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1136001170075306781381137 852000877556480086035853)
                  ·
                    refine ⟨319500329083680032263445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 852000877556480086035853 319500329083680032263445)
                    ·
                      rfl

theorem cell22_933337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 3].length) (baseStart_933337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933337 prefixEnd_933337 := by exact prefixLift 933337
  have htrace : WordTrace (prefixWord ++ tailWord_933337) baseStart_933337 baseEnd_933337 := by
    simpa [prefixWord, tailWord_933337, baseEnd_933337] using wordTrace_append hprefix tailTrace_933337
  have hstable : (prefixWord ++ tailWord_933337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933337).length < 2 ^ (prefixWord ++ tailWord_933337).sum := by decide
  have hdescent : baseEnd_933337 < baseStart_933337 := by decide
  rcases family_descends (prefixWord ++ tailWord_933337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933395 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 5]
def baseStart_933395 : Nat := 118140960795 + 933395 * 2 ^ 59
def prefixEnd_933395 : Nat := 4983230072969 + 3 ^ 40 * 933395 * 2
def baseEnd_933395 : Nat := 106506727889662404771089

theorem tailTrace_933395 : CollatzResearch.WordTrace tailWord_933395 prefixEnd_933395 106506727889662404771089 := by
  unfold tailWord_933395
  simp only [CollatzResearch.WordTrace]
  refine ⟨34043712453476801019737639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22695808302317867346491759 34043712453476801019737639)
  ·
    refine ⟨51065568680215201529606459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34043712453476801019737639 51065568680215201529606459)
    ·
      refine ⟨76598353020322802294409689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51065568680215201529606459 76598353020322802294409689)
      ·
        refine ⟨57448764765242101720807267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76598353020322802294409689 57448764765242101720807267)
        ·
          refine ⟨86173147147863152581210901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57448764765242101720807267 86173147147863152581210901)
          ·
            refine ⟨4039366272556085277244261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86173147147863152581210901 4039366272556085277244261)
            ·
              refine ⟨757381176104265989483299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4039366272556085277244261 757381176104265989483299)
              ·
                refine ⟨1136071764156398984224949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757381176104265989483299 1136071764156398984224949)
                ·
                  refine ⟨106506727889662404771089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1136071764156398984224949 106506727889662404771089)
                  ·
                    rfl

theorem cell22_933395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 5].length) (baseStart_933395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933395 prefixEnd_933395 := by exact prefixLift 933395
  have htrace : WordTrace (prefixWord ++ tailWord_933395) baseStart_933395 baseEnd_933395 := by
    simpa [prefixWord, tailWord_933395, baseEnd_933395] using wordTrace_append hprefix tailTrace_933395
  have hstable : (prefixWord ++ tailWord_933395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933395).length < 2 ^ (prefixWord ++ tailWord_933395).sum := by decide
  have hdescent : baseEnd_933395 < baseStart_933395 := by decide
  rcases family_descends (prefixWord ++ tailWord_933395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933485 : List Nat := [1, 5, 1, 1, 4, 1, 9]
def baseStart_933485 : Nat := 118140960795 + 933485 * 2 ^ 59
def prefixEnd_933485 : Nat := 4983230072969 + 3 ^ 40 * 933485 * 2
def baseEnd_933485 : Nat := 11835221944750258502333

theorem tailTrace_933485 : CollatzResearch.WordTrace tailWord_933485 prefixEnd_933485 11835221944750258502333 := by
  unfold tailWord_933485
  simp only [CollatzResearch.WordTrace]
  refine ⟨34046995023150746390513909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22697996682100497593675939 34046995023150746390513909)
  ·
    refine ⟨3191905783420382474110679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34046995023150746390513909 3191905783420382474110679)
    ·
      refine ⟨4787858675130573711166019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191905783420382474110679 4787858675130573711166019)
      ·
        refine ⟨7181788012695860566749029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787858675130573711166019 7181788012695860566749029)
        ·
          refine ⟨1346585252380473856265443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7181788012695860566749029 1346585252380473856265443)
          ·
            refine ⟨2019877878570710784398165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346585252380473856265443 2019877878570710784398165)
            ·
              refine ⟨11835221944750258502333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2019877878570710784398165 11835221944750258502333)
              ·
                rfl

theorem cell22_933485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 9].length) (baseStart_933485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933485 prefixEnd_933485 := by exact prefixLift 933485
  have htrace : WordTrace (prefixWord ++ tailWord_933485) baseStart_933485 baseEnd_933485 := by
    simpa [prefixWord, tailWord_933485, baseEnd_933485] using wordTrace_append hprefix tailTrace_933485
  have hstable : (prefixWord ++ tailWord_933485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933485).length < 2 ^ (prefixWord ++ tailWord_933485).sum := by decide
  have hdescent : baseEnd_933485 < baseStart_933485 := by decide
  rcases family_descends (prefixWord ++ tailWord_933485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933498 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_933498 : Nat := 118140960795 + 933498 * 2 ^ 59
def prefixEnd_933498 : Nat := 4983230072969 + 3 ^ 40 * 933498 * 2
def baseEnd_933498 : Nat := 319555442673929278987951

theorem tailTrace_933498 : CollatzResearch.WordTrace tailWord_933498 prefixEnd_933498 319555442673929278987951 := by
  unfold tailWord_933498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511867293025912402684287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22698312781402433073824765 8511867293025912402684287)
  ·
    refine ⟨12767800939538868604026431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8511867293025912402684287 12767800939538868604026431)
    ·
      refine ⟨19151701409308302906039647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12767800939538868604026431 19151701409308302906039647)
      ·
        refine ⟨28727552113962454359059471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19151701409308302906039647 28727552113962454359059471)
        ·
          refine ⟨43091328170943681538589207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28727552113962454359059471 43091328170943681538589207)
          ·
            refine ⟨64636992256415522307883811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43091328170943681538589207 64636992256415522307883811)
            ·
              refine ⟨96955488384623283461825717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64636992256415522307883811 96955488384623283461825717)
              ·
                refine ⟨9089577036058432824546161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96955488384623283461825717 9089577036058432824546161)
                ·
                  refine ⟨6817182777043824618409621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9089577036058432824546161 6817182777043824618409621)
                  ·
                    refine ⟨319555442673929278987951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6817182777043824618409621 319555442673929278987951)
                    ·
                      rfl

theorem cell22_933498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_933498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933498 prefixEnd_933498 := by exact prefixLift 933498
  have htrace : WordTrace (prefixWord ++ tailWord_933498) baseStart_933498 baseEnd_933498 := by
    simpa [prefixWord, tailWord_933498, baseEnd_933498] using wordTrace_append hprefix tailTrace_933498
  have hstable : (prefixWord ++ tailWord_933498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933498).length < 2 ^ (prefixWord ++ tailWord_933498).sum := by decide
  have hdescent : baseEnd_933498 < baseStart_933498 := by decide
  rcases family_descends (prefixWord ++ tailWord_933498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933564 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 5]
def baseStart_933564 : Nat := 118140960795 + 933564 * 2 ^ 59
def prefixEnd_933564 : Nat := 4983230072969 + 3 ^ 40 * 933564 * 2
def baseEnd_933564 : Nat := 106526011940909035612583

theorem tailTrace_933564 : CollatzResearch.WordTrace tailWord_933564 prefixEnd_933564 106526011940909035612583 := by
  unfold tailWord_933564
  simp only [CollatzResearch.WordTrace]
  refine ⟨17024938194932271441319873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22699917593243028588426497 17024938194932271441319873)
  ·
    refine ⟨12768703646199203580989905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17024938194932271441319873 12768703646199203580989905)
    ·
      refine ⟨9576527734649402685742429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12768703646199203580989905 9576527734649402685742429)
      ·
        refine ⟨3591197900493526007153411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9576527734649402685742429 3591197900493526007153411)
        ·
          refine ⟨5386796850740289010730117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591197900493526007153411 5386796850740289010730117)
          ·
            refine ⟨1010024409513804189511897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5386796850740289010730117 1010024409513804189511897)
            ·
              refine ⟨757518307135353142133923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010024409513804189511897 757518307135353142133923)
              ·
                refine ⟨1136277460703029713200885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757518307135353142133923 1136277460703029713200885)
                ·
                  refine ⟨106526011940909035612583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1136277460703029713200885 106526011940909035612583)
                  ·
                    rfl

theorem cell22_933564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_933564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933564 prefixEnd_933564 := by exact prefixLift 933564
  have htrace : WordTrace (prefixWord ++ tailWord_933564) baseStart_933564 baseEnd_933564 := by
    simpa [prefixWord, tailWord_933564, baseEnd_933564] using wordTrace_append hprefix tailTrace_933564
  have hstable : (prefixWord ++ tailWord_933564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933564).length < 2 ^ (prefixWord ++ tailWord_933564).sum := by decide
  have hdescent : baseEnd_933564 < baseStart_933564 := by decide
  rcases family_descends (prefixWord ++ tailWord_933564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933592 : List Nat := [2, 1, 2, 2, 3, 1, 2, 5, 4]
def baseStart_933592 : Nat := 118140960795 + 933592 * 2 ^ 59
def prefixEnd_933592 : Nat := 4983230072969 + 3 ^ 40 * 933592 * 2
def baseEnd_933592 : Nat := 106529206931648122379221

theorem tailTrace_933592 : CollatzResearch.WordTrace tailWord_933592 prefixEnd_933592 106529206931648122379221 := by
  unfold tailWord_933592
  simp only [CollatzResearch.WordTrace]
  refine ⟨17025448816881551832329515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22700598422508735776439353 17025448816881551832329515)
  ·
    refine ⟨25538173225322327748494273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17025448816881551832329515 25538173225322327748494273)
    ·
      refine ⟨19153629918991745811370705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25538173225322327748494273 19153629918991745811370705)
      ·
        refine ⟨14365222439243809358528029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19153629918991745811370705 14365222439243809358528029)
        ·
          refine ⟨5386958414716428509448011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14365222439243809358528029 5386958414716428509448011)
          ·
            refine ⟨8080437622074642764172017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386958414716428509448011 8080437622074642764172017)
            ·
              refine ⟨6060328216555982073129013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8080437622074642764172017 6060328216555982073129013)
              ·
                refine ⟨568155770302123319355845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6060328216555982073129013 568155770302123319355845)
                ·
                  refine ⟨106529206931648122379221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568155770302123319355845 106529206931648122379221)
                  ·
                    rfl

theorem cell22_933592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 4].length) (baseStart_933592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933592 prefixEnd_933592 := by exact prefixLift 933592
  have htrace : WordTrace (prefixWord ++ tailWord_933592) baseStart_933592 baseEnd_933592 := by
    simpa [prefixWord, tailWord_933592, baseEnd_933592] using wordTrace_append hprefix tailTrace_933592
  have hstable : (prefixWord ++ tailWord_933592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933592).length < 2 ^ (prefixWord ++ tailWord_933592).sum := by decide
  have hdescent : baseEnd_933592 < baseStart_933592 := by decide
  rcases family_descends (prefixWord ++ tailWord_933592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933594 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 1, 4]
def baseStart_933594 : Nat := 118140960795 + 933594 * 2 ^ 59
def prefixEnd_933594 : Nat := 4983230072969 + 3 ^ 40 * 933594 * 2
def baseEnd_933594 : Nat := 319588305435817028587657

theorem tailTrace_933594 : CollatzResearch.WordTrace tailWord_933594 prefixEnd_933594 319588305435817028587657 := by
  unfold tailWord_933594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512742644938964501557959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22700647053170572004154557 8512742644938964501557959)
  ·
    refine ⟨12769113967408446752336939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8512742644938964501557959 12769113967408446752336939)
    ·
      refine ⟨19153670951112670128505409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769113967408446752336939 19153670951112670128505409)
      ·
        refine ⟨14365253213334502596379057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19153670951112670128505409 14365253213334502596379057)
        ·
          refine ⟨10773939910000876947284293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14365253213334502596379057 10773939910000876947284293)
          ·
            refine ⟨2020113733125164427615805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10773939910000876947284293 2020113733125164427615805)
            ·
              refine ⟨757542649921936660355927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2020113733125164427615805 757542649921936660355927)
              ·
                refine ⟨1136313974882904990533891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757542649921936660355927 1136313974882904990533891)
                ·
                  refine ⟨1704470962324357485800837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136313974882904990533891 1704470962324357485800837)
                  ·
                    refine ⟨319588305435817028587657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1704470962324357485800837 319588305435817028587657)
                    ·
                      rfl

theorem cell22_933594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_933594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933594 prefixEnd_933594 := by exact prefixLift 933594
  have htrace : WordTrace (prefixWord ++ tailWord_933594) baseStart_933594 baseEnd_933594 := by
    simpa [prefixWord, tailWord_933594, baseEnd_933594] using wordTrace_append hprefix tailTrace_933594
  have hstable : (prefixWord ++ tailWord_933594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933594).length < 2 ^ (prefixWord ++ tailWord_933594).sum := by decide
  have hdescent : baseEnd_933594 < baseStart_933594 := by decide
  rcases family_descends (prefixWord ++ tailWord_933594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933645 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_933645 : Nat := 118140960795 + 933645 * 2 ^ 59
def prefixEnd_933645 : Nat := 4983230072969 + 3 ^ 40 * 933645 * 2
def baseEnd_933645 : Nat := 319605763778069895562501

theorem tailTrace_933645 : CollatzResearch.WordTrace tailWord_933645 prefixEnd_933645 319605763778069895562501 := by
  unfold tailWord_933645
  simp only [CollatzResearch.WordTrace]
  refine ⟨34052830702571093716338389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22701887135047395810892259 34052830702571093716338389)
  ·
    refine ⟨798113219591510008976681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 34052830702571093716338389 798113219591510008976681)
    ·
      refine ⟨598584914693632506732511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798113219591510008976681 598584914693632506732511)
      ·
        refine ⟨897877372040448760098767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598584914693632506732511 897877372040448760098767)
        ·
          refine ⟨1346816058060673140148151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897877372040448760098767 1346816058060673140148151)
          ·
            refine ⟨2020224087091009710222227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346816058060673140148151 2020224087091009710222227)
            ·
              refine ⟨3030336130636514565333341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020224087091009710222227 3030336130636514565333341)
              ·
                refine ⟨1136376048988692962000003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3030336130636514565333341 1136376048988692962000003)
                ·
                  refine ⟨1704564073483039443000005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136376048988692962000003 1704564073483039443000005)
                  ·
                    refine ⟨319605763778069895562501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1704564073483039443000005 319605763778069895562501)
                    ·
                      rfl

theorem cell22_933645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_933645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933645 prefixEnd_933645 := by exact prefixLift 933645
  have htrace : WordTrace (prefixWord ++ tailWord_933645) baseStart_933645 baseEnd_933645 := by
    simpa [prefixWord, tailWord_933645, baseEnd_933645] using wordTrace_append hprefix tailTrace_933645
  have hstable : (prefixWord ++ tailWord_933645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933645).length < 2 ^ (prefixWord ++ tailWord_933645).sum := by decide
  have hdescent : baseEnd_933645 < baseStart_933645 := by decide
  rcases family_descends (prefixWord ++ tailWord_933645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933669 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_933669 : Nat := 118140960795 + 933669 * 2 ^ 59
def prefixEnd_933669 : Nat := 4983230072969 + 3 ^ 40 * 933669 * 2
def baseEnd_933669 : Nat := 319613979468541832962427

theorem tailTrace_933669 : CollatzResearch.WordTrace tailWord_933669 prefixEnd_933669 319613979468541832962427 := by
  unfold tailWord_933669
  simp only [CollatzResearch.WordTrace]
  refine ⟨34053706054484145815212061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22702470702989430543474707 34053706054484145815212061)
  ·
    refine ⟨12770139770431554680704523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34053706054484145815212061 12770139770431554680704523)
    ·
      refine ⟨19155209655647332021056785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12770139770431554680704523 19155209655647332021056785)
      ·
        refine ⟨14366407241735499015792589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19155209655647332021056785 14366407241735499015792589)
        ·
          refine ⟨5387402715650812130922221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14366407241735499015792589 5387402715650812130922221)
          ·
            refine ⟨2020276018369054549095833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5387402715650812130922221 2020276018369054549095833)
            ·
              refine ⟨1515207013776790911821875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2020276018369054549095833 1515207013776790911821875)
              ·
                refine ⟨2272810520665186367732813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515207013776790911821875 2272810520665186367732813)
                ·
                  refine ⟨852303945249444887899805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2272810520665186367732813 852303945249444887899805)
                  ·
                    refine ⟨319613979468541832962427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 852303945249444887899805 319613979468541832962427)
                    ·
                      rfl

theorem cell22_933669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_933669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933669 prefixEnd_933669 := by exact prefixLift 933669
  have htrace : WordTrace (prefixWord ++ tailWord_933669) baseStart_933669 baseEnd_933669 := by
    simpa [prefixWord, tailWord_933669, baseEnd_933669] using wordTrace_append hprefix tailTrace_933669
  have hstable : (prefixWord ++ tailWord_933669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933669).length < 2 ^ (prefixWord ++ tailWord_933669).sum := by decide
  have hdescent : baseEnd_933669 < baseStart_933669 := by decide
  rcases family_descends (prefixWord ++ tailWord_933669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933686 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_933686 : Nat := 118140960795 + 933686 * 2 ^ 59
def prefixEnd_933686 : Nat := 4983230072969 + 3 ^ 40 * 933686 * 2
def baseEnd_933686 : Nat := 319619798915959455287375

theorem tailTrace_933686 : CollatzResearch.WordTrace tailWord_933686 prefixEnd_933686 319619798915959455287375 := by
  unfold tailWord_933686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2128395380963909857411307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22702884063615038479053941 2128395380963909857411307)
  ·
    refine ⟨3192593071445864786116961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2128395380963909857411307 3192593071445864786116961)
    ·
      refine ⟨2394444803584398589587721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3192593071445864786116961 2394444803584398589587721)
      ·
        refine ⟨1795833602688298942190791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2394444803584398589587721 1795833602688298942190791)
        ·
          refine ⟨2693750404032448413286187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795833602688298942190791 2693750404032448413286187)
          ·
            refine ⟨4040625606048672619929281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693750404032448413286187 4040625606048672619929281)
            ·
              refine ⟨3030469204536504464946961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040625606048672619929281 3030469204536504464946961)
              ·
                refine ⟨2272851903402378348710221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3030469204536504464946961 2272851903402378348710221)
                ·
                  refine ⟨852319463775891880766333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2272851903402378348710221 852319463775891880766333)
                  ·
                    refine ⟨319619798915959455287375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 852319463775891880766333 319619798915959455287375)
                    ·
                      rfl

theorem cell22_933686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_933686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933686 prefixEnd_933686 := by exact prefixLift 933686
  have htrace : WordTrace (prefixWord ++ tailWord_933686) baseStart_933686 baseEnd_933686 := by
    simpa [prefixWord, tailWord_933686, baseEnd_933686] using wordTrace_append hprefix tailTrace_933686
  have hstable : (prefixWord ++ tailWord_933686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933686).length < 2 ^ (prefixWord ++ tailWord_933686).sum := by decide
  have hdescent : baseEnd_933686 < baseStart_933686 := by decide
  rcases family_descends (prefixWord ++ tailWord_933686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933727 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 6]
def baseStart_933727 : Nat := 118140960795 + 933727 * 2 ^ 59
def prefixEnd_933727 : Nat := 4983230072969 + 3 ^ 40 * 933727 * 2
def baseEnd_933727 : Nat := 106544611351283005004083

theorem tailTrace_933727 : CollatzResearch.WordTrace tailWord_933727 prefixEnd_933727 106544611351283005004083 := by
  unfold tailWord_933727
  simp only [CollatzResearch.WordTrace]
  refine ⟨34055821488274021720823435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22703880992182681147215623 34055821488274021720823435)
  ·
    refine ⟨51083732232411032581235153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34055821488274021720823435 51083732232411032581235153)
    ·
      refine ⟨38312799174308274435926365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51083732232411032581235153 38312799174308274435926365)
      ·
        refine ⟨14367299690365602913472387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38312799174308274435926365 14367299690365602913472387)
        ·
          refine ⟨21550949535548404370208581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14367299690365602913472387 21550949535548404370208581)
          ·
            refine ⟨4040803037915325819414109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21550949535548404370208581 4040803037915325819414109)
            ·
              refine ⟨1515301139218247182280291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4040803037915325819414109 1515301139218247182280291)
              ·
                refine ⟨2272951708827370773420437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515301139218247182280291 2272951708827370773420437)
                ·
                  refine ⟨106544611351283005004083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2272951708827370773420437 106544611351283005004083)
                  ·
                    rfl

theorem cell22_933727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 6].length) (baseStart_933727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933727 prefixEnd_933727 := by exact prefixLift 933727
  have htrace : WordTrace (prefixWord ++ tailWord_933727) baseStart_933727 baseEnd_933727 := by
    simpa [prefixWord, tailWord_933727, baseEnd_933727] using wordTrace_append hprefix tailTrace_933727
  have hstable : (prefixWord ++ tailWord_933727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933727).length < 2 ^ (prefixWord ++ tailWord_933727).sum := by decide
  have hdescent : baseEnd_933727 < baseStart_933727 := by decide
  rcases family_descends (prefixWord ++ tailWord_933727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933778 : List Nat := [3, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_933778 : Nat := 118140960795 + 933778 * 2 ^ 59
def prefixEnd_933778 : Nat := 4983230072969 + 3 ^ 40 * 933778 * 2
def baseEnd_933778 : Nat := 106550430798700627329031

theorem tailTrace_933778 : CollatzResearch.WordTrace tailWord_933778 prefixEnd_933778 106550430798700627329031 := by
  unfold tailWord_933778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514420402772314357732497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22705121074059504953953325 8514420402772314357732497)
  ·
    refine ⟨6385815302079235768299373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8514420402772314357732497 6385815302079235768299373)
    ·
      refine ⟨2394680738279713413112265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6385815302079235768299373 2394680738279713413112265)
      ·
        refine ⟨1796010553709785059834199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2394680738279713413112265 1796010553709785059834199)
        ·
          refine ⟨2694015830564677589751299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796010553709785059834199 2694015830564677589751299)
          ·
            refine ⟨4041023745847016384626949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694015830564677589751299 4041023745847016384626949)
            ·
              refine ⟨757691952346315572117553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4041023745847016384626949 757691952346315572117553)
              ·
                refine ⟨568268964259736679088165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757691952346315572117553 568268964259736679088165)
                ·
                  refine ⟨106550430798700627329031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568268964259736679088165 106550430798700627329031)
                  ·
                    rfl

theorem cell22_933778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_933778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933778 prefixEnd_933778 := by exact prefixLift 933778
  have htrace : WordTrace (prefixWord ++ tailWord_933778) baseStart_933778 baseEnd_933778 := by
    simpa [prefixWord, tailWord_933778, baseEnd_933778] using wordTrace_append hprefix tailTrace_933778
  have hstable : (prefixWord ++ tailWord_933778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933778).length < 2 ^ (prefixWord ++ tailWord_933778).sum := by decide
  have hdescent : baseEnd_933778 < baseStart_933778 := by decide
  rcases family_descends (prefixWord ++ tailWord_933778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933789 : List Nat := [1, 4, 2, 1, 2, 4, 1, 7]
def baseStart_933789 : Nat := 118140960795 + 933789 * 2 ^ 59
def prefixEnd_933789 : Nat := 4983230072969 + 3 ^ 40 * 933789 * 2
def baseEnd_933789 : Nat := 35517228657877946662451

theorem tailTrace_933789 : CollatzResearch.WordTrace tailWord_933789 prefixEnd_933789 35517228657877946662451 := by
  unfold tailWord_933789
  simp only [CollatzResearch.WordTrace]
  refine ⟨34058082814049406309580421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22705388542699604206386947 34058082814049406309580421)
  ·
    refine ⟨6385890527634263683046329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34058082814049406309580421 6385890527634263683046329)
    ·
      refine ⟨4789417895725697762284747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6385890527634263683046329 4789417895725697762284747)
      ·
        refine ⟨7184126843588546643427121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4789417895725697762284747 7184126843588546643427121)
        ·
          refine ⟨5388095132691409982570341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7184126843588546643427121 5388095132691409982570341)
          ·
            refine ⟨1010267837379639371731939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5388095132691409982570341 1010267837379639371731939)
            ·
              refine ⟨1515401756069459057597909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010267837379639371731939 1515401756069459057597909)
              ·
                refine ⟨35517228657877946662451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1515401756069459057597909 35517228657877946662451)
                ·
                  rfl

theorem cell22_933789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 7].length) (baseStart_933789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933789 prefixEnd_933789 := by exact prefixLift 933789
  have htrace : WordTrace (prefixWord ++ tailWord_933789) baseStart_933789 baseEnd_933789 := by
    simpa [prefixWord, tailWord_933789, baseEnd_933789] using wordTrace_append hprefix tailTrace_933789
  have hstable : (prefixWord ++ tailWord_933789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933789).length < 2 ^ (prefixWord ++ tailWord_933789).sum := by decide
  have hdescent : baseEnd_933789 < baseStart_933789 := by decide
  rcases family_descends (prefixWord ++ tailWord_933789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933817 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 7]
def baseStart_933817 : Nat := 118140960795 + 933817 * 2 ^ 59
def prefixEnd_933817 : Nat := 4983230072969 + 3 ^ 40 * 933817 * 2
def baseEnd_933817 : Nat := 106554880964372926753991

theorem tailTrace_933817 : CollatzResearch.WordTrace tailWord_933817 prefixEnd_933817 106554880964372926753991 := by
  unfold tailWord_933817
  simp only [CollatzResearch.WordTrace]
  refine ⟨34059104057947967091599705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22706069371965311394399803 34059104057947967091599705)
  ·
    refine ⟨25544328043460975318699779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34059104057947967091599705 25544328043460975318699779)
    ·
      refine ⟨38316492065191462978049669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25544328043460975318699779 38316492065191462978049669)
      ·
        refine ⟨7184342262223399308384313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38316492065191462978049669 7184342262223399308384313)
        ·
          refine ⟨5388256696667549481288235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7184342262223399308384313 5388256696667549481288235)
          ·
            refine ⟨8082385045001324221932353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5388256696667549481288235 8082385045001324221932353)
            ·
              refine ⟨6061788783750993166449265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8082385045001324221932353 6061788783750993166449265)
              ·
                refine ⟨4546341587813244874836949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6061788783750993166449265 4546341587813244874836949)
                ·
                  refine ⟨106554880964372926753991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4546341587813244874836949 106554880964372926753991)
                  ·
                    rfl

theorem cell22_933817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_933817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933817 prefixEnd_933817 := by exact prefixLift 933817
  have htrace : WordTrace (prefixWord ++ tailWord_933817) baseStart_933817 baseEnd_933817 := by
    simpa [prefixWord, tailWord_933817, baseEnd_933817] using wordTrace_append hprefix tailTrace_933817
  have hstable : (prefixWord ++ tailWord_933817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933817).length < 2 ^ (prefixWord ++ tailWord_933817).sum := by decide
  have hdescent : baseEnd_933817 < baseStart_933817 := by decide
  rcases family_descends (prefixWord ++ tailWord_933817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933834 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_933834 : Nat := 118140960795 + 933834 * 2 ^ 59
def prefixEnd_933834 : Nat := 4983230072969 + 3 ^ 40 * 933834 * 2
def baseEnd_933834 : Nat := 106556820780178800862307

theorem tailTrace_933834 : CollatzResearch.WordTrace tailWord_933834 prefixEnd_933834 106556820780178800862307 := by
  unfold tailWord_933834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514931024721594748742139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22706482732590919329979037 8514931024721594748742139)
  ·
    refine ⟨12772396537082392123113209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8514931024721594748742139 12772396537082392123113209)
    ·
      refine ⟨9579297402811794092334907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12772396537082392123113209 9579297402811794092334907)
      ·
        refine ⟨14368946104217691138502361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9579297402811794092334907 14368946104217691138502361)
        ·
          refine ⟨10776709578163268353876771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14368946104217691138502361 10776709578163268353876771)
          ·
            refine ⟨16165064367244902530815157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776709578163268353876771 16165064367244902530815157)
            ·
              refine ⟨1515474784429209612263921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16165064367244902530815157 1515474784429209612263921)
              ·
                refine ⟨1136606088321907209197941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515474784429209612263921 1136606088321907209197941)
                ·
                  refine ⟨106556820780178800862307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1136606088321907209197941 106556820780178800862307)
                  ·
                    rfl

theorem cell22_933834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_933834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933834 prefixEnd_933834 := by exact prefixLift 933834
  have htrace : WordTrace (prefixWord ++ tailWord_933834) baseStart_933834 baseEnd_933834 := by
    simpa [prefixWord, tailWord_933834, baseEnd_933834] using wordTrace_append hprefix tailTrace_933834
  have hstable : (prefixWord ++ tailWord_933834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933834).length < 2 ^ (prefixWord ++ tailWord_933834).sum := by decide
  have hdescent : baseEnd_933834 < baseStart_933834 := by decide
  rcases family_descends (prefixWord ++ tailWord_933834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933907 : List Nat := [1, 1, 1, 2, 1, 4, 3, 9]
def baseStart_933907 : Nat := 118140960795 + 933907 * 2 ^ 59
def prefixEnd_933907 : Nat := 4983230072969 + 3 ^ 40 * 933907 * 2
def baseEnd_933907 : Nat := 35521716859154282834633

theorem tailTrace_933907 : CollatzResearch.WordTrace tailWord_933907 prefixEnd_933907 35521716859154282834633 := by
  unfold tailWord_933907
  simp only [CollatzResearch.WordTrace]
  refine ⟨34062386627621912462375975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22708257751747941641583983 34062386627621912462375975)
  ·
    refine ⟨51093579941432868693563963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34062386627621912462375975 51093579941432868693563963)
    ·
      refine ⟨76640369912149303040345945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51093579941432868693563963 76640369912149303040345945)
      ·
        refine ⟨57480277434111977280259459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76640369912149303040345945 57480277434111977280259459)
        ·
          refine ⟨86220416151167965920389189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57480277434111977280259459 86220416151167965920389189)
          ·
            refine ⟨16166328028343993610072973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86220416151167965920389189 16166328028343993610072973)
            ·
              refine ⟨6062373010628997603777365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16166328028343993610072973 6062373010628997603777365)
              ·
                refine ⟨35521716859154282834633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6062373010628997603777365 35521716859154282834633)
                ·
                  rfl

theorem cell22_933907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 9].length) (baseStart_933907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933907 prefixEnd_933907 := by exact prefixLift 933907
  have htrace : WordTrace (prefixWord ++ tailWord_933907) baseStart_933907 baseEnd_933907 := by
    simpa [prefixWord, tailWord_933907, baseEnd_933907] using wordTrace_append hprefix tailTrace_933907
  have hstable : (prefixWord ++ tailWord_933907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933907).length < 2 ^ (prefixWord ++ tailWord_933907).sum := by decide
  have hdescent : baseEnd_933907 < baseStart_933907 := by decide
  rcases family_descends (prefixWord ++ tailWord_933907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933928 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 1, 5]
def baseStart_933928 : Nat := 118140960795 + 933928 * 2 ^ 59
def prefixEnd_933928 : Nat := 4983230072969 + 3 ^ 40 * 933928 * 2
def baseEnd_933928 : Nat := 319702640461551490736633

theorem tailTrace_933928 : CollatzResearch.WordTrace tailWord_933928 prefixEnd_933928 319702640461551490736633 := by
  unfold tailWord_933928
  simp only [CollatzResearch.WordTrace]
  refine ⟨17031576280272916524445219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22708768373697222032593625 17031576280272916524445219)
  ·
    refine ⟨25547364420409374786667829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17031576280272916524445219 25547364420409374786667829)
    ·
      refine ⟨2395065414413378886250109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25547364420409374786667829 2395065414413378886250109)
      ·
        refine ⟨898149530405017082343791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2395065414413378886250109 898149530405017082343791)
        ·
          refine ⟨1347224295607525623515687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898149530405017082343791 1347224295607525623515687)
          ·
            refine ⟨2020836443411288435273531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347224295607525623515687 2020836443411288435273531)
            ·
              refine ⟨3031254665116932652910297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020836443411288435273531 3031254665116932652910297)
              ·
                refine ⟨2273440998837699489682723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3031254665116932652910297 2273440998837699489682723)
                ·
                  refine ⟨3410161498256549234524085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273440998837699489682723 3410161498256549234524085)
                  ·
                    refine ⟨319702640461551490736633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3410161498256549234524085 319702640461551490736633)
                    ·
                      rfl

theorem cell22_933928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_933928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_933928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_933928 prefixEnd_933928 := by exact prefixLift 933928
  have htrace : WordTrace (prefixWord ++ tailWord_933928) baseStart_933928 baseEnd_933928 := by
    simpa [prefixWord, tailWord_933928, baseEnd_933928] using wordTrace_append hprefix tailTrace_933928
  have hstable : (prefixWord ++ tailWord_933928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933928).length < 2 ^ (prefixWord ++ tailWord_933928).sum := by decide
  have hdescent : baseEnd_933928 < baseStart_933928 := by decide
  rcases family_descends (prefixWord ++ tailWord_933928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934048 : List Nat := [2, 1, 1, 4, 2, 2, 3, 3, 4]
def baseStart_934048 : Nat := 118140960795 + 934048 * 2 ^ 59
def prefixEnd_934048 : Nat := 4983230072969 + 3 ^ 40 * 934048 * 2
def baseEnd_934048 : Nat := 106581239637970392578755

theorem tailTrace_934048 : CollatzResearch.WordTrace tailWord_934048 prefixEnd_934048 106581239637970392578755 := by
  unfold tailWord_934048
  simp only [CollatzResearch.WordTrace]
  refine ⟨17033764660055546771629399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22711686213407395695505865 17033764660055546771629399)
  ·
    refine ⟨25550646990083320157444099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17033764660055546771629399 25550646990083320157444099)
    ·
      refine ⟨38325970485124980236166149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25550646990083320157444099 38325970485124980236166149)
      ·
        refine ⟨7186119465960933794281153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38325970485124980236166149 7186119465960933794281153)
        ·
          refine ⟨5389589599470700345710865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7186119465960933794281153 5389589599470700345710865)
          ·
            refine ⟨4042192199603025259283149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5389589599470700345710865 4042192199603025259283149)
            ·
              refine ⟨1515822074851134472231181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4042192199603025259283149 1515822074851134472231181)
              ·
                refine ⟨568433278069175427086693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1515822074851134472231181 568433278069175427086693)
                ·
                  refine ⟨106581239637970392578755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568433278069175427086693 106581239637970392578755)
                  ·
                    rfl

theorem cell22_934048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 4].length) (baseStart_934048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_934048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_934048 prefixEnd_934048 := by exact prefixLift 934048
  have htrace : WordTrace (prefixWord ++ tailWord_934048) baseStart_934048 baseEnd_934048 := by
    simpa [prefixWord, tailWord_934048, baseEnd_934048] using wordTrace_append hprefix tailTrace_934048
  have hstable : (prefixWord ++ tailWord_934048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934048).length < 2 ^ (prefixWord ++ tailWord_934048).sum := by decide
  have hdescent : baseEnd_934048 < baseStart_934048 := by decide
  rcases family_descends (prefixWord ++ tailWord_934048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
