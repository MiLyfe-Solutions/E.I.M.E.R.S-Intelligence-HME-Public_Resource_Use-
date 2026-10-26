import V185TrunkScan23Chunk0439

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2601320 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 1, 6]
def baseStart_2601320 : Nat := 118140960795 + 2601320 * 2 ^ 59
def prefixEnd_2601320 : Nat := 4983230072969 + 3 ^ 40 * 2601320 * 2
def baseEnd_2601320 : Nat := 445242498717955852412251

theorem tailTrace_2601320 : CollatzResearch.WordTrace tailWord_2601320 prefixEnd_2601320 445242498717955852412251 := by
  unfold tailWord_2601320
  simp only [CollatzResearch.WordTrace]
  refine ⟨47438967467934692465480707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63251956623912923287307609 47438967467934692465480707)
  ·
    refine ⟨71158451201902038698221061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47438967467934692465480707 71158451201902038698221061)
    ·
      refine ⟨13342209600356632255916449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71158451201902038698221061 13342209600356632255916449)
      ·
        refine ⟨10006657200267474191937337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13342209600356632255916449 10006657200267474191937337)
        ·
          refine ⟨7504992900200605643953003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10006657200267474191937337 7504992900200605643953003)
          ·
            refine ⟨11257489350300908465929505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7504992900200605643953003 11257489350300908465929505)
            ·
              refine ⟨8443117012725681349447129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11257489350300908465929505 8443117012725681349447129)
              ·
                refine ⟨6332337759544261012085347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8443117012725681349447129 6332337759544261012085347)
                ·
                  refine ⟨9498506639316391518128021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6332337759544261012085347 9498506639316391518128021)
                  ·
                    refine ⟨445242498717955852412251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9498506639316391518128021 445242498717955852412251)
                    ·
                      rfl

theorem cell23_2601320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_2601320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601320 prefixEnd_2601320 := by exact prefixLift 2601320
  have htrace : WordTrace (prefixWord ++ tailWord_2601320) baseStart_2601320 baseEnd_2601320 := by
    simpa [prefixWord, tailWord_2601320, baseEnd_2601320] using wordTrace_append hprefix tailTrace_2601320
  have hstable : (prefixWord ++ tailWord_2601320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601320).length < 2 ^ (prefixWord ++ tailWord_2601320).sum := by decide
  have hdescent : baseEnd_2601320 < baseStart_2601320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601324 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_2601324 : Nat := 118140960795 + 2601324 * 2 ^ 59
def prefixEnd_2601324 : Nat := 4983230072969 + 3 ^ 40 * 2601324 * 2
def baseEnd_2601324 : Nat := 445243183358828513862245

theorem tailTrace_2601324 : CollatzResearch.WordTrace tailWord_2601324 prefixEnd_2601324 445243183358828513862245 := by
  unfold tailWord_2601324
  simp only [CollatzResearch.WordTrace]
  refine ⟨47439040413927446807053513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63252053885236595742738017 47439040413927446807053513)
  ·
    refine ⟨35579280310445585105290135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47439040413927446807053513 35579280310445585105290135)
    ·
      refine ⟨53368920465668377657935203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35579280310445585105290135 53368920465668377657935203)
      ·
        refine ⟨80053380698502566486902805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53368920465668377657935203 80053380698502566486902805)
        ·
          refine ⟨3752502220242307804073569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80053380698502566486902805 3752502220242307804073569)
          ·
            refine ⟨2814376665181730853055177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752502220242307804073569 2814376665181730853055177)
            ·
              refine ⟨2110782498886298139791383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2814376665181730853055177 2110782498886298139791383)
              ·
                refine ⟨3166173748329447209687075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110782498886298139791383 3166173748329447209687075)
                ·
                  refine ⟨4749260622494170814530613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3166173748329447209687075 4749260622494170814530613)
                  ·
                    refine ⟨445243183358828513862245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4749260622494170814530613 445243183358828513862245)
                    ·
                      rfl

theorem cell23_2601324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_2601324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601324 prefixEnd_2601324 := by exact prefixLift 2601324
  have htrace : WordTrace (prefixWord ++ tailWord_2601324) baseStart_2601324 baseEnd_2601324 := by
    simpa [prefixWord, tailWord_2601324, baseEnd_2601324] using wordTrace_append hprefix tailTrace_2601324
  have hstable : (prefixWord ++ tailWord_2601324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601324).length < 2 ^ (prefixWord ++ tailWord_2601324).sum := by decide
  have hdescent : baseEnd_2601324 < baseStart_2601324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601354 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_2601354 : Nat := 118140960795 + 2601354 * 2 ^ 59
def prefixEnd_2601354 : Nat := 4983230072969 + 3 ^ 40 * 2601354 * 2
def baseEnd_2601354 : Nat := 445248318165373474737199

theorem tailTrace_2601354 : CollatzResearch.WordTrace tailWord_2601354 prefixEnd_2601354 445248318165373474737199 := by
  unfold tailWord_2601354
  simp only [CollatzResearch.WordTrace]
  refine ⟨23719793754436552184424779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63252783345164139158466077 23719793754436552184424779)
  ·
    refine ⟨35579690631654828276637169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23719793754436552184424779 35579690631654828276637169)
    ·
      refine ⟨26684767973741121207477877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35579690631654828276637169 26684767973741121207477877)
      ·
        refine ⟨2501696997538230113201051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26684767973741121207477877 2501696997538230113201051)
        ·
          refine ⟨3752545496307345169801577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501696997538230113201051 3752545496307345169801577)
          ·
            refine ⟨2814409122230508877351183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752545496307345169801577 2814409122230508877351183)
            ·
              refine ⟨4221613683345763316026775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814409122230508877351183 4221613683345763316026775)
              ·
                refine ⟨6332420525018644974040163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4221613683345763316026775 6332420525018644974040163)
                ·
                  refine ⟨9498630787527967461060245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6332420525018644974040163 9498630787527967461060245)
                  ·
                    refine ⟨445248318165373474737199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9498630787527967461060245 445248318165373474737199)
                    ·
                      rfl

theorem cell23_2601354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_2601354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601354 prefixEnd_2601354 := by exact prefixLift 2601354
  have htrace : WordTrace (prefixWord ++ tailWord_2601354) baseStart_2601354 baseEnd_2601354 := by
    simpa [prefixWord, tailWord_2601354, baseEnd_2601354] using wordTrace_append hprefix tailTrace_2601354
  have hstable : (prefixWord ++ tailWord_2601354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601354).length < 2 ^ (prefixWord ++ tailWord_2601354).sum := by decide
  have hdescent : baseEnd_2601354 < baseStart_2601354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601413 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_2601413 : Nat := 118140960795 + 2601413 * 2 ^ 59
def prefixEnd_2601413 : Nat := 4983230072969 + 3 ^ 40 * 2601413 * 2
def baseEnd_2601413 : Nat := 1335775249854735693373825

theorem tailTrace_2601413 : CollatzResearch.WordTrace tailWord_2601413 prefixEnd_2601413 1335775249854735693373825 := by
  unfold tailWord_2601413
  simp only [CollatzResearch.WordTrace]
  refine ⟨94881326924532461814096893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63254217949688307876064595 94881326924532461814096893)
  ·
    refine ⟨35580497596699673180286335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94881326924532461814096893 35580497596699673180286335)
    ·
      refine ⟨53370746395049509770429503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35580497596699673180286335 53370746395049509770429503)
      ·
        refine ⟨80056119592574264655644255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53370746395049509770429503 80056119592574264655644255)
        ·
          refine ⟨120084179388861396983466383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80056119592574264655644255 120084179388861396983466383)
          ·
            refine ⟨180126269083292095475199575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120084179388861396983466383 180126269083292095475199575)
            ·
              refine ⟨270189403624938143212799363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180126269083292095475199575 270189403624938143212799363)
              ·
                refine ⟨405284105437407214819199045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270189403624938143212799363 405284105437407214819199045)
                ·
                  refine ⟨75990769769513852778599821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405284105437407214819199045 75990769769513852778599821)
                  ·
                    refine ⟨28496538663567694791974933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75990769769513852778599821 28496538663567694791974933)
                    ·
                      refine ⟨1335775249854735693373825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28496538663567694791974933 1335775249854735693373825)
                      ·
                        rfl

theorem cell23_2601413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_2601413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601413 prefixEnd_2601413 := by exact prefixLift 2601413
  have htrace : WordTrace (prefixWord ++ tailWord_2601413) baseStart_2601413 baseEnd_2601413 := by
    simpa [prefixWord, tailWord_2601413, baseEnd_2601413] using wordTrace_append hprefix tailTrace_2601413
  have hstable : (prefixWord ++ tailWord_2601413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601413).length < 2 ^ (prefixWord ++ tailWord_2601413).sum := by decide
  have hdescent : baseEnd_2601413 < baseStart_2601413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601423 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 9]
def baseStart_2601423 : Nat := 118140960795 + 2601423 * 2 ^ 59
def prefixEnd_2601423 : Nat := 4983230072969 + 3 ^ 40 * 2601423 * 2
def baseEnd_2601423 : Nat := 148420042740142294916531

theorem tailTrace_2601423 : CollatzResearch.WordTrace tailWord_2601423 prefixEnd_2601423 148420042740142294916531 := by
  unfold tailWord_2601423
  simp only [CollatzResearch.WordTrace]
  refine ⟨94881691654496233521960923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63254461102997489014640615 94881691654496233521960923)
  ·
    refine ⟨142322537481744350282941385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94881691654496233521960923 142322537481744350282941385)
    ·
      refine ⟨106741903111308262712206039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142322537481744350282941385 106741903111308262712206039)
      ·
        refine ⟨160112854666962394068309059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106741903111308262712206039 160112854666962394068309059)
        ·
          refine ⟨240169282000443591102463589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160112854666962394068309059 240169282000443591102463589)
          ·
            refine ⟨45031740375083173331711923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240169282000443591102463589 45031740375083173331711923)
            ·
              refine ⟨67547610562624759997567885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45031740375083173331711923 67547610562624759997567885)
              ·
                refine ⟨25330353960984284999087957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67547610562624759997567885 25330353960984284999087957)
                ·
                  refine ⟨148420042740142294916531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25330353960984284999087957 148420042740142294916531)
                  ·
                    rfl

theorem cell23_2601423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 9].length) (baseStart_2601423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601423 prefixEnd_2601423 := by exact prefixLift 2601423
  have htrace : WordTrace (prefixWord ++ tailWord_2601423) baseStart_2601423 baseEnd_2601423 := by
    simpa [prefixWord, tailWord_2601423, baseEnd_2601423] using wordTrace_append hprefix tailTrace_2601423
  have hstable : (prefixWord ++ tailWord_2601423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601423).length < 2 ^ (prefixWord ++ tailWord_2601423).sum := by decide
  have hdescent : baseEnd_2601423 < baseStart_2601423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601457 : List Nat := [1, 2, 2, 2, 3, 1, 3, 4, 5]
def baseStart_2601457 : Nat := 118140960795 + 2601457 * 2 ^ 59
def prefixEnd_2601457 : Nat := 4983230072969 + 3 ^ 40 * 2601457 * 2
def baseEnd_2601457 : Nat := 148421982555948169024847

theorem tailTrace_2601457 : CollatzResearch.WordTrace tailWord_2601457 prefixEnd_2601457 148421982555948169024847 := by
  unfold tailWord_2601457
  simp only [CollatzResearch.WordTrace]
  refine ⟨94882931736373057328698625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63255287824248704885799083 94882931736373057328698625)
  ·
    refine ⟨71162198802279792996523969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94882931736373057328698625 71162198802279792996523969)
    ·
      refine ⟨53371649101709844747392977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71162198802279792996523969 53371649101709844747392977)
      ·
        refine ⟨40028736826282383560544733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53371649101709844747392977 40028736826282383560544733)
        ·
          refine ⟨15010776309855893835204275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40028736826282383560544733 15010776309855893835204275)
          ·
            refine ⟨22516164464783840752806413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15010776309855893835204275 22516164464783840752806413)
            ·
              refine ⟨8443561674293940282302405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22516164464783840752806413 8443561674293940282302405)
              ·
                refine ⟨1583167813930113802931701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8443561674293940282302405 1583167813930113802931701)
                ·
                  refine ⟨148421982555948169024847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1583167813930113802931701 148421982555948169024847)
                  ·
                    rfl

theorem cell23_2601457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 5].length) (baseStart_2601457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601457 prefixEnd_2601457 := by exact prefixLift 2601457
  have htrace : WordTrace (prefixWord ++ tailWord_2601457) baseStart_2601457 baseEnd_2601457 := by
    simpa [prefixWord, tailWord_2601457, baseEnd_2601457] using wordTrace_append hprefix tailTrace_2601457
  have hstable : (prefixWord ++ tailWord_2601457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601457).length < 2 ^ (prefixWord ++ tailWord_2601457).sum := by decide
  have hdescent : baseEnd_2601457 < baseStart_2601457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601474 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2601474 : Nat := 118140960795 + 2601474 * 2 ^ 59
def prefixEnd_2601474 : Nat := 4983230072969 + 3 ^ 40 * 2601474 * 2
def baseEnd_2601474 : Nat := 148422952463851106079005

theorem tailTrace_2601474 : CollatzResearch.WordTrace tailWord_2601474 prefixEnd_2601474 148422952463851106079005 := by
  unfold tailWord_2601474
  simp only [CollatzResearch.WordTrace]
  refine ⟨23720887944327867308016869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63255701184874312821378317 23720887944327867308016869)
  ·
    refine ⟨4447666489561475120253163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23720887944327867308016869 4447666489561475120253163)
    ·
      refine ⟨6671499734342212680379745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4447666489561475120253163 6671499734342212680379745)
      ·
        refine ⟨5003624800756659510284809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6671499734342212680379745 5003624800756659510284809)
        ·
          refine ⟨3752718600567494632713607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5003624800756659510284809 3752718600567494632713607)
          ·
            refine ⟨5629077900851241949070411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3752718600567494632713607 5629077900851241949070411)
            ·
              refine ⟨8443616851276862923605617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5629077900851241949070411 8443616851276862923605617)
              ·
                refine ⟨6332712638457647192704213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8443616851276862923605617 6332712638457647192704213)
                ·
                  refine ⟨148422952463851106079005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6332712638457647192704213 148422952463851106079005)
                  ·
                    rfl

theorem cell23_2601474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2601474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601474 prefixEnd_2601474 := by exact prefixLift 2601474
  have htrace : WordTrace (prefixWord ++ tailWord_2601474) baseStart_2601474 baseEnd_2601474 := by
    simpa [prefixWord, tailWord_2601474, baseEnd_2601474] using wordTrace_append hprefix tailTrace_2601474
  have hstable : (prefixWord ++ tailWord_2601474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601474).length < 2 ^ (prefixWord ++ tailWord_2601474).sum := by decide
  have hdescent : baseEnd_2601474 < baseStart_2601474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601581 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 6]
def baseStart_2601581 : Nat := 118140960795 + 2601581 * 2 ^ 59
def prefixEnd_2601581 : Nat := 4983230072969 + 3 ^ 40 * 2601581 * 2
def baseEnd_2601581 : Nat := 148429057178299004008117

theorem tailTrace_2601581 : CollatzResearch.WordTrace tailWord_2601581 prefixEnd_2601581 148429057178299004008117 := by
  unfold tailWord_2601581
  simp only [CollatzResearch.WordTrace]
  refine ⟨94887454387923826506212597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63258302925282551004141731 94887454387923826506212597)
  ·
    refine ⟨8895698848867858734957431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94887454387923826506212597 8895698848867858734957431)
    ·
      refine ⟨13343548273301788102436147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8895698848867858734957431 13343548273301788102436147)
      ·
        refine ⟨20015322409952682153654221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13343548273301788102436147 20015322409952682153654221)
        ·
          refine ⟨7505745903732255807620333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20015322409952682153654221 7505745903732255807620333)
          ·
            refine ⟨2814654713899595927857625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7505745903732255807620333 2814654713899595927857625)
            ·
              refine ⟨2110991035424696945893219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2814654713899595927857625 2110991035424696945893219)
              ·
                refine ⟨3166486553137045418839829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110991035424696945893219 3166486553137045418839829)
                ·
                  refine ⟨148429057178299004008117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3166486553137045418839829 148429057178299004008117)
                  ·
                    rfl

theorem cell23_2601581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_2601581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601581 prefixEnd_2601581 := by exact prefixLift 2601581
  have htrace : WordTrace (prefixWord ++ tailWord_2601581) baseStart_2601581 baseEnd_2601581 := by
    simpa [prefixWord, tailWord_2601581, baseEnd_2601581] using wordTrace_append hprefix tailTrace_2601581
  have hstable : (prefixWord ++ tailWord_2601581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601581).length < 2 ^ (prefixWord ++ tailWord_2601581).sum := by decide
  have hdescent : baseEnd_2601581 < baseStart_2601581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601601 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_2601601 : Nat := 118140960795 + 2601601 * 2 ^ 59
def prefixEnd_2601601 : Nat := 4983230072969 + 3 ^ 40 * 2601601 * 2
def baseEnd_2601601 : Nat := 1335871784217780957822961

theorem tailTrace_2601601 : CollatzResearch.WordTrace tailWord_2601601 prefixEnd_2601601 1335871784217780957822961 := by
  unfold tailWord_2601601
  simp only [CollatzResearch.WordTrace]
  refine ⟨94888183847851369921940657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63258789231900913281293771 94888183847851369921940657)
  ·
    refine ⟨71166137885888527441455493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94888183847851369921940657 71166137885888527441455493)
    ·
      refine ⟨13343650853604098895272905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71166137885888527441455493 13343650853604098895272905)
      ·
        refine ⟨10007738140203074171454679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13343650853604098895272905 10007738140203074171454679)
        ·
          refine ⟨15011607210304611257182019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10007738140203074171454679 15011607210304611257182019)
          ·
            refine ⟨22517410815456916885773029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15011607210304611257182019 22517410815456916885773029)
            ·
              refine ⟨4222014527898171916082443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22517410815456916885773029 4222014527898171916082443)
              ·
                refine ⟨6333021791847257874123665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222014527898171916082443 6333021791847257874123665)
                ·
                  refine ⟨4749766343885443405592749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6333021791847257874123665 4749766343885443405592749)
                  ·
                    refine ⟨1781162378957041277097281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4749766343885443405592749 1781162378957041277097281)
                    ·
                      refine ⟨1335871784217780957822961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781162378957041277097281 1335871784217780957822961)
                      ·
                        rfl

theorem cell23_2601601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_2601601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601601 prefixEnd_2601601 := by exact prefixLift 2601601
  have htrace : WordTrace (prefixWord ++ tailWord_2601601) baseStart_2601601 baseEnd_2601601 := by
    simpa [prefixWord, tailWord_2601601, baseEnd_2601601] using wordTrace_append hprefix tailTrace_2601601
  have hstable : (prefixWord ++ tailWord_2601601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601601).length < 2 ^ (prefixWord ++ tailWord_2601601).sum := by decide
  have hdescent : baseEnd_2601601 < baseStart_2601601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601607 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 1, 6]
def baseStart_2601607 : Nat := 118140960795 + 2601607 * 2 ^ 59
def prefixEnd_2601607 : Nat := 4983230072969 + 3 ^ 40 * 2601607 * 2
def baseEnd_2601607 : Nat := 445291621700569311449311

theorem tailTrace_2601607 : CollatzResearch.WordTrace tailWord_2601607 prefixEnd_2601607 445291621700569311449311 := by
  unfold tailWord_2601607
  simp only [CollatzResearch.WordTrace]
  refine ⟨94888402685829632946659075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63258935123886421964439383 94888402685829632946659075)
  ·
    refine ⟨142332604028744449419988613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94888402685829632946659075 142332604028744449419988613)
    ·
      refine ⟨26687363255389584266247865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142332604028744449419988613 26687363255389584266247865)
      ·
        refine ⟨20015522441542188199685899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26687363255389584266247865 20015522441542188199685899)
        ·
          refine ⟨30023283662313282299528849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20015522441542188199685899 30023283662313282299528849)
          ·
            refine ⟨22517462746734961724646637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30023283662313282299528849 22517462746734961724646637)
            ·
              refine ⟨8444048530025610646742489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22517462746734961724646637 8444048530025610646742489)
              ·
                refine ⟨6333036397519207985056867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8444048530025610646742489 6333036397519207985056867)
                ·
                  refine ⟨9499554596278811977585301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6333036397519207985056867 9499554596278811977585301)
                  ·
                    refine ⟨445291621700569311449311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9499554596278811977585301 445291621700569311449311)
                    ·
                      rfl

theorem cell23_2601607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_2601607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601607 prefixEnd_2601607 := by exact prefixLift 2601607
  have htrace : WordTrace (prefixWord ++ tailWord_2601607) baseStart_2601607 baseEnd_2601607 := by
    simpa [prefixWord, tailWord_2601607, baseEnd_2601607] using wordTrace_append hprefix tailTrace_2601607
  have hstable : (prefixWord ++ tailWord_2601607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601607).length < 2 ^ (prefixWord ++ tailWord_2601607).sum := by decide
  have hdescent : baseEnd_2601607 < baseStart_2601607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601664 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 3]
def baseStart_2601664 : Nat := 118140960795 + 2601664 * 2 ^ 59
def prefixEnd_2601664 : Nat := 4983230072969 + 3 ^ 40 * 2601664 * 2
def baseEnd_2601664 : Nat := 1335904133499014211335171

theorem tailTrace_2601664 : CollatzResearch.WordTrace tailWord_2601664 prefixEnd_2601664 1335904133499014211335171 := by
  unfold tailWord_2601664
  simp only [CollatzResearch.WordTrace]
  refine ⟨47445240823311565840742023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63260321097748754454322697 47445240823311565840742023)
  ·
    refine ⟨71167861234967348761113035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47445240823311565840742023 71167861234967348761113035)
    ·
      refine ⟨106751791852451023141669553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71167861234967348761113035 106751791852451023141669553)
      ·
        refine ⟨80063843889338267356252165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106751791852451023141669553 80063843889338267356252165)
        ·
          refine ⟨15011970729250925129297281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80063843889338267356252165 15011970729250925129297281)
          ·
            refine ⟨11258978046938193846972961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15011970729250925129297281 11258978046938193846972961)
            ·
              refine ⟨8444233535203645385229721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11258978046938193846972961 8444233535203645385229721)
              ·
                refine ⟨6333175151402734038922291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8444233535203645385229721 6333175151402734038922291)
                ·
                  refine ⟨9499762727104101058383437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6333175151402734038922291 9499762727104101058383437)
                  ·
                    refine ⟨3562411022664037896893789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9499762727104101058383437 3562411022664037896893789)
                    ·
                      refine ⟨1335904133499014211335171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3562411022664037896893789 1335904133499014211335171)
                      ·
                        rfl

theorem cell23_2601664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_2601664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601664 prefixEnd_2601664 := by exact prefixLift 2601664
  have htrace : WordTrace (prefixWord ++ tailWord_2601664) baseStart_2601664 baseEnd_2601664 := by
    simpa [prefixWord, tailWord_2601664, baseEnd_2601664] using wordTrace_append hprefix tailTrace_2601664
  have hstable : (prefixWord ++ tailWord_2601664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601664).length < 2 ^ (prefixWord ++ tailWord_2601664).sum := by decide
  have hdescent : baseEnd_2601664 < baseStart_2601664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601668 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_2601668 : Nat := 118140960795 + 2601668 * 2 ^ 59
def prefixEnd_2601668 : Nat := 4983230072969 + 3 ^ 40 * 2601668 * 2
def baseEnd_2601668 : Nat := 1335906187421632195685153

theorem tailTrace_2601668 : CollatzResearch.WordTrace tailWord_2601668 prefixEnd_2601668 1335906187421632195685153 := by
  unfold tailWord_2601668
  simp only [CollatzResearch.WordTrace]
  refine ⟨47445313769304320182314829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63260418359072426909753105 47445313769304320182314829)
  ·
    refine ⟨17791992663489120068368061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47445313769304320182314829 17791992663489120068368061)
    ·
      refine ⟨6671997248808420025638023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17791992663489120068368061 6671997248808420025638023)
      ·
        refine ⟨10007995873212630038457035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6671997248808420025638023 10007995873212630038457035)
        ·
          refine ⟨15011993809818945057685553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10007995873212630038457035 15011993809818945057685553)
          ·
            refine ⟨11258995357364208793264165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15011993809818945057685553 11258995357364208793264165)
            ·
              refine ⟨2111061629505789148737031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11258995357364208793264165 2111061629505789148737031)
              ·
                refine ⟨3166592444258683723105547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111061629505789148737031 3166592444258683723105547)
                ·
                  refine ⟨4749888666388025584658321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3166592444258683723105547 4749888666388025584658321)
                  ·
                    refine ⟨3562416499791019188493741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4749888666388025584658321 3562416499791019188493741)
                    ·
                      refine ⟨1335906187421632195685153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3562416499791019188493741 1335906187421632195685153)
                      ·
                        rfl

theorem cell23_2601668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_2601668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601668 prefixEnd_2601668 := by exact prefixLift 2601668
  have htrace : WordTrace (prefixWord ++ tailWord_2601668) baseStart_2601668 baseEnd_2601668 := by
    simpa [prefixWord, tailWord_2601668, baseEnd_2601668] using wordTrace_append hprefix tailTrace_2601668
  have hstable : (prefixWord ++ tailWord_2601668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601668).length < 2 ^ (prefixWord ++ tailWord_2601668).sum := by decide
  have hdescent : baseEnd_2601668 < baseStart_2601668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601707 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 5]
def baseStart_2601707 : Nat := 118140960795 + 2601707 * 2 ^ 59
def prefixEnd_2601707 : Nat := 4983230072969 + 3 ^ 40 * 2601707 * 2
def baseEnd_2601707 : Nat := 1335926213167157543097473

theorem tailTrace_2601707 : CollatzResearch.WordTrace tailWord_2601707 prefixEnd_2601707 1335926213167157543097473 := by
  unfold tailWord_2601707
  simp only [CollatzResearch.WordTrace]
  refine ⟨94892049985467350025299375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63261366656978233350199583 94892049985467350025299375)
  ·
    refine ⟨142338074978201025037949063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94892049985467350025299375 142338074978201025037949063)
    ·
      refine ⟨213507112467301537556923595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142338074978201025037949063 213507112467301537556923595)
      ·
        refine ⟨320260668700952306335385393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213507112467301537556923595 320260668700952306335385393)
        ·
          refine ⟨240195501525714229751539045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320260668700952306335385393 240195501525714229751539045)
          ·
            refine ⟨45036656536071418078413571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240195501525714229751539045 45036656536071418078413571)
            ·
              refine ⟨67554984804107127117620357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45036656536071418078413571 67554984804107127117620357)
              ·
                refine ⟨12666559650770086334553817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67554984804107127117620357 12666559650770086334553817)
                ·
                  refine ⟨9499919738077564750915363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12666559650770086334553817 9499919738077564750915363)
                  ·
                    refine ⟨14249879607116347126373045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9499919738077564750915363 14249879607116347126373045)
                    ·
                      refine ⟨1335926213167157543097473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14249879607116347126373045 1335926213167157543097473)
                      ·
                        rfl

theorem cell23_2601707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 5].length) (baseStart_2601707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601707 prefixEnd_2601707 := by exact prefixLift 2601707
  have htrace : WordTrace (prefixWord ++ tailWord_2601707) baseStart_2601707 baseEnd_2601707 := by
    simpa [prefixWord, tailWord_2601707, baseEnd_2601707] using wordTrace_append hprefix tailTrace_2601707
  have hstable : (prefixWord ++ tailWord_2601707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601707).length < 2 ^ (prefixWord ++ tailWord_2601707).sum := by decide
  have hdescent : baseEnd_2601707 < baseStart_2601707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601716 : List Nat := [2, 6, 1, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2601716 : Nat := 118140960795 + 2601716 * 2 ^ 59
def prefixEnd_2601716 : Nat := 4983230072969 + 3 ^ 40 * 2601716 * 2
def baseEnd_2601716 : Nat := 1335930834493048007884933

theorem tailTrace_2601716 : CollatzResearch.WordTrace tailWord_2601716 prefixEnd_2601716 1335930834493048007884933 := by
  unfold tailWord_2601716
  simp only [CollatzResearch.WordTrace]
  refine ⟨47446189121217372281188501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63261585494956496374918001 47446189121217372281188501)
  ·
    refine ⟨2224040115057064325680711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47446189121217372281188501 2224040115057064325680711)
    ·
      refine ⟨3336060172585596488521067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224040115057064325680711 3336060172585596488521067)
      ·
        refine ⟨5004090258878394732781601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3336060172585596488521067 5004090258878394732781601)
        ·
          refine ⟨3753067694158796049586201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5004090258878394732781601 3753067694158796049586201)
          ·
            refine ⟨2814800770619097037189651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3753067694158796049586201 2814800770619097037189651)
            ·
              refine ⟨4222201155928645555784477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814800770619097037189651 4222201155928645555784477)
              ·
                refine ⟨1583325433473242083419179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4222201155928645555784477 1583325433473242083419179)
                ·
                  refine ⟨2374988150209863125128769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583325433473242083419179 2374988150209863125128769)
                  ·
                    refine ⟨1781241112657397343846577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2374988150209863125128769 1781241112657397343846577)
                    ·
                      refine ⟨1335930834493048007884933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781241112657397343846577 1335930834493048007884933)
                      ·
                        rfl

theorem cell23_2601716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2601716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601716 prefixEnd_2601716 := by exact prefixLift 2601716
  have htrace : WordTrace (prefixWord ++ tailWord_2601716) baseStart_2601716 baseEnd_2601716 := by
    simpa [prefixWord, tailWord_2601716, baseEnd_2601716] using wordTrace_append hprefix tailTrace_2601716
  have hstable : (prefixWord ++ tailWord_2601716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601716).length < 2 ^ (prefixWord ++ tailWord_2601716).sum := by decide
  have hdescent : baseEnd_2601716 < baseStart_2601716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601724 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_2601724 : Nat := 118140960795 + 2601724 * 2 ^ 59
def prefixEnd_2601724 : Nat := 4983230072969 + 3 ^ 40 * 2601724 * 2
def baseEnd_2601724 : Nat := 1335934942338283976584895

theorem tailTrace_2601724 : CollatzResearch.WordTrace tailWord_2601724 prefixEnd_2601724 1335934942338283976584895 := by
  unfold tailWord_2601724
  simp only [CollatzResearch.WordTrace]
  refine ⟨47446335013202880964334113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63261780017603841285778817 47446335013202880964334113)
  ·
    refine ⟨35584751259902160723250585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47446335013202880964334113 35584751259902160723250585)
    ·
      refine ⟨26688563444926620542437939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35584751259902160723250585 26688563444926620542437939)
      ·
        refine ⟨40032845167389930813656909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26688563444926620542437939 40032845167389930813656909)
        ·
          refine ⟨15012316937771224055121341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40032845167389930813656909 15012316937771224055121341)
          ·
            refine ⟨5629618851664209020670503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15012316937771224055121341 5629618851664209020670503)
            ·
              refine ⟨8444428277496313531005755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5629618851664209020670503 8444428277496313531005755)
              ·
                refine ⟨12666642416244470296508633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8444428277496313531005755 12666642416244470296508633)
                ·
                  refine ⟨9499981812183352722381475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12666642416244470296508633 9499981812183352722381475)
                  ·
                    refine ⟨14249972718275029083572213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9499981812183352722381475 14249972718275029083572213)
                    ·
                      refine ⟨1335934942338283976584895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14249972718275029083572213 1335934942338283976584895)
                      ·
                        rfl

theorem cell23_2601724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_2601724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601724 prefixEnd_2601724 := by exact prefixLift 2601724
  have htrace : WordTrace (prefixWord ++ tailWord_2601724) baseStart_2601724 baseEnd_2601724 := by
    simpa [prefixWord, tailWord_2601724, baseEnd_2601724] using wordTrace_append hprefix tailTrace_2601724
  have hstable : (prefixWord ++ tailWord_2601724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601724).length < 2 ^ (prefixWord ++ tailWord_2601724).sum := by decide
  have hdescent : baseEnd_2601724 < baseStart_2601724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601738 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_2601738 : Nat := 118140960795 + 2601738 * 2 ^ 59
def prefixEnd_2601738 : Nat := 4983230072969 + 3 ^ 40 * 2601738 * 2
def baseEnd_2601738 : Nat := 1335942131067446921809831

theorem tailTrace_2601738 : CollatzResearch.WordTrace tailWord_2601738 prefixEnd_2601738 1335942131067446921809831 := by
  unfold tailWord_2601738
  simp only [CollatzResearch.WordTrace]
  refine ⟨23723295162088760579919467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63262120432236694879785245 23723295162088760579919467)
  ·
    refine ⟨35584942743133140869879201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23723295162088760579919467 35584942743133140869879201)
    ·
      refine ⟨26688707057349855652409401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35584942743133140869879201 26688707057349855652409401)
      ·
        refine ⟨20016530293012391739307051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26688707057349855652409401 20016530293012391739307051)
        ·
          refine ⟨30024795439518587608960577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20016530293012391739307051 30024795439518587608960577)
          ·
            refine ⟨22518596579638940706720433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30024795439518587608960577 22518596579638940706720433)
            ·
              refine ⟨16888947434729205530040325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22518596579638940706720433 16888947434729205530040325)
              ·
                refine ⟨3166677644011726036882561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16888947434729205530040325 3166677644011726036882561)
                ·
                  refine ⟨2375008233008794527661921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3166677644011726036882561 2375008233008794527661921)
                  ·
                    refine ⟨1781256174756595895746441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2375008233008794527661921 1781256174756595895746441)
                    ·
                      refine ⟨1335942131067446921809831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781256174756595895746441 1335942131067446921809831)
                      ·
                        rfl

theorem cell23_2601738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_2601738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601738 prefixEnd_2601738 := by exact prefixLift 2601738
  have htrace : WordTrace (prefixWord ++ tailWord_2601738) baseStart_2601738 baseEnd_2601738 := by
    simpa [prefixWord, tailWord_2601738, baseEnd_2601738] using wordTrace_append hprefix tailTrace_2601738
  have hstable : (prefixWord ++ tailWord_2601738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601738).length < 2 ^ (prefixWord ++ tailWord_2601738).sum := by decide
  have hdescent : baseEnd_2601738 < baseStart_2601738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601754 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_2601754 : Nat := 118140960795 + 2601754 * 2 ^ 59
def prefixEnd_2601754 : Nat := 4983230072969 + 3 ^ 40 * 2601754 * 2
def baseEnd_2601754 : Nat := 1335950346757918859209757

theorem tailTrace_2601754 : CollatzResearch.WordTrace tailWord_2601754 prefixEnd_2601754 1335950346757918859209757 := by
  unfold tailWord_2601754
  simp only [CollatzResearch.WordTrace]
  refine ⟨23723441054074269263065079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63262509477531384701506877 23723441054074269263065079)
  ·
    refine ⟨35585161581111403894597619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23723441054074269263065079 35585161581111403894597619)
    ·
      refine ⟨53377742371667105841896429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35585161581111403894597619 53377742371667105841896429)
      ·
        refine ⟨20016653389375164690711161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53377742371667105841896429 20016653389375164690711161)
        ·
          refine ⟨15012490042031373518033371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20016653389375164690711161 15012490042031373518033371)
          ·
            refine ⟨22518735063047060277050057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15012490042031373518033371 22518735063047060277050057)
            ·
              refine ⟨16889051297285295207787543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22518735063047060277050057 16889051297285295207787543)
              ·
                refine ⟨25333576945927942811681315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16889051297285295207787543 25333576945927942811681315)
                ·
                  refine ⟨38000365418891914217521973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25333576945927942811681315 38000365418891914217521973)
                  ·
                    refine ⟨3562534258021116957892685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38000365418891914217521973 3562534258021116957892685)
                    ·
                      refine ⟨1335950346757918859209757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3562534258021116957892685 1335950346757918859209757)
                      ·
                        rfl

theorem cell23_2601754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_2601754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601754 prefixEnd_2601754 := by exact prefixLift 2601754
  have htrace : WordTrace (prefixWord ++ tailWord_2601754) baseStart_2601754 baseEnd_2601754 := by
    simpa [prefixWord, tailWord_2601754, baseEnd_2601754] using wordTrace_append hprefix tailTrace_2601754
  have hstable : (prefixWord ++ tailWord_2601754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601754).length < 2 ^ (prefixWord ++ tailWord_2601754).sum := by decide
  have hdescent : baseEnd_2601754 < baseStart_2601754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601828 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_2601828 : Nat := 118140960795 + 2601828 * 2 ^ 59
def prefixEnd_2601828 : Nat := 4983230072969 + 3 ^ 40 * 2601828 * 2
def baseEnd_2601828 : Nat := 1335988344326351569684417

theorem tailTrace_2601828 : CollatzResearch.WordTrace tailWord_2601828 prefixEnd_2601828 1335988344326351569684417 := by
  unfold tailWord_2601828
  simp only [CollatzResearch.WordTrace]
  refine ⟨47448231609014493845227069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63264308812019325126969425 47448231609014493845227069)
  ·
    refine ⟨17793086853380435191960151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47448231609014493845227069 17793086853380435191960151)
    ·
      refine ⟨26689630280070652787940227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17793086853380435191960151 26689630280070652787940227)
      ·
        refine ⟨40034445420105979181910341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26689630280070652787940227 40034445420105979181910341)
        ·
          refine ⟨7506458516269871096608189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40034445420105979181910341 7506458516269871096608189)
          ·
            refine ⟨2814921943601201661228071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7506458516269871096608189 2814921943601201661228071)
            ·
              refine ⟨4222382915401802491842107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814921943601201661228071 4222382915401802491842107)
              ·
                refine ⟨6333574373102703737763161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222382915401802491842107 6333574373102703737763161)
                ·
                  refine ⟨4750180779827027803322371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6333574373102703737763161 4750180779827027803322371)
                  ·
                    refine ⟨7125271169740541704983557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4750180779827027803322371 7125271169740541704983557)
                    ·
                      refine ⟨1335988344326351569684417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7125271169740541704983557 1335988344326351569684417)
                      ·
                        rfl

theorem cell23_2601828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_2601828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601828 prefixEnd_2601828 := by exact prefixLift 2601828
  have htrace : WordTrace (prefixWord ++ tailWord_2601828) baseStart_2601828 baseEnd_2601828 := by
    simpa [prefixWord, tailWord_2601828, baseEnd_2601828] using wordTrace_append hprefix tailTrace_2601828
  have hstable : (prefixWord ++ tailWord_2601828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601828).length < 2 ^ (prefixWord ++ tailWord_2601828).sum := by decide
  have hdescent : baseEnd_2601828 < baseStart_2601828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601831 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_2601831 : Nat := 118140960795 + 2601831 * 2 ^ 59
def prefixEnd_2601831 : Nat := 4983230072969 + 3 ^ 40 * 2601831 * 2
def baseEnd_2601831 : Nat := 1335989884768315057946903

theorem tailTrace_2601831 : CollatzResearch.WordTrace tailWord_2601831 prefixEnd_2601831 1335989884768315057946903 := by
  unfold tailWord_2601831
  simp only [CollatzResearch.WordTrace]
  refine ⟨94896572637018119202813347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63264381758012079468542231 94896572637018119202813347)
  ·
    refine ⟨142344858955527178804220021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94896572637018119202813347 142344858955527178804220021)
    ·
      refine ⟨13344830527080673012895627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142344858955527178804220021 13344830527080673012895627)
      ·
        refine ⟨20017245790621009519343441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13344830527080673012895627 20017245790621009519343441)
        ·
          refine ⟨15012934342965757139507581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20017245790621009519343441 15012934342965757139507581)
          ·
            refine ⟨5629850378612158927315343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15012934342965757139507581 5629850378612158927315343)
            ·
              refine ⟨8444775567918238390973015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5629850378612158927315343 8444775567918238390973015)
              ·
                refine ⟨12667163351877357586459523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8444775567918238390973015 12667163351877357586459523)
                ·
                  refine ⟨19000745027816036379689285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12667163351877357586459523 19000745027816036379689285)
                  ·
                    refine ⟨3562639692715506821191741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19000745027816036379689285 3562639692715506821191741)
                    ·
                      refine ⟨1335989884768315057946903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3562639692715506821191741 1335989884768315057946903)
                      ·
                        rfl

theorem cell23_2601831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_2601831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601831 prefixEnd_2601831 := by exact prefixLift 2601831
  have htrace : WordTrace (prefixWord ++ tailWord_2601831) baseStart_2601831 baseEnd_2601831 := by
    simpa [prefixWord, tailWord_2601831, baseEnd_2601831] using wordTrace_append hprefix tailTrace_2601831
  have hstable : (prefixWord ++ tailWord_2601831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601831).length < 2 ^ (prefixWord ++ tailWord_2601831).sum := by decide
  have hdescent : baseEnd_2601831 < baseStart_2601831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601905 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 2, 3, 2]
def baseStart_2601905 : Nat := 118140960795 + 2601905 * 2 ^ 59
def prefixEnd_2601905 : Nat := 4983230072969 + 3 ^ 40 * 2601905 * 2
def baseEnd_2601905 : Nat := 1336027882336747768421563

theorem tailTrace_2601905 : CollatzResearch.WordTrace tailWord_2601905 prefixEnd_2601905 1336027882336747768421563 := by
  unfold tailWord_2601905
  simp only [CollatzResearch.WordTrace]
  refine ⟨94899271638750029841007169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63266181092500019894004779 94899271638750029841007169)
  ·
    refine ⟨71174453729062522380755377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94899271638750029841007169 71174453729062522380755377)
    ·
      refine ⟨53380840296796891785566533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71174453729062522380755377 53380840296796891785566533)
      ·
        refine ⟨10008907555649417209793725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53380840296796891785566533 10008907555649417209793725)
        ·
          refine ⟨3753340333368531453672647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10008907555649417209793725 3753340333368531453672647)
          ·
            refine ⟨5630010500052797180508971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753340333368531453672647 5630010500052797180508971)
            ·
              refine ⟨8445015750079195770763457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5630010500052797180508971 8445015750079195770763457)
              ·
                refine ⟨6333761812559396828072593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8445015750079195770763457 6333761812559396828072593)
                ·
                  refine ⟨4750321359419547621054445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6333761812559396828072593 4750321359419547621054445)
                  ·
                    refine ⟨1781370509782330357895417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4750321359419547621054445 1781370509782330357895417)
                    ·
                      refine ⟨1336027882336747768421563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781370509782330357895417 1336027882336747768421563)
                      ·
                        rfl

theorem cell23_2601905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_2601905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601905 prefixEnd_2601905 := by exact prefixLift 2601905
  have htrace : WordTrace (prefixWord ++ tailWord_2601905) baseStart_2601905 baseEnd_2601905 := by
    simpa [prefixWord, tailWord_2601905, baseEnd_2601905] using wordTrace_append hprefix tailTrace_2601905
  have hstable : (prefixWord ++ tailWord_2601905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601905).length < 2 ^ (prefixWord ++ tailWord_2601905).sum := by decide
  have hdescent : baseEnd_2601905 < baseStart_2601905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601911 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 4, 4]
def baseStart_2601911 : Nat := 118140960795 + 2601911 * 2 ^ 59
def prefixEnd_2601911 : Nat := 4983230072969 + 3 ^ 40 * 2601911 * 2
def baseEnd_2601911 : Nat := 445343654406891581648845

theorem tailTrace_2601911 : CollatzResearch.WordTrace tailWord_2601911 prefixEnd_2601911 445343654406891581648845 := by
  unfold tailWord_2601911
  simp only [CollatzResearch.WordTrace]
  refine ⟨94899490476728292865725587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63266326984485528577150391 94899490476728292865725587)
  ·
    refine ⟨142349235715092439298588381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94899490476728292865725587 142349235715092439298588381)
    ·
      refine ⟨53380963393159664736970643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142349235715092439298588381 53380963393159664736970643)
      ·
        refine ⟨80071445089739497105455965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53380963393159664736970643 80071445089739497105455965)
        ·
          refine ⟨30026791908652311414545987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80071445089739497105455965 30026791908652311414545987)
          ·
            refine ⟨45040187862978467121818981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30026791908652311414545987 45040187862978467121818981)
            ·
              refine ⟨8445035224308462585341059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45040187862978467121818981 8445035224308462585341059)
              ·
                refine ⟨12667552836462693878011589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8445035224308462585341059 12667552836462693878011589)
                ·
                  refine ⟨2375166156836755102127173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12667552836462693878011589 2375166156836755102127173)
                  ·
                    refine ⟨445343654406891581648845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2375166156836755102127173 445343654406891581648845)
                    ·
                      rfl

theorem cell23_2601911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_2601911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601911 prefixEnd_2601911 := by exact prefixLift 2601911
  have htrace : WordTrace (prefixWord ++ tailWord_2601911) baseStart_2601911 baseEnd_2601911 := by
    simpa [prefixWord, tailWord_2601911, baseEnd_2601911] using wordTrace_append hprefix tailTrace_2601911
  have hstable : (prefixWord ++ tailWord_2601911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601911).length < 2 ^ (prefixWord ++ tailWord_2601911).sum := by decide
  have hdescent : baseEnd_2601911 < baseStart_2601911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601912 : List Nat := [2, 1, 2, 1, 2, 5, 3, 2, 1, 1, 3]
def baseStart_2601912 : Nat := 118140960795 + 2601912 * 2 ^ 59
def prefixEnd_2601912 : Nat := 4983230072969 + 3 ^ 40 * 2601912 * 2
def baseEnd_2601912 : Nat := 1336031476701329241034031

theorem tailTrace_2601912 : CollatzResearch.WordTrace tailWord_2601912 prefixEnd_2601912 1336031476701329241034031 := by
  unfold tailWord_2601912
  simp only [CollatzResearch.WordTrace]
  refine ⟨47449763474862335018255995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63266351299816446691007993 47449763474862335018255995)
  ·
    refine ⟨71174645212293502527383993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47449763474862335018255995 71174645212293502527383993)
    ·
      refine ⟨53380983909220126895537995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71174645212293502527383993 53380983909220126895537995)
      ·
        refine ⟨80071475863830190343306993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53380983909220126895537995 80071475863830190343306993)
        ·
          refine ⟨60053606897872642757480245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80071475863830190343306993 60053606897872642757480245)
          ·
            refine ⟨5630025646675560258513773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60053606897872642757480245 5630025646675560258513773)
            ·
              refine ⟨2111259617503335096942665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5630025646675560258513773 2111259617503335096942665)
              ·
                refine ⟨1583444713127501322706999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2111259617503335096942665 1583444713127501322706999)
                ·
                  refine ⟨2375167069691251984060499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583444713127501322706999 2375167069691251984060499)
                  ·
                    refine ⟨3562750604536877976090749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2375167069691251984060499 3562750604536877976090749)
                    ·
                      refine ⟨1336031476701329241034031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3562750604536877976090749 1336031476701329241034031)
                      ·
                        rfl

theorem cell23_2601912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 1, 1, 3].length) (baseStart_2601912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601912 prefixEnd_2601912 := by exact prefixLift 2601912
  have htrace : WordTrace (prefixWord ++ tailWord_2601912) baseStart_2601912 baseEnd_2601912 := by
    simpa [prefixWord, tailWord_2601912, baseEnd_2601912] using wordTrace_append hprefix tailTrace_2601912
  have hstable : (prefixWord ++ tailWord_2601912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601912).length < 2 ^ (prefixWord ++ tailWord_2601912).sum := by decide
  have hdescent : baseEnd_2601912 < baseStart_2601912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601914 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_2601914 : Nat := 118140960795 + 2601914 * 2 ^ 59
def prefixEnd_2601914 : Nat := 4983230072969 + 3 ^ 40 * 2601914 * 2
def baseEnd_2601914 : Nat := 1336032503662638233209021

theorem tailTrace_2601914 : CollatzResearch.WordTrace tailWord_2601914 prefixEnd_2601914 1336032503662638233209021 := by
  unfold tailWord_2601914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23724899973929356094521199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63266399930478282918723197 23724899973929356094521199)
  ·
    refine ⟨35587349960894034141781799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23724899973929356094521199 35587349960894034141781799)
    ·
      refine ⟨53381024941341051212672699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35587349960894034141781799 53381024941341051212672699)
      ·
        refine ⟨80071537412011576819009049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53381024941341051212672699 80071537412011576819009049)
        ·
          refine ⟨60053653059008682614256787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80071537412011576819009049 60053653059008682614256787)
          ·
            refine ⟨90080479588513023921385181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60053653059008682614256787 90080479588513023921385181)
            ·
              refine ⟨33780179845692383970519443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90080479588513023921385181 33780179845692383970519443)
              ·
                refine ⟨50670269768538575955779165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33780179845692383970519443 50670269768538575955779165)
                ·
                  refine ⟨19001351163201965983417187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50670269768538575955779165 19001351163201965983417187)
                  ·
                    refine ⟨28502026744802948975125781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19001351163201965983417187 28502026744802948975125781)
                    ·
                      refine ⟨1336032503662638233209021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28502026744802948975125781 1336032503662638233209021)
                      ·
                        rfl

theorem cell23_2601914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_2601914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601914 prefixEnd_2601914 := by exact prefixLift 2601914
  have htrace : WordTrace (prefixWord ++ tailWord_2601914) baseStart_2601914 baseEnd_2601914 := by
    simpa [prefixWord, tailWord_2601914, baseEnd_2601914] using wordTrace_append hprefix tailTrace_2601914
  have hstable : (prefixWord ++ tailWord_2601914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601914).length < 2 ^ (prefixWord ++ tailWord_2601914).sum := by decide
  have hdescent : baseEnd_2601914 < baseStart_2601914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601955 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 1, 2, 3]
def baseStart_2601955 : Nat := 118140960795 + 2601955 * 2 ^ 59
def prefixEnd_2601955 : Nat := 4983230072969 + 3 ^ 40 * 2601955 * 2
def baseEnd_2601955 : Nat := 1336053556369472572796333

theorem tailTrace_2601955 : CollatzResearch.WordTrace tailWord_2601955 prefixEnd_2601955 1336053556369472572796333 := by
  unfold tailWord_2601955
  simp only [CollatzResearch.WordTrace]
  refine ⟨94901095288568888380327319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63267396859045925586884879 94901095288568888380327319)
  ·
    refine ⟨142351642932853332570490979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94901095288568888380327319 142351642932853332570490979)
    ·
      refine ⟨213527464399279998855736469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142351642932853332570490979 213527464399279998855736469)
      ·
        refine ⟨10009099893716249946362647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 213527464399279998855736469 10009099893716249946362647)
        ·
          refine ⟨15013649840574374919543971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10009099893716249946362647 15013649840574374919543971)
          ·
            refine ⟨22520474760861562379315957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15013649840574374919543971 22520474760861562379315957)
            ·
              refine ⟨2111294508830771473060871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22520474760861562379315957 2111294508830771473060871)
              ·
                refine ⟨3166941763246157209591307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111294508830771473060871 3166941763246157209591307)
                ·
                  refine ⟨4750412644869235814386961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3166941763246157209591307 4750412644869235814386961)
                  ·
                    refine ⟨3562809483651926860790221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4750412644869235814386961 3562809483651926860790221)
                    ·
                      refine ⟨1336053556369472572796333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3562809483651926860790221 1336053556369472572796333)
                      ·
                        rfl

theorem cell23_2601955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_2601955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601955 prefixEnd_2601955 := by exact prefixLift 2601955
  have htrace : WordTrace (prefixWord ++ tailWord_2601955) baseStart_2601955 baseEnd_2601955 := by
    simpa [prefixWord, tailWord_2601955, baseEnd_2601955] using wordTrace_append hprefix tailTrace_2601955
  have hstable : (prefixWord ++ tailWord_2601955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601955).length < 2 ^ (prefixWord ++ tailWord_2601955).sum := by decide
  have hdescent : baseEnd_2601955 < baseStart_2601955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601964 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2601964 : Nat := 118140960795 + 2601964 * 2 ^ 59
def prefixEnd_2601964 : Nat := 4983230072969 + 3 ^ 40 * 2601964 * 2
def baseEnd_2601964 : Nat := 1336058177695363037583791

theorem tailTrace_2601964 : CollatzResearch.WordTrace tailWord_2601964 prefixEnd_2601964 1336058177695363037583791 := by
  unfold tailWord_2601964
  simp only [CollatzResearch.WordTrace]
  refine ⟨47450711772768141458702473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63267615697024188611603297 47450711772768141458702473)
  ·
    refine ⟨35588033829576106094026855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47450711772768141458702473 35588033829576106094026855)
    ·
      refine ⟨53382050744364159141040283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35588033829576106094026855 53382050744364159141040283)
      ·
        refine ⟨80073076116546238711560425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53382050744364159141040283 80073076116546238711560425)
        ·
          refine ⟨60054807087409679033670319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80073076116546238711560425 60054807087409679033670319)
          ·
            refine ⟨90082210631114518550505479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60054807087409679033670319 90082210631114518550505479)
            ·
              refine ⟨135123315946671777825758219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90082210631114518550505479 135123315946671777825758219)
              ·
                refine ⟨202684973920007666738637329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135123315946671777825758219 202684973920007666738637329)
                ·
                  refine ⟨152013730440005750053977997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202684973920007666738637329 152013730440005750053977997)
                  ·
                    refine ⟨57005148915002156270241749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152013730440005750053977997 57005148915002156270241749)
                    ·
                      refine ⟨1336058177695363037583791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57005148915002156270241749 1336058177695363037583791)
                      ·
                        rfl

theorem cell23_2601964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2601964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601964 prefixEnd_2601964 := by exact prefixLift 2601964
  have htrace : WordTrace (prefixWord ++ tailWord_2601964) baseStart_2601964 baseEnd_2601964 := by
    simpa [prefixWord, tailWord_2601964, baseEnd_2601964] using wordTrace_append hprefix tailTrace_2601964
  have hstable : (prefixWord ++ tailWord_2601964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601964).length < 2 ^ (prefixWord ++ tailWord_2601964).sum := by decide
  have hdescent : baseEnd_2601964 < baseStart_2601964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601969 : List Nat := [1, 2, 2, 2, 4, 1, 4, 2, 1, 2, 2]
def baseStart_2601969 : Nat := 118140960795 + 2601969 * 2 ^ 59
def prefixEnd_2601969 : Nat := 4983230072969 + 3 ^ 40 * 2601969 * 2
def baseEnd_2601969 : Nat := 1336060745098635518021269

theorem tailTrace_2601969 : CollatzResearch.WordTrace tailWord_2601969 prefixEnd_2601969 1336060745098635518021269 := by
  unfold tailWord_2601969
  simp only [CollatzResearch.WordTrace]
  refine ⟨94901605910518168771336961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63267737273678779180891307 94901605910518168771336961)
  ·
    refine ⟨71176204432888626578502721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94901605910518168771336961 71176204432888626578502721)
    ·
      refine ⟨53382153324666469933877041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71176204432888626578502721 53382153324666469933877041)
      ·
        refine ⟨40036614993499852450407781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53382153324666469933877041 40036614993499852450407781)
        ·
          refine ⟨7506865311281222334451459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40036614993499852450407781 7506865311281222334451459)
          ·
            refine ⟨11260297966921833501677189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7506865311281222334451459 11260297966921833501677189)
            ·
              refine ⟨2111305868797843781564473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11260297966921833501677189 2111305868797843781564473)
              ·
                refine ⟨1583479401598382836173355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2111305868797843781564473 1583479401598382836173355)
                ·
                  refine ⟨2375219102397574254260033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583479401598382836173355 2375219102397574254260033)
                  ·
                    refine ⟨1781414326798180690695025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2375219102397574254260033 1781414326798180690695025)
                    ·
                      refine ⟨1336060745098635518021269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781414326798180690695025 1336060745098635518021269)
                      ·
                        rfl

theorem cell23_2601969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_2601969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601969 prefixEnd_2601969 := by exact prefixLift 2601969
  have htrace : WordTrace (prefixWord ++ tailWord_2601969) baseStart_2601969 baseEnd_2601969 := by
    simpa [prefixWord, tailWord_2601969, baseEnd_2601969] using wordTrace_append hprefix tailTrace_2601969
  have hstable : (prefixWord ++ tailWord_2601969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601969).length < 2 ^ (prefixWord ++ tailWord_2601969).sum := by decide
  have hdescent : baseEnd_2601969 < baseStart_2601969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601985 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_2601985 : Nat := 118140960795 + 2601985 * 2 ^ 59
def prefixEnd_2601985 : Nat := 4983230072969 + 3 ^ 40 * 2601985 * 2
def baseEnd_2601985 : Nat := 1336068960789107455421195

theorem tailTrace_2601985 : CollatzResearch.WordTrace tailWord_2601985 prefixEnd_2601985 1336068960789107455421195 := by
  unfold tailWord_2601985
  simp only [CollatzResearch.WordTrace]
  refine ⟨94902189478460203503919409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63268126318973469002612939 94902189478460203503919409)
  ·
    refine ⟨71176642108845152627939557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94902189478460203503919409 71176642108845152627939557)
    ·
      refine ⟨13345620395408466117738667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71176642108845152627939557 13345620395408466117738667)
      ·
        refine ⟨20018430593112699176608001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13345620395408466117738667 20018430593112699176608001)
        ·
          refine ⟨15013822944834524382456001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20018430593112699176608001 15013822944834524382456001)
          ·
            refine ⟨11260367208625893286842001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15013822944834524382456001 11260367208625893286842001)
            ·
              refine ⟨8445275406469419965131501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11260367208625893286842001 8445275406469419965131501)
              ·
                refine ⟨3166978277426032486924313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8445275406469419965131501 3166978277426032486924313)
                ·
                  refine ⟨2375233708069524365193235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3166978277426032486924313 2375233708069524365193235)
                  ·
                    refine ⟨3562850562104286547789853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2375233708069524365193235 3562850562104286547789853)
                    ·
                      refine ⟨1336068960789107455421195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3562850562104286547789853 1336068960789107455421195)
                      ·
                        rfl

theorem cell23_2601985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_2601985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601985 prefixEnd_2601985 := by exact prefixLift 2601985
  have htrace : WordTrace (prefixWord ++ tailWord_2601985) baseStart_2601985 baseEnd_2601985 := by
    simpa [prefixWord, tailWord_2601985, baseEnd_2601985] using wordTrace_append hprefix tailTrace_2601985
  have hstable : (prefixWord ++ tailWord_2601985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601985).length < 2 ^ (prefixWord ++ tailWord_2601985).sum := by decide
  have hdescent : baseEnd_2601985 < baseStart_2601985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2601991 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2601991 : Nat := 118140960795 + 2601991 * 2 ^ 59
def prefixEnd_2601991 : Nat := 4983230072969 + 3 ^ 40 * 2601991 * 2
def baseEnd_2601991 : Nat := 1336072041673034431946167

theorem tailTrace_2601991 : CollatzResearch.WordTrace tailWord_2601991 prefixEnd_2601991 1336072041673034431946167 := by
  unfold tailWord_2601991
  simp only [CollatzResearch.WordTrace]
  refine ⟨94902408316438466528637827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63268272210958977685758551 94902408316438466528637827)
  ·
    refine ⟨142353612474657699792956741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94902408316438466528637827 142353612474657699792956741)
    ·
      refine ⟨26691302338998318711179389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142353612474657699792956741 26691302338998318711179389)
      ·
        refine ⟨10009238377124369516692271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26691302338998318711179389 10009238377124369516692271)
        ·
          refine ⟨15013857565686554275038407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10009238377124369516692271 15013857565686554275038407)
          ·
            refine ⟨22520786348529831412557611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15013857565686554275038407 22520786348529831412557611)
            ·
              refine ⟨33781179522794747118836417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22520786348529831412557611 33781179522794747118836417)
              ·
                refine ⟨25335884642096060339127313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33781179522794747118836417 25335884642096060339127313)
                ·
                  refine ⟨19001913481572045254345485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25335884642096060339127313 19001913481572045254345485)
                  ·
                    refine ⟨7125717555589516970379557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19001913481572045254345485 7125717555589516970379557)
                    ·
                      refine ⟨1336072041673034431946167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7125717555589516970379557 1336072041673034431946167)
                      ·
                        rfl

theorem cell23_2601991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2601991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2601991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2601991 prefixEnd_2601991 := by exact prefixLift 2601991
  have htrace : WordTrace (prefixWord ++ tailWord_2601991) baseStart_2601991 baseEnd_2601991 := by
    simpa [prefixWord, tailWord_2601991, baseEnd_2601991] using wordTrace_append hprefix tailTrace_2601991
  have hstable : (prefixWord ++ tailWord_2601991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2601991).length < 2 ^ (prefixWord ++ tailWord_2601991).sum := by decide
  have hdescent : baseEnd_2601991 < baseStart_2601991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2601991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602012 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_2602012 : Nat := 118140960795 + 2602012 * 2 ^ 59
def prefixEnd_2602012 : Nat := 4983230072969 + 3 ^ 40 * 2602012 * 2
def baseEnd_2602012 : Nat := 1336082824766778849783571

theorem tailTrace_2602012 : CollatzResearch.WordTrace tailWord_2602012 prefixEnd_2602012 1336082824766778849783571 := by
  unfold tailWord_2602012
  simp only [CollatzResearch.WordTrace]
  refine ⟨47451587124681193557576145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63268782832908258076768193 47451587124681193557576145)
  ·
    refine ⟨35588690343510895168182109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47451587124681193557576145 35588690343510895168182109)
    ·
      refine ⟨13345758878816585688068291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35588690343510895168182109 13345758878816585688068291)
      ·
        refine ⟨20018638318224878532102437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13345758878816585688068291 20018638318224878532102437)
        ·
          refine ⟨3753494684667164724769207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20018638318224878532102437 3753494684667164724769207)
          ·
            refine ⟨5630242027000747087153811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753494684667164724769207 5630242027000747087153811)
            ·
              refine ⟨8445363040501120630730717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5630242027000747087153811 8445363040501120630730717)
              ·
                refine ⟨3167011140187920236524019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8445363040501120630730717 3167011140187920236524019)
                ·
                  refine ⟨4750516710281880354786029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3167011140187920236524019 4750516710281880354786029)
                  ·
                    refine ⟨1781443766355705133044761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4750516710281880354786029 1781443766355705133044761)
                    ·
                      refine ⟨1336082824766778849783571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781443766355705133044761 1336082824766778849783571)
                      ·
                        rfl

theorem cell23_2602012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_2602012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602012 prefixEnd_2602012 := by exact prefixLift 2602012
  have htrace : WordTrace (prefixWord ++ tailWord_2602012) baseStart_2602012 baseEnd_2602012 := by
    simpa [prefixWord, tailWord_2602012, baseEnd_2602012] using wordTrace_append hprefix tailTrace_2602012
  have hstable : (prefixWord ++ tailWord_2602012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602012).length < 2 ^ (prefixWord ++ tailWord_2602012).sum := by decide
  have hdescent : baseEnd_2602012 < baseStart_2602012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602021 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_2602021 : Nat := 118140960795 + 2602021 * 2 ^ 59
def prefixEnd_2602021 : Nat := 4983230072969 + 3 ^ 40 * 2602021 * 2
def baseEnd_2602021 : Nat := 1336087446092669314571029

theorem tailTrace_2602021 : CollatzResearch.WordTrace tailWord_2602021 prefixEnd_2602021 1336087446092669314571029 := by
  unfold tailWord_2602021
  simp only [CollatzResearch.WordTrace]
  refine ⟨94903502506329781652229917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63269001670886521101486611 94903502506329781652229917)
  ·
    refine ⟨35588813439873668119586219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94903502506329781652229917 35588813439873668119586219)
    ·
      refine ⟨53383220159810502179379329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35588813439873668119586219 53383220159810502179379329)
      ·
        refine ⟨40037415119857876634534497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53383220159810502179379329 40037415119857876634534497)
        ·
          refine ⟨30028061339893407475900873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40037415119857876634534497 30028061339893407475900873)
          ·
            refine ⟨22521046004920055606925655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30028061339893407475900873 22521046004920055606925655)
            ·
              refine ⟨33781569007380083410388483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22521046004920055606925655 33781569007380083410388483)
              ·
                refine ⟨50672353511070125115582725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33781569007380083410388483 50672353511070125115582725)
                ·
                  refine ⟨9501066283325648459171761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50672353511070125115582725 9501066283325648459171761)
                  ·
                    refine ⟨7125799712494236344378821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9501066283325648459171761 7125799712494236344378821)
                    ·
                      refine ⟨1336087446092669314571029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7125799712494236344378821 1336087446092669314571029)
                      ·
                        rfl

theorem cell23_2602021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_2602021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602021 prefixEnd_2602021 := by exact prefixLift 2602021
  have htrace : WordTrace (prefixWord ++ tailWord_2602021) baseStart_2602021 baseEnd_2602021 := by
    simpa [prefixWord, tailWord_2602021, baseEnd_2602021] using wordTrace_append hprefix tailTrace_2602021
  have hstable : (prefixWord ++ tailWord_2602021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602021).length < 2 ^ (prefixWord ++ tailWord_2602021).sum := by decide
  have hdescent : baseEnd_2602021 < baseStart_2602021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602071 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_2602071 : Nat := 118140960795 + 2602071 * 2 ^ 59
def prefixEnd_2602071 : Nat := 4983230072969 + 3 ^ 40 * 2602071 * 2
def baseEnd_2602071 : Nat := 1336113120125394118945799

theorem tailTrace_2602071 : CollatzResearch.WordTrace tailWord_2602071 prefixEnd_2602071 1336113120125394118945799 := by
  unfold tailWord_2602071
  simp only [CollatzResearch.WordTrace]
  refine ⟨94905326156148640191550067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63270217437432426794366711 94905326156148640191550067)
  ·
    refine ⟨142357989234222960287325101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94905326156148640191550067 142357989234222960287325101)
    ·
      refine ⟨53384245962833610107746913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142357989234222960287325101 53384245962833610107746913)
      ·
        refine ⟨40038184472125207580810185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53384245962833610107746913 40038184472125207580810185)
        ·
          refine ⟨30028638354093905685607639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40038184472125207580810185 30028638354093905685607639)
          ·
            refine ⟨45042957531140858528411459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30028638354093905685607639 45042957531140858528411459)
            ·
              refine ⟨67564436296711287792617189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45042957531140858528411459 67564436296711287792617189)
              ·
                refine ⟨12668331805633366461115723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67564436296711287792617189 12668331805633366461115723)
                ·
                  refine ⟨19002497708450049691673585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12668331805633366461115723 19002497708450049691673585)
                  ·
                    refine ⟨14251873281337537268755189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19002497708450049691673585 14251873281337537268755189)
                    ·
                      refine ⟨1336113120125394118945799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14251873281337537268755189 1336113120125394118945799)
                      ·
                        rfl

theorem cell23_2602071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_2602071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602071 prefixEnd_2602071 := by exact prefixLift 2602071
  have htrace : WordTrace (prefixWord ++ tailWord_2602071) baseStart_2602071 baseEnd_2602071 := by
    simpa [prefixWord, tailWord_2602071, baseEnd_2602071] using wordTrace_append hprefix tailTrace_2602071
  have hstable : (prefixWord ++ tailWord_2602071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602071).length < 2 ^ (prefixWord ++ tailWord_2602071).sum := by decide
  have hdescent : baseEnd_2602071 < baseStart_2602071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602098 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2602098 : Nat := 118140960795 + 2602098 * 2 ^ 59
def prefixEnd_2602098 : Nat := 4983230072969 + 3 ^ 40 * 2602098 * 2
def baseEnd_2602098 : Nat := 1336126984103065513308175

theorem tailTrace_2602098 : CollatzResearch.WordTrace tailWord_2602098 prefixEnd_2602098 1336126984103065513308175 := by
  unfold tailWord_2602098
  simp only [CollatzResearch.WordTrace]
  refine ⟨23726577731762705950695737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63270873951367215868521965 23726577731762705950695737)
  ·
    refine ⟨17794933298822029463021803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23726577731762705950695737 17794933298822029463021803)
    ·
      refine ⟨26692399948233044194532705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17794933298822029463021803 26692399948233044194532705)
      ·
        refine ⟨20019299961174783145899529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26692399948233044194532705 20019299961174783145899529)
        ·
          refine ⟨15014474970881087359424647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20019299961174783145899529 15014474970881087359424647)
          ·
            refine ⟨22521712456321631039136971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15014474970881087359424647 22521712456321631039136971)
            ·
              refine ⟨33782568684482446558705457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22521712456321631039136971 33782568684482446558705457)
              ·
                refine ⟨25336926513361834919029093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33782568684482446558705457 25336926513361834919029093)
                ·
                  refine ⟨4750673721255344047317955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25336926513361834919029093 4750673721255344047317955)
                  ·
                    refine ⟨7126010581883016070976933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4750673721255344047317955 7126010581883016070976933)
                    ·
                      refine ⟨1336126984103065513308175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7126010581883016070976933 1336126984103065513308175)
                      ·
                        rfl

theorem cell23_2602098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2602098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602098 prefixEnd_2602098 := by exact prefixLift 2602098
  have htrace : WordTrace (prefixWord ++ tailWord_2602098) baseStart_2602098 baseEnd_2602098 := by
    simpa [prefixWord, tailWord_2602098, baseEnd_2602098] using wordTrace_append hprefix tailTrace_2602098
  have hstable : (prefixWord ++ tailWord_2602098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602098).length < 2 ^ (prefixWord ++ tailWord_2602098).sum := by decide
  have hdescent : baseEnd_2602098 < baseStart_2602098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602108 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_2602108 : Nat := 118140960795 + 2602108 * 2 ^ 59
def prefixEnd_2602108 : Nat := 4983230072969 + 3 ^ 40 * 2602108 * 2
def baseEnd_2602108 : Nat := 445377372969870158061043

theorem tailTrace_2602108 : CollatzResearch.WordTrace tailWord_2602108 prefixEnd_2602108 445377372969870158061043 := by
  unfold tailWord_2602108
  simp only [CollatzResearch.WordTrace]
  refine ⟨47453337828507297755323489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63271117104676397007097985 47453337828507297755323489)
  ·
    refine ⟨35590003371380473316492617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47453337828507297755323489 35590003371380473316492617)
    ·
      refine ⟨26692502528535354987369463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35590003371380473316492617 26692502528535354987369463)
      ·
        refine ⟨40038753792803032481054195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26692502528535354987369463 40038753792803032481054195)
        ·
          refine ⟨60058130689204548721581293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40038753792803032481054195 60058130689204548721581293)
          ·
            refine ⟨22521799008451705770592985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60058130689204548721581293 22521799008451705770592985)
            ·
              refine ⟨16891349256338779327944739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22521799008451705770592985 16891349256338779327944739)
              ·
                refine ⟨25337023884508168991917109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16891349256338779327944739 25337023884508168991917109)
                ·
                  refine ⟨2375345989172640842992229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25337023884508168991917109 2375345989172640842992229)
                  ·
                    refine ⟨445377372969870158061043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2375345989172640842992229 445377372969870158061043)
                    ·
                      rfl

theorem cell23_2602108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_2602108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602108 prefixEnd_2602108 := by exact prefixLift 2602108
  have htrace : WordTrace (prefixWord ++ tailWord_2602108) baseStart_2602108 baseEnd_2602108 := by
    simpa [prefixWord, tailWord_2602108, baseEnd_2602108] using wordTrace_append hprefix tailTrace_2602108
  have hstable : (prefixWord ++ tailWord_2602108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602108).length < 2 ^ (prefixWord ++ tailWord_2602108).sum := by decide
  have hdescent : baseEnd_2602108 < baseStart_2602108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602135 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_2602135 : Nat := 118140960795 + 2602135 * 2 ^ 59
def prefixEnd_2602135 : Nat := 4983230072969 + 3 ^ 40 * 2602135 * 2
def baseEnd_2602135 : Nat := 1336145982887281868545505

theorem tailTrace_2602135 : CollatzResearch.WordTrace tailWord_2602135 prefixEnd_2602135 1336145982887281868545505 := by
  unfold tailWord_2602135
  simp only [CollatzResearch.WordTrace]
  refine ⟨94907660427916779121879859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63271773618611186081253239 94907660427916779121879859)
  ·
    refine ⟨142361490641875168682819789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94907660427916779121879859 142361490641875168682819789)
    ·
      refine ⟨53385558990703188256057421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142361490641875168682819789 53385558990703188256057421)
      ·
        refine ⟨20019584621513695596021533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53385558990703188256057421 20019584621513695596021533)
        ·
          refine ⟨7507344233067635848508075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20019584621513695596021533 7507344233067635848508075)
          ·
            refine ⟨11261016349601453772762113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7507344233067635848508075 11261016349601453772762113)
            ·
              refine ⟨8445762262201090329571585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11261016349601453772762113 8445762262201090329571585)
              ·
                refine ⟨6334321696650817747178689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8445762262201090329571585 6334321696650817747178689)
                ·
                  refine ⟨4750741272488113310384017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6334321696650817747178689 4750741272488113310384017)
                  ·
                    refine ⟨3563055954366084982788013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4750741272488113310384017 3563055954366084982788013)
                    ·
                      refine ⟨1336145982887281868545505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3563055954366084982788013 1336145982887281868545505)
                      ·
                        rfl

theorem cell23_2602135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_2602135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602135 prefixEnd_2602135 := by exact prefixLift 2602135
  have htrace : WordTrace (prefixWord ++ tailWord_2602135) baseStart_2602135 baseEnd_2602135 := by
    simpa [prefixWord, tailWord_2602135, baseEnd_2602135] using wordTrace_append hprefix tailTrace_2602135
  have hstable : (prefixWord ++ tailWord_2602135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602135).length < 2 ^ (prefixWord ++ tailWord_2602135).sum := by decide
  have hdescent : baseEnd_2602135 < baseStart_2602135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602166 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2602166 : Nat := 118140960795 + 2602166 * 2 ^ 59
def prefixEnd_2602166 : Nat := 4983230072969 + 3 ^ 40 * 2602166 * 2
def baseEnd_2602166 : Nat := 1336161900787571247257863

theorem tailTrace_2602166 : CollatzResearch.WordTrace tailWord_2602166 prefixEnd_2602166 1336161900787571247257863 := by
  unfold tailWord_2602166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5931799443175279463516147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63272527393869647610838901 5931799443175279463516147)
  ·
    refine ⟨8897699164762919195274221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5931799443175279463516147 8897699164762919195274221)
    ·
      refine ⟨3336637186786094698227833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8897699164762919195274221 3336637186786094698227833)
      ·
        refine ⟨2502477890089571023670875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3336637186786094698227833 2502477890089571023670875)
        ·
          refine ⟨3753716835134356535506313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2502477890089571023670875 3753716835134356535506313)
          ·
            refine ⟨2815287626350767401629735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3753716835134356535506313 2815287626350767401629735)
            ·
              refine ⟨4222931439526151102444603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815287626350767401629735 4222931439526151102444603)
              ·
                refine ⟨6334397159289226653666905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4222931439526151102444603 6334397159289226653666905)
                ·
                  refine ⟨4750797869466919990250179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6334397159289226653666905 4750797869466919990250179)
                  ·
                    refine ⟨7126196804200379985375269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4750797869466919990250179 7126196804200379985375269)
                    ·
                      refine ⟨1336161900787571247257863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7126196804200379985375269 1336161900787571247257863)
                      ·
                        rfl

theorem cell23_2602166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2602166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602166 prefixEnd_2602166 := by exact prefixLift 2602166
  have htrace : WordTrace (prefixWord ++ tailWord_2602166) baseStart_2602166 baseEnd_2602166 := by
    simpa [prefixWord, tailWord_2602166, baseEnd_2602166] using wordTrace_append hprefix tailTrace_2602166
  have hstable : (prefixWord ++ tailWord_2602166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602166).length < 2 ^ (prefixWord ++ tailWord_2602166).sum := by decide
  have hdescent : baseEnd_2602166 < baseStart_2602166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602208 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_2602208 : Nat := 118140960795 + 2602208 * 2 ^ 59
def prefixEnd_2602208 : Nat := 4983230072969 + 3 ^ 40 * 2602208 * 2
def baseEnd_2602208 : Nat := 1336183466975060082932669

theorem tailTrace_2602208 : CollatzResearch.WordTrace tailWord_2602208 prefixEnd_2602208 1336183466975060082932669 := by
  unfold tailWord_2602208
  simp only [CollatzResearch.WordTrace]
  refine ⟨47455161478326156294643639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63273548637768208392858185 47455161478326156294643639)
  ·
    refine ⟨71182742217489234441965459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47455161478326156294643639 71182742217489234441965459)
    ·
      refine ⟨106774113326233851662948189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71182742217489234441965459 106774113326233851662948189)
      ·
        refine ⟨40040292497337694373605571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106774113326233851662948189 40040292497337694373605571)
        ·
          refine ⟨60060438746006541560408357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40040292497337694373605571 60060438746006541560408357)
          ·
            refine ⟨11261332264876226542576567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60060438746006541560408357 11261332264876226542576567)
            ·
              refine ⟨16891998397314339813864851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11261332264876226542576567 16891998397314339813864851)
              ·
                refine ⟨25337997595971509720797277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16891998397314339813864851 25337997595971509720797277)
                ·
                  refine ⟨9501749098489316145298979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25337997595971509720797277 9501749098489316145298979)
                  ·
                    refine ⟨14252623647733974217948469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9501749098489316145298979 14252623647733974217948469)
                    ·
                      refine ⟨1336183466975060082932669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14252623647733974217948469 1336183466975060082932669)
                      ·
                        rfl

theorem cell23_2602208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_2602208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602208 prefixEnd_2602208 := by exact prefixLift 2602208
  have htrace : WordTrace (prefixWord ++ tailWord_2602208) baseStart_2602208 baseEnd_2602208 := by
    simpa [prefixWord, tailWord_2602208, baseEnd_2602208] using wordTrace_append hprefix tailTrace_2602208
  have hstable : (prefixWord ++ tailWord_2602208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602208).length < 2 ^ (prefixWord ++ tailWord_2602208).sum := by decide
  have hdescent : baseEnd_2602208 < baseStart_2602208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602325 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2602325 : Nat := 118140960795 + 2602325 * 2 ^ 59
def prefixEnd_2602325 : Nat := 4983230072969 + 3 ^ 40 * 2602325 * 2
def baseEnd_2602325 : Nat := 1336243544211636125169631

theorem tailTrace_2602325 : CollatzResearch.WordTrace tailWord_2602325 prefixEnd_2602325 1336243544211636125169631 := by
  unfold tailWord_2602325
  simp only [CollatzResearch.WordTrace]
  refine ⟨94914590297228441571296429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63276393531485627714197619 94914590297228441571296429)
  ·
    refine ⟨35592971361460665589236161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94914590297228441571296429 35592971361460665589236161)
    ·
      refine ⟨26694728521095499191927121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35592971361460665589236161 26694728521095499191927121)
      ·
        refine ⟨20021046390821624393945341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26694728521095499191927121 20021046390821624393945341)
        ·
          refine ⟨7507892396558109147729503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20021046390821624393945341 7507892396558109147729503)
          ·
            refine ⟨11261838594837163721594255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7507892396558109147729503 11261838594837163721594255)
            ·
              refine ⟨16892757892255745582391383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11261838594837163721594255 16892757892255745582391383)
              ·
                refine ⟨25339136838383618373587075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16892757892255745582391383 25339136838383618373587075)
                ·
                  refine ⟨38008705257575427560380613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25339136838383618373587075 38008705257575427560380613)
                  ·
                    refine ⟨7126632235795392667571365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38008705257575427560380613 7126632235795392667571365)
                    ·
                      refine ⟨1336243544211636125169631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7126632235795392667571365 1336243544211636125169631)
                      ·
                        rfl

theorem cell23_2602325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2602325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602325 prefixEnd_2602325 := by exact prefixLift 2602325
  have htrace : WordTrace (prefixWord ++ tailWord_2602325) baseStart_2602325 baseEnd_2602325 := by
    simpa [prefixWord, tailWord_2602325, baseEnd_2602325] using wordTrace_append hprefix tailTrace_2602325
  have hstable : (prefixWord ++ tailWord_2602325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602325).length < 2 ^ (prefixWord ++ tailWord_2602325).sum := by decide
  have hdescent : baseEnd_2602325 < baseStart_2602325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602329 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 2, 2, 2]
def baseStart_2602329 : Nat := 118140960795 + 2602329 * 2 ^ 59
def prefixEnd_2602329 : Nat := 4983230072969 + 3 ^ 40 * 2602329 * 2
def baseEnd_2602329 : Nat := 1336245598134254109519613

theorem tailTrace_2602329 : CollatzResearch.WordTrace tailWord_2602329 prefixEnd_2602329 1336245598134254109519613 := by
  unfold tailWord_2602329
  simp only [CollatzResearch.WordTrace]
  refine ⟨94914736189213950254442041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63276490792809300169628027 94914736189213950254442041)
  ·
    refine ⟨71186052141910462690831531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94914736189213950254442041 71186052141910462690831531)
    ·
      refine ⟨106779078212865694036247297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71186052141910462690831531 106779078212865694036247297)
      ·
        refine ⟨80084308659649270527185473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106779078212865694036247297 80084308659649270527185473)
        ·
          refine ⟨60063231494736952895389105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80084308659649270527185473 60063231494736952895389105)
          ·
            refine ⟨45047423621052714671541829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60063231494736952895389105 45047423621052714671541829)
            ·
              refine ⟨8446391928947384000914093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45047423621052714671541829 8446391928947384000914093)
              ·
                refine ⟨3167396973355269000342785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8446391928947384000914093 3167396973355269000342785)
                ·
                  refine ⟨2375547730016451750257089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3167396973355269000342785 2375547730016451750257089)
                  ·
                    refine ⟨1781660797512338812692817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2375547730016451750257089 1781660797512338812692817)
                    ·
                      refine ⟨1336245598134254109519613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781660797512338812692817 1336245598134254109519613)
                      ·
                        rfl

theorem cell23_2602329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_2602329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602329 prefixEnd_2602329 := by exact prefixLift 2602329
  have htrace : WordTrace (prefixWord ++ tailWord_2602329) baseStart_2602329 baseEnd_2602329 := by
    simpa [prefixWord, tailWord_2602329, baseEnd_2602329] using wordTrace_append hprefix tailTrace_2602329
  have hstable : (prefixWord ++ tailWord_2602329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602329).length < 2 ^ (prefixWord ++ tailWord_2602329).sum := by decide
  have hdescent : baseEnd_2602329 < baseStart_2602329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602350 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2602350 : Nat := 118140960795 + 2602350 * 2 ^ 59
def prefixEnd_2602350 : Nat := 4983230072969 + 3 ^ 40 * 2602350 * 2
def baseEnd_2602350 : Nat := 1336256381227998527357017

theorem tailTrace_2602350 : CollatzResearch.WordTrace tailWord_2602350 prefixEnd_2602350 1336256381227998527357017 := by
  unfold tailWord_2602350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11864437765267233855119563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63277001414758580560637669 11864437765267233855119563)
  ·
    refine ⟨17796656647900850782679345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11864437765267233855119563 17796656647900850782679345)
    ·
      refine ⟨13347492485925638087009509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17796656647900850782679345 13347492485925638087009509)
      ·
        refine ⟨2502654841111057141314283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13347492485925638087009509 2502654841111057141314283)
        ·
          refine ⟨3753982261666585711971425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2502654841111057141314283 3753982261666585711971425)
          ·
            refine ⟨2815486696249939283978569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3753982261666585711971425 2815486696249939283978569)
            ·
              refine ⟨2111615022187454462983927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2815486696249939283978569 2111615022187454462983927)
              ·
                refine ⟨3167422533281181694475891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111615022187454462983927 3167422533281181694475891)
                ·
                  refine ⟨4751133799921772541713837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3167422533281181694475891 4751133799921772541713837)
                  ·
                    refine ⟨1781675174970664703142689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4751133799921772541713837 1781675174970664703142689)
                    ·
                      refine ⟨1336256381227998527357017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781675174970664703142689 1336256381227998527357017)
                      ·
                        rfl

theorem cell23_2602350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2602350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602350 prefixEnd_2602350 := by exact prefixLift 2602350
  have htrace : WordTrace (prefixWord ++ tailWord_2602350) baseStart_2602350 baseEnd_2602350 := by
    simpa [prefixWord, tailWord_2602350, baseEnd_2602350] using wordTrace_append hprefix tailTrace_2602350
  have hstable : (prefixWord ++ tailWord_2602350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602350).length < 2 ^ (prefixWord ++ tailWord_2602350).sum := by decide
  have hdescent : baseEnd_2602350 < baseStart_2602350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602352 : List Nat := [2, 1, 1, 1, 4, 2, 4, 3, 5]
def baseStart_2602352 : Nat := 118140960795 + 2602352 * 2 ^ 59
def prefixEnd_2602352 : Nat := 4983230072969 + 3 ^ 40 * 2602352 * 2
def baseEnd_2602352 : Nat := 148473045354367502170223

theorem tailTrace_2602352 : CollatzResearch.WordTrace tailWord_2602352 prefixEnd_2602352 148473045354367502170223 := by
  unfold tailWord_2602352
  simp only [CollatzResearch.WordTrace]
  refine ⟨47457787534065312591264655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63277050045420416788352873 47457787534065312591264655)
  ·
    refine ⟨71186681301097968886896983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47457787534065312591264655 71186681301097968886896983)
    ·
      refine ⟨106780021951646953330345475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71186681301097968886896983 106780021951646953330345475)
      ·
        refine ⟨160170032927470429995518213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106780021951646953330345475 160170032927470429995518213)
        ·
          refine ⟨30031881173900705624159665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160170032927470429995518213 30031881173900705624159665)
          ·
            refine ⟨22523910880425529218119749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30031881173900705624159665 22523910880425529218119749)
            ·
              refine ⟨4223233290079786728397453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22523910880425529218119749 4223233290079786728397453)
              ·
                refine ⟨1583712483779920023149045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4223233290079786728397453 1583712483779920023149045)
                ·
                  refine ⟨148473045354367502170223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1583712483779920023149045 148473045354367502170223)
                  ·
                    rfl

theorem cell23_2602352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 5].length) (baseStart_2602352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602352 prefixEnd_2602352 := by exact prefixLift 2602352
  have htrace : WordTrace (prefixWord ++ tailWord_2602352) baseStart_2602352 baseEnd_2602352 := by
    simpa [prefixWord, tailWord_2602352, baseEnd_2602352] using wordTrace_append hprefix tailTrace_2602352
  have hstable : (prefixWord ++ tailWord_2602352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602352).length < 2 ^ (prefixWord ++ tailWord_2602352).sum := by decide
  have hdescent : baseEnd_2602352 < baseStart_2602352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602365 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_2602365 : Nat := 118140960795 + 2602365 * 2 ^ 59
def prefixEnd_2602365 : Nat := 4983230072969 + 3 ^ 40 * 2602365 * 2
def baseEnd_2602365 : Nat := 445421361145938656223149

theorem tailTrace_2602365 : CollatzResearch.WordTrace tailWord_2602365 prefixEnd_2602365 445421361145938656223149 := by
  unfold tailWord_2602365
  simp only [CollatzResearch.WordTrace]
  refine ⟨94916049217083528402752549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63277366144722352268501699 94916049217083528402752549)
  ·
    refine ⟨17796759228203161575516103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94916049217083528402752549 17796759228203161575516103)
    ·
      refine ⟨26695138842304742363274155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17796759228203161575516103 26695138842304742363274155)
      ·
        refine ⟨40042708263457113544911233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26695138842304742363274155 40042708263457113544911233)
        ·
          refine ⟨30032031197592835158683425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40042708263457113544911233 30032031197592835158683425)
          ·
            refine ⟨22524023398194626369012569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30032031197592835158683425 22524023398194626369012569)
            ·
              refine ⟨16893017548645969776759427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22524023398194626369012569 16893017548645969776759427)
              ·
                refine ⟨25339526322968954665139141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16893017548645969776759427 25339526322968954665139141)
                ·
                  refine ⟨4751161185556678999713589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25339526322968954665139141 4751161185556678999713589)
                  ·
                    refine ⟨445421361145938656223149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4751161185556678999713589 445421361145938656223149)
                    ·
                      rfl

theorem cell23_2602365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_2602365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602365 prefixEnd_2602365 := by exact prefixLift 2602365
  have htrace : WordTrace (prefixWord ++ tailWord_2602365) baseStart_2602365 baseEnd_2602365 := by
    simpa [prefixWord, tailWord_2602365, baseEnd_2602365] using wordTrace_append hprefix tailTrace_2602365
  have hstable : (prefixWord ++ tailWord_2602365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602365).length < 2 ^ (prefixWord ++ tailWord_2602365).sum := by decide
  have hdescent : baseEnd_2602365 < baseStart_2602365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602385 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_2602385 : Nat := 118140960795 + 2602385 * 2 ^ 59
def prefixEnd_2602385 : Nat := 4983230072969 + 3 ^ 40 * 2602385 * 2
def baseEnd_2602385 : Nat := 1336274353050905890419355

theorem tailTrace_2602385 : CollatzResearch.WordTrace tailWord_2602385 prefixEnd_2602385 1336274353050905890419355 := by
  unfold tailWord_2602385
  simp only [CollatzResearch.WordTrace]
  refine ⟨94916778677011071818480609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63277852451340714545653739 94916778677011071818480609)
  ·
    refine ⟨71187584007758303863860457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94916778677011071818480609 71187584007758303863860457)
    ·
      refine ⟨53390688005818727897895343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71187584007758303863860457 53390688005818727897895343)
      ·
        refine ⟨80086032008728091846843015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53390688005818727897895343 80086032008728091846843015)
        ·
          refine ⟨120129048013092137770264523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80086032008728091846843015 120129048013092137770264523)
          ·
            refine ⟨180193572019638206655396785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120129048013092137770264523 180193572019638206655396785)
            ·
              refine ⟨135145179014728654991547589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180193572019638206655396785 135145179014728654991547589)
              ·
                refine ⟨25339721065261622810915173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135145179014728654991547589 25339721065261622810915173)
                ·
                  refine ⟨4751197699736554277046595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25339721065261622810915173 4751197699736554277046595)
                  ·
                    refine ⟨7126796549604831415569893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4751197699736554277046595 7126796549604831415569893)
                    ·
                      refine ⟨1336274353050905890419355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7126796549604831415569893 1336274353050905890419355)
                      ·
                        rfl

theorem cell23_2602385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_2602385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602385 prefixEnd_2602385 := by exact prefixLift 2602385
  have htrace : WordTrace (prefixWord ++ tailWord_2602385) baseStart_2602385 baseEnd_2602385 := by
    simpa [prefixWord, tailWord_2602385, baseEnd_2602385] using wordTrace_append hprefix tailTrace_2602385
  have hstable : (prefixWord ++ tailWord_2602385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602385).length < 2 ^ (prefixWord ++ tailWord_2602385).sum := by decide
  have hdescent : baseEnd_2602385 < baseStart_2602385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602402 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2602402 : Nat := 118140960795 + 2602402 * 2 ^ 59
def prefixEnd_2602402 : Nat := 4983230072969 + 3 ^ 40 * 2602402 * 2
def baseEnd_2602402 : Nat := 1336283082222032323906777

theorem tailTrace_2602402 : CollatzResearch.WordTrace tailWord_2602402 prefixEnd_2602402 1336283082222032323906777 := by
  unfold tailWord_2602402
  simp only [CollatzResearch.WordTrace]
  refine ⟨23729349679487370930462365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63278265811966322481232973 23729349679487370930462365)
  ·
    refine ⟨8898506129807764098923387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23729349679487370930462365 8898506129807764098923387)
    ·
      refine ⟨13347759194711646148385081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8898506129807764098923387 13347759194711646148385081)
      ·
        refine ⟨10010819396033734611288811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13347759194711646148385081 10010819396033734611288811)
        ·
          refine ⟨15016229094050601916933217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10010819396033734611288811 15016229094050601916933217)
          ·
            refine ⟨11262171820537951437699913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15016229094050601916933217 11262171820537951437699913)
            ·
              refine ⟨8446628865403463578274935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11262171820537951437699913 8446628865403463578274935)
              ·
                refine ⟨12669943298105195367412403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8446628865403463578274935 12669943298105195367412403)
                ·
                  refine ⟨19004914947157793051118605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12669943298105195367412403 19004914947157793051118605)
                  ·
                    refine ⟨7126843105184172394169477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19004914947157793051118605 7126843105184172394169477)
                    ·
                      refine ⟨1336283082222032323906777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7126843105184172394169477 1336283082222032323906777)
                      ·
                        rfl

theorem cell23_2602402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2602402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602402 prefixEnd_2602402 := by exact prefixLift 2602402
  have htrace : WordTrace (prefixWord ++ tailWord_2602402) baseStart_2602402 baseEnd_2602402 := by
    simpa [prefixWord, tailWord_2602402, baseEnd_2602402] using wordTrace_append hprefix tailTrace_2602402
  have hstable : (prefixWord ++ tailWord_2602402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602402).length < 2 ^ (prefixWord ++ tailWord_2602402).sum := by decide
  have hdescent : baseEnd_2602402 < baseStart_2602402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602442 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 6]
def baseStart_2602442 : Nat := 118140960795 + 2602442 * 2 ^ 59
def prefixEnd_2602442 : Nat := 4983230072969 + 3 ^ 40 * 2602442 * 2
def baseEnd_2602442 : Nat := 148478180160912463045177

theorem tailTrace_2602442 : CollatzResearch.WordTrace tailWord_2602442 prefixEnd_2602442 148478180160912463045177 := by
  unfold tailWord_2602442
  simp only [CollatzResearch.WordTrace]
  refine ⟨23729714409451142638326395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63279238425203047035537053 23729714409451142638326395)
  ·
    refine ⟨35594571614176713957489593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23729714409451142638326395 35594571614176713957489593)
    ·
      refine ⟨26695928710632535468117195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35594571614176713957489593 26695928710632535468117195)
      ·
        refine ⟨40043893065948803202175793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26695928710632535468117195 40043893065948803202175793)
        ·
          refine ⟨30032919799461602401631845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40043893065948803202175793 30032919799461602401631845)
          ·
            refine ⟨5631172462399050450305971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30032919799461602401631845 5631172462399050450305971)
            ·
              refine ⟨8446758693598575675458957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5631172462399050450305971 8446758693598575675458957)
              ·
                refine ⟨3167534510099465878297109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8446758693598575675458957 3167534510099465878297109)
                ·
                  refine ⟨148478180160912463045177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3167534510099465878297109 148478180160912463045177)
                  ·
                    rfl

theorem cell23_2602442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_2602442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602442 prefixEnd_2602442 := by exact prefixLift 2602442
  have htrace : WordTrace (prefixWord ++ tailWord_2602442) baseStart_2602442 baseEnd_2602442 := by
    simpa [prefixWord, tailWord_2602442, baseEnd_2602442] using wordTrace_append hprefix tailTrace_2602442
  have hstable : (prefixWord ++ tailWord_2602442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602442).length < 2 ^ (prefixWord ++ tailWord_2602442).sum := by decide
  have hdescent : baseEnd_2602442 < baseStart_2602442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602479 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 2, 3, 2]
def baseStart_2602479 : Nat := 118140960795 + 2602479 * 2 ^ 59
def prefixEnd_2602479 : Nat := 4983230072969 + 3 ^ 40 * 2602479 * 2
def baseEnd_2602479 : Nat := 1336322620232428522643923

theorem tailTrace_2602479 : CollatzResearch.WordTrace tailWord_2602479 prefixEnd_2602479 1336322620232428522643923 := by
  unfold tailWord_2602479
  simp only [CollatzResearch.WordTrace]
  refine ⟨94920207138670525872402491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63280138092447017248268327 94920207138670525872402491)
  ·
    refine ⟨142380310708005788808603737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94920207138670525872402491 142380310708005788808603737)
    ·
      refine ⟨106785233031004341606452803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142380310708005788808603737 106785233031004341606452803)
      ·
        refine ⟨160177849546506512409679205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106785233031004341606452803 160177849546506512409679205)
        ·
          refine ⟨30033346789969971076814851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160177849546506512409679205 30033346789969971076814851)
          ·
            refine ⟨45050020184954956615222277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30033346789969971076814851 45050020184954956615222277)
            ·
              refine ⟨8446878784679054365354177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45050020184954956615222277 8446878784679054365354177)
              ·
                refine ⟨6335159088509290774015633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8446878784679054365354177 6335159088509290774015633)
                ·
                  refine ⟨4751369316381968080511725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6335159088509290774015633 4751369316381968080511725)
                  ·
                    refine ⟨1781763493643238030191897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4751369316381968080511725 1781763493643238030191897)
                    ·
                      refine ⟨1336322620232428522643923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781763493643238030191897 1336322620232428522643923)
                      ·
                        rfl

theorem cell23_2602479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 3, 2].length) (baseStart_2602479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602479 prefixEnd_2602479 := by exact prefixLift 2602479
  have htrace : WordTrace (prefixWord ++ tailWord_2602479) baseStart_2602479 baseEnd_2602479 := by
    simpa [prefixWord, tailWord_2602479, baseEnd_2602479] using wordTrace_append hprefix tailTrace_2602479
  have hstable : (prefixWord ++ tailWord_2602479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602479).length < 2 ^ (prefixWord ++ tailWord_2602479).sum := by decide
  have hdescent : baseEnd_2602479 < baseStart_2602479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602492 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_2602492 : Nat := 118140960795 + 2602492 * 2 ^ 59
def prefixEnd_2602492 : Nat := 4983230072969 + 3 ^ 40 * 2602492 * 2
def baseEnd_2602492 : Nat := 1336329295480936971781363

theorem tailTrace_2602492 : CollatzResearch.WordTrace tailWord_2602492 prefixEnd_2602492 1336329295480936971781363 := by
  unfold tailWord_2602492
  simp only [CollatzResearch.WordTrace]
  refine ⟨47460340643811714546312865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63280454191748952728417153 47460340643811714546312865)
  ·
    refine ⟨35595255482858785909734649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47460340643811714546312865 35595255482858785909734649)
    ·
      refine ⟨26696441612144089432300987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35595255482858785909734649 26696441612144089432300987)
      ·
        refine ⟨40044662418216134148451481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26696441612144089432300987 40044662418216134148451481)
        ·
          refine ⟨30033496813662100611338611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40044662418216134148451481 30033496813662100611338611)
          ·
            refine ⟨45050245220493150917007917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30033496813662100611338611 45050245220493150917007917)
            ·
              refine ⟨16893841957684931593877969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45050245220493150917007917 16893841957684931593877969)
              ·
                refine ⟨12670381468263698695408477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16893841957684931593877969 12670381468263698695408477)
                ·
                  refine ⟨4751393050598887010778179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12670381468263698695408477 4751393050598887010778179)
                  ·
                    refine ⟨7127089575898330516167269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4751393050598887010778179 7127089575898330516167269)
                    ·
                      refine ⟨1336329295480936971781363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7127089575898330516167269 1336329295480936971781363)
                      ·
                        rfl

theorem cell23_2602492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_2602492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602492 prefixEnd_2602492 := by exact prefixLift 2602492
  have htrace : WordTrace (prefixWord ++ tailWord_2602492) baseStart_2602492 baseEnd_2602492 := by
    simpa [prefixWord, tailWord_2602492, baseEnd_2602492] using wordTrace_append hprefix tailTrace_2602492
  have hstable : (prefixWord ++ tailWord_2602492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602492).length < 2 ^ (prefixWord ++ tailWord_2602492).sum := by decide
  have hdescent : baseEnd_2602492 < baseStart_2602492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602536 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 4, 4]
def baseStart_2602536 : Nat := 118140960795 + 2602536 * 2 ^ 59
def prefixEnd_2602536 : Nat := 4983230072969 + 3 ^ 40 * 2602536 * 2
def baseEnd_2602536 : Nat := 445450629543244933210387

theorem tailTrace_2602536 : CollatzResearch.WordTrace tailWord_2602536 prefixEnd_2602536 445450629543244933210387 := by
  unfold tailWord_2602536
  simp only [CollatzResearch.WordTrace]
  refine ⟨47461143049732012303613731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63281524066309349738151641 47461143049732012303613731)
  ·
    refine ⟨71191714574598018455420597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47461143049732012303613731 71191714574598018455420597)
    ·
      refine ⟨6674223241368564230195681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71191714574598018455420597 6674223241368564230195681)
      ·
        refine ⟨5005667431026423172646761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6674223241368564230195681 5005667431026423172646761)
        ·
          refine ⟨3754250573269817379485071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5005667431026423172646761 3754250573269817379485071)
          ·
            refine ⟨5631375859904726069227607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3754250573269817379485071 5631375859904726069227607)
            ·
              refine ⟨8447063789857089103841411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5631375859904726069227607 8447063789857089103841411)
              ·
                refine ⟨12670595684785633655762117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8447063789857089103841411 12670595684785633655762117)
                ·
                  refine ⟨2375736690897306310455397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12670595684785633655762117 2375736690897306310455397)
                  ·
                    refine ⟨445450629543244933210387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2375736690897306310455397 445450629543244933210387)
                    ·
                      rfl

theorem cell23_2602536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_2602536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602536 prefixEnd_2602536 := by exact prefixLift 2602536
  have htrace : WordTrace (prefixWord ++ tailWord_2602536) baseStart_2602536 baseEnd_2602536 := by
    simpa [prefixWord, tailWord_2602536, baseEnd_2602536] using wordTrace_append hprefix tailTrace_2602536
  have hstable : (prefixWord ++ tailWord_2602536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602536).length < 2 ^ (prefixWord ++ tailWord_2602536).sum := by decide
  have hdescent : baseEnd_2602536 < baseStart_2602536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602555 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 7]
def baseStart_2602555 : Nat := 118140960795 + 2602555 * 2 ^ 59
def prefixEnd_2602555 : Nat := 4983230072969 + 3 ^ 40 * 2602555 * 2
def baseEnd_2602555 : Nat := 1336361644762170225293573

theorem tailTrace_2602555 : CollatzResearch.WordTrace tailWord_2602555 prefixEnd_2602555 1336361644762170225293573 := by
  unfold tailWord_2602555
  simp only [CollatzResearch.WordTrace]
  refine ⟨94922979086395190852169119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63281986057596793901446079 94922979086395190852169119)
  ·
    refine ⟨142384468629592786278253679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94922979086395190852169119 142384468629592786278253679)
    ·
      refine ⟨213576702944389179417380519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142384468629592786278253679 213576702944389179417380519)
      ·
        refine ⟨320365054416583769126070779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213576702944389179417380519 320365054416583769126070779)
        ·
          refine ⟨480547581624875653689106169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320365054416583769126070779 480547581624875653689106169)
          ·
            refine ⟨360410686218656740266829627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480547581624875653689106169 360410686218656740266829627)
            ·
              refine ⟨540616029327985110400244441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360410686218656740266829627 540616029327985110400244441)
              ·
                refine ⟨405462021995988832800183331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540616029327985110400244441 405462021995988832800183331)
                ·
                  refine ⟨608193032993983249200274997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405462021995988832800183331 608193032993983249200274997)
                  ·
                    refine ⟨57018096843185929612525781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 608193032993983249200274997 57018096843185929612525781)
                    ·
                      refine ⟨1336361644762170225293573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57018096843185929612525781 1336361644762170225293573)
                      ·
                        rfl

theorem cell23_2602555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_2602555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602555 prefixEnd_2602555 := by exact prefixLift 2602555
  have htrace : WordTrace (prefixWord ++ tailWord_2602555) baseStart_2602555 baseEnd_2602555 := by
    simpa [prefixWord, tailWord_2602555, baseEnd_2602555] using wordTrace_append hprefix tailTrace_2602555
  have hstable : (prefixWord ++ tailWord_2602555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602555).length < 2 ^ (prefixWord ++ tailWord_2602555).sum := by decide
  have hdescent : baseEnd_2602555 < baseStart_2602555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602556 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_2602556 : Nat := 118140960795 + 2602556 * 2 ^ 59
def prefixEnd_2602556 : Nat := 4983230072969 + 3 ^ 40 * 2602556 * 2
def baseEnd_2602556 : Nat := 1336362158242824721381069

theorem tailTrace_2602556 : CollatzResearch.WordTrace tailWord_2602556 prefixEnd_2602556 1336362158242824721381069 := by
  unfold tailWord_2602556
  simp only [CollatzResearch.WordTrace]
  refine ⟨47461507779695784011477761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63282010372927712015303681 47461507779695784011477761)
  ·
    refine ⟨35596130834771838008608321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47461507779695784011477761 35596130834771838008608321)
    ·
      refine ⟨26697098126078878506456241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35596130834771838008608321 26697098126078878506456241)
      ·
        refine ⟨20022823594559158879842181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26697098126078878506456241 20022823594559158879842181)
        ·
          refine ⟨3754279423979842289970409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20022823594559158879842181 3754279423979842289970409)
          ·
            refine ⟨2815709567984881717477807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3754279423979842289970409 2815709567984881717477807)
            ·
              refine ⟨4223564351977322576216711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815709567984881717477807 4223564351977322576216711)
              ·
                refine ⟨6335346527965983864325067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223564351977322576216711 6335346527965983864325067)
                ·
                  refine ⟨9503019791948975796487601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6335346527965983864325067 9503019791948975796487601)
                  ·
                    refine ⟨7127264843961731847365701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9503019791948975796487601 7127264843961731847365701)
                    ·
                      refine ⟨1336362158242824721381069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7127264843961731847365701 1336362158242824721381069)
                      ·
                        rfl

theorem cell23_2602556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_2602556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602556 prefixEnd_2602556 := by exact prefixLift 2602556
  have htrace : WordTrace (prefixWord ++ tailWord_2602556) baseStart_2602556 baseEnd_2602556 := by
    simpa [prefixWord, tailWord_2602556, baseEnd_2602556] using wordTrace_append hprefix tailTrace_2602556
  have hstable : (prefixWord ++ tailWord_2602556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602556).length < 2 ^ (prefixWord ++ tailWord_2602556).sum := by decide
  have hdescent : baseEnd_2602556 < baseStart_2602556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602559 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 3]
def baseStart_2602559 : Nat := 118140960795 + 2602559 * 2 ^ 59
def prefixEnd_2602559 : Nat := 4983230072969 + 3 ^ 40 * 2602559 * 2
def baseEnd_2602559 : Nat := 1336363698684788209643555

theorem tailTrace_2602559 : CollatzResearch.WordTrace tailWord_2602559 prefixEnd_2602559 1336363698684788209643555 := by
  unfold tailWord_2602559
  simp only [CollatzResearch.WordTrace]
  refine ⟨94923124978380699535314731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63282083318920466356876487 94923124978380699535314731)
  ·
    refine ⟨142384687467571049302972097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94923124978380699535314731 142384687467571049302972097)
    ·
      refine ⟨106788515600678286977229073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142384687467571049302972097 106788515600678286977229073)
      ·
        refine ⟨80091386700508715232921805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106788515600678286977229073 80091386700508715232921805)
        ·
          refine ⟨30034270012690768212345677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80091386700508715232921805 30034270012690768212345677)
          ·
            refine ⟨11262851254759038079629629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30034270012690768212345677 11262851254759038079629629)
            ·
              refine ⟨4223569220534639279861111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11262851254759038079629629 4223569220534639279861111)
              ·
                refine ⟨6335353830801958919791667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223569220534639279861111 6335353830801958919791667)
                ·
                  refine ⟨9503030746202938379687501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6335353830801958919791667 9503030746202938379687501)
                  ·
                    refine ⟨3563636529826101892382813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9503030746202938379687501 3563636529826101892382813)
                    ·
                      refine ⟨1336363698684788209643555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3563636529826101892382813 1336363698684788209643555)
                      ·
                        rfl

theorem cell23_2602559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_2602559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602559 prefixEnd_2602559 := by exact prefixLift 2602559
  have htrace : WordTrace (prefixWord ++ tailWord_2602559) baseStart_2602559 baseEnd_2602559 := by
    simpa [prefixWord, tailWord_2602559, baseEnd_2602559] using wordTrace_append hprefix tailTrace_2602559
  have hstable : (prefixWord ++ tailWord_2602559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602559).length < 2 ^ (prefixWord ++ tailWord_2602559).sum := by decide
  have hdescent : baseEnd_2602559 < baseStart_2602559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602566 : List Nat := [6, 1, 1, 1, 3, 1, 1, 9]
def baseStart_2602566 : Nat := 118140960795 + 2602566 * 2 ^ 59
def prefixEnd_2602566 : Nat := 4983230072969 + 3 ^ 40 * 2602566 * 2
def baseEnd_2602566 : Nat := 49495084927754432676149

theorem tailTrace_2602566 : CollatzResearch.WordTrace tailWord_2602566 prefixEnd_2602566 49495084927754432676149 := by
  unfold tailWord_2602566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2966355634042354366588111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63282253526236893153879701 2966355634042354366588111)
  ·
    refine ⟨4449533451063531549882167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2966355634042354366588111 4449533451063531549882167)
    ·
      refine ⟨6674300176595297324823251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4449533451063531549882167 6674300176595297324823251)
      ·
        refine ⟨10011450264892945987234877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6674300176595297324823251 10011450264892945987234877)
        ·
          refine ⟨3754293849334854745213079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10011450264892945987234877 3754293849334854745213079)
          ·
            refine ⟨5631440774002282117819619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3754293849334854745213079 5631440774002282117819619)
            ·
              refine ⟨8447161161003423176729429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5631440774002282117819619 8447161161003423176729429)
              ·
                refine ⟨49495084927754432676149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8447161161003423176729429 49495084927754432676149)
                ·
                  rfl

theorem cell23_2602566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_2602566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602566 prefixEnd_2602566 := by exact prefixLift 2602566
  have htrace : WordTrace (prefixWord ++ tailWord_2602566) baseStart_2602566 baseEnd_2602566 := by
    simpa [prefixWord, tailWord_2602566, baseEnd_2602566] using wordTrace_append hprefix tailTrace_2602566
  have hstable : (prefixWord ++ tailWord_2602566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602566).length < 2 ^ (prefixWord ++ tailWord_2602566).sum := by decide
  have hdescent : baseEnd_2602566 < baseStart_2602566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602569 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 3, 3, 2]
def baseStart_2602569 : Nat := 118140960795 + 2602569 * 2 ^ 59
def prefixEnd_2602569 : Nat := 4983230072969 + 3 ^ 40 * 2602569 * 2
def baseEnd_2602569 : Nat := 1336368833491333170518509

theorem tailTrace_2602569 : CollatzResearch.WordTrace tailWord_2602569 prefixEnd_2602569 1336368833491333170518509 := by
  unfold tailWord_2602569
  simp only [CollatzResearch.WordTrace]
  refine ⟨94923489708344471243178761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63282326472229647495452507 94923489708344471243178761)
  ·
    refine ⟨71192617281258353432384071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94923489708344471243178761 71192617281258353432384071)
    ·
      refine ⟨106788925921887530148576107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71192617281258353432384071 106788925921887530148576107)
      ·
        refine ⟨160183388882831295222864161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106788925921887530148576107 160183388882831295222864161)
        ·
          refine ⟨120137541662123471417148121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160183388882831295222864161 120137541662123471417148121)
          ·
            refine ⟨90103156246592603562861091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120137541662123471417148121 90103156246592603562861091)
            ·
              refine ⟨135154734369888905344291637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90103156246592603562861091 135154734369888905344291637)
              ·
                refine ⟨12670756347177084876027341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135154734369888905344291637 12670756347177084876027341)
                ·
                  refine ⟨4751533630191406828510253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12670756347177084876027341 4751533630191406828510253)
                  ·
                    refine ⟨1781825111321777560691345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4751533630191406828510253 1781825111321777560691345)
                    ·
                      refine ⟨1336368833491333170518509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781825111321777560691345 1336368833491333170518509)
                      ·
                        rfl

theorem cell23_2602569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 3, 2].length) (baseStart_2602569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602569 prefixEnd_2602569 := by exact prefixLift 2602569
  have htrace : WordTrace (prefixWord ++ tailWord_2602569) baseStart_2602569 baseEnd_2602569 := by
    simpa [prefixWord, tailWord_2602569, baseEnd_2602569] using wordTrace_append hprefix tailTrace_2602569
  have hstable : (prefixWord ++ tailWord_2602569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602569).length < 2 ^ (prefixWord ++ tailWord_2602569).sum := by decide
  have hdescent : baseEnd_2602569 < baseStart_2602569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602572 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2602572 : Nat := 118140960795 + 2602572 * 2 ^ 59
def prefixEnd_2602572 : Nat := 4983230072969 + 3 ^ 40 * 2602572 * 2
def baseEnd_2602572 : Nat := 1336370373933296658780995

theorem tailTrace_2602572 : CollatzResearch.WordTrace tailWord_2602572 prefixEnd_2602572 1336370373933296658780995 := by
  unfold tailWord_2602572
  simp only [CollatzResearch.WordTrace]
  refine ⟨47461799563666801377768985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63282399418222401837025313 47461799563666801377768985)
  ·
    refine ⟨35596349672750101033326739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47461799563666801377768985 35596349672750101033326739)
    ·
      refine ⟨53394524509125151549990109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35596349672750101033326739 53394524509125151549990109)
      ·
        refine ⟨20022946690921931831246291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53394524509125151549990109 20022946690921931831246291)
        ·
          refine ⟨30034420036382897746869437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20022946690921931831246291 30034420036382897746869437)
          ·
            refine ⟨11262907513643586655076039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30034420036382897746869437 11262907513643586655076039)
            ·
              refine ⟨16894361270465379982614059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11262907513643586655076039 16894361270465379982614059)
              ·
                refine ⟨25341541905698069973921089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16894361270465379982614059 25341541905698069973921089)
                ·
                  refine ⟨19006156429273552480440817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25341541905698069973921089 19006156429273552480440817)
                  ·
                    refine ⟨14254617321955164360330613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19006156429273552480440817 14254617321955164360330613)
                    ·
                      refine ⟨1336370373933296658780995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14254617321955164360330613 1336370373933296658780995)
                      ·
                        rfl

theorem cell23_2602572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2602572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602572 prefixEnd_2602572 := by exact prefixLift 2602572
  have htrace : WordTrace (prefixWord ++ tailWord_2602572) baseStart_2602572 baseEnd_2602572 := by
    simpa [prefixWord, tailWord_2602572, baseEnd_2602572] using wordTrace_append hprefix tailTrace_2602572
  have hstable : (prefixWord ++ tailWord_2602572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602572).length < 2 ^ (prefixWord ++ tailWord_2602572).sum := by decide
  have hdescent : baseEnd_2602572 < baseStart_2602572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602610 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_2602610 : Nat := 118140960795 + 2602610 * 2 ^ 59
def prefixEnd_2602610 : Nat := 4983230072969 + 3 ^ 40 * 2602610 * 2
def baseEnd_2602610 : Nat := 1336389886198167510105821

theorem tailTrace_2602610 : CollatzResearch.WordTrace tailWord_2602610 prefixEnd_2602610 1336389886198167510105821 := by
  unfold tailWord_2602610
  simp only [CollatzResearch.WordTrace]
  refine ⟨23731246275298983811355321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63283323400797290163614189 23731246275298983811355321)
  ·
    refine ⟨17798434706474237858516491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23731246275298983811355321 17798434706474237858516491)
    ·
      refine ⟨26697652059711356787774737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17798434706474237858516491 26697652059711356787774737)
      ·
        refine ⟨20023239044783517590831053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26697652059711356787774737 20023239044783517590831053)
        ·
          refine ⟨7508714641793819096561645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20023239044783517590831053 7508714641793819096561645)
          ·
            refine ⟨2815767990672682161210617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7508714641793819096561645 2815767990672682161210617)
            ·
              refine ⟨2111825993004511620907963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2815767990672682161210617 2111825993004511620907963)
              ·
                refine ⟨3167738989506767431361945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111825993004511620907963 3167738989506767431361945)
                ·
                  refine ⟨2375804242130075573521459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3167738989506767431361945 2375804242130075573521459)
                  ·
                    refine ⟨3563706363195113360282189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2375804242130075573521459 3563706363195113360282189)
                    ·
                      refine ⟨1336389886198167510105821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3563706363195113360282189 1336389886198167510105821)
                      ·
                        rfl

theorem cell23_2602610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_2602610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602610 prefixEnd_2602610 := by exact prefixLift 2602610
  have htrace : WordTrace (prefixWord ++ tailWord_2602610) baseStart_2602610 baseEnd_2602610 := by
    simpa [prefixWord, tailWord_2602610, baseEnd_2602610] using wordTrace_append hprefix tailTrace_2602610
  have hstable : (prefixWord ++ tailWord_2602610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602610).length < 2 ^ (prefixWord ++ tailWord_2602610).sum := by decide
  have hdescent : baseEnd_2602610 < baseStart_2602610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602656 : List Nat := [2, 1, 1, 4, 3, 2, 1, 4, 5]
def baseStart_2602656 : Nat := 118140960795 + 2602656 * 2 ^ 59
def prefixEnd_2602656 : Nat := 4983230072969 + 3 ^ 40 * 2602656 * 2
def baseEnd_2602656 : Nat := 148490389589808258903401

theorem tailTrace_2602656 : CollatzResearch.WordTrace tailWord_2602656 prefixEnd_2602656 148490389589808258903401 := by
  unfold tailWord_2602656
  simp only [CollatzResearch.WordTrace]
  refine ⟨47463331429514642550797911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63284441906019523401063881 47463331429514642550797911)
  ·
    refine ⟨71194997144271963826196867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47463331429514642550797911 71194997144271963826196867)
    ·
      refine ⟨106792495716407945739295301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71194997144271963826196867 106792495716407945739295301)
      ·
        refine ⟨20023592946826489826117869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106792495716407945739295301 20023592946826489826117869)
        ·
          refine ⟨7508847355059933684794201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20023592946826489826117869 7508847355059933684794201)
          ·
            refine ⟨5631635516294950263595651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7508847355059933684794201 5631635516294950263595651)
            ·
              refine ⟨8447453274442425395393477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5631635516294950263595651 8447453274442425395393477)
              ·
                refine ⟨1583897488957954761636277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8447453274442425395393477 1583897488957954761636277)
                ·
                  refine ⟨148490389589808258903401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1583897488957954761636277 148490389589808258903401)
                  ·
                    rfl

theorem cell23_2602656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 5].length) (baseStart_2602656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602656 prefixEnd_2602656 := by exact prefixLift 2602656
  have htrace : WordTrace (prefixWord ++ tailWord_2602656) baseStart_2602656 baseEnd_2602656 := by
    simpa [prefixWord, tailWord_2602656, baseEnd_2602656] using wordTrace_append hprefix tailTrace_2602656
  have hstable : (prefixWord ++ tailWord_2602656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602656).length < 2 ^ (prefixWord ++ tailWord_2602656).sum := by decide
  have hdescent : baseEnd_2602656 < baseStart_2602656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602659 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 1, 7, 2]
def baseStart_2602659 : Nat := 118140960795 + 2602659 * 2 ^ 59
def prefixEnd_2602659 : Nat := 4983230072969 + 3 ^ 40 * 2602659 * 2
def baseEnd_2602659 : Nat := 1336415046750237818393095

theorem tailTrace_2602659 : CollatzResearch.WordTrace tailWord_2602659 prefixEnd_2602659 1336415046750237818393095 := by
  unfold tailWord_2602659
  simp only [CollatzResearch.WordTrace]
  refine ⟨94926772278018416613955031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63284514852012277742636687 94926772278018416613955031)
  ·
    refine ⟨142390158417027624920932547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94926772278018416613955031 142390158417027624920932547)
    ·
      refine ⟨213585237625541437381398821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142390158417027624920932547 213585237625541437381398821)
      ·
        refine ⟨40047232054789019509012279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213585237625541437381398821 40047232054789019509012279)
        ·
          refine ⟨60070848082183529263518419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40047232054789019509012279 60070848082183529263518419)
          ·
            refine ⟨90106272123275293895277629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60070848082183529263518419 90106272123275293895277629)
            ·
              refine ⟨33789852046228235210729111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90106272123275293895277629 33789852046228235210729111)
              ·
                refine ⟨50684778069342352816093667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33789852046228235210729111 50684778069342352816093667)
                ·
                  refine ⟨76027167104013529224140501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50684778069342352816093667 76027167104013529224140501)
                  ·
                    refine ⟨1781886729000317091190793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 76027167104013529224140501 1781886729000317091190793)
                    ·
                      refine ⟨1336415046750237818393095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1781886729000317091190793 1336415046750237818393095)
                      ·
                        rfl

theorem cell23_2602659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_2602659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602659 prefixEnd_2602659 := by exact prefixLift 2602659
  have htrace : WordTrace (prefixWord ++ tailWord_2602659) baseStart_2602659 baseEnd_2602659 := by
    simpa [prefixWord, tailWord_2602659, baseEnd_2602659] using wordTrace_append hprefix tailTrace_2602659
  have hstable : (prefixWord ++ tailWord_2602659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602659).length < 2 ^ (prefixWord ++ tailWord_2602659).sum := by decide
  have hdescent : baseEnd_2602659 < baseStart_2602659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602669 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2602669 : Nat := 118140960795 + 2602669 * 2 ^ 59
def prefixEnd_2602669 : Nat := 4983230072969 + 3 ^ 40 * 2602669 * 2
def baseEnd_2602669 : Nat := 445473393852260926422683

theorem tailTrace_2602669 : CollatzResearch.WordTrace tailWord_2602669 prefixEnd_2602669 445473393852260926422683 := by
  unfold tailWord_2602669
  simp only [CollatzResearch.WordTrace]
  refine ⟨94927137007982188321819061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63284758005321458881212707 94927137007982188321819061)
  ·
    refine ⟨8899419094498330155170537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94927137007982188321819061 8899419094498330155170537)
    ·
      refine ⟨6674564320873747616377903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8899419094498330155170537 6674564320873747616377903)
      ·
        refine ⟨10011846481310621424566855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6674564320873747616377903 10011846481310621424566855)
        ·
          refine ⟨15017769721965932136850283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10011846481310621424566855 15017769721965932136850283)
          ·
            refine ⟨22526654582948898205275425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15017769721965932136850283 22526654582948898205275425)
            ·
              refine ⟨16894990937211673653956569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22526654582948898205275425 16894990937211673653956569)
              ·
                refine ⟨12671243202908755240467427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16894990937211673653956569 12671243202908755240467427)
                ·
                  refine ⟨19006864804363132860701141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12671243202908755240467427 19006864804363132860701141)
                  ·
                    refine ⟨445473393852260926422683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19006864804363132860701141 445473393852260926422683)
                    ·
                      rfl

theorem cell23_2602669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2602669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602669 prefixEnd_2602669 := by exact prefixLift 2602669
  have htrace : WordTrace (prefixWord ++ tailWord_2602669) baseStart_2602669 baseEnd_2602669 := by
    simpa [prefixWord, tailWord_2602669, baseEnd_2602669] using wordTrace_append hprefix tailTrace_2602669
  have hstable : (prefixWord ++ tailWord_2602669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602669).length < 2 ^ (prefixWord ++ tailWord_2602669).sum := by decide
  have hdescent : baseEnd_2602669 < baseStart_2602669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602686 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2602686 : Nat := 118140960795 + 2602686 * 2 ^ 59
def prefixEnd_2602686 : Nat := 4983230072969 + 3 ^ 40 * 2602686 * 2
def baseEnd_2602686 : Nat := 445476303575969737585157

theorem tailTrace_2602686 : CollatzResearch.WordTrace tailWord_2602686 prefixEnd_2602686 445476303575969737585157 := by
  unfold tailWord_2602686
  simp only [CollatzResearch.WordTrace]
  refine ⟨11865969631115075028148489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63285171365947066816791941 11865969631115075028148489)
  ·
    refine ⟨8899477223336306271111367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11865969631115075028148489 8899477223336306271111367)
    ·
      refine ⟨13349215835004459406667051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8899477223336306271111367 13349215835004459406667051)
      ·
        refine ⟨20023823752506689110000577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13349215835004459406667051 20023823752506689110000577)
        ·
          refine ⟨15017867814380016832500433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20023823752506689110000577 15017867814380016832500433)
          ·
            refine ⟨11263400860785012624375325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15017867814380016832500433 11263400860785012624375325)
            ·
              refine ⟨4223775322794379734140747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11263400860785012624375325 4223775322794379734140747)
              ·
                refine ⟨6335662984191569601211121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223775322794379734140747 6335662984191569601211121)
                ·
                  refine ⟨4751747238143677200908341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6335662984191569601211121 4751747238143677200908341)
                  ·
                    refine ⟨445476303575969737585157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4751747238143677200908341 445476303575969737585157)
                    ·
                      rfl

theorem cell23_2602686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2602686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602686 prefixEnd_2602686 := by exact prefixLift 2602686
  have htrace : WordTrace (prefixWord ++ tailWord_2602686) baseStart_2602686 baseEnd_2602686 := by
    simpa [prefixWord, tailWord_2602686, baseEnd_2602686] using wordTrace_append hprefix tailTrace_2602686
  have hstable : (prefixWord ++ tailWord_2602686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602686).length < 2 ^ (prefixWord ++ tailWord_2602686).sum := by decide
  have hdescent : baseEnd_2602686 < baseStart_2602686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602773 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_2602773 : Nat := 118140960795 + 2602773 * 2 ^ 59
def prefixEnd_2602773 : Nat := 4983230072969 + 3 ^ 40 * 2602773 * 2
def baseEnd_2602773 : Nat := 1336473583544850372367571

theorem tailTrace_2602773 : CollatzResearch.WordTrace tailWord_2602773 prefixEnd_2602773 1336473583544850372367571 := by
  unfold tailWord_2602773
  simp only [CollatzResearch.WordTrace]
  refine ⟨94930930199605414083604973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63287286799736942722403315 94930930199605414083604973)
  ·
    refine ⟨35599098824852030281351865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94930930199605414083604973 35599098824852030281351865)
    ·
      refine ⟨26699324118639022711013899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35599098824852030281351865 26699324118639022711013899)
      ·
        refine ⟨40048986177958534066520849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26699324118639022711013899 40048986177958534066520849)
        ·
          refine ⟨30036739633468900549890637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40048986177958534066520849 30036739633468900549890637)
          ·
            refine ⟨11263777362550837706208989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30036739633468900549890637 11263777362550837706208989)
            ·
              refine ⟨4223916510956564139828371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11263777362550837706208989 4223916510956564139828371)
              ·
                refine ⟨6335874766434846209742557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223916510956564139828371 6335874766434846209742557)
                ·
                  refine ⟨2375953037413067328653459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6335874766434846209742557 2375953037413067328653459)
                  ·
                    refine ⟨3563929556119600992980189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2375953037413067328653459 3563929556119600992980189)
                    ·
                      refine ⟨1336473583544850372367571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3563929556119600992980189 1336473583544850372367571)
                      ·
                        rfl

theorem cell23_2602773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_2602773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602773 prefixEnd_2602773 := by exact prefixLift 2602773
  have htrace : WordTrace (prefixWord ++ tailWord_2602773) baseStart_2602773 baseEnd_2602773 := by
    simpa [prefixWord, tailWord_2602773, baseEnd_2602773] using wordTrace_append hprefix tailTrace_2602773
  have hstable : (prefixWord ++ tailWord_2602773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602773).length < 2 ^ (prefixWord ++ tailWord_2602773).sum := by decide
  have hdescent : baseEnd_2602773 < baseStart_2602773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602779 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 4]
def baseStart_2602779 : Nat := 118140960795 + 2602779 * 2 ^ 59
def prefixEnd_2602779 : Nat := 4983230072969 + 3 ^ 40 * 2602779 * 2
def baseEnd_2602779 : Nat := 1336476664428777348892543

theorem tailTrace_2602779 : CollatzResearch.WordTrace tailWord_2602779 prefixEnd_2602779 1336476664428777348892543 := by
  unfold tailWord_2602779
  simp only [CollatzResearch.WordTrace]
  refine ⟨94931149037583677108323391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63287432691722451405548927 94931149037583677108323391)
  ·
    refine ⟨142396723556375515662485087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94931149037583677108323391 142396723556375515662485087)
    ·
      refine ⟨213595085334563273493727631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142396723556375515662485087 213595085334563273493727631)
      ·
        refine ⟨320392628001844910240591447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213595085334563273493727631 320392628001844910240591447)
        ·
          refine ⟨480588942002767365360887171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320392628001844910240591447 480588942002767365360887171)
          ·
            refine ⟨720883413004151048041330757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480588942002767365360887171 720883413004151048041330757)
            ·
              refine ⟨135165639938278321507749517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 720883413004151048041330757 135165639938278321507749517)
              ·
                refine ⟨50687114976854370565406069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135165639938278321507749517 50687114976854370565406069)
                ·
                  refine ⟨4751917029080097240506819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50687114976854370565406069 4751917029080097240506819)
                  ·
                    refine ⟨7127875543620145860760229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4751917029080097240506819 7127875543620145860760229)
                    ·
                      refine ⟨1336476664428777348892543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7127875543620145860760229 1336476664428777348892543)
                      ·
                        rfl

theorem cell23_2602779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 4].length) (baseStart_2602779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602779 prefixEnd_2602779 := by exact prefixLift 2602779
  have htrace : WordTrace (prefixWord ++ tailWord_2602779) baseStart_2602779 baseEnd_2602779 := by
    simpa [prefixWord, tailWord_2602779, baseEnd_2602779] using wordTrace_append hprefix tailTrace_2602779
  have hstable : (prefixWord ++ tailWord_2602779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602779).length < 2 ^ (prefixWord ++ tailWord_2602779).sum := by decide
  have hdescent : baseEnd_2602779 < baseStart_2602779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602796 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_2602796 : Nat := 118140960795 + 2602796 * 2 ^ 59
def prefixEnd_2602796 : Nat := 4983230072969 + 3 ^ 40 * 2602796 * 2
def baseEnd_2602796 : Nat := 1336485393599903782379965

theorem tailTrace_2602796 : CollatzResearch.WordTrace tailWord_2602796 prefixEnd_2602796 1336485393599903782379965 := by
  unfold tailWord_2602796
  simp only [CollatzResearch.WordTrace]
  refine ⟨47465884539261044505846121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63287846052348059341128161 47465884539261044505846121)
  ·
    refine ⟨35599413404445783379384591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47465884539261044505846121 35599413404445783379384591)
    ·
      refine ⟨53399120106668675069076887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35599413404445783379384591 53399120106668675069076887)
      ·
        refine ⟨80098680160003012603615331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53399120106668675069076887 80098680160003012603615331)
        ·
          refine ⟨120148020240004518905422997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80098680160003012603615331 120148020240004518905422997)
          ·
            refine ⟨5631938448750211823691703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120148020240004518905422997 5631938448750211823691703)
            ·
              refine ⟨8447907673125317735537555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5631938448750211823691703 8447907673125317735537555)
              ·
                refine ⟨12671861509687976603306333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8447907673125317735537555 12671861509687976603306333)
                ·
                  refine ⟨4751948066132991226239875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12671861509687976603306333 4751948066132991226239875)
                  ·
                    refine ⟨7127922099199486839359813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4751948066132991226239875 7127922099199486839359813)
                    ·
                      refine ⟨1336485393599903782379965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7127922099199486839359813 1336485393599903782379965)
                      ·
                        rfl

theorem cell23_2602796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_2602796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602796 prefixEnd_2602796 := by exact prefixLift 2602796
  have htrace : WordTrace (prefixWord ++ tailWord_2602796) baseStart_2602796 baseEnd_2602796 := by
    simpa [prefixWord, tailWord_2602796, baseEnd_2602796] using wordTrace_append hprefix tailTrace_2602796
  have hstable : (prefixWord ++ tailWord_2602796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602796).length < 2 ^ (prefixWord ++ tailWord_2602796).sum := by decide
  have hdescent : baseEnd_2602796 < baseStart_2602796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602799 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 3]
def baseStart_2602799 : Nat := 118140960795 + 2602799 * 2 ^ 59
def prefixEnd_2602799 : Nat := 4983230072969 + 3 ^ 40 * 2602799 * 2
def baseEnd_2602799 : Nat := 1336486934041867270642451

theorem tailTrace_2602799 : CollatzResearch.WordTrace tailWord_2602799 prefixEnd_2602799 1336486934041867270642451 := by
  unfold tailWord_2602799
  simp only [CollatzResearch.WordTrace]
  refine ⟨94931878497511220524051451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63287918998340813682700967 94931878497511220524051451)
  ·
    refine ⟨142397817746266830786077177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94931878497511220524051451 142397817746266830786077177)
    ·
      refine ⟨106798363309700123089557883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142397817746266830786077177 106798363309700123089557883)
      ·
        refine ⟨160197544964550184634336825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106798363309700123089557883 160197544964550184634336825)
        ·
          refine ⟨120148158723412638475752619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160197544964550184634336825 120148158723412638475752619)
          ·
            refine ⟨180222238085118957713628929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120148158723412638475752619 180222238085118957713628929)
            ·
              refine ⟨135166678563839218285221697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180222238085118957713628929 135166678563839218285221697)
              ·
                refine ⟨101375008922879413713916273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135166678563839218285221697 101375008922879413713916273)
                ·
                  refine ⟨76031256692159560285437205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101375008922879413713916273 76031256692159560285437205)
                  ·
                    refine ⟨3563965157444979388379869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76031256692159560285437205 3563965157444979388379869)
                    ·
                      refine ⟨1336486934041867270642451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3563965157444979388379869 1336486934041867270642451)
                      ·
                        rfl

theorem cell23_2602799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_2602799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602799 prefixEnd_2602799 := by exact prefixLift 2602799
  have htrace : WordTrace (prefixWord ++ tailWord_2602799) baseStart_2602799 baseEnd_2602799 := by
    simpa [prefixWord, tailWord_2602799, baseEnd_2602799] using wordTrace_append hprefix tailTrace_2602799
  have hstable : (prefixWord ++ tailWord_2602799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602799).length < 2 ^ (prefixWord ++ tailWord_2602799).sum := by decide
  have hdescent : baseEnd_2602799 < baseStart_2602799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602836 : List Nat := [2, 4, 1, 1, 3, 1, 3, 8]
def baseStart_2602836 : Nat := 118140960795 + 2602836 * 2 ^ 59
def prefixEnd_2602836 : Nat := 4983230072969 + 3 ^ 40 * 2602836 * 2
def baseEnd_2602836 : Nat := 49500219734299393551103

theorem tailTrace_2602836 : CollatzResearch.WordTrace tailWord_2602836 prefixEnd_2602836 49500219734299393551103 := by
  unfold tailWord_2602836
  simp only [CollatzResearch.WordTrace]
  refine ⟨47466613999188587921574181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63288818665584783895432241 47466613999188587921574181)
  ·
    refine ⟨8899990124847860235295159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47466613999188587921574181 8899990124847860235295159)
    ·
      refine ⟨13349985187271790352942739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8899990124847860235295159 13349985187271790352942739)
      ·
        refine ⟨20024977780907685529414109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13349985187271790352942739 20024977780907685529414109)
        ·
          refine ⟨7509366667840382073530291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20024977780907685529414109 7509366667840382073530291)
          ·
            refine ⟨11264050001760573110295437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7509366667840382073530291 11264050001760573110295437)
            ·
              refine ⟨4224018750660214916360789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11264050001760573110295437 4224018750660214916360789)
              ·
                refine ⟨49500219734299393551103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4224018750660214916360789 49500219734299393551103)
                ·
                  rfl

theorem cell23_2602836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 8].length) (baseStart_2602836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602836 prefixEnd_2602836 := by exact prefixLift 2602836
  have htrace : WordTrace (prefixWord ++ tailWord_2602836) baseStart_2602836 baseEnd_2602836 := by
    simpa [prefixWord, tailWord_2602836, baseEnd_2602836] using wordTrace_append hprefix tailTrace_2602836
  have hstable : (prefixWord ++ tailWord_2602836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602836).length < 2 ^ (prefixWord ++ tailWord_2602836).sum := by decide
  have hdescent : baseEnd_2602836 < baseStart_2602836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602849 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 2, 7]
def baseStart_2602849 : Nat := 118140960795 + 2602849 * 2 ^ 59
def prefixEnd_2602849 : Nat := 4983230072969 + 3 ^ 40 * 2602849 * 2
def baseEnd_2602849 : Nat := 445504202691530691672407

theorem tailTrace_2602849 : CollatzResearch.WordTrace tailWord_2602849 prefixEnd_2602849 445504202691530691672407 := by
  unfold tailWord_2602849
  simp only [CollatzResearch.WordTrace]
  refine ⟨94933702147330079063371601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63289134764886719375581067 94933702147330079063371601)
  ·
    refine ⟨71200276610497559297528701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94933702147330079063371601 71200276610497559297528701)
    ·
      refine ⟨26700103728936584736573263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71200276610497559297528701 26700103728936584736573263)
      ·
        refine ⟨40050155593404877104859895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26700103728936584736573263 40050155593404877104859895)
        ·
          refine ⟨60075233390107315657289843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40050155593404877104859895 60075233390107315657289843)
          ·
            refine ⟨90112850085160973485934765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60075233390107315657289843 90112850085160973485934765)
            ·
              refine ⟨33792318781935365057225537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90112850085160973485934765 33792318781935365057225537)
              ·
                refine ⟨25344239086451523792919153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33792318781935365057225537 25344239086451523792919153)
                ·
                  refine ⟨19008179314838642844689365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25344239086451523792919153 19008179314838642844689365)
                  ·
                    refine ⟨445504202691530691672407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19008179314838642844689365 445504202691530691672407)
                    ·
                      rfl

theorem cell23_2602849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_2602849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602849 prefixEnd_2602849 := by exact prefixLift 2602849
  have htrace : WordTrace (prefixWord ++ tailWord_2602849) baseStart_2602849 baseEnd_2602849 := by
    simpa [prefixWord, tailWord_2602849, baseEnd_2602849] using wordTrace_append hprefix tailTrace_2602849
  have hstable : (prefixWord ++ tailWord_2602849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602849).length < 2 ^ (prefixWord ++ tailWord_2602849).sum := by decide
  have hdescent : baseEnd_2602849 < baseStart_2602849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602859 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 5]
def baseStart_2602859 : Nat := 118140960795 + 2602859 * 2 ^ 59
def prefixEnd_2602859 : Nat := 4983230072969 + 3 ^ 40 * 2602859 * 2
def baseEnd_2602859 : Nat := 1336517742881137035892175

theorem tailTrace_2602859 : CollatzResearch.WordTrace tailWord_2602859 prefixEnd_2602859 1336517742881137035892175 := by
  unfold tailWord_2602859
  simp only [CollatzResearch.WordTrace]
  refine ⟨94934066877293850771235631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63289377918195900514157087 94934066877293850771235631)
  ·
    refine ⟨142401100315940776156853447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94934066877293850771235631 142401100315940776156853447)
    ·
      refine ⟨213601650473911164235280171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142401100315940776156853447 213601650473911164235280171)
      ·
        refine ⟨320402475710866746352920257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213601650473911164235280171 320402475710866746352920257)
        ·
          refine ⟨240301856783150059764690193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320402475710866746352920257 240301856783150059764690193)
          ·
            refine ⟨180226392587362544823517645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240301856783150059764690193 180226392587362544823517645)
            ·
              refine ⟨67584897220260954308819117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180226392587362544823517645 67584897220260954308819117)
              ·
                refine ⟨25344336457597857865807169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67584897220260954308819117 25344336457597857865807169)
                ·
                  refine ⟨19008252343198393399355377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25344336457597857865807169 19008252343198393399355377)
                  ·
                    refine ⟨14256189257398795049516533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19008252343198393399355377 14256189257398795049516533)
                    ·
                      refine ⟨1336517742881137035892175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14256189257398795049516533 1336517742881137035892175)
                      ·
                        rfl

theorem cell23_2602859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_2602859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602859 prefixEnd_2602859 := by exact prefixLift 2602859
  have htrace : WordTrace (prefixWord ++ tailWord_2602859) baseStart_2602859 baseEnd_2602859 := by
    simpa [prefixWord, tailWord_2602859, baseEnd_2602859] using wordTrace_append hprefix tailTrace_2602859
  have hstable : (prefixWord ++ tailWord_2602859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602859).length < 2 ^ (prefixWord ++ tailWord_2602859).sum := by decide
  have hdescent : baseEnd_2602859 < baseStart_2602859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2602976 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_2602976 : Nat := 118140960795 + 2602976 * 2 ^ 59
def prefixEnd_2602976 : Nat := 4983230072969 + 3 ^ 40 * 2602976 * 2
def baseEnd_2602976 : Nat := 1336577820117713078129137

theorem tailTrace_2602976 : CollatzResearch.WordTrace tailWord_2602976 prefixEnd_2602976 1336577820117713078129137 := by
  unfold tailWord_2602976
  simp only [CollatzResearch.WordTrace]
  refine ⟨47469167108934989876622391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63292222811913319835496521 47469167108934989876622391)
  ·
    refine ⟨71203750663402484814933587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47469167108934989876622391 71203750663402484814933587)
    ·
      refine ⟨106805625995103727222400381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71203750663402484814933587 106805625995103727222400381)
      ·
        refine ⟨40052109748163897708400143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106805625995103727222400381 40052109748163897708400143)
        ·
          refine ⟨60078164622245846562600215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40052109748163897708400143 60078164622245846562600215)
          ·
            refine ⟨90117246933368769843900323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60078164622245846562600215 90117246933368769843900323)
            ·
              refine ⟨135175870400053154765850485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90117246933368769843900323 135175870400053154765850485)
              ·
                refine ⟨12672737850004983259298483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135175870400053154765850485 12672737850004983259298483)
                ·
                  refine ⟨19009106775007474888947725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12672737850004983259298483 19009106775007474888947725)
                  ·
                    refine ⟨7128415040627803083355397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19009106775007474888947725 7128415040627803083355397)
                    ·
                      refine ⟨1336577820117713078129137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7128415040627803083355397 1336577820117713078129137)
                      ·
                        rfl

theorem cell23_2602976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_2602976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2602976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2602976 prefixEnd_2602976 := by exact prefixLift 2602976
  have htrace : WordTrace (prefixWord ++ tailWord_2602976) baseStart_2602976 baseEnd_2602976 := by
    simpa [prefixWord, tailWord_2602976, baseEnd_2602976] using wordTrace_append hprefix tailTrace_2602976
  have hstable : (prefixWord ++ tailWord_2602976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2602976).length < 2 ^ (prefixWord ++ tailWord_2602976).sum := by decide
  have hdescent : baseEnd_2602976 < baseStart_2602976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2602976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603037 : List Nat := [1, 4, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_2603037 : Nat := 118140960795 + 2603037 * 2 ^ 59
def prefixEnd_2603037 : Nat := 4983230072969 + 3 ^ 40 * 2603037 * 2
def baseEnd_2603037 : Nat := 445536380812545779822119

theorem tailTrace_2603037 : CollatzResearch.WordTrace tailWord_2603037 prefixEnd_2603037 445536380812545779822119 := by
  unfold tailWord_2603037
  simp only [CollatzResearch.WordTrace]
  refine ⟨94940559070648987171215365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63293706047099324780810243 94940559070648987171215365)
  ·
    refine ⟨17801354825746685094602881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94940559070648987171215365 17801354825746685094602881)
    ·
      refine ⟨13351016119310013820952161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17801354825746685094602881 13351016119310013820952161)
      ·
        refine ⟨10013262089482510365714121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13351016119310013820952161 10013262089482510365714121)
        ·
          refine ⟨7509946567111882774285591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10013262089482510365714121 7509946567111882774285591)
          ·
            refine ⟨11264919850667824161428387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7509946567111882774285591 11264919850667824161428387)
            ·
              refine ⟨16897379776001736242142581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11264919850667824161428387 16897379776001736242142581)
              ·
                refine ⟨1584129354000162772700867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16897379776001736242142581 1584129354000162772700867)
                ·
                  refine ⟨2376194031000244159051301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584129354000162772700867 2376194031000244159051301)
                  ·
                    refine ⟨445536380812545779822119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2376194031000244159051301 445536380812545779822119)
                    ·
                      rfl

theorem cell23_2603037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_2603037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603037 prefixEnd_2603037 := by exact prefixLift 2603037
  have htrace : WordTrace (prefixWord ++ tailWord_2603037) baseStart_2603037 baseEnd_2603037 := by
    simpa [prefixWord, tailWord_2603037, baseEnd_2603037] using wordTrace_append hprefix tailTrace_2603037
  have hstable : (prefixWord ++ tailWord_2603037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603037).length < 2 ^ (prefixWord ++ tailWord_2603037).sum := by decide
  have hdescent : baseEnd_2603037 < baseStart_2603037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603050 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 6]
def baseStart_2603050 : Nat := 118140960795 + 2603050 * 2 ^ 59
def prefixEnd_2603050 : Nat := 4983230072969 + 3 ^ 40 * 2603050 * 2
def baseEnd_2603050 : Nat := 148512868631793976511533

theorem tailTrace_2603050 : CollatzResearch.WordTrace tailWord_2603050 prefixEnd_2603050 148512868631793976511533 := by
  unfold tailWord_2603050
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735258304900472597859651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63294022146401260260959069 23735258304900472597859651)
  ·
    refine ⟨35602887457350708896789477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23735258304900472597859651 35602887457350708896789477)
    ·
      refine ⟨6675541398253257918148027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35602887457350708896789477 6675541398253257918148027)
      ·
        refine ⟨10013312097379886877222041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6675541398253257918148027 10013312097379886877222041)
        ·
          refine ⟨7509984073034915157916531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10013312097379886877222041 7509984073034915157916531)
          ·
            refine ⟨11264976109552372736874797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7509984073034915157916531 11264976109552372736874797)
            ·
              refine ⟨4224366041082139776328049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11264976109552372736874797 4224366041082139776328049)
              ·
                refine ⟨3168274530811604832246037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4224366041082139776328049 3168274530811604832246037)
                ·
                  refine ⟨148512868631793976511533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3168274530811604832246037 148512868631793976511533)
                  ·
                    rfl

theorem cell23_2603050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_2603050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603050 prefixEnd_2603050 := by exact prefixLift 2603050
  have htrace : WordTrace (prefixWord ++ tailWord_2603050) baseStart_2603050 baseEnd_2603050 := by
    simpa [prefixWord, tailWord_2603050, baseEnd_2603050] using wordTrace_append hprefix tailTrace_2603050
  have hstable : (prefixWord ++ tailWord_2603050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603050).length < 2 ^ (prefixWord ++ tailWord_2603050).sum := by decide
  have hdescent : baseEnd_2603050 < baseStart_2603050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603127 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 2, 4]
def baseStart_2603127 : Nat := 118140960795 + 2603127 * 2 ^ 59
def prefixEnd_2603127 : Nat := 4983230072969 + 3 ^ 40 * 2603127 * 2
def baseEnd_2603127 : Nat := 445551785232180662446981

theorem tailTrace_2603127 : CollatzResearch.WordTrace tailWord_2603127 prefixEnd_2603127 445551785232180662446981 := by
  unfold tailWord_2603127
  simp only [CollatzResearch.WordTrace]
  refine ⟨94943841640322932541991635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63295894426881955027994423 94943841640322932541991635)
  ·
    refine ⟨142415762460484398812987453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94943841640322932541991635 142415762460484398812987453)
    ·
      refine ⟨53405910922681649554870295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142415762460484398812987453 53405910922681649554870295)
      ·
        refine ⟨80108866384022474332305443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53405910922681649554870295 80108866384022474332305443)
        ·
          refine ⟨120163299576033711498458165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80108866384022474332305443 120163299576033711498458165)
          ·
            refine ⟨11265309335253160452980453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120163299576033711498458165 11265309335253160452980453)
            ·
              refine ⟨2112245500359967584933835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11265309335253160452980453 2112245500359967584933835)
              ·
                refine ⟨3168368250539951377400753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112245500359967584933835 3168368250539951377400753)
                ·
                  refine ⟨2376276187904963533050565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3168368250539951377400753 2376276187904963533050565)
                  ·
                    refine ⟨445551785232180662446981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2376276187904963533050565 445551785232180662446981)
                    ·
                      rfl

theorem cell23_2603127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_2603127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603127 prefixEnd_2603127 := by exact prefixLift 2603127
  have htrace : WordTrace (prefixWord ++ tailWord_2603127) baseStart_2603127 baseEnd_2603127 := by
    simpa [prefixWord, tailWord_2603127, baseEnd_2603127] using wordTrace_append hprefix tailTrace_2603127
  have hstable : (prefixWord ++ tailWord_2603127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603127).length < 2 ^ (prefixWord ++ tailWord_2603127).sum := by decide
  have hdescent : baseEnd_2603127 < baseStart_2603127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603137 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2603137 : Nat := 118140960795 + 2603137 * 2 ^ 59
def prefixEnd_2603137 : Nat := 4983230072969 + 3 ^ 40 * 2603137 * 2
def baseEnd_2603137 : Nat := 1336660490503086948215897

theorem tailTrace_2603137 : CollatzResearch.WordTrace tailWord_2603137 prefixEnd_2603137 1336660490503086948215897 := by
  unfold tailWord_2603137
  simp only [CollatzResearch.WordTrace]
  refine ⟨94944206370286704249855665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63296137580191136166570443 94944206370286704249855665)
  ·
    refine ⟨71208154777715028187391749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94944206370286704249855665 71208154777715028187391749)
    ·
      refine ⟨13351529020821567785135953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71208154777715028187391749 13351529020821567785135953)
      ·
        refine ⟨10013646765616175838851965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13351529020821567785135953 10013646765616175838851965)
        ·
          refine ⟨3755117537106065939569487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10013646765616175838851965 3755117537106065939569487)
          ·
            refine ⟨5632676305659098909354231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755117537106065939569487 5632676305659098909354231)
            ·
              refine ⟨8449014458488648364031347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632676305659098909354231 8449014458488648364031347)
              ·
                refine ⟨12673521687732972546047021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449014458488648364031347 12673521687732972546047021)
                ·
                  refine ⟨4752570632899864704767633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12673521687732972546047021 4752570632899864704767633)
                  ·
                    refine ⟨3564427974674898528575725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4752570632899864704767633 3564427974674898528575725)
                    ·
                      refine ⟨1336660490503086948215897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3564427974674898528575725 1336660490503086948215897)
                      ·
                        rfl

theorem cell23_2603137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2603137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603137 prefixEnd_2603137 := by exact prefixLift 2603137
  have htrace : WordTrace (prefixWord ++ tailWord_2603137) baseStart_2603137 baseEnd_2603137 := by
    simpa [prefixWord, tailWord_2603137, baseEnd_2603137] using wordTrace_append hprefix tailTrace_2603137
  have hstable : (prefixWord ++ tailWord_2603137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603137).length < 2 ^ (prefixWord ++ tailWord_2603137).sum := by decide
  have hdescent : baseEnd_2603137 < baseStart_2603137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603154 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_2603154 : Nat := 118140960795 + 2603154 * 2 ^ 59
def prefixEnd_2603154 : Nat := 4983230072969 + 3 ^ 40 * 2603154 * 2
def baseEnd_2603154 : Nat := 1336669219674213381703319

theorem tailTrace_2603154 : CollatzResearch.WordTrace tailWord_2603154 prefixEnd_2603154 1336669219674213381703319 := by
  unfold tailWord_2603154
  simp only [CollatzResearch.WordTrace]
  refine ⟨23736206602806279038306129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63296550940816744102149677 23736206602806279038306129)
  ·
    refine ⟨17802154952104709278729597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23736206602806279038306129 17802154952104709278729597)
    ·
      refine ⟨6675808107039265979523599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17802154952104709278729597 6675808107039265979523599)
      ·
        refine ⟨10013712160558898969285399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6675808107039265979523599 10013712160558898969285399)
        ·
          refine ⟨15020568240838348453928099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10013712160558898969285399 15020568240838348453928099)
          ·
            refine ⟨22530852361257522680892149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15020568240838348453928099 22530852361257522680892149)
            ·
              refine ⟨2112267408867892751333639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22530852361257522680892149 2112267408867892751333639)
              ·
                refine ⟨3168401113301839127000459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112267408867892751333639 3168401113301839127000459)
                ·
                  refine ⟨4752601669952758690500689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168401113301839127000459 4752601669952758690500689)
                  ·
                    refine ⟨3564451252464569017875517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4752601669952758690500689 3564451252464569017875517)
                    ·
                      refine ⟨1336669219674213381703319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3564451252464569017875517 1336669219674213381703319)
                      ·
                        rfl

theorem cell23_2603154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_2603154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603154 prefixEnd_2603154 := by exact prefixLift 2603154
  have htrace : WordTrace (prefixWord ++ tailWord_2603154) baseStart_2603154 baseEnd_2603154 := by
    simpa [prefixWord, tailWord_2603154, baseEnd_2603154] using wordTrace_append hprefix tailTrace_2603154
  have hstable : (prefixWord ++ tailWord_2603154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603154).length < 2 ^ (prefixWord ++ tailWord_2603154).sum := by decide
  have hdescent : baseEnd_2603154 < baseStart_2603154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603168 : List Nat := [2, 1, 1, 4, 2, 4, 2, 2, 1, 2, 2]
def baseStart_2603168 : Nat := 118140960795 + 2603168 * 2 ^ 59
def prefixEnd_2603168 : Nat := 4983230072969 + 3 ^ 40 * 2603168 * 2
def baseEnd_2603168 : Nat := 1336676408403376326928255

theorem tailTrace_2603168 : CollatzResearch.WordTrace tailWord_2603168 prefixEnd_2603168 1336676408403376326928255 := by
  unfold tailWord_2603168
  simp only [CollatzResearch.WordTrace]
  refine ⟨47472668516587198272117079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63296891355449597696156105 47472668516587198272117079)
  ·
    refine ⟨71209002774880797408175619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47472668516587198272117079 71209002774880797408175619)
    ·
      refine ⟨106813504162321196112263429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71209002774880797408175619 106813504162321196112263429)
      ·
        refine ⟨20027532030435224271049393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106813504162321196112263429 20027532030435224271049393)
        ·
          refine ⟨15020649022826418203287045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20027532030435224271049393 15020649022826418203287045)
          ·
            refine ⟨2816371691779953413116321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15020649022826418203287045 2816371691779953413116321)
            ·
              refine ⟨2112278768834965059837241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2816371691779953413116321 2112278768834965059837241)
              ·
                refine ⟨1584209076626223794877931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2112278768834965059837241 1584209076626223794877931)
                ·
                  refine ⟨2376313614939335692316897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584209076626223794877931 2376313614939335692316897)
                  ·
                    refine ⟨1782235211204501769237673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2376313614939335692316897 1782235211204501769237673)
                    ·
                      refine ⟨1336676408403376326928255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1782235211204501769237673 1336676408403376326928255)
                      ·
                        rfl

theorem cell23_2603168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_2603168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603168 prefixEnd_2603168 := by exact prefixLift 2603168
  have htrace : WordTrace (prefixWord ++ tailWord_2603168) baseStart_2603168 baseEnd_2603168 := by
    simpa [prefixWord, tailWord_2603168, baseEnd_2603168] using wordTrace_append hprefix tailTrace_2603168
  have hstable : (prefixWord ++ tailWord_2603168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603168).length < 2 ^ (prefixWord ++ tailWord_2603168).sum := by decide
  have hdescent : baseEnd_2603168 < baseStart_2603168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603170 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2603170 : Nat := 118140960795 + 2603170 * 2 ^ 59
def prefixEnd_2603170 : Nat := 4983230072969 + 3 ^ 40 * 2603170 * 2
def baseEnd_2603170 : Nat := 445559145121561773034415

theorem tailTrace_2603170 : CollatzResearch.WordTrace tailWord_2603170 prefixEnd_2603170 445559145121561773034415 := by
  unfold tailWord_2603170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23736352494791787721451741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63296939986111433923871309 23736352494791787721451741)
  ·
    refine ⟨8901132185546920395544403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23736352494791787721451741 8901132185546920395544403)
    ·
      refine ⟨13351698278320380593316605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8901132185546920395544403 13351698278320380593316605)
      ·
        refine ⟨5006886854370142722493727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13351698278320380593316605 5006886854370142722493727)
        ·
          refine ⟨7510330281555214083740591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5006886854370142722493727 7510330281555214083740591)
          ·
            refine ⟨11265495422332821125610887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7510330281555214083740591 11265495422332821125610887)
            ·
              refine ⟨16898243133499231688416331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11265495422332821125610887 16898243133499231688416331)
              ·
                refine ⟨25347364700248847532624497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16898243133499231688416331 25347364700248847532624497)
                ·
                  refine ⟨19010523525186635649468373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25347364700248847532624497 19010523525186635649468373)
                  ·
                    refine ⟨445559145121561773034415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19010523525186635649468373 445559145121561773034415)
                    ·
                      rfl

theorem cell23_2603170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2603170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603170 prefixEnd_2603170 := by exact prefixLift 2603170
  have htrace : WordTrace (prefixWord ++ tailWord_2603170) baseStart_2603170 baseEnd_2603170 := by
    simpa [prefixWord, tailWord_2603170, baseEnd_2603170] using wordTrace_append hprefix tailTrace_2603170
  have hstable : (prefixWord ++ tailWord_2603170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603170).length < 2 ^ (prefixWord ++ tailWord_2603170).sum := by decide
  have hdescent : baseEnd_2603170 < baseStart_2603170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603173 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_2603173 : Nat := 118140960795 + 2603173 * 2 ^ 59
def prefixEnd_2603173 : Nat := 4983230072969 + 3 ^ 40 * 2603173 * 2
def baseEnd_2603173 : Nat := 1336678975806648807365731

theorem tailTrace_2603173 : CollatzResearch.WordTrace tailWord_2603173 prefixEnd_2603173 1336678975806648807365731 := by
  unfold tailWord_2603173
  simp only [CollatzResearch.WordTrace]
  refine ⟨94945519398156282398166173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63297012932104188265444115 94945519398156282398166173)
  ·
    refine ⟨35604569774308605899312315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94945519398156282398166173 35604569774308605899312315)
    ·
      refine ⟨53406854661462908848968473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35604569774308605899312315 53406854661462908848968473)
      ·
        refine ⟨40055140996097181636726355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53406854661462908848968473 40055140996097181636726355)
        ·
          refine ⟨60082711494145772455089533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40055140996097181636726355 60082711494145772455089533)
          ·
            refine ⟨22531016810304664670658575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60082711494145772455089533 22531016810304664670658575)
            ·
              refine ⟨33796525215456997005987863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22531016810304664670658575 33796525215456997005987863)
              ·
                refine ⟨50694787823185495508981795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33796525215456997005987863 50694787823185495508981795)
                ·
                  refine ⟨76042181734778243263472693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50694787823185495508981795 76042181734778243263472693)
                  ·
                    refine ⟨7128954537635460305950565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76042181734778243263472693 7128954537635460305950565)
                    ·
                      refine ⟨1336678975806648807365731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7128954537635460305950565 1336678975806648807365731)
                      ·
                        rfl

theorem cell23_2603173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_2603173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603173 prefixEnd_2603173 := by exact prefixLift 2603173
  have htrace : WordTrace (prefixWord ++ tailWord_2603173) baseStart_2603173 baseEnd_2603173 := by
    simpa [prefixWord, tailWord_2603173, baseEnd_2603173] using wordTrace_append hprefix tailTrace_2603173
  have hstable : (prefixWord ++ tailWord_2603173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603173).length < 2 ^ (prefixWord ++ tailWord_2603173).sum := by decide
  have hdescent : baseEnd_2603173 < baseStart_2603173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603224 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 4, 2, 2]
def baseStart_2603224 : Nat := 118140960795 + 2603224 * 2 ^ 59
def prefixEnd_2603224 : Nat := 4983230072969 + 3 ^ 40 * 2603224 * 2
def baseEnd_2603224 : Nat := 1336705163320028107827997

theorem tailTrace_2603224 : CollatzResearch.WordTrace tailWord_2603224 prefixEnd_2603224 1336705163320028107827997 := by
  unfold tailWord_2603224
  simp only [CollatzResearch.WordTrace]
  refine ⟨47473689760485759054136363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63298253013981012072181817 47473689760485759054136363)
  ·
    refine ⟨71210534640728638581204545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47473689760485759054136363 71210534640728638581204545)
    ·
      refine ⟨53407900980546478935903409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71210534640728638581204545 53407900980546478935903409)
      ·
        refine ⟨40055925735409859201927557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53407900980546478935903409 40055925735409859201927557)
        ·
          refine ⟨7510486075389348600361417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40055925735409859201927557 7510486075389348600361417)
          ·
            refine ⟨5632864556542011450271063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7510486075389348600361417 5632864556542011450271063)
            ·
              refine ⟨8449296834813017175406595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632864556542011450271063 8449296834813017175406595)
              ·
                refine ⟨12673945252219525763109893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449296834813017175406595 12673945252219525763109893)
                ·
                  refine ⟨2376364734791161080583105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12673945252219525763109893 2376364734791161080583105)
                  ·
                    refine ⟨1782273551093370810437329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2376364734791161080583105 1782273551093370810437329)
                    ·
                      refine ⟨1336705163320028107827997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1782273551093370810437329 1336705163320028107827997)
                      ·
                        rfl

theorem cell23_2603224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_2603224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603224 prefixEnd_2603224 := by exact prefixLift 2603224
  have htrace : WordTrace (prefixWord ++ tailWord_2603224) baseStart_2603224 baseEnd_2603224 := by
    simpa [prefixWord, tailWord_2603224, baseEnd_2603224] using wordTrace_append hprefix tailTrace_2603224
  have hstable : (prefixWord ++ tailWord_2603224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603224).length < 2 ^ (prefixWord ++ tailWord_2603224).sum := by decide
  have hdescent : baseEnd_2603224 < baseStart_2603224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603243 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 3, 7]
def baseStart_2603243 : Nat := 118140960795 + 2603243 * 2 ^ 59
def prefixEnd_2603243 : Nat := 4983230072969 + 3 ^ 40 * 2603243 * 2
def baseEnd_2603243 : Nat := 445571639817487844496803

theorem tailTrace_2603243 : CollatzResearch.WordTrace tailWord_2603243 prefixEnd_2603243 445571639817487844496803 := by
  unfold tailWord_2603243
  simp only [CollatzResearch.WordTrace]
  refine ⟨94948072507902684353214383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63298715005268456235476255 94948072507902684353214383)
  ·
    refine ⟨142422108761854026529821575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94948072507902684353214383 142422108761854026529821575)
    ·
      refine ⟨213633163142781039794732363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142422108761854026529821575 213633163142781039794732363)
      ·
        refine ⟨320449744714171559692098545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213633163142781039794732363 320449744714171559692098545)
        ·
          refine ⟨240337308535628669769073909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320449744714171559692098545 240337308535628669769073909)
          ·
            refine ⟨22531622675215187790850679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 240337308535628669769073909 22531622675215187790850679)
            ·
              refine ⟨33797434012822781686276019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22531622675215187790850679 33797434012822781686276019)
              ·
                refine ⟨50696151019234172529414029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33797434012822781686276019 50696151019234172529414029)
                ·
                  refine ⟨19011056632212814698530261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50696151019234172529414029 19011056632212814698530261)
                  ·
                    refine ⟨445571639817487844496803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19011056632212814698530261 445571639817487844496803)
                    ·
                      rfl

theorem cell23_2603243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 7].length) (baseStart_2603243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603243 prefixEnd_2603243 := by exact prefixLift 2603243
  have htrace : WordTrace (prefixWord ++ tailWord_2603243) baseStart_2603243 baseEnd_2603243 := by
    simpa [prefixWord, tailWord_2603243, baseEnd_2603243] using wordTrace_append hprefix tailTrace_2603243
  have hstable : (prefixWord ++ tailWord_2603243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603243).length < 2 ^ (prefixWord ++ tailWord_2603243).sum := by decide
  have hdescent : baseEnd_2603243 < baseStart_2603243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603260 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_2603260 : Nat := 118140960795 + 2603260 * 2 ^ 59
def prefixEnd_2603260 : Nat := 4983230072969 + 3 ^ 40 * 2603260 * 2
def baseEnd_2603260 : Nat := 445574549541196655659277

theorem tailTrace_2603260 : CollatzResearch.WordTrace tailWord_2603260 prefixEnd_2603260 445574549541196655659277 := by
  unfold tailWord_2603260
  simp only [CollatzResearch.WordTrace]
  refine ⟨47474346274420548128291617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63299128365894064171055489 47474346274420548128291617)
  ·
    refine ⟨35605759705815411096218713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47474346274420548128291617 35605759705815411096218713)
    ·
      refine ⟨26704319779361558322164035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35605759705815411096218713 26704319779361558322164035)
      ·
        refine ⟨40056479669042337483246053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26704319779361558322164035 40056479669042337483246053)
        ·
          refine ⟨7510589937945438278108635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40056479669042337483246053 7510589937945438278108635)
          ·
            refine ⟨11265884906918157417162953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7510589937945438278108635 11265884906918157417162953)
            ·
              refine ⟨8449413680188618062872215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11265884906918157417162953 8449413680188618062872215)
              ·
                refine ⟨12674120520282927094308323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449413680188618062872215 12674120520282927094308323)
                ·
                  refine ⟨19011180780424390641462485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12674120520282927094308323 19011180780424390641462485)
                  ·
                    refine ⟨445574549541196655659277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19011180780424390641462485 445574549541196655659277)
                    ·
                      rfl

theorem cell23_2603260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_2603260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603260 prefixEnd_2603260 := by exact prefixLift 2603260
  have htrace : WordTrace (prefixWord ++ tailWord_2603260) baseStart_2603260 baseEnd_2603260 := by
    simpa [prefixWord, tailWord_2603260, baseEnd_2603260] using wordTrace_append hprefix tailTrace_2603260
  have hstable : (prefixWord ++ tailWord_2603260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603260).length < 2 ^ (prefixWord ++ tailWord_2603260).sum := by decide
  have hdescent : baseEnd_2603260 < baseStart_2603260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603297 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_2603297 : Nat := 118140960795 + 2603297 * 2 ^ 59
def prefixEnd_2603297 : Nat := 4983230072969 + 3 ^ 40 * 2603297 * 2
def baseEnd_2603297 : Nat := 1336742647407806322215161

theorem tailTrace_2603297 : CollatzResearch.WordTrace tailWord_2603297 prefixEnd_2603297 1336742647407806322215161 := by
  unfold tailWord_2603297
  simp only [CollatzResearch.WordTrace]
  refine ⟨94950042049707051575680145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63300028033138034383786763 94950042049707051575680145)
  ·
    refine ⟨71212531537280288681760109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94950042049707051575680145 71212531537280288681760109)
    ·
      refine ⟨26704699326480108255660041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71212531537280288681760109 26704699326480108255660041)
      ·
        refine ⟨20028524494860081191745031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26704699326480108255660041 20028524494860081191745031)
        ·
          refine ⟨30042786742290121787617547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20028524494860081191745031 30042786742290121787617547)
          ·
            refine ⟨45064180113435182681426321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30042786742290121787617547 45064180113435182681426321)
            ·
              refine ⟨33798135085076387011069741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45064180113435182681426321 33798135085076387011069741)
              ·
                refine ⟨12674300656903645129151153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33798135085076387011069741 12674300656903645129151153)
                ·
                  refine ⟨9505725492677733846863365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12674300656903645129151153 9505725492677733846863365)
                  ·
                    refine ⟨1782323529877075096286881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9505725492677733846863365 1782323529877075096286881)
                    ·
                      refine ⟨1336742647407806322215161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1782323529877075096286881 1336742647407806322215161)
                      ·
                        rfl

theorem cell23_2603297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_2603297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603297 prefixEnd_2603297 := by exact prefixLift 2603297
  have htrace : WordTrace (prefixWord ++ tailWord_2603297) baseStart_2603297 baseEnd_2603297 := by
    simpa [prefixWord, tailWord_2603297, baseEnd_2603297] using wordTrace_append hprefix tailTrace_2603297
  have hstable : (prefixWord ++ tailWord_2603297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603297).length < 2 ^ (prefixWord ++ tailWord_2603297).sum := by decide
  have hdescent : baseEnd_2603297 < baseStart_2603297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603314 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_2603314 : Nat := 118140960795 + 2603314 * 2 ^ 59
def prefixEnd_2603314 : Nat := 4983230072969 + 3 ^ 40 * 2603314 * 2
def baseEnd_2603314 : Nat := 1336751376578932755702583

theorem tailTrace_2603314 : CollatzResearch.WordTrace tailWord_2603314 prefixEnd_2603314 1336751376578932755702583 := by
  unfold tailWord_2603314
  simp only [CollatzResearch.WordTrace]
  refine ⟨23737665522661365869762249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63300441393763642319365997 23737665522661365869762249)
  ·
    refine ⟨17803249141996024402321687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23737665522661365869762249 17803249141996024402321687)
    ·
      refine ⟨26704873712994036603482531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17803249141996024402321687 26704873712994036603482531)
      ·
        refine ⟨40057310569491054905223797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26704873712994036603482531 40057310569491054905223797)
        ·
          refine ⟨3755372865889786397364731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40057310569491054905223797 3755372865889786397364731)
          ·
            refine ⟨5633059298834679596047097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755372865889786397364731 5633059298834679596047097)
            ·
              refine ⟨4224794474126009697035323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5633059298834679596047097 4224794474126009697035323)
              ·
                refine ⟨6337191711189014545552985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4224794474126009697035323 6337191711189014545552985)
                ·
                  refine ⟨4752893783391760909164739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6337191711189014545552985 4752893783391760909164739)
                  ·
                    refine ⟨7129340675087641363747109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4752893783391760909164739 7129340675087641363747109)
                    ·
                      refine ⟨1336751376578932755702583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7129340675087641363747109 1336751376578932755702583)
                      ·
                        rfl

theorem cell23_2603314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_2603314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603314 prefixEnd_2603314 := by exact prefixLift 2603314
  have htrace : WordTrace (prefixWord ++ tailWord_2603314) baseStart_2603314 baseEnd_2603314 := by
    simpa [prefixWord, tailWord_2603314, baseEnd_2603314] using wordTrace_append hprefix tailTrace_2603314
  have hstable : (prefixWord ++ tailWord_2603314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603314).length < 2 ^ (prefixWord ++ tailWord_2603314).sum := by decide
  have hdescent : baseEnd_2603314 < baseStart_2603314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603324 : List Nat := [2, 2, 2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_2603324 : Nat := 118140960795 + 2603324 * 2 ^ 59
def prefixEnd_2603324 : Nat := 4983230072969 + 3 ^ 40 * 2603324 * 2
def baseEnd_2603324 : Nat := 445585503795159238859179

theorem tailTrace_2603324 : CollatzResearch.WordTrace tailWord_2603324 prefixEnd_2603324 445585503795159238859179 := by
  unfold tailWord_2603324
  simp only [CollatzResearch.WordTrace]
  refine ⟨47475513410304617593456513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63300684547072823457942017 47475513410304617593456513)
  ·
    refine ⟨35606635057728463195092385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47475513410304617593456513 35606635057728463195092385)
    ·
      refine ⟨26704976293296347396319289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35606635057728463195092385 26704976293296347396319289)
      ·
        refine ⟨20028732219972260547239467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26704976293296347396319289 20028732219972260547239467)
        ·
          refine ⟨30043098329958390820859201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20028732219972260547239467 30043098329958390820859201)
          ·
            refine ⟨22532323747468793115644401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30043098329958390820859201 22532323747468793115644401)
            ·
              refine ⟨16899242810601594836733301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22532323747468793115644401 16899242810601594836733301)
              ·
                refine ⟨1584304013493899515943747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16899242810601594836733301 1584304013493899515943747)
                ·
                  refine ⟨2376456020240849273915621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584304013493899515943747 2376456020240849273915621)
                  ·
                    refine ⟨445585503795159238859179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2376456020240849273915621 445585503795159238859179)
                    ·
                      rfl

theorem cell23_2603324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_2603324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603324 prefixEnd_2603324 := by exact prefixLift 2603324
  have htrace : WordTrace (prefixWord ++ tailWord_2603324) baseStart_2603324 baseEnd_2603324 := by
    simpa [prefixWord, tailWord_2603324, baseEnd_2603324] using wordTrace_append hprefix tailTrace_2603324
  have hstable : (prefixWord ++ tailWord_2603324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603324).length < 2 ^ (prefixWord ++ tailWord_2603324).sum := by decide
  have hdescent : baseEnd_2603324 < baseStart_2603324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603340 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2603340 : Nat := 118140960795 + 2603340 * 2 ^ 59
def prefixEnd_2603340 : Nat := 4983230072969 + 3 ^ 40 * 2603340 * 2
def baseEnd_2603340 : Nat := 1336764727075949653977463

theorem tailTrace_2603340 : CollatzResearch.WordTrace tailWord_2603340 prefixEnd_2603340 1336764727075949653977463 := by
  unfold tailWord_2603340
  simp only [CollatzResearch.WordTrace]
  refine ⟨47475805194275634959747737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63301073592367513279663649 47475805194275634959747737)
  ·
    refine ⟨35606853895706726219810803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47475805194275634959747737 35606853895706726219810803)
    ·
      refine ⟨53410280843560089329716205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35606853895706726219810803 53410280843560089329716205)
      ·
        refine ⟨20028855316335033498643577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53410280843560089329716205 20028855316335033498643577)
        ·
          refine ⟨15021641487251275123982683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20028855316335033498643577 15021641487251275123982683)
          ·
            refine ⟨22532462230876912685974025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15021641487251275123982683 22532462230876912685974025)
            ·
              refine ⟨16899346673157684514480519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22532462230876912685974025 16899346673157684514480519)
              ·
                refine ⟨25349020009736526771720779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16899346673157684514480519 25349020009736526771720779)
                ·
                  refine ⟨38023530014604790157581169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25349020009736526771720779 38023530014604790157581169)
                  ·
                    refine ⟨28517647510953592618185877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38023530014604790157581169 28517647510953592618185877)
                    ·
                      refine ⟨1336764727075949653977463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28517647510953592618185877 1336764727075949653977463)
                      ·
                        rfl

theorem cell23_2603340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2603340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603340 prefixEnd_2603340 := by exact prefixLift 2603340
  have htrace : WordTrace (prefixWord ++ tailWord_2603340) baseStart_2603340 baseEnd_2603340 := by
    simpa [prefixWord, tailWord_2603340, baseEnd_2603340] using wordTrace_append hprefix tailTrace_2603340
  have hstable : (prefixWord ++ tailWord_2603340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603340).length < 2 ^ (prefixWord ++ tailWord_2603340).sum := by decide
  have hdescent : baseEnd_2603340 < baseStart_2603340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603364 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_2603364 : Nat := 118140960795 + 2603364 * 2 ^ 59
def prefixEnd_2603364 : Nat := 4983230072969 + 3 ^ 40 * 2603364 * 2
def baseEnd_2603364 : Nat := 1336777050611657560077353

theorem tailTrace_2603364 : CollatzResearch.WordTrace tailWord_2603364 prefixEnd_2603364 1336777050611657560077353 := by
  unfold tailWord_2603364
  simp only [CollatzResearch.WordTrace]
  refine ⟨47476242870232161009184573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63301657160309548012246097 47476242870232161009184573)
  ·
    refine ⟨17803591076337060378444215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47476242870232161009184573 17803591076337060378444215)
    ·
      refine ⟨26705386614505590567666323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17803591076337060378444215 26705386614505590567666323)
      ·
        refine ⟨40058079921758385851499485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26705386614505590567666323 40058079921758385851499485)
        ·
          refine ⟨15021779970659394694312307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40058079921758385851499485 15021779970659394694312307)
          ·
            refine ⟨22532669955989092041468461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15021779970659394694312307 22532669955989092041468461)
            ·
              refine ⟨8449751233495909515550673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22532669955989092041468461 8449751233495909515550673)
              ·
                refine ⟨6337313425121932136663005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8449751233495909515550673 6337313425121932136663005)
                ·
                  refine ⟨2376492534420724551248627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6337313425121932136663005 2376492534420724551248627)
                  ·
                    refine ⟨3564738801631086826872941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2376492534420724551248627 3564738801631086826872941)
                    ·
                      refine ⟨1336777050611657560077353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3564738801631086826872941 1336777050611657560077353)
                      ·
                        rfl

theorem cell23_2603364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_2603364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603364 prefixEnd_2603364 := by exact prefixLift 2603364
  have htrace : WordTrace (prefixWord ++ tailWord_2603364) baseStart_2603364 baseEnd_2603364 := by
    simpa [prefixWord, tailWord_2603364, baseEnd_2603364] using wordTrace_append hprefix tailTrace_2603364
  have hstable : (prefixWord ++ tailWord_2603364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603364).length < 2 ^ (prefixWord ++ tailWord_2603364).sum := by decide
  have hdescent : baseEnd_2603364 < baseStart_2603364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603367 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 3, 5]
def baseStart_2603367 : Nat := 118140960795 + 2603367 * 2 ^ 59
def prefixEnd_2603367 : Nat := 4983230072969 + 3 ^ 40 * 2603367 * 2
def baseEnd_2603367 : Nat := 445592863684540349446613

theorem tailTrace_2603367 : CollatzResearch.WordTrace tailWord_2603367 prefixEnd_2603367 445592863684540349446613 := by
  unfold tailWord_2603367
  simp only [CollatzResearch.WordTrace]
  refine ⟨94952595159453453530728355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63301730106302302353818903 94952595159453453530728355)
  ·
    refine ⟨142428892739180180296092533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94952595159453453530728355 142428892739180180296092533)
    ·
      refine ⟨13352708694298141902758675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142428892739180180296092533 13352708694298141902758675)
      ·
        refine ⟨20029063041447212854138013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13352708694298141902758675 20029063041447212854138013)
        ·
          refine ⟨7510898640542704820301755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20029063041447212854138013 7510898640542704820301755)
          ·
            refine ⟨11266347960814057230452633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7510898640542704820301755 11266347960814057230452633)
            ·
              refine ⟨8449760970610542922839475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11266347960814057230452633 8449760970610542922839475)
              ·
                refine ⟨12674641455915814384259213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449760970610542922839475 12674641455915814384259213)
                ·
                  refine ⟨4752990545968430394097205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12674641455915814384259213 4752990545968430394097205)
                  ·
                    refine ⟨445592863684540349446613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4752990545968430394097205 445592863684540349446613)
                    ·
                      rfl

theorem cell23_2603367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_2603367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603367 prefixEnd_2603367 := by exact prefixLift 2603367
  have htrace : WordTrace (prefixWord ++ tailWord_2603367) baseStart_2603367 baseEnd_2603367 := by
    simpa [prefixWord, tailWord_2603367, baseEnd_2603367] using wordTrace_append hprefix tailTrace_2603367
  have hstable : (prefixWord ++ tailWord_2603367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603367).length < 2 ^ (prefixWord ++ tailWord_2603367).sum := by decide
  have hdescent : baseEnd_2603367 < baseStart_2603367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603421 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_2603421 : Nat := 118140960795 + 2603421 * 2 ^ 59
def prefixEnd_2603421 : Nat := 4983230072969 + 3 ^ 40 * 2603421 * 2
def baseEnd_2603421 : Nat := 1336806319008963837064591

theorem tailTrace_2603421 : CollatzResearch.WordTrace tailWord_2603421 prefixEnd_2603421 1336806319008963837064591 := by
  unfold tailWord_2603421
  simp only [CollatzResearch.WordTrace]
  refine ⟨94954564701257820753194117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63303043134171880502129411 94954564701257820753194117)
  ·
    refine ⟨17803980881485841391223897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94954564701257820753194117 17803980881485841391223897)
    ·
      refine ⟨13352985661114381043417923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17803980881485841391223897 13352985661114381043417923)
      ·
        refine ⟨20029478491671571565126885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13352985661114381043417923 20029478491671571565126885)
        ·
          refine ⟨3755527217188419668461291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20029478491671571565126885 3755527217188419668461291)
          ·
            refine ⟨5633290825782629502691937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755527217188419668461291 5633290825782629502691937)
            ·
              refine ⟨4224968119336972127018953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5633290825782629502691937 4224968119336972127018953)
              ·
                refine ⟨3168726089502729095264215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4224968119336972127018953 3168726089502729095264215)
                ·
                  refine ⟨4753089134254093642896323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168726089502729095264215 4753089134254093642896323)
                  ·
                    refine ⟨7129633701381140464344485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753089134254093642896323 7129633701381140464344485)
                    ·
                      refine ⟨1336806319008963837064591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7129633701381140464344485 1336806319008963837064591)
                      ·
                        rfl

theorem cell23_2603421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_2603421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603421 prefixEnd_2603421 := by exact prefixLift 2603421
  have htrace : WordTrace (prefixWord ++ tailWord_2603421) baseStart_2603421 baseEnd_2603421 := by
    simpa [prefixWord, tailWord_2603421, baseEnd_2603421] using wordTrace_append hprefix tailTrace_2603421
  have hstable : (prefixWord ++ tailWord_2603421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603421).length < 2 ^ (prefixWord ++ tailWord_2603421).sum := by decide
  have hdescent : baseEnd_2603421 < baseStart_2603421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603424 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 3]
def baseStart_2603424 : Nat := 118140960795 + 2603424 * 2 ^ 59
def prefixEnd_2603424 : Nat := 4983230072969 + 3 ^ 40 * 2603424 * 2
def baseEnd_2603424 : Nat := 1336807859450927325327077

theorem tailTrace_2603424 : CollatzResearch.WordTrace tailWord_2603424 prefixEnd_2603424 1336807859450927325327077 := by
  unfold tailWord_2603424
  simp only [CollatzResearch.WordTrace]
  refine ⟨47477337060123476132776663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63303116080164634843702217 47477337060123476132776663)
  ·
    refine ⟨71216005590185214199164995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47477337060123476132776663 71216005590185214199164995)
    ·
      refine ⟨106824008385277821298747493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71216005590185214199164995 106824008385277821298747493)
      ·
        refine ⟨20029501572239591493515155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106824008385277821298747493 20029501572239591493515155)
        ·
          refine ⟨30044252358359387240272733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20029501572239591493515155 30044252358359387240272733)
          ·
            refine ⟨11266594634384770215102275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30044252358359387240272733 11266594634384770215102275)
            ·
              refine ⟨16899891951577155322653413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11266594634384770215102275 16899891951577155322653413)
              ·
                refine ⟨3168729740920716622997515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16899891951577155322653413 3168729740920716622997515)
                ·
                  refine ⟨4753094611381074934496273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168729740920716622997515 4753094611381074934496273)
                  ·
                    refine ⟨3564820958535806200872205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4753094611381074934496273 3564820958535806200872205)
                    ·
                      refine ⟨1336807859450927325327077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3564820958535806200872205 1336807859450927325327077)
                      ·
                        rfl

theorem cell23_2603424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_2603424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603424 prefixEnd_2603424 := by exact prefixLift 2603424
  have htrace : WordTrace (prefixWord ++ tailWord_2603424) baseStart_2603424 baseEnd_2603424 := by
    simpa [prefixWord, tailWord_2603424, baseEnd_2603424] using wordTrace_append hprefix tailTrace_2603424
  have hstable : (prefixWord ++ tailWord_2603424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603424).length < 2 ^ (prefixWord ++ tailWord_2603424).sum := by decide
  have hdescent : baseEnd_2603424 < baseStart_2603424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603427 : List Nat := [1, 1, 1, 4, 1, 4, 4, 7]
def baseStart_2603427 : Nat := 118140960795 + 2603427 * 2 ^ 59
def prefixEnd_2603427 : Nat := 4983230072969 + 3 ^ 40 * 2603427 * 2
def baseEnd_2603427 : Nat := 49511459255292252355169

theorem tailTrace_2603427 : CollatzResearch.WordTrace tailWord_2603427 prefixEnd_2603427 49511459255292252355169 := by
  unfold tailWord_2603427
  simp only [CollatzResearch.WordTrace]
  refine ⟨94954783539236083777912535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63303189026157389185275023 94954783539236083777912535)
  ·
    refine ⟨142432175308854125666868803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94954783539236083777912535 142432175308854125666868803)
    ·
      refine ⟨213648262963281188500303205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142432175308854125666868803 213648262963281188500303205)
      ·
        refine ⟨40059049305615222843806851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213648262963281188500303205 40059049305615222843806851)
        ·
          refine ⟨60088573958422834265710277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40059049305615222843806851 60088573958422834265710277)
          ·
            refine ⟨11266607617204281424820677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60088573958422834265710277 11266607617204281424820677)
            ·
              refine ⟨2112488928225802767153877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11266607617204281424820677 2112488928225802767153877)
              ·
                refine ⟨49511459255292252355169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2112488928225802767153877 49511459255292252355169)
                ·
                  rfl

theorem cell23_2603427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 7].length) (baseStart_2603427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603427 prefixEnd_2603427 := by exact prefixLift 2603427
  have htrace : WordTrace (prefixWord ++ tailWord_2603427) baseStart_2603427 baseEnd_2603427 := by
    simpa [prefixWord, tailWord_2603427, baseEnd_2603427] using wordTrace_append hprefix tailTrace_2603427
  have hstable : (prefixWord ++ tailWord_2603427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603427).length < 2 ^ (prefixWord ++ tailWord_2603427).sum := by decide
  have hdescent : baseEnd_2603427 < baseStart_2603427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603507 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 4]
def baseStart_2603507 : Nat := 118140960795 + 2603507 * 2 ^ 59
def prefixEnd_2603507 : Nat := 4983230072969 + 3 ^ 40 * 2603507 * 2
def baseEnd_2603507 : Nat := 1336850478345250500589195

theorem tailTrace_2603507 : CollatzResearch.WordTrace tailWord_2603507 prefixEnd_2603507 1336850478345250500589195 := by
  unfold tailWord_2603507
  simp only [CollatzResearch.WordTrace]
  refine ⟨94957701378946257440824775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63305134252630838293883183 94957701378946257440824775)
  ·
    refine ⟨142436552068419386161237163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94957701378946257440824775 142436552068419386161237163)
    ·
      refine ⟨213654828102629079241855745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142436552068419386161237163 213654828102629079241855745)
      ·
        refine ⟨160241121076971809431391809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213654828102629079241855745 160241121076971809431391809)
        ·
          refine ⟨120180840807728857073543857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160241121076971809431391809 120180840807728857073543857)
          ·
            refine ⟨90135630605796642805157893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120180840807728857073543857 90135630605796642805157893)
            ·
              refine ⟨16900430738586870525967105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90135630605796642805157893 16900430738586870525967105)
              ·
                refine ⟨12675323053940152894475329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16900430738586870525967105 12675323053940152894475329)
                ·
                  refine ⟨9506492290455114670856497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12675323053940152894475329 9506492290455114670856497)
                  ·
                    refine ⟨7129869217841336003142373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9506492290455114670856497 7129869217841336003142373)
                    ·
                      refine ⟨1336850478345250500589195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7129869217841336003142373 1336850478345250500589195)
                      ·
                        rfl

theorem cell23_2603507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_2603507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603507 prefixEnd_2603507 := by exact prefixLift 2603507
  have htrace : WordTrace (prefixWord ++ tailWord_2603507) baseStart_2603507 baseEnd_2603507 := by
    simpa [prefixWord, tailWord_2603507, baseEnd_2603507] using wordTrace_append hprefix tailTrace_2603507
  have hstable : (prefixWord ++ tailWord_2603507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603507).length < 2 ^ (prefixWord ++ tailWord_2603507).sum := by decide
  have hdescent : baseEnd_2603507 < baseStart_2603507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603517 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 7]
def baseStart_2603517 : Nat := 118140960795 + 2603517 * 2 ^ 59
def prefixEnd_2603517 : Nat := 4983230072969 + 3 ^ 40 * 2603517 * 2
def baseEnd_2603517 : Nat := 148539512572421717940461

theorem tailTrace_2603517 : CollatzResearch.WordTrace tailWord_2603517 prefixEnd_2603517 148539512572421717940461 := by
  unfold tailWord_2603517
  simp only [CollatzResearch.WordTrace]
  refine ⟨94958066108910029148688805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63305377405940019432459203 94958066108910029148688805)
  ·
    refine ⟨17804637395420630465379151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94958066108910029148688805 17804637395420630465379151)
    ·
      refine ⟨26706956093130945698068727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17804637395420630465379151 26706956093130945698068727)
      ·
        refine ⟨40060434139696418547103091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26706956093130945698068727 40060434139696418547103091)
        ·
          refine ⟨60090651209544627820654637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40060434139696418547103091 60090651209544627820654637)
          ·
            refine ⟨22533994203579235432745489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60090651209544627820654637 22533994203579235432745489)
            ·
              refine ⟨16900495652684426574559117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22533994203579235432745489 16900495652684426574559117)
              ·
                refine ⟨6337685869756659965459669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16900495652684426574559117 6337685869756659965459669)
                ·
                  refine ⟨148539512572421717940461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6337685869756659965459669 148539512572421717940461)
                  ·
                    rfl

theorem cell23_2603517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_2603517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603517 prefixEnd_2603517 := by exact prefixLift 2603517
  have htrace : WordTrace (prefixWord ++ tailWord_2603517) baseStart_2603517 baseEnd_2603517 := by
    simpa [prefixWord, tailWord_2603517, baseEnd_2603517] using wordTrace_append hprefix tailTrace_2603517
  have hstable : (prefixWord ++ tailWord_2603517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603517).length < 2 ^ (prefixWord ++ tailWord_2603517).sum := by decide
  have hdescent : baseEnd_2603517 < baseStart_2603517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603524 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2603524 : Nat := 118140960795 + 2603524 * 2 ^ 59
def prefixEnd_2603524 : Nat := 4983230072969 + 3 ^ 40 * 2603524 * 2
def baseEnd_2603524 : Nat := 1336859207516376934076617

theorem tailTrace_2603524 : CollatzResearch.WordTrace tailWord_2603524 prefixEnd_2603524 1336859207516376934076617 := by
  unfold tailWord_2603524
  simp only [CollatzResearch.WordTrace]
  refine ⟨47479160709942334672096813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63305547613256446229462417 47479160709942334672096813)
  ·
    refine ⟨17804685266228375502036305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47479160709942334672096813 17804685266228375502036305)
    ·
      refine ⟨13353513949671281626527229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17804685266228375502036305 13353513949671281626527229)
      ·
        refine ⟨5007567731126730609947711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13353513949671281626527229 5007567731126730609947711)
        ·
          refine ⟨7511351596690095914921567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007567731126730609947711 7511351596690095914921567)
          ·
            refine ⟨11267027395035143872382351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511351596690095914921567 11267027395035143872382351)
            ·
              refine ⟨16900541092552715808573527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11267027395035143872382351 16900541092552715808573527)
              ·
                refine ⟨25350811638829073712860291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16900541092552715808573527 25350811638829073712860291)
                ·
                  refine ⟨38026217458243610569290437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25350811638829073712860291 38026217458243610569290437)
                  ·
                    refine ⟨7129915773420676981741957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38026217458243610569290437 7129915773420676981741957)
                    ·
                      refine ⟨1336859207516376934076617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7129915773420676981741957 1336859207516376934076617)
                      ·
                        rfl

theorem cell23_2603524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2603524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603524 prefixEnd_2603524 := by exact prefixLift 2603524
  have htrace : WordTrace (prefixWord ++ tailWord_2603524) baseStart_2603524 baseEnd_2603524 := by
    simpa [prefixWord, tailWord_2603524, baseEnd_2603524] using wordTrace_append hprefix tailTrace_2603524
  have hstable : (prefixWord ++ tailWord_2603524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603524).length < 2 ^ (prefixWord ++ tailWord_2603524).sum := by decide
  have hdescent : baseEnd_2603524 < baseStart_2603524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603534 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_2603534 : Nat := 118140960795 + 2603534 * 2 ^ 59
def prefixEnd_2603534 : Nat := 4983230072969 + 3 ^ 40 * 2603534 * 2
def baseEnd_2603534 : Nat := 148540482480324654994619

theorem tailTrace_2603534 : CollatzResearch.WordTrace tailWord_2603534 prefixEnd_2603534 148540482480324654994619 := by
  unfold tailWord_2603534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869835768731055131507207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63305790766565627368038437 11869835768731055131507207)
  ·
    refine ⟨17804753653096582697260811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11869835768731055131507207 17804753653096582697260811)
    ·
      refine ⟨26707130479644874045891217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17804753653096582697260811 26707130479644874045891217)
      ·
        refine ⟨20030347859733655534418413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26707130479644874045891217 20030347859733655534418413)
        ·
          refine ⟨7511380447400120825406905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20030347859733655534418413 7511380447400120825406905)
          ·
            refine ⟨5633535335550090619055179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7511380447400120825406905 5633535335550090619055179)
            ·
              refine ⟨8450303003325135928582769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5633535335550090619055179 8450303003325135928582769)
              ·
                refine ⟨6337727252493851946437077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8450303003325135928582769 6337727252493851946437077)
                ·
                  refine ⟨148540482480324654994619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6337727252493851946437077 148540482480324654994619)
                  ·
                    rfl

theorem cell23_2603534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_2603534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603534 prefixEnd_2603534 := by exact prefixLift 2603534
  have htrace : WordTrace (prefixWord ++ tailWord_2603534) baseStart_2603534 baseEnd_2603534 := by
    simpa [prefixWord, tailWord_2603534, baseEnd_2603534] using wordTrace_append hprefix tailTrace_2603534
  have hstable : (prefixWord ++ tailWord_2603534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603534).length < 2 ^ (prefixWord ++ tailWord_2603534).sum := by decide
  have hdescent : baseEnd_2603534 < baseStart_2603534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603557 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_2603557 : Nat := 118140960795 + 2603557 * 2 ^ 59
def prefixEnd_2603557 : Nat := 4983230072969 + 3 ^ 40 * 2603557 * 2
def baseEnd_2603557 : Nat := 1336876152377975304963965

theorem tailTrace_2603557 : CollatzResearch.WordTrace tailWord_2603557 prefixEnd_2603557 1336876152377975304963965 := by
  unfold tailWord_2603557
  simp only [CollatzResearch.WordTrace]
  refine ⟨94959525028765115980144925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63306350019176743986763283 94959525028765115980144925)
  ·
    refine ⟨35609821885786918492554347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94959525028765115980144925 35609821885786918492554347)
    ·
      refine ⟨53414732828680377738831521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35609821885786918492554347 53414732828680377738831521)
      ·
        refine ⟨40061049621510283304123641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53414732828680377738831521 40061049621510283304123641)
        ·
          refine ⟨30045787216132712478092731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40061049621510283304123641 30045787216132712478092731)
          ·
            refine ⟨45068680824199068717139097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30045787216132712478092731 45068680824199068717139097)
            ·
              refine ⟨33801510618149301537854323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45068680824199068717139097 33801510618149301537854323)
              ·
                refine ⟨50702265927223952306781485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33801510618149301537854323 50702265927223952306781485)
                ·
                  refine ⟨19013349722708982115043057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50702265927223952306781485 19013349722708982115043057)
                  ·
                    refine ⟨14260012292031736586282293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19013349722708982115043057 14260012292031736586282293)
                    ·
                      refine ⟨1336876152377975304963965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14260012292031736586282293 1336876152377975304963965)
                      ·
                        rfl

theorem cell23_2603557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_2603557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603557 prefixEnd_2603557 := by exact prefixLift 2603557
  have htrace : WordTrace (prefixWord ++ tailWord_2603557) baseStart_2603557 baseEnd_2603557 := by
    simpa [prefixWord, tailWord_2603557, baseEnd_2603557] using wordTrace_append hprefix tailTrace_2603557
  have hstable : (prefixWord ++ tailWord_2603557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603557).length < 2 ^ (prefixWord ++ tailWord_2603557).sum := by decide
  have hdescent : baseEnd_2603557 < baseStart_2603557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603607 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 10]
def baseStart_2603607 : Nat := 118140960795 + 2603607 * 2 ^ 59
def prefixEnd_2603607 : Nat := 4983230072969 + 3 ^ 40 * 2603607 * 2
def baseEnd_2603607 : Nat := 148544647378966678815415

theorem tailTrace_2603607 : CollatzResearch.WordTrace tailWord_2603607 prefixEnd_2603607 148544647378966678815415 := by
  unfold tailWord_2603607
  simp only [CollatzResearch.WordTrace]
  refine ⟨94961348678583974519465075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63307565785722649679643383 94961348678583974519465075)
  ·
    refine ⟨142442023017875961779197613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94961348678583974519465075 142442023017875961779197613)
    ·
      refine ⟨53415758631703485667199105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142442023017875961779197613 53415758631703485667199105)
      ·
        refine ⟨40061818973777614250399329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53415758631703485667199105 40061818973777614250399329)
        ·
          refine ⟨30046364230333210687799497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40061818973777614250399329 30046364230333210687799497)
          ·
            refine ⟨22534773172749908015849623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30046364230333210687799497 22534773172749908015849623)
            ·
              refine ⟨33802159759124862023774435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22534773172749908015849623 33802159759124862023774435)
              ·
                refine ⟨50703239638687293035661653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33802159759124862023774435 50703239638687293035661653)
                ·
                  refine ⟨148544647378966678815415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50703239638687293035661653 148544647378966678815415)
                  ·
                    rfl

theorem cell23_2603607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 10].length) (baseStart_2603607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603607 prefixEnd_2603607 := by exact prefixLift 2603607
  have htrace : WordTrace (prefixWord ++ tailWord_2603607) baseStart_2603607 baseEnd_2603607 := by
    simpa [prefixWord, tailWord_2603607, baseEnd_2603607] using wordTrace_append hprefix tailTrace_2603607
  have hstable : (prefixWord ++ tailWord_2603607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603607).length < 2 ^ (prefixWord ++ tailWord_2603607).sum := by decide
  have hdescent : baseEnd_2603607 < baseStart_2603607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603627 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 6]
def baseStart_2603627 : Nat := 118140960795 + 2603627 * 2 ^ 59
def prefixEnd_2603627 : Nat := 4983230072969 + 3 ^ 40 * 2603627 * 2
def baseEnd_2603627 : Nat := 1336912096023790031088643

theorem tailTrace_2603627 : CollatzResearch.WordTrace tailWord_2603627 prefixEnd_2603627 1336912096023790031088643 := by
  unfold tailWord_2603627
  simp only [CollatzResearch.WordTrace]
  refine ⟨94962078138511517935193135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63308052092341011956795423 94962078138511517935193135)
  ·
    refine ⟨142443117207767276902789703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94962078138511517935193135 142443117207767276902789703)
    ·
      refine ⟨213664675811650915354184555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142443117207767276902789703 213664675811650915354184555)
      ·
        refine ⟨320497013717476373031276833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213664675811650915354184555 320497013717476373031276833)
        ·
          refine ⟨240372760288107279773457625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320497013717476373031276833 240372760288107279773457625)
          ·
            refine ⟨180279570216080459830093219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240372760288107279773457625 180279570216080459830093219)
            ·
              refine ⟨270419355324120689745139829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180279570216080459830093219 270419355324120689745139829)
              ·
                refine ⟨25351814561636314663606859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270419355324120689745139829 25351814561636314663606859)
                ·
                  refine ⟨38027721842454471995410289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25351814561636314663606859 38027721842454471995410289)
                  ·
                    refine ⟨28520791381840853996557717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38027721842454471995410289 28520791381840853996557717)
                    ·
                      refine ⟨1336912096023790031088643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28520791381840853996557717 1336912096023790031088643)
                      ·
                        rfl

theorem cell23_2603627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_2603627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603627 prefixEnd_2603627 := by exact prefixLift 2603627
  have htrace : WordTrace (prefixWord ++ tailWord_2603627) baseStart_2603627 baseEnd_2603627 := by
    simpa [prefixWord, tailWord_2603627, baseEnd_2603627] using wordTrace_append hprefix tailTrace_2603627
  have hstable : (prefixWord ++ tailWord_2603627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603627).length < 2 ^ (prefixWord ++ tailWord_2603627).sum := by decide
  have hdescent : baseEnd_2603627 < baseStart_2603627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603641 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 6]
def baseStart_2603641 : Nat := 118140960795 + 2603641 * 2 ^ 59
def prefixEnd_2603641 : Nat := 4983230072969 + 3 ^ 40 * 2603641 * 2
def baseEnd_2603641 : Nat := 148546587194772552923731

theorem tailTrace_2603641 : CollatzResearch.WordTrace tailWord_2603641 prefixEnd_2603641 148546587194772552923731 := by
  unfold tailWord_2603641
  simp only [CollatzResearch.WordTrace]
  refine ⟨94962588760460798326202777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63308392506973865550801851 94962588760460798326202777)
  ·
    refine ⟨71221941570345598744652083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94962588760460798326202777 71221941570345598744652083)
    ·
      refine ⟨106832912355518398116978125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71221941570345598744652083 106832912355518398116978125)
      ·
        refine ⟨40062342133319399293866797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106832912355518398116978125 40062342133319399293866797)
        ·
          refine ⟨15023378299994774735200049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40062342133319399293866797 15023378299994774735200049)
          ·
            refine ⟨11267533724996081051400037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15023378299994774735200049 11267533724996081051400037)
            ·
              refine ⟨2112662573436765197137507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11267533724996081051400037 2112662573436765197137507)
              ·
                refine ⟨3168993860155147795706261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112662573436765197137507 3168993860155147795706261)
                ·
                  refine ⟨148546587194772552923731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3168993860155147795706261 148546587194772552923731)
                  ·
                    rfl

theorem cell23_2603641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 6].length) (baseStart_2603641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603641 prefixEnd_2603641 := by exact prefixLift 2603641
  have htrace : WordTrace (prefixWord ++ tailWord_2603641) baseStart_2603641 baseEnd_2603641 := by
    simpa [prefixWord, tailWord_2603641, baseEnd_2603641] using wordTrace_append hprefix tailTrace_2603641
  have hstable : (prefixWord ++ tailWord_2603641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603641).length < 2 ^ (prefixWord ++ tailWord_2603641).sum := by decide
  have hdescent : baseEnd_2603641 < baseStart_2603641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603647 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_2603647 : Nat := 118140960795 + 2603647 * 2 ^ 59
def prefixEnd_2603647 : Nat := 4983230072969 + 3 ^ 40 * 2603647 * 2
def baseEnd_2603647 : Nat := 1336922365636879952838551

theorem tailTrace_2603647 : CollatzResearch.WordTrace tailWord_2603647 prefixEnd_2603647 1336922365636879952838551 := by
  unfold tailWord_2603647
  simp only [CollatzResearch.WordTrace]
  refine ⟨94962807598439061350921195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63308538398959374233947463 94962807598439061350921195)
  ·
    refine ⟨142444211397658592026381793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94962807598439061350921195 142444211397658592026381793)
    ·
      refine ⟨106833158548243944019786345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142444211397658592026381793 106833158548243944019786345)
      ·
        refine ⟨80124868911182958014839759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106833158548243944019786345 80124868911182958014839759)
        ·
          refine ⟨120187303366774437022259639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80124868911182958014839759 120187303366774437022259639)
          ·
            refine ⟨180280955050161655533389459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120187303366774437022259639 180280955050161655533389459)
            ·
              refine ⟨270421432575242483300084189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180280955050161655533389459 270421432575242483300084189)
              ·
                refine ⟨101408037215715931237531571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270421432575242483300084189 101408037215715931237531571)
                ·
                  refine ⟨152112055823573896856297357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101408037215715931237531571 152112055823573896856297357)
                  ·
                    refine ⟨57042020933840211321111509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152112055823573896856297357 57042020933840211321111509)
                    ·
                      refine ⟨1336922365636879952838551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57042020933840211321111509 1336922365636879952838551)
                      ·
                        rfl

theorem cell23_2603647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_2603647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603647 prefixEnd_2603647 := by exact prefixLift 2603647
  have htrace : WordTrace (prefixWord ++ tailWord_2603647) baseStart_2603647 baseEnd_2603647 := by
    simpa [prefixWord, tailWord_2603647, baseEnd_2603647] using wordTrace_append hprefix tailTrace_2603647
  have hstable : (prefixWord ++ tailWord_2603647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603647).length < 2 ^ (prefixWord ++ tailWord_2603647).sum := by decide
  have hdescent : baseEnd_2603647 < baseStart_2603647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603651 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 3]
def baseStart_2603651 : Nat := 118140960795 + 2603651 * 2 ^ 59
def prefixEnd_2603651 : Nat := 4983230072969 + 3 ^ 40 * 2603651 * 2
def baseEnd_2603651 : Nat := 1336924419559497937188533

theorem tailTrace_2603651 : CollatzResearch.WordTrace tailWord_2603651 prefixEnd_2603651 1336924419559497937188533 := by
  unfold tailWord_2603651
  simp only [CollatzResearch.WordTrace]
  refine ⟨94962953490424570034066807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63308635660283046689377871 94962953490424570034066807)
  ·
    refine ⟨142444430235636855051100211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94962953490424570034066807 142444430235636855051100211)
    ·
      refine ⟨213666645353455282576650317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142444430235636855051100211 213666645353455282576650317)
      ·
        refine ⟨80124992007545730966243869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213666645353455282576650317 80124992007545730966243869)
        ·
          refine ⟨30046872002829649112341451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80124992007545730966243869 30046872002829649112341451)
          ·
            refine ⟨45070308004244473668512177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30046872002829649112341451 45070308004244473668512177)
            ·
              refine ⟨33802731003183355251384133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45070308004244473668512177 33802731003183355251384133)
              ·
                refine ⟨6338012063096879109634525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33802731003183355251384133 6338012063096879109634525)
                ·
                  refine ⟨2376754523661329666112947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6338012063096879109634525 2376754523661329666112947)
                  ·
                    refine ⟨3565131785491994499169421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2376754523661329666112947 3565131785491994499169421)
                    ·
                      refine ⟨1336924419559497937188533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3565131785491994499169421 1336924419559497937188533)
                      ·
                        rfl

theorem cell23_2603651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_2603651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603651 prefixEnd_2603651 := by exact prefixLift 2603651
  have htrace : WordTrace (prefixWord ++ tailWord_2603651) baseStart_2603651 baseEnd_2603651 := by
    simpa [prefixWord, tailWord_2603651, baseEnd_2603651] using wordTrace_append hprefix tailTrace_2603651
  have hstable : (prefixWord ++ tailWord_2603651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603651).length < 2 ^ (prefixWord ++ tailWord_2603651).sum := by decide
  have hdescent : baseEnd_2603651 < baseStart_2603651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603684 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_2603684 : Nat := 118140960795 + 2603684 * 2 ^ 59
def prefixEnd_2603684 : Nat := 4983230072969 + 3 ^ 40 * 2603684 * 2
def baseEnd_2603684 : Nat := 445647121473698769358627

theorem tailTrace_2603684 : CollatzResearch.WordTrace tailWord_2603684 prefixEnd_2603684 445647121473698769358627 := by
  unfold tailWord_2603684
  simp only [CollatzResearch.WordTrace]
  refine ⟨47482078549652508335009053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63309438066203344446678737 47482078549652508335009053)
  ·
    refine ⟨17805779456119690625628395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47482078549652508335009053 17805779456119690625628395)
    ·
      refine ⟨26708669184179535938442593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17805779456119690625628395 26708669184179535938442593)
      ·
        refine ⟨20031501888134651953831945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26708669184179535938442593 20031501888134651953831945)
        ·
          refine ⟨15023626416100988965373959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20031501888134651953831945 15023626416100988965373959)
          ·
            refine ⟨22535439624151483448060939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15023626416100988965373959 22535439624151483448060939)
            ·
              refine ⟨33803159436227225172091409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22535439624151483448060939 33803159436227225172091409)
              ·
                refine ⟨25352369577170418879068557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33803159436227225172091409 25352369577170418879068557)
                ·
                  refine ⟨9507138591438907079650709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25352369577170418879068557 9507138591438907079650709)
                  ·
                    refine ⟨445647121473698769358627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9507138591438907079650709 445647121473698769358627)
                    ·
                      rfl

theorem cell23_2603684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_2603684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603684 prefixEnd_2603684 := by exact prefixLift 2603684
  have htrace : WordTrace (prefixWord ++ tailWord_2603684) baseStart_2603684 baseEnd_2603684 := by
    simpa [prefixWord, tailWord_2603684, baseEnd_2603684] using wordTrace_append hprefix tailTrace_2603684
  have hstable : (prefixWord ++ tailWord_2603684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603684).length < 2 ^ (prefixWord ++ tailWord_2603684).sum := by decide
  have hdescent : baseEnd_2603684 < baseStart_2603684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603701 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2603701 : Nat := 118140960795 + 2603701 * 2 ^ 59
def prefixEnd_2603701 : Nat := 4983230072969 + 3 ^ 40 * 2603701 * 2
def baseEnd_2603701 : Nat := 445650031197407580521101

theorem tailTrace_2603701 : CollatzResearch.WordTrace tailWord_2603701 prefixEnd_2603701 445650031197407580521101 := by
  unfold tailWord_2603701
  simp only [CollatzResearch.WordTrace]
  refine ⟨94964777140243428573386957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63309851426828952382257971 94964777140243428573386957)
  ·
    refine ⟨35611791427591285715020109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94964777140243428573386957 35611791427591285715020109)
    ·
      refine ⟨13354421785346732143132541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35611791427591285715020109 13354421785346732143132541)
      ·
        refine ⟨5007908169505024553674703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13354421785346732143132541 5007908169505024553674703)
        ·
          refine ⟨7511862254257536830512055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007908169505024553674703 7511862254257536830512055)
          ·
            refine ⟨11267793381386305245768083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511862254257536830512055 11267793381386305245768083)
            ·
              refine ⟨16901690072079457868652125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11267793381386305245768083 16901690072079457868652125)
              ·
                refine ⟨6338133777029796700744547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16901690072079457868652125 6338133777029796700744547)
                ·
                  refine ⟨9507200665544695051116821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6338133777029796700744547 9507200665544695051116821)
                  ·
                    refine ⟨445650031197407580521101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9507200665544695051116821 445650031197407580521101)
                    ·
                      rfl

theorem cell23_2603701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2603701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603701 prefixEnd_2603701 := by exact prefixLift 2603701
  have htrace : WordTrace (prefixWord ++ tailWord_2603701) baseStart_2603701 baseEnd_2603701 := by
    simpa [prefixWord, tailWord_2603701, baseEnd_2603701] using wordTrace_append hprefix tailTrace_2603701
  have hstable : (prefixWord ++ tailWord_2603701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603701).length < 2 ^ (prefixWord ++ tailWord_2603701).sum := by decide
  have hdescent : baseEnd_2603701 < baseStart_2603701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603702 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2603702 : Nat := 118140960795 + 2603702 * 2 ^ 59
def prefixEnd_2603702 : Nat := 4983230072969 + 3 ^ 40 * 2603702 * 2
def baseEnd_2603702 : Nat := 1336950607072877237650799

theorem tailTrace_2603702 : CollatzResearch.WordTrace tailWord_2603702 prefixEnd_2603702 1336950607072877237650799 := by
  unfold tailWord_2603702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5935300850827487859010835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63309875742159870496115573 5935300850827487859010835)
  ·
    refine ⟨8902951276241231788516253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5935300850827487859010835 8902951276241231788516253)
    ·
      refine ⟨3338606728590461920693595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8902951276241231788516253 3338606728590461920693595)
      ·
        refine ⟨5007910092885692881040393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3338606728590461920693595 5007910092885692881040393)
        ·
          refine ⟨3755932569664269660780295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5007910092885692881040393 3755932569664269660780295)
          ·
            refine ⟨5633898854496404491170443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3755932569664269660780295 5633898854496404491170443)
            ·
              refine ⟨8450848281744606736755665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5633898854496404491170443 8450848281744606736755665)
              ·
                refine ⟨6338136211308455052566749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8450848281744606736755665 6338136211308455052566749)
                ·
                  refine ⟨2376801079240670644712531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6338136211308455052566749 2376801079240670644712531)
                  ·
                    refine ⟨3565201618861005967068797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2376801079240670644712531 3565201618861005967068797)
                    ·
                      refine ⟨1336950607072877237650799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3565201618861005967068797 1336950607072877237650799)
                      ·
                        rfl

theorem cell23_2603702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2603702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603702 prefixEnd_2603702 := by exact prefixLift 2603702
  have htrace : WordTrace (prefixWord ++ tailWord_2603702) baseStart_2603702 baseEnd_2603702 := by
    simpa [prefixWord, tailWord_2603702, baseEnd_2603702] using wordTrace_append hprefix tailTrace_2603702
  have hstable : (prefixWord ++ tailWord_2603702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603702).length < 2 ^ (prefixWord ++ tailWord_2603702).sum := by decide
  have hdescent : baseEnd_2603702 < baseStart_2603702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603711 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 3]
def baseStart_2603711 : Nat := 118140960795 + 2603711 * 2 ^ 59
def prefixEnd_2603711 : Nat := 4983230072969 + 3 ^ 40 * 2603711 * 2
def baseEnd_2603711 : Nat := 1336955228398767702438257

theorem tailTrace_2603711 : CollatzResearch.WordTrace tailWord_2603711 prefixEnd_2603711 1336955228398767702438257 := by
  unfold tailWord_2603711
  simp only [CollatzResearch.WordTrace]
  refine ⟨94965141870207200281250987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63310094580138133520833991 94965141870207200281250987)
  ·
    refine ⟨142447712805310800421876481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94965141870207200281250987 142447712805310800421876481)
    ·
      refine ⟨106835784603983100316407361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142447712805310800421876481 106835784603983100316407361)
      ·
        refine ⟨80126838452987325237305521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106835784603983100316407361 80126838452987325237305521)
        ·
          refine ⟨60095128839740493927979141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80126838452987325237305521 60095128839740493927979141)
          ·
            refine ⟨11267836657451342611496089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60095128839740493927979141 11267836657451342611496089)
            ·
              refine ⟨8450877493088506958622067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11267836657451342611496089 8450877493088506958622067)
              ·
                refine ⟨12676316239632760437933101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8450877493088506958622067 12676316239632760437933101)
                ·
                  refine ⟨4753618589862285164224913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12676316239632760437933101 4753618589862285164224913)
                  ·
                    refine ⟨3565213942396713873168685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4753618589862285164224913 3565213942396713873168685)
                    ·
                      refine ⟨1336955228398767702438257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3565213942396713873168685 1336955228398767702438257)
                      ·
                        rfl

theorem cell23_2603711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_2603711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603711 prefixEnd_2603711 := by exact prefixLift 2603711
  have htrace : WordTrace (prefixWord ++ tailWord_2603711) baseStart_2603711 baseEnd_2603711 := by
    simpa [prefixWord, tailWord_2603711, baseEnd_2603711] using wordTrace_append hprefix tailTrace_2603711
  have hstable : (prefixWord ++ tailWord_2603711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603711).length < 2 ^ (prefixWord ++ tailWord_2603711).sum := by decide
  have hdescent : baseEnd_2603711 < baseStart_2603711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603758 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_2603758 : Nat := 118140960795 + 2603758 * 2 ^ 59
def prefixEnd_2603758 : Nat := 4983230072969 + 3 ^ 40 * 2603758 * 2
def baseEnd_2603758 : Nat := 1336979361989529018550541

theorem tailTrace_2603758 : CollatzResearch.WordTrace tailWord_2603758 prefixEnd_2603758 1336979361989529018550541 := by
  unfold tailWord_2603758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11870857012629615913526491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63311237400691284872141285 11870857012629615913526491)
  ·
    refine ⟨17806285518944423870289737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11870857012629615913526491 17806285518944423870289737)
    ·
      refine ⟨13354714139208317902717303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17806285518944423870289737 13354714139208317902717303)
      ·
        refine ⟨20032071208812476854075955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13354714139208317902717303 20032071208812476854075955)
        ·
          refine ⟨30048106813218715281113933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20032071208812476854075955 30048106813218715281113933)
          ·
            refine ⟨11268040054957018230417725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30048106813218715281113933 11268040054957018230417725)
            ·
              refine ⟨4225515020608881836406647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11268040054957018230417725 4225515020608881836406647)
              ·
                refine ⟨6338272530913322754609971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225515020608881836406647 6338272530913322754609971)
                ·
                  refine ⟨9507408796369984131914957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6338272530913322754609971 9507408796369984131914957)
                  ·
                    refine ⟨3565278298638744049468109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9507408796369984131914957 3565278298638744049468109)
                    ·
                      refine ⟨1336979361989529018550541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3565278298638744049468109 1336979361989529018550541)
                      ·
                        rfl

theorem cell23_2603758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_2603758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603758 prefixEnd_2603758 := by exact prefixLift 2603758
  have htrace : WordTrace (prefixWord ++ tailWord_2603758) baseStart_2603758 baseEnd_2603758 := by
    simpa [prefixWord, tailWord_2603758, baseEnd_2603758] using wordTrace_append hprefix tailTrace_2603758
  have hstable : (prefixWord ++ tailWord_2603758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603758).length < 2 ^ (prefixWord ++ tailWord_2603758).sum := by decide
  have hdescent : baseEnd_2603758 < baseStart_2603758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603765 : List Nat := [1, 3, 6, 1, 1, 1, 1, 9]
def baseStart_2603765 : Nat := 118140960795 + 2603765 * 2 ^ 59
def prefixEnd_2603765 : Nat := 4983230072969 + 3 ^ 40 * 2603765 * 2
def baseEnd_2603765 : Nat := 49517887272374462635667

theorem tailTrace_2603765 : CollatzResearch.WordTrace tailWord_2603765 prefixEnd_2603765 49517887272374462635667 := by
  unfold tailWord_2603765
  simp only [CollatzResearch.WordTrace]
  refine ⟨94967111412011567503716749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63311407608007711669144499 94967111412011567503716749)
  ·
    refine ⟨35612666779504337813893781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94967111412011567503716749 35612666779504337813893781)
    ·
      refine ⟨1669343755289265835026271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35612666779504337813893781 1669343755289265835026271)
      ·
        refine ⟨2504015632933898752539407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669343755289265835026271 2504015632933898752539407)
        ·
          refine ⟨3756023449400848128809111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504015632933898752539407 3756023449400848128809111)
          ·
            refine ⟨5634035174101272193213667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756023449400848128809111 5634035174101272193213667)
            ·
              refine ⟨8451052761151908289820501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634035174101272193213667 8451052761151908289820501)
              ·
                refine ⟨49517887272374462635667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8451052761151908289820501 49517887272374462635667)
                ·
                  rfl

theorem cell23_2603765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 9].length) (baseStart_2603765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603765 prefixEnd_2603765 := by exact prefixLift 2603765
  have htrace : WordTrace (prefixWord ++ tailWord_2603765) baseStart_2603765 baseEnd_2603765 := by
    simpa [prefixWord, tailWord_2603765, baseEnd_2603765] using wordTrace_append hprefix tailTrace_2603765
  have hstable : (prefixWord ++ tailWord_2603765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603765).length < 2 ^ (prefixWord ++ tailWord_2603765).sum := by decide
  have hdescent : baseEnd_2603765 < baseStart_2603765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603824 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_2603824 : Nat := 118140960795 + 2603824 * 2 ^ 59
def prefixEnd_2603824 : Nat := 4983230072969 + 3 ^ 40 * 2603824 * 2
def baseEnd_2603824 : Nat := 1337013251712725760325237

theorem tailTrace_2603824 : CollatzResearch.WordTrace tailWord_2603824 prefixEnd_2603824 1337013251712725760325237 := by
  unfold tailWord_2603824
  simp only [CollatzResearch.WordTrace]
  refine ⟨47484631659398910290057263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63312842212531880386743017 47484631659398910290057263)
  ·
    refine ⟨71226947489098365435085895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47484631659398910290057263 71226947489098365435085895)
    ·
      refine ⟨106840421233647548152628843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71226947489098365435085895 106840421233647548152628843)
      ·
        refine ⟨160260631850471322228943265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106840421233647548152628843 160260631850471322228943265)
        ·
          refine ⟨120195473887853491671707449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160260631850471322228943265 120195473887853491671707449)
          ·
            refine ⟨90146605415890118753780587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120195473887853491671707449 90146605415890118753780587)
            ·
              refine ⟨135219908123835178130670881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90146605415890118753780587 135219908123835178130670881)
              ·
                refine ⟨101414931092876383598003161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135219908123835178130670881 101414931092876383598003161)
                ·
                  refine ⟨76061198319657287698502371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101414931092876383598003161 76061198319657287698502371)
                  ·
                    refine ⟨114091797479485931547753557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76061198319657287698502371 114091797479485931547753557)
                    ·
                      refine ⟨1337013251712725760325237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 114091797479485931547753557 1337013251712725760325237)
                      ·
                        rfl

theorem cell23_2603824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_2603824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603824 prefixEnd_2603824 := by exact prefixLift 2603824
  have htrace : WordTrace (prefixWord ++ tailWord_2603824) baseStart_2603824 baseEnd_2603824 := by
    simpa [prefixWord, tailWord_2603824, baseEnd_2603824] using wordTrace_append hprefix tailTrace_2603824
  have hstable : (prefixWord ++ tailWord_2603824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603824).length < 2 ^ (prefixWord ++ tailWord_2603824).sum := by decide
  have hdescent : baseEnd_2603824 < baseStart_2603824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603858 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_2603858 : Nat := 118140960795 + 2603858 * 2 ^ 59
def prefixEnd_2603858 : Nat := 4983230072969 + 3 ^ 40 * 2603858 * 2
def baseEnd_2603858 : Nat := 1337030710054978627300081

theorem tailTrace_2603858 : CollatzResearch.WordTrace tailWord_2603858 prefixEnd_2603858 1337030710054978627300081 := by
  unfold tailWord_2603858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23742625850168661096713057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63313668933783096257901485 23742625850168661096713057)
  ·
    refine ⟨17806969387626495822534793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23742625850168661096713057 17806969387626495822534793)
    ·
      refine ⟨13355227040719871866901095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17806969387626495822534793 13355227040719871866901095)
      ·
        refine ⟨20032840561079807800351643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13355227040719871866901095 20032840561079807800351643)
        ·
          refine ⟨30049260841619711700527465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20032840561079807800351643 30049260841619711700527465)
          ·
            refine ⟨22536945631214783775395599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30049260841619711700527465 22536945631214783775395599)
            ·
              refine ⟨33805418446822175663093399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22536945631214783775395599 33805418446822175663093399)
              ·
                refine ⟨50708127670233263494640099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33805418446822175663093399 50708127670233263494640099)
                ·
                  refine ⟨76062191505349895241960149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50708127670233263494640099 76062191505349895241960149)
                  ·
                    refine ⟨1782707613406638169733441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 76062191505349895241960149 1782707613406638169733441)
                    ·
                      refine ⟨1337030710054978627300081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1782707613406638169733441 1337030710054978627300081)
                      ·
                        rfl

theorem cell23_2603858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_2603858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603858 prefixEnd_2603858 := by exact prefixLift 2603858
  have htrace : WordTrace (prefixWord ++ tailWord_2603858) baseStart_2603858 baseEnd_2603858 := by
    simpa [prefixWord, tailWord_2603858, baseEnd_2603858] using wordTrace_append hprefix tailTrace_2603858
  have hstable : (prefixWord ++ tailWord_2603858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603858).length < 2 ^ (prefixWord ++ tailWord_2603858).sum := by decide
  have hdescent : baseEnd_2603858 < baseStart_2603858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603861 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2603861 : Nat := 118140960795 + 2603861 * 2 ^ 59
def prefixEnd_2603861 : Nat := 4983230072969 + 3 ^ 40 * 2603861 * 2
def baseEnd_2603861 : Nat := 1337032250496942115562567

theorem tailTrace_2603861 : CollatzResearch.WordTrace tailWord_2603861 prefixEnd_2603861 1337032250496942115562567 := by
  unfold tailWord_2603861
  simp only [CollatzResearch.WordTrace]
  refine ⟨94970612819663775899211437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63313741879775850599474291 94970612819663775899211437)
  ·
    refine ⟨35613979807373915962204289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94970612819663775899211437 35613979807373915962204289)
    ·
      refine ⟨26710484855530436971653217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35613979807373915962204289 26710484855530436971653217)
      ·
        refine ⟨20032863641647827728739913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26710484855530436971653217 20032863641647827728739913)
        ·
          refine ⟨15024647731235870796554935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20032863641647827728739913 15024647731235870796554935)
          ·
            refine ⟨22536971596853806194832403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15024647731235870796554935 22536971596853806194832403)
            ·
              refine ⟨33805457395280709292248605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22536971596853806194832403 33805457395280709292248605)
              ·
                refine ⟨12677046523230265984593227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33805457395280709292248605 12677046523230265984593227)
                ·
                  refine ⟨19015569784845398976889841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12677046523230265984593227 19015569784845398976889841)
                  ·
                    refine ⟨14261677338634049232667381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19015569784845398976889841 14261677338634049232667381)
                    ·
                      refine ⟨1337032250496942115562567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14261677338634049232667381 1337032250496942115562567)
                      ·
                        rfl

theorem cell23_2603861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2603861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603861 prefixEnd_2603861 := by exact prefixLift 2603861
  have htrace : WordTrace (prefixWord ++ tailWord_2603861) baseStart_2603861 baseEnd_2603861 := by
    simpa [prefixWord, tailWord_2603861, baseEnd_2603861] using wordTrace_append hprefix tailTrace_2603861
  have hstable : (prefixWord ++ tailWord_2603861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603861).length < 2 ^ (prefixWord ++ tailWord_2603861).sum := by decide
  have hdescent : baseEnd_2603861 < baseStart_2603861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603871 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_2603871 : Nat := 118140960795 + 2603871 * 2 ^ 59
def prefixEnd_2603871 : Nat := 4983230072969 + 3 ^ 40 * 2603871 * 2
def baseEnd_2603871 : Nat := 1337037385303487076437521

theorem tailTrace_2603871 : CollatzResearch.WordTrace tailWord_2603871 prefixEnd_2603871 1337037385303487076437521 := by
  unfold tailWord_2603871
  simp only [CollatzResearch.WordTrace]
  refine ⟨94970977549627547607075467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63313985033085031738050311 94970977549627547607075467)
  ·
    refine ⟨142456466324441321410613201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94970977549627547607075467 142456466324441321410613201)
    ·
      refine ⟨106842349743330991057959901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142456466324441321410613201 106842349743330991057959901)
      ·
        refine ⟨40065881153749121646734963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106842349743330991057959901 40065881153749121646734963)
        ·
          refine ⟨60098821730623682470102445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40065881153749121646734963 60098821730623682470102445)
          ·
            refine ⟨22537058148983880926288417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60098821730623682470102445 22537058148983880926288417)
            ·
              refine ⟨16902793611737910694716313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22537058148983880926288417 16902793611737910694716313)
              ·
                refine ⟨12677095208803433021037235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16902793611737910694716313 12677095208803433021037235)
                ·
                  refine ⟨19015642813205149531555853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12677095208803433021037235 19015642813205149531555853)
                  ·
                    refine ⟨7130866054951931074333445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19015642813205149531555853 7130866054951931074333445)
                    ·
                      refine ⟨1337037385303487076437521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7130866054951931074333445 1337037385303487076437521)
                      ·
                        rfl

theorem cell23_2603871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_2603871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603871 prefixEnd_2603871 := by exact prefixLift 2603871
  have htrace : WordTrace (prefixWord ++ tailWord_2603871) baseStart_2603871 baseEnd_2603871 := by
    simpa [prefixWord, tailWord_2603871, baseEnd_2603871] using wordTrace_append hprefix tailTrace_2603871
  have hstable : (prefixWord ++ tailWord_2603871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603871).length < 2 ^ (prefixWord ++ tailWord_2603871).sum := by decide
  have hdescent : baseEnd_2603871 < baseStart_2603871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603888 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 4]
def baseStart_2603888 : Nat := 118140960795 + 2603888 * 2 ^ 59
def prefixEnd_2603888 : Nat := 4983230072969 + 3 ^ 40 * 2603888 * 2
def baseEnd_2603888 : Nat := 1337046114474613509924943

theorem tailTrace_2603888 : CollatzResearch.WordTrace tailWord_2603888 prefixEnd_2603888 1337046114474613509924943 := by
  unfold tailWord_2603888
  simp only [CollatzResearch.WordTrace]
  refine ⟨47485798795282979755222159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63314398393710639673629545 47485798795282979755222159)
  ·
    refine ⟨71228698192924469632833239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47485798795282979755222159 71228698192924469632833239)
    ·
      refine ⟨106843047289386704449249859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71228698192924469632833239 106843047289386704449249859)
      ·
        refine ⟨160264570934080056673874789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106843047289386704449249859 160264570934080056673874789)
        ·
          refine ⟨30049607050140010626351523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160264570934080056673874789 30049607050140010626351523)
          ·
            refine ⟨45074410575210015939527285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30049607050140010626351523 45074410575210015939527285)
            ·
              refine ⟨4225725991425938994330683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45074410575210015939527285 4225725991425938994330683)
              ·
                refine ⟨6338588987138908491496025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225725991425938994330683 6338588987138908491496025)
                ·
                  refine ⟨4753941740354181368622019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6338588987138908491496025 4753941740354181368622019)
                  ·
                    refine ⟨7130912610531272052933029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753941740354181368622019 7130912610531272052933029)
                    ·
                      refine ⟨1337046114474613509924943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7130912610531272052933029 1337046114474613509924943)
                      ·
                        rfl

theorem cell23_2603888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_2603888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603888 prefixEnd_2603888 := by exact prefixLift 2603888
  have htrace : WordTrace (prefixWord ++ tailWord_2603888) baseStart_2603888 baseEnd_2603888 := by
    simpa [prefixWord, tailWord_2603888, baseEnd_2603888] using wordTrace_append hprefix tailTrace_2603888
  have hstable : (prefixWord ++ tailWord_2603888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603888).length < 2 ^ (prefixWord ++ tailWord_2603888).sum := by decide
  have hdescent : baseEnd_2603888 < baseStart_2603888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603901 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_2603901 : Nat := 118140960795 + 2603901 * 2 ^ 59
def prefixEnd_2603901 : Nat := 4983230072969 + 3 ^ 40 * 2603901 * 2
def baseEnd_2603901 : Nat := 1337052789723121959062383

theorem tailTrace_2603901 : CollatzResearch.WordTrace tailWord_2603901 prefixEnd_2603901 1337052789723121959062383 := by
  unfold tailWord_2603901
  simp only [CollatzResearch.WordTrace]
  refine ⟨94972071739518862730667557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63314714493012575153778371 94972071739518862730667557)
  ·
    refine ⟨17807263451159786762000167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94972071739518862730667557 17807263451159786762000167)
    ·
      refine ⟨26710895176739680143000251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17807263451159786762000167 26710895176739680143000251)
      ·
        refine ⟨40066342765109520214500377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26710895176739680143000251 40066342765109520214500377)
        ·
          refine ⟨30049757073832140160875283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40066342765109520214500377 30049757073832140160875283)
          ·
            refine ⟨45074635610748210241312925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30049757073832140160875283 45074635610748210241312925)
            ·
              refine ⟨16902988354030578840492347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45074635610748210241312925 16902988354030578840492347)
              ·
                refine ⟨25354482531045868260738521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16902988354030578840492347 25354482531045868260738521)
                ·
                  refine ⟨19015861898284401195553891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25354482531045868260738521 19015861898284401195553891)
                  ·
                    refine ⟨28523792847426601793330837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19015861898284401195553891 28523792847426601793330837)
                    ·
                      refine ⟨1337052789723121959062383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28523792847426601793330837 1337052789723121959062383)
                      ·
                        rfl

theorem cell23_2603901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_2603901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603901 prefixEnd_2603901 := by exact prefixLift 2603901
  have htrace : WordTrace (prefixWord ++ tailWord_2603901) baseStart_2603901 baseEnd_2603901 := by
    simpa [prefixWord, tailWord_2603901, baseEnd_2603901] using wordTrace_append hprefix tailTrace_2603901
  have hstable : (prefixWord ++ tailWord_2603901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603901).length < 2 ^ (prefixWord ++ tailWord_2603901).sum := by decide
  have hdescent : baseEnd_2603901 < baseStart_2603901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603908 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_2603908 : Nat := 118140960795 + 2603908 * 2 ^ 59
def prefixEnd_2603908 : Nat := 4983230072969 + 3 ^ 40 * 2603908 * 2
def baseEnd_2603908 : Nat := 1337056384087703431674851

theorem tailTrace_2603908 : CollatzResearch.WordTrace tailWord_2603908 prefixEnd_2603908 1337056384087703431674851 := by
  unfold tailWord_2603908
  simp only [CollatzResearch.WordTrace]
  refine ⟨47486163525246751463086189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63314884700329001950781585 47486163525246751463086189)
  ·
    refine ⟨17807311321967531798657321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47486163525246751463086189 17807311321967531798657321)
    ·
      refine ⟨13355483491475648848992991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17807311321967531798657321 13355483491475648848992991)
      ·
        refine ⟨20033225237213473273489487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13355483491475648848992991 20033225237213473273489487)
        ·
          refine ⟨30049837855820209910234231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20033225237213473273489487 30049837855820209910234231)
          ·
            refine ⟨45074756783730314865351347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30049837855820209910234231 45074756783730314865351347)
            ·
              refine ⟨67612135175595472298027021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45074756783730314865351347 67612135175595472298027021)
              ·
                refine ⟨25354550690848302111760133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67612135175595472298027021 25354550690848302111760133)
                ·
                  refine ⟨4753978254534056645955025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25354550690848302111760133 4753978254534056645955025)
                  ·
                    refine ⟨3565483690900542484466269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4753978254534056645955025 3565483690900542484466269)
                    ·
                      refine ⟨1337056384087703431674851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3565483690900542484466269 1337056384087703431674851)
                      ·
                        rfl

theorem cell23_2603908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_2603908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603908 prefixEnd_2603908 := by exact prefixLift 2603908
  have htrace : WordTrace (prefixWord ++ tailWord_2603908) baseStart_2603908 baseEnd_2603908 := by
    simpa [prefixWord, tailWord_2603908, baseEnd_2603908] using wordTrace_append hprefix tailTrace_2603908
  have hstable : (prefixWord ++ tailWord_2603908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603908).length < 2 ^ (prefixWord ++ tailWord_2603908).sum := by decide
  have hdescent : baseEnd_2603908 < baseStart_2603908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603915 : List Nat := [1, 1, 1, 1, 4, 2, 4, 4, 1, 4]
def baseStart_2603915 : Nat := 118140960795 + 2603915 * 2 ^ 59
def prefixEnd_2603915 : Nat := 4983230072969 + 3 ^ 40 * 2603915 * 2
def baseEnd_2603915 : Nat := 445686659484094968095773

theorem tailTrace_2603915 : CollatzResearch.WordTrace tailWord_2603915 prefixEnd_2603915 445686659484094968095773 := by
  unfold tailWord_2603915
  simp only [CollatzResearch.WordTrace]
  refine ⟨94972582361468143121677199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63315054907645428747784799 94972582361468143121677199)
  ·
    refine ⟨142458873542202214682515799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94972582361468143121677199 142458873542202214682515799)
    ·
      refine ⟨213688310313303322023773699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142458873542202214682515799 213688310313303322023773699)
      ·
        refine ⟨320532465469954983035660549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213688310313303322023773699 320532465469954983035660549)
        ·
          refine ⟨60099837275616559319186353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 320532465469954983035660549 60099837275616559319186353)
          ·
            refine ⟨45074877956712419489389765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60099837275616559319186353 45074877956712419489389765)
            ·
              refine ⟨8451539616883578654260581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45074877956712419489389765 8451539616883578654260581)
              ·
                refine ⟨1584663678165670997673859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8451539616883578654260581 1584663678165670997673859)
                ·
                  refine ⟨2376995517248506496510789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584663678165670997673859 2376995517248506496510789)
                  ·
                    refine ⟨445686659484094968095773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2376995517248506496510789 445686659484094968095773)
                    ·
                      rfl

theorem cell23_2603915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 4].length) (baseStart_2603915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603915 prefixEnd_2603915 := by exact prefixLift 2603915
  have htrace : WordTrace (prefixWord ++ tailWord_2603915) baseStart_2603915 baseEnd_2603915 := by
    simpa [prefixWord, tailWord_2603915, baseEnd_2603915] using wordTrace_append hprefix tailTrace_2603915
  have hstable : (prefixWord ++ tailWord_2603915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603915).length < 2 ^ (prefixWord ++ tailWord_2603915).sum := by decide
  have hdescent : baseEnd_2603915 < baseStart_2603915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603971 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 3, 6]
def baseStart_2603971 : Nat := 118140960795 + 2603971 * 2 ^ 59
def prefixEnd_2603971 : Nat := 4983230072969 + 3 ^ 40 * 2603971 * 2
def baseEnd_2603971 : Nat := 445696244456312228395687

theorem tailTrace_2603971 : CollatzResearch.WordTrace tailWord_2603971 prefixEnd_2603971 445696244456312228395687 := by
  unfold tailWord_2603971
  simp only [CollatzResearch.WordTrace]
  refine ⟨94974624849265264685715767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63316416566176843123810511 94974624849265264685715767)
  ·
    refine ⟨142461937273897897028573651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94974624849265264685715767 142461937273897897028573651)
    ·
      refine ⟨213692905910846845542860477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142461937273897897028573651 213692905910846845542860477)
      ·
        refine ⟨80134839716567567078572679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213692905910846845542860477 80134839716567567078572679)
        ·
          refine ⟨120202259574851350617859019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80134839716567567078572679 120202259574851350617859019)
          ·
            refine ⟨180303389362277025926788529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120202259574851350617859019 180303389362277025926788529)
            ·
              refine ⟨135227542021707769445091397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180303389362277025926788529 135227542021707769445091397)
              ·
                refine ⟨25355164129070206770954637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135227542021707769445091397 25355164129070206770954637)
                ·
                  refine ⟨9508186548401327539107989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25355164129070206770954637 9508186548401327539107989)
                  ·
                    refine ⟨445696244456312228395687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9508186548401327539107989 445696244456312228395687)
                    ·
                      rfl

theorem cell23_2603971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 6].length) (baseStart_2603971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603971 prefixEnd_2603971 := by exact prefixLift 2603971
  have htrace : WordTrace (prefixWord ++ tailWord_2603971) baseStart_2603971 baseEnd_2603971 := by
    simpa [prefixWord, tailWord_2603971, baseEnd_2603971] using wordTrace_append hprefix tailTrace_2603971
  have hstable : (prefixWord ++ tailWord_2603971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603971).length < 2 ^ (prefixWord ++ tailWord_2603971).sum := by decide
  have hdescent : baseEnd_2603971 < baseStart_2603971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2603978 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_2603978 : Nat := 118140960795 + 2603978 * 2 ^ 59
def prefixEnd_2603978 : Nat := 4983230072969 + 3 ^ 40 * 2603978 * 2
def baseEnd_2603978 : Nat := 1337092327733518157799529

theorem tailTrace_2603978 : CollatzResearch.WordTrace tailWord_2603978 prefixEnd_2603978 1337092327733518157799529 := by
  unfold tailWord_2603978
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743720040059976220305147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63316586773493269920813725 23743720040059976220305147)
  ·
    refine ⟨35615580060089964330457721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23743720040059976220305147 35615580060089964330457721)
    ·
      refine ⟨26711685045067473247843291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35615580060089964330457721 26711685045067473247843291)
      ·
        refine ⟨40067527567601209871764937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26711685045067473247843291 40067527567601209871764937)
        ·
          refine ⟨30050645675700907403823703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40067527567601209871764937 30050645675700907403823703)
          ·
            refine ⟨45075968513551361105735555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30050645675700907403823703 45075968513551361105735555)
            ·
              refine ⟨67613952770327041658603333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45075968513551361105735555 67613952770327041658603333)
              ·
                refine ⟨12677616144436320310988125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67613952770327041658603333 12677616144436320310988125)
                ·
                  refine ⟨4754106054163620116620547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12677616144436320310988125 4754106054163620116620547)
                  ·
                    refine ⟨7131159081245430174930821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4754106054163620116620547 7131159081245430174930821)
                    ·
                      refine ⟨1337092327733518157799529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7131159081245430174930821 1337092327733518157799529)
                      ·
                        rfl

theorem cell23_2603978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_2603978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2603978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2603978 prefixEnd_2603978 := by exact prefixLift 2603978
  have htrace : WordTrace (prefixWord ++ tailWord_2603978) baseStart_2603978 baseEnd_2603978 := by
    simpa [prefixWord, tailWord_2603978, baseEnd_2603978] using wordTrace_append hprefix tailTrace_2603978
  have hstable : (prefixWord ++ tailWord_2603978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2603978).length < 2 ^ (prefixWord ++ tailWord_2603978).sum := by decide
  have hdescent : baseEnd_2603978 < baseStart_2603978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2603978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604008 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2604008 : Nat := 118140960795 + 2604008 * 2 ^ 59
def prefixEnd_2604008 : Nat := 4983230072969 + 3 ^ 40 * 2604008 * 2
def baseEnd_2604008 : Nat := 1337107732153153040424391

theorem tailTrace_2604008 : CollatzResearch.WordTrace tailWord_2604008 prefixEnd_2604008 1337107732153153040424391 := by
  unfold tailWord_2604008
  simp only [CollatzResearch.WordTrace]
  refine ⟨47487987175065610002406339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63317316233420813336541785 47487987175065610002406339)
  ·
    refine ⟨71231980762598415003609509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47487987175065610002406339 71231980762598415003609509)
    ·
      refine ⟨13355996392987202813176783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71231980762598415003609509 13355996392987202813176783)
      ·
        refine ⟨20033994589480804219765175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13355996392987202813176783 20033994589480804219765175)
        ·
          refine ⟨30050991884221206329647763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20033994589480804219765175 30050991884221206329647763)
          ·
            refine ⟨45076487826331809494471645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30050991884221206329647763 45076487826331809494471645)
            ·
              refine ⟨16903682934874428560426867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45076487826331809494471645 16903682934874428560426867)
              ·
                refine ⟨25355524402311642840640301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16903682934874428560426867 25355524402311642840640301)
                ·
                  refine ⟨9508321650866866065240113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25355524402311642840640301 9508321650866866065240113)
                  ·
                    refine ⟨7131241238150149548930085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9508321650866866065240113 7131241238150149548930085)
                    ·
                      refine ⟨1337107732153153040424391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7131241238150149548930085 1337107732153153040424391)
                      ·
                        rfl

theorem cell23_2604008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2604008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604008 prefixEnd_2604008 := by exact prefixLift 2604008
  have htrace : WordTrace (prefixWord ++ tailWord_2604008) baseStart_2604008 baseEnd_2604008 := by
    simpa [prefixWord, tailWord_2604008, baseEnd_2604008] using wordTrace_append hprefix tailTrace_2604008
  have hstable : (prefixWord ++ tailWord_2604008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604008).length < 2 ^ (prefixWord ++ tailWord_2604008).sum := by decide
  have hdescent : baseEnd_2604008 < baseStart_2604008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604015 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 5]
def baseStart_2604015 : Nat := 118140960795 + 2604015 * 2 ^ 59
def prefixEnd_2604015 : Nat := 4983230072969 + 3 ^ 40 * 2604015 * 2
def baseEnd_2604015 : Nat := 1337111326517734513036859

theorem tailTrace_2604015 : CollatzResearch.WordTrace tailWord_2604015 prefixEnd_2604015 1337111326517734513036859 := by
  unfold tailWord_2604015
  simp only [CollatzResearch.WordTrace]
  refine ⟨94976229661105860200317499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63317486440737240133544999 94976229661105860200317499)
  ·
    refine ⟨142464344491658790300476249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94976229661105860200317499 142464344491658790300476249)
    ·
      refine ⟨106848258368744092725357187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142464344491658790300476249 106848258368744092725357187)
      ·
        refine ⟨160272387553116139088035781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106848258368744092725357187 160272387553116139088035781)
        ·
          refine ⟨30051072666209276079006709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160272387553116139088035781 30051072666209276079006709)
          ·
            refine ⟨2817288062457119632406879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30051072666209276079006709 2817288062457119632406879)
            ·
              refine ⟨4225932093685679448610319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817288062457119632406879 4225932093685679448610319)
              ·
                refine ⟨6338898140528519172915479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225932093685679448610319 6338898140528519172915479)
                ·
                  refine ⟨9508347210792778759373219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6338898140528519172915479 9508347210792778759373219)
                  ·
                    refine ⟨14262520816189168139059829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9508347210792778759373219 14262520816189168139059829)
                    ·
                      refine ⟨1337111326517734513036859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14262520816189168139059829 1337111326517734513036859)
                      ·
                        rfl

theorem cell23_2604015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 5].length) (baseStart_2604015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604015 prefixEnd_2604015 := by exact prefixLift 2604015
  have htrace : WordTrace (prefixWord ++ tailWord_2604015) baseStart_2604015 baseEnd_2604015 := by
    simpa [prefixWord, tailWord_2604015, baseEnd_2604015] using wordTrace_append hprefix tailTrace_2604015
  have hstable : (prefixWord ++ tailWord_2604015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604015).length < 2 ^ (prefixWord ++ tailWord_2604015).sum := by decide
  have hdescent : baseEnd_2604015 < baseStart_2604015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604018 : List Nat := [3, 2, 1, 5, 12]
def baseStart_2604018 : Nat := 118140960795 + 2604018 * 2 ^ 59
def prefixEnd_2604018 : Nat := 4983230072969 + 3 ^ 40 * 2604018 * 2
def baseEnd_2604018 : Nat := 1834174028751300413305

theorem tailTrace_2604018 : CollatzResearch.WordTrace tailWord_2604018 prefixEnd_2604018 1834174028751300413305 := by
  unfold tailWord_2604018
  simp only [CollatzResearch.WordTrace]
  refine ⟨23744084770023747928169177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63317559386729994475117805 23744084770023747928169177)
  ·
    refine ⟨17808063577517810946126883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23744084770023747928169177 17808063577517810946126883)
    ·
      refine ⟨26712095366276716419190325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17808063577517810946126883 26712095366276716419190325)
      ·
        refine ⟨2504258940588442164299093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26712095366276716419190325 2504258940588442164299093)
        ·
          refine ⟨1834174028751300413305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2504258940588442164299093 1834174028751300413305)
          ·
            rfl

theorem cell23_2604018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 12].length) (baseStart_2604018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604018 prefixEnd_2604018 := by exact prefixLift 2604018
  have htrace : WordTrace (prefixWord ++ tailWord_2604018) baseStart_2604018 baseEnd_2604018 := by
    simpa [prefixWord, tailWord_2604018, baseEnd_2604018] using wordTrace_append hprefix tailTrace_2604018
  have hstable : (prefixWord ++ tailWord_2604018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604018).length < 2 ^ (prefixWord ++ tailWord_2604018).sum := by decide
  have hdescent : baseEnd_2604018 < baseStart_2604018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604022 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2604022 : Nat := 118140960795 + 2604022 * 2 ^ 59
def prefixEnd_2604022 : Nat := 4983230072969 + 3 ^ 40 * 2604022 * 2
def baseEnd_2604022 : Nat := 445704973627438661883109

theorem tailTrace_2604022 : CollatzResearch.WordTrace tailWord_2604022 prefixEnd_2604022 445704973627438661883109 := by
  unfold tailWord_2604022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936030310755031274738895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63317656648053666930548213 5936030310755031274738895)
  ·
    refine ⟨8904045466132546912108343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5936030310755031274738895 8904045466132546912108343)
    ·
      refine ⟨13356068199198820368162515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8904045466132546912108343 13356068199198820368162515)
      ·
        refine ⟨20034102298798230552243773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13356068199198820368162515 20034102298798230552243773)
        ·
          refine ⟨7512788362049336457091415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20034102298798230552243773 7512788362049336457091415)
          ·
            refine ⟨11269182543074004685637123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7512788362049336457091415 11269182543074004685637123)
            ·
              refine ⟨16903773814611007028455685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11269182543074004685637123 16903773814611007028455685)
              ·
                refine ⟨3169457590239563817835441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16903773814611007028455685 3169457590239563817835441)
                ·
                  refine ⟨2377093192679672863376581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3169457590239563817835441 2377093192679672863376581)
                  ·
                    refine ⟨445704973627438661883109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2377093192679672863376581 445704973627438661883109)
                    ·
                      rfl

theorem cell23_2604022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2604022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604022 prefixEnd_2604022 := by exact prefixLift 2604022
  have htrace : WordTrace (prefixWord ++ tailWord_2604022) baseStart_2604022 baseEnd_2604022 := by
    simpa [prefixWord, tailWord_2604022, baseEnd_2604022] using wordTrace_append hprefix tailTrace_2604022
  have hstable : (prefixWord ++ tailWord_2604022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604022).length < 2 ^ (prefixWord ++ tailWord_2604022).sum := by decide
  have hdescent : baseEnd_2604022 < baseStart_2604022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604050 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2604050 : Nat := 118140960795 + 2604050 * 2 ^ 59
def prefixEnd_2604050 : Nat := 4983230072969 + 3 ^ 40 * 2604050 * 2
def baseEnd_2604050 : Nat := 1337129298340641876099199

theorem tailTrace_2604050 : CollatzResearch.WordTrace tailWord_2604050 prefixEnd_2604050 1337129298340641876099199 := by
  unfold tailWord_2604050
  simp only [CollatzResearch.WordTrace]
  refine ⟨23744376553994765294460401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63318337477319374118561069 23744376553994765294460401)
  ·
    refine ⟨17808282415496073970845301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23744376553994765294460401 17808282415496073970845301)
    ·
      refine ⟨1669526476452756934766747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17808282415496073970845301 1669526476452756934766747)
      ·
        refine ⟨2504289714679135402150121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669526476452756934766747 2504289714679135402150121)
        ·
          refine ⟨1878217286009351551612591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2504289714679135402150121 1878217286009351551612591)
          ·
            refine ⟨2817325929014027327418887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878217286009351551612591 2817325929014027327418887)
            ·
              refine ⟨4225988893521040991128331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817325929014027327418887 4225988893521040991128331)
              ·
                refine ⟨6338983340281561486692497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225988893521040991128331 6338983340281561486692497)
                ·
                  refine ⟨4754237505211171115019373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6338983340281561486692497 4754237505211171115019373)
                  ·
                    refine ⟨1782839064454189168132265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4754237505211171115019373 1782839064454189168132265)
                    ·
                      refine ⟨1337129298340641876099199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1782839064454189168132265 1337129298340641876099199)
                      ·
                        rfl

theorem cell23_2604050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2604050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604050 prefixEnd_2604050 := by exact prefixLift 2604050
  have htrace : WordTrace (prefixWord ++ tailWord_2604050) baseStart_2604050 baseEnd_2604050 := by
    simpa [prefixWord, tailWord_2604050, baseEnd_2604050] using wordTrace_append hprefix tailTrace_2604050
  have hstable : (prefixWord ++ tailWord_2604050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604050).length < 2 ^ (prefixWord ++ tailWord_2604050).sum := by decide
  have hdescent : baseEnd_2604050 < baseStart_2604050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604058 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2604058 : Nat := 118140960795 + 2604058 * 2 ^ 59
def prefixEnd_2604058 : Nat := 4983230072969 + 3 ^ 40 * 2604058 * 2
def baseEnd_2604058 : Nat := 1337133406185877844799161

theorem tailTrace_2604058 : CollatzResearch.WordTrace tailWord_2604058 prefixEnd_2604058 1337133406185877844799161 := by
  unfold tailWord_2604058
  simp only [CollatzResearch.WordTrace]
  refine ⟨23744449499987519636033207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63318531999966719029421885 23744449499987519636033207)
  ·
    refine ⟨35616674249981279454049811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23744449499987519636033207 35616674249981279454049811)
    ·
      refine ⟨53425011374971919181074717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35616674249981279454049811 53425011374971919181074717)
      ·
        refine ⟨20034379265614469692903019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53425011374971919181074717 20034379265614469692903019)
        ·
          refine ⟨30051568898421704539354529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20034379265614469692903019 30051568898421704539354529)
          ·
            refine ⟨22538676673816278404515897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30051568898421704539354529 22538676673816278404515897)
            ·
              refine ⟨16904007505362208803386923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22538676673816278404515897 16904007505362208803386923)
              ·
                refine ⟨25356011258043313205080385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16904007505362208803386923 25356011258043313205080385)
                ·
                  refine ⟨19017008443532484903810289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25356011258043313205080385 19017008443532484903810289)
                  ·
                    refine ⟨14262756332649363677857717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19017008443532484903810289 14262756332649363677857717)
                    ·
                      refine ⟨1337133406185877844799161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14262756332649363677857717 1337133406185877844799161)
                      ·
                        rfl

theorem cell23_2604058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2604058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604058 prefixEnd_2604058 := by exact prefixLift 2604058
  have htrace : WordTrace (prefixWord ++ tailWord_2604058) baseStart_2604058 baseEnd_2604058 := by
    simpa [prefixWord, tailWord_2604058, baseEnd_2604058] using wordTrace_append hprefix tailTrace_2604058
  have hstable : (prefixWord ++ tailWord_2604058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604058).length < 2 ^ (prefixWord ++ tailWord_2604058).sum := by decide
  have hdescent : baseEnd_2604058 < baseStart_2604058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604142 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_2604142 : Nat := 118140960795 + 2604142 * 2 ^ 59
def prefixEnd_2604142 : Nat := 4983230072969 + 3 ^ 40 * 2604142 * 2
def baseEnd_2604142 : Nat := 148575170951206168460975

theorem tailTrace_2604142 : CollatzResearch.WordTrace tailWord_2604142 prefixEnd_2604142 148575170951206168460975 := by
  unfold tailWord_2604142
  simp only [CollatzResearch.WordTrace]
  refine ⟨11872607716455720111273835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63320574487763840593460453 11872607716455720111273835)
  ·
    refine ⟨17808911574683580166910753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11872607716455720111273835 17808911574683580166910753)
    ·
      refine ⟨13356683681012685125183065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17808911574683580166910753 13356683681012685125183065)
      ·
        refine ⟨10017512760759513843887299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13356683681012685125183065 10017512760759513843887299)
        ·
          refine ⟨15026269141139270765830949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10017512760759513843887299 15026269141139270765830949)
          ·
            refine ⟨2817425463963613268593303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15026269141139270765830949 2817425463963613268593303)
            ·
              refine ⟨4226138195945419902889955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817425463963613268593303 4226138195945419902889955)
              ·
                refine ⟨6339207293918129854334933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4226138195945419902889955 6339207293918129854334933)
                ·
                  refine ⟨148575170951206168460975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6339207293918129854334933 148575170951206168460975)
                  ·
                    rfl

theorem cell23_2604142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_2604142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604142 prefixEnd_2604142 := by exact prefixLift 2604142
  have htrace : WordTrace (prefixWord ++ tailWord_2604142) baseStart_2604142 baseEnd_2604142 := by
    simpa [prefixWord, tailWord_2604142, baseEnd_2604142] using wordTrace_append hprefix tailTrace_2604142
  have hstable : (prefixWord ++ tailWord_2604142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604142).length < 2 ^ (prefixWord ++ tailWord_2604142).sum := by decide
  have hdescent : baseEnd_2604142 < baseStart_2604142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604153 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 2, 2, 2]
def baseStart_2604153 : Nat := 118140960795 + 2604153 * 2 ^ 59
def prefixEnd_2604153 : Nat := 4983230072969 + 3 ^ 40 * 2604153 * 2
def baseEnd_2604153 : Nat := 1337182186848054973111225

theorem tailTrace_2604153 : CollatzResearch.WordTrace tailWord_2604153 prefixEnd_2604153 1337182186848054973111225 := by
  unfold tailWord_2604153
  simp only [CollatzResearch.WordTrace]
  refine ⟨94981262934605909768841113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63320841956403939845894075 94981262934605909768841113)
  ·
    refine ⟨71235947200954432326630835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94981262934605909768841113 71235947200954432326630835)
    ·
      refine ⟨106853920801431648489946253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71235947200954432326630835 106853920801431648489946253)
      ·
        refine ⟨40070220300536868183729845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106853920801431648489946253 40070220300536868183729845)
        ·
          refine ⟨3756583153175331392224673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40070220300536868183729845 3756583153175331392224673)
          ·
            refine ⟨2817437364881498544168505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3756583153175331392224673 2817437364881498544168505)
            ·
              refine ⟨2113078023661123908126379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2817437364881498544168505 2113078023661123908126379)
              ·
                refine ⟨3169617035491685862189569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113078023661123908126379 3169617035491685862189569)
                ·
                  refine ⟨2377212776618764396642177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3169617035491685862189569 2377212776618764396642177)
                  ·
                    refine ⟨1782909582464073297481633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2377212776618764396642177 1782909582464073297481633)
                    ·
                      refine ⟨1337182186848054973111225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1782909582464073297481633 1337182186848054973111225)
                      ·
                        rfl

theorem cell23_2604153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_2604153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604153 prefixEnd_2604153 := by exact prefixLift 2604153
  have htrace : WordTrace (prefixWord ++ tailWord_2604153) baseStart_2604153 baseEnd_2604153 := by
    simpa [prefixWord, tailWord_2604153, baseEnd_2604153] using wordTrace_append hprefix tailTrace_2604153
  have hstable : (prefixWord ++ tailWord_2604153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604153).length < 2 ^ (prefixWord ++ tailWord_2604153).sum := by decide
  have hdescent : baseEnd_2604153 < baseStart_2604153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604192 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 2, 4, 2]
def baseStart_2604192 : Nat := 118140960795 + 2604192 * 2 ^ 59
def prefixEnd_2604192 : Nat := 4983230072969 + 3 ^ 40 * 2604192 * 2
def baseEnd_2604192 : Nat := 1337202212593580320523545

theorem tailTrace_2604192 : CollatzResearch.WordTrace tailWord_2604192 prefixEnd_2604192 1337202212593580320523545 := by
  unfold tailWord_2604192
  simp only [CollatzResearch.WordTrace]
  refine ⟨47491342690732309714755415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63321790254309746286340553 47491342690732309714755415)
  ·
    refine ⟨71237014036098464572133123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47491342690732309714755415 71237014036098464572133123)
    ·
      refine ⟨106855521054147696858199685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71237014036098464572133123 106855521054147696858199685)
      ·
        refine ⟨20035410197652693160912441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106855521054147696858199685 20035410197652693160912441)
        ·
          refine ⟨15026557648239519870684331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20035410197652693160912441 15026557648239519870684331)
          ·
            refine ⟨22539836472359279806026497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15026557648239519870684331 22539836472359279806026497)
            ·
              refine ⟨16904877354269459854519873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22539836472359279806026497 16904877354269459854519873)
              ·
                refine ⟨12678658015702094890889905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16904877354269459854519873 12678658015702094890889905)
                ·
                  refine ⟨9508993511776571168167429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12678658015702094890889905 9508993511776571168167429)
                  ·
                    refine ⟨1782936283458107094031393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9508993511776571168167429 1782936283458107094031393)
                    ·
                      refine ⟨1337202212593580320523545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1782936283458107094031393 1337202212593580320523545)
                      ·
                        rfl

theorem cell23_2604192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_2604192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604192 prefixEnd_2604192 := by exact prefixLift 2604192
  have htrace : WordTrace (prefixWord ++ tailWord_2604192) baseStart_2604192 baseEnd_2604192 := by
    simpa [prefixWord, tailWord_2604192, baseEnd_2604192] using wordTrace_append hprefix tailTrace_2604192
  have hstable : (prefixWord ++ tailWord_2604192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604192).length < 2 ^ (prefixWord ++ tailWord_2604192).sum := by decide
  have hdescent : baseEnd_2604192 < baseStart_2604192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604209 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 2, 4, 2]
def baseStart_2604209 : Nat := 118140960795 + 2604209 * 2 ^ 59
def prefixEnd_2604209 : Nat := 4983230072969 + 3 ^ 40 * 2604209 * 2
def baseEnd_2604209 : Nat := 1337210941764706754010967

theorem tailTrace_2604209 : CollatzResearch.WordTrace tailWord_2604209 prefixEnd_2604209 1337210941764706754010967 := by
  unfold tailWord_2604209
  simp only [CollatzResearch.WordTrace]
  refine ⟨94983305422403031332879681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63322203614935354221919787 94983305422403031332879681)
  ·
    refine ⟨71237479066802273499659761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94983305422403031332879681 71237479066802273499659761)
    ·
      refine ⟨53428109300101705124744821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71237479066802273499659761 53428109300101705124744821)
      ·
        refine ⟨5008885246884534855444827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53428109300101705124744821 5008885246884534855444827)
        ·
          refine ⟨7513327870326802283167241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5008885246884534855444827 7513327870326802283167241)
          ·
            refine ⟨5634995902745101712375431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7513327870326802283167241 5634995902745101712375431)
            ·
              refine ⟨8452493854117652568563147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634995902745101712375431 8452493854117652568563147)
              ·
                refine ⟨12678740781176478852844721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8452493854117652568563147 12678740781176478852844721)
                ·
                  refine ⟨9509055585882359139633541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12678740781176478852844721 9509055585882359139633541)
                  ·
                    refine ⟨1782947922352942338681289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9509055585882359139633541 1782947922352942338681289)
                    ·
                      refine ⟨1337210941764706754010967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1782947922352942338681289 1337210941764706754010967)
                      ·
                        rfl

theorem cell23_2604209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_2604209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604209 prefixEnd_2604209 := by exact prefixLift 2604209
  have htrace : WordTrace (prefixWord ++ tailWord_2604209) baseStart_2604209 baseEnd_2604209 := by
    simpa [prefixWord, tailWord_2604209, baseEnd_2604209] using wordTrace_append hprefix tailTrace_2604209
  have hstable : (prefixWord ++ tailWord_2604209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604209).length < 2 ^ (prefixWord ++ tailWord_2604209).sum := by decide
  have hdescent : baseEnd_2604209 < baseStart_2604209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604215 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 6]
def baseStart_2604215 : Nat := 118140960795 + 2604215 * 2 ^ 59
def prefixEnd_2604215 : Nat := 4983230072969 + 3 ^ 40 * 2604215 * 2
def baseEnd_2604215 : Nat := 148579335849848192281771

theorem tailTrace_2604215 : CollatzResearch.WordTrace tailWord_2604215 prefixEnd_2604215 148579335849848192281771 := by
  unfold tailWord_2604215
  simp only [CollatzResearch.WordTrace]
  refine ⟨94983524260381294357598099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63322349506920862905065399 94983524260381294357598099)
  ·
    refine ⟨142475286390571941536397149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94983524260381294357598099 142475286390571941536397149)
    ·
      refine ⟨53428232396464478076148931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142475286390571941536397149 53428232396464478076148931)
      ·
        refine ⟨80142348594696717114223397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53428232396464478076148931 80142348594696717114223397)
        ·
          refine ⟨15026690361505634458916887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80142348594696717114223397 15026690361505634458916887)
          ·
            refine ⟨22540035542258451688375331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15026690361505634458916887 22540035542258451688375331)
            ·
              refine ⟨33810053313387677532562997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22540035542258451688375331 33810053313387677532562997)
              ·
                refine ⟨3169692498130094768677781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33810053313387677532562997 3169692498130094768677781)
                ·
                  refine ⟨148579335849848192281771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3169692498130094768677781 148579335849848192281771)
                  ·
                    rfl

theorem cell23_2604215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 6].length) (baseStart_2604215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604215 prefixEnd_2604215 := by exact prefixLift 2604215
  have htrace : WordTrace (prefixWord ++ tailWord_2604215) baseStart_2604215 baseEnd_2604215 := by
    simpa [prefixWord, tailWord_2604215, baseEnd_2604215] using wordTrace_append hprefix tailTrace_2604215
  have hstable : (prefixWord ++ tailWord_2604215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604215).length < 2 ^ (prefixWord ++ tailWord_2604215).sum := by decide
  have hdescent : baseEnd_2604215 < baseStart_2604215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604226 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2604226 : Nat := 118140960795 + 2604226 * 2 ^ 59
def prefixEnd_2604226 : Nat := 4983230072969 + 3 ^ 40 * 2604226 * 2
def baseEnd_2604226 : Nat := 1337219670935833187498389

theorem tailTrace_2604226 : CollatzResearch.WordTrace tailWord_2604226 prefixEnd_2604226 1337219670935833187498389 := by
  unfold tailWord_2604226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23745981365835360809062133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63322616975560962157499021 23745981365835360809062133)
  ·
    refine ⟨2226185753047065075849575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23745981365835360809062133 2226185753047065075849575)
    ·
      refine ⟨3339278629570597613774363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2226185753047065075849575 3339278629570597613774363)
      ·
        refine ⟨5008917944355896420661545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3339278629570597613774363 5008917944355896420661545)
        ·
          refine ⟨3756688458266922315496159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5008917944355896420661545 3756688458266922315496159)
          ·
            refine ⟨5635032687400383473244239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756688458266922315496159 5635032687400383473244239)
            ·
              refine ⟨8452549031100575209866359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635032687400383473244239 8452549031100575209866359)
              ·
                refine ⟨12678823546650862814799539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8452549031100575209866359 12678823546650862814799539)
                ·
                  refine ⟨19018235319976294222199309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12678823546650862814799539 19018235319976294222199309)
                  ·
                    refine ⟨7131838244991110333324741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19018235319976294222199309 7131838244991110333324741)
                    ·
                      refine ⟨1337219670935833187498389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7131838244991110333324741 1337219670935833187498389)
                      ·
                        rfl

theorem cell23_2604226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2604226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604226 prefixEnd_2604226 := by exact prefixLift 2604226
  have htrace : WordTrace (prefixWord ++ tailWord_2604226) baseStart_2604226 baseEnd_2604226 := by
    simpa [prefixWord, tailWord_2604226, baseEnd_2604226] using wordTrace_append hprefix tailTrace_2604226
  have hstable : (prefixWord ++ tailWord_2604226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604226).length < 2 ^ (prefixWord ++ tailWord_2604226).sum := by decide
  have hdescent : baseEnd_2604226 < baseStart_2604226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604269 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_2604269 : Nat := 118140960795 + 2604269 * 2 ^ 59
def prefixEnd_2604269 : Nat := 4983230072969 + 3 ^ 40 * 2604269 * 2
def baseEnd_2604269 : Nat := 1337241750603976519260691

theorem tailTrace_2604269 : CollatzResearch.WordTrace tailWord_2604269 prefixEnd_2604269 1337241750603976519260691 := by
  unfold tailWord_2604269
  simp only [CollatzResearch.WordTrace]
  refine ⟨94985493802185661580063861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63323662534790441053375907 94985493802185661580063861)
  ·
    refine ⟨8904890043954905773130987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94985493802185661580063861 8904890043954905773130987)
    ·
      refine ⟨13357335065932358659696481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8904890043954905773130987 13357335065932358659696481)
      ·
        refine ⟨10018001299449268994772361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13357335065932358659696481 10018001299449268994772361)
        ·
          refine ⟨7513500974586951746079271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10018001299449268994772361 7513500974586951746079271)
          ·
            refine ⟨11270251461880427619118907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7513500974586951746079271 11270251461880427619118907)
            ·
              refine ⟨16905377192820641428678361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11270251461880427619118907 16905377192820641428678361)
              ·
                refine ⟨12679032894615481071508771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16905377192820641428678361 12679032894615481071508771)
                ·
                  refine ⟨19018549341923221607263157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12679032894615481071508771 19018549341923221607263157)
                  ·
                    refine ⟨1782989000805302025680921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19018549341923221607263157 1782989000805302025680921)
                    ·
                      refine ⟨1337241750603976519260691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1782989000805302025680921 1337241750603976519260691)
                      ·
                        rfl

theorem cell23_2604269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_2604269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604269 prefixEnd_2604269 := by exact prefixLift 2604269
  have htrace : WordTrace (prefixWord ++ tailWord_2604269) baseStart_2604269 baseEnd_2604269 := by
    simpa [prefixWord, tailWord_2604269, baseEnd_2604269] using wordTrace_append hprefix tailTrace_2604269
  have hstable : (prefixWord ++ tailWord_2604269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604269).length < 2 ^ (prefixWord ++ tailWord_2604269).sum := by decide
  have hdescent : baseEnd_2604269 < baseStart_2604269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604282 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2]
def baseStart_2604282 : Nat := 118140960795 + 2604282 * 2 ^ 59
def prefixEnd_2604282 : Nat := 4983230072969 + 3 ^ 40 * 2604282 * 2
def baseEnd_2604282 : Nat := 1337248425852484968398131

theorem tailTrace_2604282 : CollatzResearch.WordTrace tailWord_2604282 prefixEnd_2604282 1337248425852484968398131 := by
  unfold tailWord_2604282
  simp only [CollatzResearch.WordTrace]
  refine ⟨23746491987784641200071775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63323978634092376533524733 23746491987784641200071775)
  ·
    refine ⟨35619737981676961800107663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23746491987784641200071775 35619737981676961800107663)
    ·
      refine ⟨53429606972515442700161495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35619737981676961800107663 53429606972515442700161495)
      ·
        refine ⟨80144410458773164050242243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53429606972515442700161495 80144410458773164050242243)
        ·
          refine ⟨120216615688159746075363365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80144410458773164050242243 120216615688159746075363365)
          ·
            refine ⟨22540615441529952389130631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120216615688159746075363365 22540615441529952389130631)
            ·
              refine ⟨33810923162294928583695947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22540615441529952389130631 33810923162294928583695947)
              ·
                refine ⟨50716384743442392875543921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33810923162294928583695947 50716384743442392875543921)
                ·
                  refine ⟨38037288557581794656657941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50716384743442392875543921 38037288557581794656657941)
                  ·
                    refine ⟨1782997901136646624530841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38037288557581794656657941 1782997901136646624530841)
                    ·
                      refine ⟨1337248425852484968398131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1782997901136646624530841 1337248425852484968398131)
                      ·
                        rfl

theorem cell23_2604282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_2604282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604282 prefixEnd_2604282 := by exact prefixLift 2604282
  have htrace : WordTrace (prefixWord ++ tailWord_2604282) baseStart_2604282 baseEnd_2604282 := by
    simpa [prefixWord, tailWord_2604282, baseEnd_2604282] using wordTrace_append hprefix tailTrace_2604282
  have hstable : (prefixWord ++ tailWord_2604282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604282).length < 2 ^ (prefixWord ++ tailWord_2604282).sum := by decide
  have hdescent : baseEnd_2604282 < baseStart_2604282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604302 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2604302 : Nat := 118140960795 + 2604302 * 2 ^ 59
def prefixEnd_2604302 : Nat := 4983230072969 + 3 ^ 40 * 2604302 * 2
def baseEnd_2604302 : Nat := 1337258695465574890148039

theorem tailTrace_2604302 : CollatzResearch.WordTrace tailWord_2604302 prefixEnd_2604302 1337258695465574890148039 := by
  unfold tailWord_2604302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11873337176383263527001895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63324464940710738810676773 11873337176383263527001895)
  ·
    refine ⟨17810005764574895290502843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11873337176383263527001895 17810005764574895290502843)
    ·
      refine ⟨26715008646862342935754265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17810005764574895290502843 26715008646862342935754265)
      ·
        refine ⟨20036256485146757201815699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26715008646862342935754265 20036256485146757201815699)
        ·
          refine ⟨30054384727720135802723549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20036256485146757201815699 30054384727720135802723549)
          ·
            refine ⟨11270394272895050926021331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30054384727720135802723549 11270394272895050926021331)
            ·
              refine ⟨16905591409342576389031997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11270394272895050926021331 16905591409342576389031997)
              ·
                refine ⟨6339596778503466145886999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16905591409342576389031997 6339596778503466145886999)
                ·
                  refine ⟨9509395167755199218830499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6339596778503466145886999 9509395167755199218830499)
                  ·
                    refine ⟨14264092751632798828245749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9509395167755199218830499 14264092751632798828245749)
                    ·
                      refine ⟨1337258695465574890148039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14264092751632798828245749 1337258695465574890148039)
                      ·
                        rfl

theorem cell23_2604302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2604302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604302 prefixEnd_2604302 := by exact prefixLift 2604302
  have htrace : WordTrace (prefixWord ++ tailWord_2604302) baseStart_2604302 baseEnd_2604302 := by
    simpa [prefixWord, tailWord_2604302, baseEnd_2604302] using wordTrace_append hprefix tailTrace_2604302
  have hstable : (prefixWord ++ tailWord_2604302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604302).length < 2 ^ (prefixWord ++ tailWord_2604302).sum := by decide
  have hdescent : baseEnd_2604302 < baseStart_2604302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604316 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_2604316 : Nat := 118140960795 + 2604316 * 2 ^ 59
def prefixEnd_2604316 : Nat := 4983230072969 + 3 ^ 40 * 2604316 * 2
def baseEnd_2604316 : Nat := 1337265884194737835372975

theorem tailTrace_2604316 : CollatzResearch.WordTrace tailWord_2604316 prefixEnd_2604316 1337265884194737835372975 := by
  unfold tailWord_2604316
  simp only [CollatzResearch.WordTrace]
  refine ⟨47493604016507694303512401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63324805355343592404683201 47493604016507694303512401)
  ·
    refine ⟨35620203012380770727634301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47493604016507694303512401 35620203012380770727634301)
    ·
      refine ⟨13357576129642789022862863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35620203012380770727634301 13357576129642789022862863)
      ·
        refine ⟨20036364194464183534294295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13357576129642789022862863 20036364194464183534294295)
        ·
          refine ⟨30054546291696275301441443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20036364194464183534294295 30054546291696275301441443)
          ·
            refine ⟨45081819437544412952162165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30054546291696275301441443 45081819437544412952162165)
            ·
              refine ⟨4226420572269788714265203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45081819437544412952162165 4226420572269788714265203)
              ·
                refine ⟨6339630858404683071397805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4226420572269788714265203 6339630858404683071397805)
                ·
                  refine ⟨2377361571901756151774177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6339630858404683071397805 2377361571901756151774177)
                  ·
                    refine ⟨1783021178926317113830633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2377361571901756151774177 1783021178926317113830633)
                    ·
                      refine ⟨1337265884194737835372975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783021178926317113830633 1337265884194737835372975)
                      ·
                        rfl

theorem cell23_2604316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_2604316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604316 prefixEnd_2604316 := by exact prefixLift 2604316
  have htrace : WordTrace (prefixWord ++ tailWord_2604316) baseStart_2604316 baseEnd_2604316 := by
    simpa [prefixWord, tailWord_2604316, baseEnd_2604316] using wordTrace_append hprefix tailTrace_2604316
  have hstable : (prefixWord ++ tailWord_2604316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604316).length < 2 ^ (prefixWord ++ tailWord_2604316).sum := by decide
  have hdescent : baseEnd_2604316 < baseStart_2604316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604332 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_2604332 : Nat := 118140960795 + 2604332 * 2 ^ 59
def prefixEnd_2604332 : Nat := 4983230072969 + 3 ^ 40 * 2604332 * 2
def baseEnd_2604332 : Nat := 1337274099885209772772901

theorem tailTrace_2604332 : CollatzResearch.WordTrace tailWord_2604332 prefixEnd_2604332 1337274099885209772772901 := by
  unfold tailWord_2604332
  simp only [CollatzResearch.WordTrace]
  refine ⟨47493895800478711669803625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63325194400638282226404833 47493895800478711669803625)
  ·
    refine ⟨35620421850359033752352719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47493895800478711669803625 35620421850359033752352719)
    ·
      refine ⟨53430632775538550628529079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35620421850359033752352719 53430632775538550628529079)
      ·
        refine ⟨80145949163307825942793619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53430632775538550628529079 80145949163307825942793619)
        ·
          refine ⟨120218923744961738914190429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80145949163307825942793619 120218923744961738914190429)
          ·
            refine ⟨45082096404360652092821411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120218923744961738914190429 45082096404360652092821411)
            ·
              refine ⟨67623144606540978139232117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45082096404360652092821411 67623144606540978139232117)
              ·
                refine ⟨6339669806863216700553011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67623144606540978139232117 6339669806863216700553011)
                ·
                  refine ⟨9509504710294825050829517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6339669806863216700553011 9509504710294825050829517)
                  ·
                    refine ⟨3566064266360559394061069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9509504710294825050829517 3566064266360559394061069)
                    ·
                      refine ⟨1337274099885209772772901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3566064266360559394061069 1337274099885209772772901)
                      ·
                        rfl

theorem cell23_2604332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_2604332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604332 prefixEnd_2604332 := by exact prefixLift 2604332
  have htrace : WordTrace (prefixWord ++ tailWord_2604332) baseStart_2604332 baseEnd_2604332 := by
    simpa [prefixWord, tailWord_2604332, baseEnd_2604332] using wordTrace_append hprefix tailTrace_2604332
  have hstable : (prefixWord ++ tailWord_2604332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604332).length < 2 ^ (prefixWord ++ tailWord_2604332).sum := by decide
  have hdescent : baseEnd_2604332 < baseStart_2604332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604333 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2604333 : Nat := 118140960795 + 2604333 * 2 ^ 59
def prefixEnd_2604333 : Nat := 4983230072969 + 3 ^ 40 * 2604333 * 2
def baseEnd_2604333 : Nat := 1337274613365864268860397

theorem tailTrace_2604333 : CollatzResearch.WordTrace tailWord_2604333 prefixEnd_2604333 1337274613365864268860397 := by
  unfold tailWord_2604333
  simp only [CollatzResearch.WordTrace]
  refine ⟨94987828073953800510393653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63325218715969200340262435 94987828073953800510393653)
  ·
    refine ⟨8905108881933168797849405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94987828073953800510393653 8905108881933168797849405)
    ·
      refine ⟨3339415830724938299193527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8905108881933168797849405 3339415830724938299193527)
      ·
        refine ⟨5009123746087407448790291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3339415830724938299193527 5009123746087407448790291)
        ·
          refine ⟨7513685619131111173185437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5009123746087407448790291 7513685619131111173185437)
          ·
            refine ⟨2817632107174166689944539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7513685619131111173185437 2817632107174166689944539)
            ·
              refine ⟨4226448160761250034916809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817632107174166689944539 4226448160761250034916809)
              ·
                refine ⟨3169836120570937526187607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4226448160761250034916809 3169836120570937526187607)
                ·
                  refine ⟨4754754180856406289281411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169836120570937526187607 4754754180856406289281411)
                  ·
                    refine ⟨7132131271284609433922117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4754754180856406289281411 7132131271284609433922117)
                    ·
                      refine ⟨1337274613365864268860397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7132131271284609433922117 1337274613365864268860397)
                      ·
                        rfl

theorem cell23_2604333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2604333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604333 prefixEnd_2604333 := by exact prefixLift 2604333
  have htrace : WordTrace (prefixWord ++ tailWord_2604333) baseStart_2604333 baseEnd_2604333 := by
    simpa [prefixWord, tailWord_2604333, baseEnd_2604333] using wordTrace_append hprefix tailTrace_2604333
  have hstable : (prefixWord ++ tailWord_2604333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604333).length < 2 ^ (prefixWord ++ tailWord_2604333).sum := by decide
  have hdescent : baseEnd_2604333 < baseStart_2604333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604353 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2604353 : Nat := 118140960795 + 2604353 * 2 ^ 59
def prefixEnd_2604353 : Nat := 4983230072969 + 3 ^ 40 * 2604353 * 2
def baseEnd_2604353 : Nat := 1337284882978954190610305

theorem tailTrace_2604353 : CollatzResearch.WordTrace tailWord_2604353 prefixEnd_2604353 1337284882978954190610305 := by
  unfold tailWord_2604353
  simp only [CollatzResearch.WordTrace]
  refine ⟨94988557533881343926121713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63325705022587562617414475 94988557533881343926121713)
  ·
    refine ⟨71241418150411007944591285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94988557533881343926121713 71241418150411007944591285)
    ·
      refine ⟨6678882951601031994805433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71241418150411007944591285 6678882951601031994805433)
      ·
        refine ⟨5009162213700773996104075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6678882951601031994805433 5009162213700773996104075)
        ·
          refine ⟨7513743320551160994156113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5009162213700773996104075 7513743320551160994156113)
          ·
            refine ⟨5635307490413370745617085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7513743320551160994156113 5635307490413370745617085)
            ·
              refine ⟨2113240308905014029606407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5635307490413370745617085 2113240308905014029606407)
              ·
                refine ⟨3169860463357521044409611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113240308905014029606407 3169860463357521044409611)
                ·
                  refine ⟨4754790695036281566614417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169860463357521044409611 4754790695036281566614417)
                  ·
                    refine ⟨3566093021277211174960813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4754790695036281566614417 3566093021277211174960813)
                    ·
                      refine ⟨1337284882978954190610305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3566093021277211174960813 1337284882978954190610305)
                      ·
                        rfl

theorem cell23_2604353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2604353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604353 prefixEnd_2604353 := by exact prefixLift 2604353
  have htrace : WordTrace (prefixWord ++ tailWord_2604353) baseStart_2604353 baseEnd_2604353 := by
    simpa [prefixWord, tailWord_2604353, baseEnd_2604353] using wordTrace_append hprefix tailTrace_2604353
  have hstable : (prefixWord ++ tailWord_2604353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604353).length < 2 ^ (prefixWord ++ tailWord_2604353).sum := by decide
  have hdescent : baseEnd_2604353 < baseStart_2604353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604366 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_2604366 : Nat := 118140960795 + 2604366 * 2 ^ 59
def prefixEnd_2604366 : Nat := 4983230072969 + 3 ^ 40 * 2604366 * 2
def baseEnd_2604366 : Nat := 1337291558227462639747745

theorem tailTrace_2604366 : CollatzResearch.WordTrace tailWord_2604366 prefixEnd_2604366 1337291558227462639747745 := by
  unfold tailWord_2604366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11873628960354280893293119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63326021121889498097563301 11873628960354280893293119)
  ·
    refine ⟨17810443440531421339939679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11873628960354280893293119 17810443440531421339939679)
    ·
      refine ⟨26715665160797132009909519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17810443440531421339939679 26715665160797132009909519)
      ·
        refine ⟨40073497741195698014864279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26715665160797132009909519 40073497741195698014864279)
        ·
          refine ⟨60110246611793547022296419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40073497741195698014864279 60110246611793547022296419)
          ·
            refine ⟨90165369917690320533444629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60110246611793547022296419 90165369917690320533444629)
            ·
              refine ⟨4226501714891733775005217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90165369917690320533444629 4226501714891733775005217)
              ·
                refine ⟨3169876286168800331253913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4226501714891733775005217 3169876286168800331253913)
                ·
                  refine ⟨2377407214626600248440435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3169876286168800331253913 2377407214626600248440435)
                  ·
                    refine ⟨3566110821939900372660653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2377407214626600248440435 3566110821939900372660653)
                    ·
                      refine ⟨1337291558227462639747745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3566110821939900372660653 1337291558227462639747745)
                      ·
                        rfl

theorem cell23_2604366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_2604366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604366 prefixEnd_2604366 := by exact prefixLift 2604366
  have htrace : WordTrace (prefixWord ++ tailWord_2604366) baseStart_2604366 baseEnd_2604366 := by
    simpa [prefixWord, tailWord_2604366, baseEnd_2604366] using wordTrace_append hprefix tailTrace_2604366
  have hstable : (prefixWord ++ tailWord_2604366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604366).length < 2 ^ (prefixWord ++ tailWord_2604366).sum := by decide
  have hdescent : baseEnd_2604366 < baseStart_2604366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604372 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_2604372 : Nat := 118140960795 + 2604372 * 2 ^ 59
def prefixEnd_2604372 : Nat := 4983230072969 + 3 ^ 40 * 2604372 * 2
def baseEnd_2604372 : Nat := 1337294639111389616272717

theorem tailTrace_2604372 : CollatzResearch.WordTrace tailWord_2604372 prefixEnd_2604372 1337294639111389616272717 := by
  unfold tailWord_2604372
  simp only [CollatzResearch.WordTrace]
  refine ⟨47494625260406255085531685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63326167013875006780708913 47494625260406255085531685)
  ·
    refine ⟨8905242236326172828537191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47494625260406255085531685 8905242236326172828537191)
    ·
      refine ⟨13357863354489259242805787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8905242236326172828537191 13357863354489259242805787)
      ·
        refine ⟨20036795031733888864208681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13357863354489259242805787 20036795031733888864208681)
        ·
          refine ⟨15027596273800416648156511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20036795031733888864208681 15027596273800416648156511)
          ·
            refine ⟨22541394410700624972234767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15027596273800416648156511 22541394410700624972234767)
            ·
              refine ⟨33812091616050937458352151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22541394410700624972234767 33812091616050937458352151)
              ·
                refine ⟨50718137424076406187528227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33812091616050937458352151 50718137424076406187528227)
                ·
                  refine ⟨76077206136114609281292341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50718137424076406187528227 76077206136114609281292341)
                  ·
                    refine ⟨7132238075260744620121157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76077206136114609281292341 7132238075260744620121157)
                    ·
                      refine ⟨1337294639111389616272717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7132238075260744620121157 1337294639111389616272717)
                      ·
                        rfl

theorem cell23_2604372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_2604372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604372 prefixEnd_2604372 := by exact prefixLift 2604372
  have htrace : WordTrace (prefixWord ++ tailWord_2604372) baseStart_2604372 baseEnd_2604372 := by
    simpa [prefixWord, tailWord_2604372, baseEnd_2604372] using wordTrace_append hprefix tailTrace_2604372
  have hstable : (prefixWord ++ tailWord_2604372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604372).length < 2 ^ (prefixWord ++ tailWord_2604372).sum := by decide
  have hdescent : baseEnd_2604372 < baseStart_2604372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604402 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2604402 : Nat := 118140960795 + 2604402 * 2 ^ 59
def prefixEnd_2604402 : Nat := 4983230072969 + 3 ^ 40 * 2604402 * 2
def baseEnd_2604402 : Nat := 1337310043531024498897579

theorem tailTrace_2604402 : CollatzResearch.WordTrace tailWord_2604402 prefixEnd_2604402 1337310043531024498897579 := by
  unfold tailWord_2604402
  simp only [CollatzResearch.WordTrace]
  refine ⟨23747586177675956323663865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63326896473802550196436973 23747586177675956323663865)
  ·
    refine ⟨17810689633256967242747899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23747586177675956323663865 17810689633256967242747899)
    ·
      refine ⟨26716034449885450864121849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17810689633256967242747899 26716034449885450864121849)
      ·
        refine ⟨20037025837414088148091387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26716034449885450864121849 20037025837414088148091387)
        ·
          refine ⟨30055538756121132222137081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20037025837414088148091387 30055538756121132222137081)
          ·
            refine ⟨22541654067090849166602811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30055538756121132222137081 22541654067090849166602811)
            ·
              refine ⟨33812481100636273749904217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22541654067090849166602811 33812481100636273749904217)
              ·
                refine ⟨25359360825477205312428163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33812481100636273749904217 25359360825477205312428163)
                ·
                  refine ⟨38039041238215807968642245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25359360825477205312428163 38039041238215807968642245)
                  ·
                    refine ⟨7132320232165463994120421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38039041238215807968642245 7132320232165463994120421)
                    ·
                      refine ⟨1337310043531024498897579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7132320232165463994120421 1337310043531024498897579)
                      ·
                        rfl

theorem cell23_2604402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2604402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604402 prefixEnd_2604402 := by exact prefixLift 2604402
  have htrace : WordTrace (prefixWord ++ tailWord_2604402) baseStart_2604402 baseEnd_2604402 := by
    simpa [prefixWord, tailWord_2604402, baseEnd_2604402] using wordTrace_append hprefix tailTrace_2604402
  have hstable : (prefixWord ++ tailWord_2604402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604402).length < 2 ^ (prefixWord ++ tailWord_2604402).sum := by decide
  have hdescent : baseEnd_2604402 < baseStart_2604402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604423 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_2604423 : Nat := 118140960795 + 2604423 * 2 ^ 59
def prefixEnd_2604423 : Nat := 4983230072969 + 3 ^ 40 * 2604423 * 2
def baseEnd_2604423 : Nat := 1337320826624768916734983

theorem tailTrace_2604423 : CollatzResearch.WordTrace tailWord_2604423 prefixEnd_2604423 1337320826624768916734983 := by
  unfold tailWord_2604423
  simp only [CollatzResearch.WordTrace]
  refine ⟨94991110643627745881169923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63327407095751830587446615 94991110643627745881169923)
  ·
    refine ⟨142486665965441618821754885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94991110643627745881169923 142486665965441618821754885)
    ·
      refine ⟨26716249868520303529079041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142486665965441618821754885 26716249868520303529079041)
      ·
        refine ⟨20037187401390227646809281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26716249868520303529079041 20037187401390227646809281)
        ·
          refine ⟨15027890551042670735106961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20037187401390227646809281 15027890551042670735106961)
          ·
            refine ⟨11270917913282003051330221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15027890551042670735106961 11270917913282003051330221)
            ·
              refine ⟨4226594217480751144248833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11270917913282003051330221 4226594217480751144248833)
              ·
                refine ⟨3169945663110563358186625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4226594217480751144248833 3169945663110563358186625)
                ·
                  refine ⟨2377459247332922518639969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3169945663110563358186625 2377459247332922518639969)
                  ·
                    refine ⟨1783094435499691888979977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2377459247332922518639969 1783094435499691888979977)
                    ·
                      refine ⟨1337320826624768916734983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783094435499691888979977 1337320826624768916734983)
                      ·
                        rfl

theorem cell23_2604423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_2604423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604423 prefixEnd_2604423 := by exact prefixLift 2604423
  have htrace : WordTrace (prefixWord ++ tailWord_2604423) baseStart_2604423 baseEnd_2604423 := by
    simpa [prefixWord, tailWord_2604423, baseEnd_2604423] using wordTrace_append hprefix tailTrace_2604423
  have hstable : (prefixWord ++ tailWord_2604423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604423).length < 2 ^ (prefixWord ++ tailWord_2604423).sum := by decide
  have hdescent : baseEnd_2604423 < baseStart_2604423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604440 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 1, 4, 2]
def baseStart_2604440 : Nat := 118140960795 + 2604440 * 2 ^ 59
def prefixEnd_2604440 : Nat := 4983230072969 + 3 ^ 40 * 2604440 * 2
def baseEnd_2604440 : Nat := 1337329555795895350222405

theorem tailTrace_2604440 : CollatzResearch.WordTrace tailWord_2604440 prefixEnd_2604440 1337329555795895350222405 := by
  unfold tailWord_2604440
  simp only [CollatzResearch.WordTrace]
  refine ⟨47495865342283078892269387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63327820456377438523025849 47495865342283078892269387)
  ·
    refine ⟨71243798013424618338404081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47495865342283078892269387 71243798013424618338404081)
    ·
      refine ⟨53432848510068463753803061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71243798013424618338404081 53432848510068463753803061)
      ·
        refine ⟨5009329547818918476919037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53432848510068463753803061 5009329547818918476919037)
        ·
          refine ⟨1878498580432094428844639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5009329547818918476919037 1878498580432094428844639)
          ·
            refine ⟨2817747870648141643266959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878498580432094428844639 2817747870648141643266959)
            ·
              refine ⟨4226621805972212464900439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817747870648141643266959 4226621805972212464900439)
              ·
                refine ⟨6339932708958318697350659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4226621805972212464900439 6339932708958318697350659)
                ·
                  refine ⟨9509899063437478046025989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6339932708958318697350659 9509899063437478046025989)
                  ·
                    refine ⟨1783106074394527133629873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9509899063437478046025989 1783106074394527133629873)
                    ·
                      refine ⟨1337329555795895350222405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783106074394527133629873 1337329555795895350222405)
                      ·
                        rfl

theorem cell23_2604440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_2604440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604440 prefixEnd_2604440 := by exact prefixLift 2604440
  have htrace : WordTrace (prefixWord ++ tailWord_2604440) baseStart_2604440 baseEnd_2604440 := by
    simpa [prefixWord, tailWord_2604440, baseEnd_2604440] using wordTrace_append hprefix tailTrace_2604440
  have hstable : (prefixWord ++ tailWord_2604440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604440).length < 2 ^ (prefixWord ++ tailWord_2604440).sum := by decide
  have hdescent : baseEnd_2604440 < baseStart_2604440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604442 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_2604442 : Nat := 118140960795 + 2604442 * 2 ^ 59
def prefixEnd_2604442 : Nat := 4983230072969 + 3 ^ 40 * 2604442 * 2
def baseEnd_2604442 : Nat := 445776860919068114132465

theorem tailTrace_2604442 : CollatzResearch.WordTrace tailWord_2604442 prefixEnd_2604442 445776860919068114132465 := by
  unfold tailWord_2604442
  simp only [CollatzResearch.WordTrace]
  refine ⟨23747950907639728031527895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63327869087039274750741053 23747950907639728031527895)
  ·
    refine ⟨35621926361459592047291843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23747950907639728031527895 35621926361459592047291843)
    ·
      refine ⟨53432889542189388070937765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35621926361459592047291843 53432889542189388070937765)
      ·
        refine ⟨10018666789160510263300831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53432889542189388070937765 10018666789160510263300831)
        ·
          refine ⟨15028000183740765394951247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10018666789160510263300831 15028000183740765394951247)
          ·
            refine ⟨22542000275611148092426871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15028000183740765394951247 22542000275611148092426871)
            ·
              refine ⟨33813000413416722138640307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22542000275611148092426871 33813000413416722138640307)
              ·
                refine ⟨50719500620125083207960461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33813000413416722138640307 50719500620125083207960461)
                ·
                  refine ⟨19019812732546906202985173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50719500620125083207960461 19019812732546906202985173)
                  ·
                    refine ⟨445776860919068114132465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19019812732546906202985173 445776860919068114132465)
                    ·
                      rfl

theorem cell23_2604442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_2604442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604442 prefixEnd_2604442 := by exact prefixLift 2604442
  have htrace : WordTrace (prefixWord ++ tailWord_2604442) baseStart_2604442 baseEnd_2604442 := by
    simpa [prefixWord, tailWord_2604442, baseEnd_2604442] using wordTrace_append hprefix tailTrace_2604442
  have hstable : (prefixWord ++ tailWord_2604442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604442).length < 2 ^ (prefixWord ++ tailWord_2604442).sum := by decide
  have hdescent : baseEnd_2604442 < baseStart_2604442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604452 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2604452 : Nat := 118140960795 + 2604452 * 2 ^ 59
def prefixEnd_2604452 : Nat := 4983230072969 + 3 ^ 40 * 2604452 * 2
def baseEnd_2604452 : Nat := 1337335717563749303272349

theorem tailTrace_2604452 : CollatzResearch.WordTrace tailWord_2604452 prefixEnd_2604452 1337335717563749303272349 := by
  unfold tailWord_2604452
  simp only [CollatzResearch.WordTrace]
  refine ⟨47496084180261341916987805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63328112240348455889317073 47496084180261341916987805)
  ·
    refine ⟨17811031567598003218870427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47496084180261341916987805 17811031567598003218870427)
    ·
      refine ⟨26716547351397004828305641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17811031567598003218870427 26716547351397004828305641)
      ·
        refine ⟨20037410513547753621229231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26716547351397004828305641 20037410513547753621229231)
        ·
          refine ⟨30056115770321630431843847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20037410513547753621229231 30056115770321630431843847)
          ·
            refine ⟨45084173655482445647765771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30056115770321630431843847 45084173655482445647765771)
            ·
              refine ⟨67626260483223668471648657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45084173655482445647765771 67626260483223668471648657)
              ·
                refine ⟨50719695362417751353736493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67626260483223668471648657 50719695362417751353736493)
                ·
                  refine ⟨19019885760906656757651185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50719695362417751353736493 19019885760906656757651185)
                  ·
                    refine ⟨14264914320679992568238389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19019885760906656757651185 14264914320679992568238389)
                    ·
                      refine ⟨1337335717563749303272349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14264914320679992568238389 1337335717563749303272349)
                      ·
                        rfl

theorem cell23_2604452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2604452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604452 prefixEnd_2604452 := by exact prefixLift 2604452
  have htrace : WordTrace (prefixWord ++ tailWord_2604452) baseStart_2604452 baseEnd_2604452 := by
    simpa [prefixWord, tailWord_2604452, baseEnd_2604452] using wordTrace_append hprefix tailTrace_2604452
  have hstable : (prefixWord ++ tailWord_2604452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604452).length < 2 ^ (prefixWord ++ tailWord_2604452).sum := by decide
  have hdescent : baseEnd_2604452 < baseStart_2604452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604476 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_2604476 : Nat := 118140960795 + 2604476 * 2 ^ 59
def prefixEnd_2604476 : Nat := 4983230072969 + 3 ^ 40 * 2604476 * 2
def baseEnd_2604476 : Nat := 445782680366485736457413

theorem tailTrace_2604476 : CollatzResearch.WordTrace tailWord_2604476 prefixEnd_2604476 445782680366485736457413 := by
  unfold tailWord_2604476
  simp only [CollatzResearch.WordTrace]
  refine ⟨47496521856217867966424641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63328695808290490621899521 47496521856217867966424641)
  ·
    refine ⟨35622391392163400974818481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47496521856217867966424641 35622391392163400974818481)
    ·
      refine ⟨26716793544122550731113861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35622391392163400974818481 26716793544122550731113861)
      ·
        refine ⟨5009398789522978262083849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26716793544122550731113861 5009398789522978262083849)
        ·
          refine ⟨3757049092142233696562887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5009398789522978262083849 3757049092142233696562887)
          ·
            refine ⟨5635573638213350544844331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757049092142233696562887 5635573638213350544844331)
            ·
              refine ⟨8453360457320025817266497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635573638213350544844331 8453360457320025817266497)
              ·
                refine ⟨6340020342990019362949873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8453360457320025817266497 6340020342990019362949873)
                ·
                  refine ⟨4755015257242514522212405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6340020342990019362949873 4755015257242514522212405)
                  ·
                    refine ⟨445782680366485736457413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4755015257242514522212405 445782680366485736457413)
                    ·
                      rfl

theorem cell23_2604476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_2604476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604476 prefixEnd_2604476 := by exact prefixLift 2604476
  have htrace : WordTrace (prefixWord ++ tailWord_2604476) baseStart_2604476 baseEnd_2604476 := by
    simpa [prefixWord, tailWord_2604476, baseEnd_2604476] using wordTrace_append hprefix tailTrace_2604476
  have hstable : (prefixWord ++ tailWord_2604476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604476).length < 2 ^ (prefixWord ++ tailWord_2604476).sum := by decide
  have hdescent : baseEnd_2604476 < baseStart_2604476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604479 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 4, 4, 2]
def baseStart_2604479 : Nat := 118140960795 + 2604479 * 2 ^ 59
def prefixEnd_2604479 : Nat := 4983230072969 + 3 ^ 40 * 2604479 * 2
def baseEnd_2604479 : Nat := 1337349581541420697634725

theorem tailTrace_2604479 : CollatzResearch.WordTrace tailWord_2604479 prefixEnd_2604479 1337349581541420697634725 := by
  unfold tailWord_2604479
  simp only [CollatzResearch.WordTrace]
  refine ⟨94993153131424867445208491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63328768754283244963472327 94993153131424867445208491)
  ·
    refine ⟨142489729697137301167812737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94993153131424867445208491 142489729697137301167812737)
    ·
      refine ⟨106867297272852975875859553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142489729697137301167812737 106867297272852975875859553)
      ·
        refine ⟨80150472954639731906894665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106867297272852975875859553 80150472954639731906894665)
        ·
          refine ⟨60112854715979798930170999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80150472954639731906894665 60112854715979798930170999)
          ·
            refine ⟨90169282073969698395256499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60112854715979798930170999 90169282073969698395256499)
            ·
              refine ⟨135253923110954547592884749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90169282073969698395256499 135253923110954547592884749)
              ·
                refine ⟨50720221166607955347331781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135253923110954547592884749 50720221166607955347331781)
                ·
                  refine ⟨9510041468738991627624709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50720221166607955347331781 9510041468738991627624709)
                  ·
                    refine ⟨1783132775388560930179633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9510041468738991627624709 1783132775388560930179633)
                    ·
                      refine ⟨1337349581541420697634725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783132775388560930179633 1337349581541420697634725)
                      ·
                        rfl

theorem cell23_2604479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_2604479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604479 prefixEnd_2604479 := by exact prefixLift 2604479
  have htrace : WordTrace (prefixWord ++ tailWord_2604479) baseStart_2604479 baseEnd_2604479 := by
    simpa [prefixWord, tailWord_2604479, baseEnd_2604479] using wordTrace_append hprefix tailTrace_2604479
  have hstable : (prefixWord ++ tailWord_2604479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604479).length < 2 ^ (prefixWord ++ tailWord_2604479).sum := by decide
  have hdescent : baseEnd_2604479 < baseStart_2604479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604533 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2604533 : Nat := 118140960795 + 2604533 * 2 ^ 59
def prefixEnd_2604533 : Nat := 4983230072969 + 3 ^ 40 * 2604533 * 2
def baseEnd_2604533 : Nat := 1337377309496763486359477

theorem tailTrace_2604533 : CollatzResearch.WordTrace tailWord_2604533 prefixEnd_2604533 1337377309496763486359477 := by
  unfold tailWord_2604533
  simp only [CollatzResearch.WordTrace]
  refine ⟨94995122673229234667674253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63330081782152823111782835 94995122673229234667674253)
  ·
    refine ⟨35623171002460963000377845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94995122673229234667674253 35623171002460963000377845)
    ·
      refine ⟨3339672281480715281285423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35623171002460963000377845 3339672281480715281285423)
      ·
        refine ⟨5009508422221072921928135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3339672281480715281285423 5009508422221072921928135)
        ·
          refine ⟨7514262633331609382892203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5009508422221072921928135 7514262633331609382892203)
          ·
            refine ⟨11271393949997414074338305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7514262633331609382892203 11271393949997414074338305)
            ·
              refine ⟨8453545462498060555753729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11271393949997414074338305 8453545462498060555753729)
              ·
                refine ⟨6340159096873545416815297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8453545462498060555753729 6340159096873545416815297)
                ·
                  refine ⟨4755119322655159062611473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6340159096873545416815297 4755119322655159062611473)
                  ·
                    refine ⟨3566339491991369296958605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4755119322655159062611473 3566339491991369296958605)
                    ·
                      refine ⟨1337377309496763486359477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3566339491991369296958605 1337377309496763486359477)
                      ·
                        rfl

theorem cell23_2604533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2604533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604533 prefixEnd_2604533 := by exact prefixLift 2604533
  have htrace : WordTrace (prefixWord ++ tailWord_2604533) baseStart_2604533 baseEnd_2604533 := by
    simpa [prefixWord, tailWord_2604533, baseEnd_2604533] using wordTrace_append hprefix tailTrace_2604533
  have hstable : (prefixWord ++ tailWord_2604533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604533).length < 2 ^ (prefixWord ++ tailWord_2604533).sum := by decide
  have hdescent : baseEnd_2604533 < baseStart_2604533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604609 : List Nat := [1, 2, 5, 1, 1, 1, 2, 10]
def baseStart_2604609 : Nat := 118140960795 + 2604609 * 2 ^ 59
def prefixEnd_2604609 : Nat := 4983230072969 + 3 ^ 40 * 2604609 * 2
def baseEnd_2604609 : Nat := 49533938297277969963301

theorem tailTrace_2604609 : CollatzResearch.WordTrace tailWord_2604609 prefixEnd_2604609 49533938297277969963301 := by
  unfold tailWord_2604609
  simp only [CollatzResearch.WordTrace]
  refine ⟨94997894620953899647440881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63331929747302599764960587 94997894620953899647440881)
  ·
    refine ⟨71248420965715424735580661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94997894620953899647440881 71248420965715424735580661)
    ·
      refine ⟨6679539465535821068960687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71248420965715424735580661 6679539465535821068960687)
      ·
        refine ⟨10019309198303731603441031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6679539465535821068960687 10019309198303731603441031)
        ·
          refine ⟨15028963797455597405161547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10019309198303731603441031 15028963797455597405161547)
          ·
            refine ⟨22543445696183396107742321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15028963797455597405161547 22543445696183396107742321)
            ·
              refine ⟨16907584272137547080806741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22543445696183396107742321 16907584272137547080806741)
              ·
                refine ⟨49533938297277969963301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16907584272137547080806741 49533938297277969963301)
                ·
                  rfl

theorem cell23_2604609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 10].length) (baseStart_2604609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604609 prefixEnd_2604609 := by exact prefixLift 2604609
  have htrace : WordTrace (prefixWord ++ tailWord_2604609) baseStart_2604609 baseEnd_2604609 := by
    simpa [prefixWord, tailWord_2604609, baseEnd_2604609] using wordTrace_append hprefix tailTrace_2604609
  have hstable : (prefixWord ++ tailWord_2604609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604609).length < 2 ^ (prefixWord ++ tailWord_2604609).sum := by decide
  have hdescent : baseEnd_2604609 < baseStart_2604609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604613 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_2604613 : Nat := 118140960795 + 2604613 * 2 ^ 59
def prefixEnd_2604613 : Nat := 4983230072969 + 3 ^ 40 * 2604613 * 2
def baseEnd_2604613 : Nat := 445806129316374391119703

theorem tailTrace_2604613 : CollatzResearch.WordTrace tailWord_2604613 prefixEnd_2604613 445806129316374391119703 := by
  unfold tailWord_2604613
  simp only [CollatzResearch.WordTrace]
  refine ⟨94998040512939408330586493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63332027008626272220390995 94998040512939408330586493)
  ·
    refine ⟨35624265192352278123969935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94998040512939408330586493 35624265192352278123969935)
    ·
      refine ⟨53436397788528417185954903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35624265192352278123969935 53436397788528417185954903)
      ·
        refine ⟨80154596682792625778932355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53436397788528417185954903 80154596682792625778932355)
        ·
          refine ⟨120231895024188938668398533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80154596682792625778932355 120231895024188938668398533)
          ·
            refine ⟨22543480317035426000324725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120231895024188938668398533 22543480317035426000324725)
            ·
              refine ⟨2113451279722071187530443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22543480317035426000324725 2113451279722071187530443)
              ·
                refine ⟨3170176919583106781295665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113451279722071187530443 3170176919583106781295665)
                ·
                  refine ⟨2377632689687330085971749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3170176919583106781295665 2377632689687330085971749)
                  ·
                    refine ⟨445806129316374391119703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2377632689687330085971749 445806129316374391119703)
                    ·
                      rfl

theorem cell23_2604613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_2604613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604613 prefixEnd_2604613 := by exact prefixLift 2604613
  have htrace : WordTrace (prefixWord ++ tailWord_2604613) baseStart_2604613 baseEnd_2604613 := by
    simpa [prefixWord, tailWord_2604613, baseEnd_2604613] using wordTrace_append hprefix tailTrace_2604613
  have hstable : (prefixWord ++ tailWord_2604613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604613).length < 2 ^ (prefixWord ++ tailWord_2604613).sum := by decide
  have hdescent : baseEnd_2604613 < baseStart_2604613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604626 : List Nat := [3, 2, 2, 1, 2, 2, 4, 7]
def baseStart_2604626 : Nat := 118140960795 + 2604626 * 2 ^ 59
def prefixEnd_2604626 : Nat := 4983230072969 + 3 ^ 40 * 2604626 * 2
def baseEnd_2604626 : Nat := 49534261599912282314687

theorem tailTrace_2604626 : CollatzResearch.WordTrace tailWord_2604626 prefixEnd_2604626 49534261599912282314687 := by
  unfold tailWord_2604626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23749628665473077887702433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63332343107928207700539821 23749628665473077887702433)
  ·
    refine ⟨17812221499104808415776825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23749628665473077887702433 17812221499104808415776825)
    ·
      refine ⟨13359166124328606311832619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17812221499104808415776825 13359166124328606311832619)
      ·
        refine ⟨20038749186492909467748929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13359166124328606311832619 20038749186492909467748929)
        ·
          refine ⟨15029061889869682100811697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20038749186492909467748929 15029061889869682100811697)
          ·
            refine ⟨11271796417402261575608773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15029061889869682100811697 11271796417402261575608773)
            ·
              refine ⟨2113461828262924045426645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11271796417402261575608773 2113461828262924045426645)
              ·
                refine ⟨49534261599912282314687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2113461828262924045426645 49534261599912282314687)
                ·
                  rfl

theorem cell23_2604626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 7].length) (baseStart_2604626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604626 prefixEnd_2604626 := by exact prefixLift 2604626
  have htrace : WordTrace (prefixWord ++ tailWord_2604626) baseStart_2604626 baseEnd_2604626 := by
    simpa [prefixWord, tailWord_2604626, baseEnd_2604626] using wordTrace_append hprefix tailTrace_2604626
  have hstable : (prefixWord ++ tailWord_2604626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604626).length < 2 ^ (prefixWord ++ tailWord_2604626).sum := by decide
  have hdescent : baseEnd_2604626 < baseStart_2604626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604654 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_2604654 : Nat := 118140960795 + 2604654 * 2 ^ 59
def prefixEnd_2604654 : Nat := 4983230072969 + 3 ^ 40 * 2604654 * 2
def baseEnd_2604654 : Nat := 1337439440655957512946421

theorem tailTrace_2604654 : CollatzResearch.WordTrace tailWord_2604654 prefixEnd_2604654 1337439440655957512946421 := by
  unfold tailWord_2604654
  simp only [CollatzResearch.WordTrace]
  refine ⟨11874941988223859041603627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63333023937193914888552677 11874941988223859041603627)
  ·
    refine ⟨17812412982335788562405441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11874941988223859041603627 17812412982335788562405441)
    ·
      refine ⟨13359309736751841421804081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17812412982335788562405441 13359309736751841421804081)
      ·
        refine ⟨10019482302563881066353061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13359309736751841421804081 10019482302563881066353061)
        ·
          refine ⟨1878652931730727699941199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10019482302563881066353061 1878652931730727699941199)
          ·
            refine ⟨2817979397596091549911799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878652931730727699941199 2817979397596091549911799)
            ·
              refine ⟨4226969096394137324867699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817979397596091549911799 4226969096394137324867699)
              ·
                refine ⟨6340453644591205987301549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4226969096394137324867699 6340453644591205987301549)
                ·
                  refine ⟨2377670116721702245238081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6340453644591205987301549 2377670116721702245238081)
                  ·
                    refine ⟨1783252587541276683928561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2377670116721702245238081 1783252587541276683928561)
                    ·
                      refine ⟨1337439440655957512946421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783252587541276683928561 1337439440655957512946421)
                      ·
                        rfl

theorem cell23_2604654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_2604654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604654 prefixEnd_2604654 := by exact prefixLift 2604654
  have htrace : WordTrace (prefixWord ++ tailWord_2604654) baseStart_2604654 baseEnd_2604654 := by
    simpa [prefixWord, tailWord_2604654, baseEnd_2604654] using wordTrace_append hprefix tailTrace_2604654
  have hstable : (prefixWord ++ tailWord_2604654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604654).length < 2 ^ (prefixWord ++ tailWord_2604654).sum := by decide
  have hdescent : baseEnd_2604654 < baseStart_2604654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604689 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_2604689 : Nat := 118140960795 + 2604689 * 2 ^ 59
def prefixEnd_2604689 : Nat := 4983230072969 + 3 ^ 40 * 2604689 * 2
def baseEnd_2604689 : Nat := 1337457412478864876008759

theorem tailTrace_2604689 : CollatzResearch.WordTrace tailWord_2604689 prefixEnd_2604689 1337457412478864876008759 := by
  unfold tailWord_2604689
  simp only [CollatzResearch.WordTrace]
  refine ⟨95000812460664073310353121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63333874973776048873568747 95000812460664073310353121)
  ·
    refine ⟨71250609345498054982764841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95000812460664073310353121 71250609345498054982764841)
    ·
      refine ⟨53437957009123541237073631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71250609345498054982764841 53437957009123541237073631)
      ·
        refine ⟨80156935513685311855610447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53437957009123541237073631 80156935513685311855610447)
        ·
          refine ⟨120235403270527967783415671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80156935513685311855610447 120235403270527967783415671)
          ·
            refine ⟨180353104905791951675123507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120235403270527967783415671 180353104905791951675123507)
            ·
              refine ⟨270529657358687927512685261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180353104905791951675123507 270529657358687927512685261)
              ·
                refine ⟨101448621509507972817256973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270529657358687927512685261 101448621509507972817256973)
                ·
                  refine ⟨38043233066065489806471365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101448621509507972817256973 38043233066065489806471365)
                  ·
                    refine ⟨7133106199887279338713381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38043233066065489806471365 7133106199887279338713381)
                    ·
                      refine ⟨1337457412478864876008759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7133106199887279338713381 1337457412478864876008759)
                      ·
                        rfl

theorem cell23_2604689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_2604689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604689 prefixEnd_2604689 := by exact prefixLift 2604689
  have htrace : WordTrace (prefixWord ++ tailWord_2604689) baseStart_2604689 baseEnd_2604689 := by
    simpa [prefixWord, tailWord_2604689, baseEnd_2604689] using wordTrace_append hprefix tailTrace_2604689
  have hstable : (prefixWord ++ tailWord_2604689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604689).length < 2 ^ (prefixWord ++ tailWord_2604689).sum := by decide
  have hdescent : baseEnd_2604689 < baseStart_2604689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604693 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_2604693 : Nat := 118140960795 + 2604693 * 2 ^ 59
def prefixEnd_2604693 : Nat := 4983230072969 + 3 ^ 40 * 2604693 * 2
def baseEnd_2604693 : Nat := 1337459466401482860358741

theorem tailTrace_2604693 : CollatzResearch.WordTrace tailWord_2604693 prefixEnd_2604693 1337459466401482860358741 := by
  unfold tailWord_2604693
  simp only [CollatzResearch.WordTrace]
  refine ⟨95000958352649581993498733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63333972235099721328999155 95000958352649581993498733)
  ·
    refine ⟨35625359382243593247562025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95000958352649581993498733 35625359382243593247562025)
    ·
      refine ⟨26719019536682694935671519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35625359382243593247562025 26719019536682694935671519)
      ·
        refine ⟨40078529305024042403507279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26719019536682694935671519 40078529305024042403507279)
        ·
          refine ⟨60117793957536063605260919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40078529305024042403507279 60117793957536063605260919)
          ·
            refine ⟨90176690936304095407891379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60117793957536063605260919 90176690936304095407891379)
            ·
              refine ⟨135265036404456143111837069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90176690936304095407891379 135265036404456143111837069)
              ·
                refine ⟨50724388651671053666938901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135265036404456143111837069 50724388651671053666938901)
                ·
                  refine ⟨2377705718047080640637761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50724388651671053666938901 2377705718047080640637761)
                  ·
                    refine ⟨1783279288535310480478321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2377705718047080640637761 1783279288535310480478321)
                    ·
                      refine ⟨1337459466401482860358741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783279288535310480478321 1337459466401482860358741)
                      ·
                        rfl

theorem cell23_2604693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_2604693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604693 prefixEnd_2604693 := by exact prefixLift 2604693
  have htrace : WordTrace (prefixWord ++ tailWord_2604693) baseStart_2604693 baseEnd_2604693 := by
    simpa [prefixWord, tailWord_2604693, baseEnd_2604693] using wordTrace_append hprefix tailTrace_2604693
  have hstable : (prefixWord ++ tailWord_2604693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604693).length < 2 ^ (prefixWord ++ tailWord_2604693).sum := by decide
  have hdescent : baseEnd_2604693 < baseStart_2604693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604696 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2604696 : Nat := 118140960795 + 2604696 * 2 ^ 59
def prefixEnd_2604696 : Nat := 4983230072969 + 3 ^ 40 * 2604696 * 2
def baseEnd_2604696 : Nat := 1337461006843446348621227

theorem tailTrace_2604696 : CollatzResearch.WordTrace tailWord_2604696 prefixEnd_2604696 1337461006843446348621227 := by
  unfold tailWord_2604696
  simp only [CollatzResearch.WordTrace]
  refine ⟨47500533885819356752928971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63334045181092475670571961 47500533885819356752928971)
  ·
    refine ⟨71250800828729035129393457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47500533885819356752928971 71250800828729035129393457)
    ·
      refine ⟨53438100621546776347045093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71250800828729035129393457 53438100621546776347045093)
      ·
        refine ⟨10019643866540020565070955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53438100621546776347045093 10019643866540020565070955)
        ·
          refine ⟨15029465799810030847606433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10019643866540020565070955 15029465799810030847606433)
          ·
            refine ⟨11272099349857523135704825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15029465799810030847606433 11272099349857523135704825)
            ·
              refine ⟨8454074512393142351778619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11272099349857523135704825 8454074512393142351778619)
              ·
                refine ⟨12681111768589713527667929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8454074512393142351778619 12681111768589713527667929)
                ·
                  refine ⟨9510833826442285145750947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12681111768589713527667929 9510833826442285145750947)
                  ·
                    refine ⟨14266250739663427718626421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9510833826442285145750947 14266250739663427718626421)
                    ·
                      refine ⟨1337461006843446348621227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14266250739663427718626421 1337461006843446348621227)
                      ·
                        rfl

theorem cell23_2604696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2604696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604696 prefixEnd_2604696 := by exact prefixLift 2604696
  have htrace : WordTrace (prefixWord ++ tailWord_2604696) baseStart_2604696 baseEnd_2604696 := by
    simpa [prefixWord, tailWord_2604696, baseEnd_2604696] using wordTrace_append hprefix tailTrace_2604696
  have hstable : (prefixWord ++ tailWord_2604696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604696).length < 2 ^ (prefixWord ++ tailWord_2604696).sum := by decide
  have hdescent : baseEnd_2604696 < baseStart_2604696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604709 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_2604709 : Nat := 118140960795 + 2604709 * 2 ^ 59
def prefixEnd_2604709 : Nat := 4983230072969 + 3 ^ 40 * 2604709 * 2
def baseEnd_2604709 : Nat := 1337467682091954797758667

theorem tailTrace_2604709 : CollatzResearch.WordTrace tailWord_2604709 prefixEnd_2604709 1337467682091954797758667 := by
  unfold tailWord_2604709
  simp only [CollatzResearch.WordTrace]
  refine ⟨95001541920591616726081181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63334361280394411150720787 95001541920591616726081181)
  ·
    refine ⟨35625578220221856272280443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95001541920591616726081181 35625578220221856272280443)
    ·
      refine ⟨53438367330332784408420665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35625578220221856272280443 53438367330332784408420665)
      ·
        refine ⟨40078775497749588306315499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53438367330332784408420665 40078775497749588306315499)
        ·
          refine ⟨60118163246624382459473249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40078775497749588306315499 60118163246624382459473249)
          ·
            refine ⟨45088622434968286844604937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60118163246624382459473249 45088622434968286844604937)
            ·
              refine ⟨33816466826226215133453703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45088622434968286844604937 33816466826226215133453703)
              ·
                refine ⟨50724700239339322700180555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33816466826226215133453703 50724700239339322700180555)
                ·
                  refine ⟨76087050359008984050270833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50724700239339322700180555 76087050359008984050270833)
                  ·
                    refine ⟨57065287769256738037703125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76087050359008984050270833 57065287769256738037703125)
                    ·
                      refine ⟨1337467682091954797758667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57065287769256738037703125 1337467682091954797758667)
                      ·
                        rfl

theorem cell23_2604709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_2604709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604709 prefixEnd_2604709 := by exact prefixLift 2604709
  have htrace : WordTrace (prefixWord ++ tailWord_2604709) baseStart_2604709 baseEnd_2604709 := by
    simpa [prefixWord, tailWord_2604709, baseEnd_2604709] using wordTrace_append hprefix tailTrace_2604709
  have hstable : (prefixWord ++ tailWord_2604709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604709).length < 2 ^ (prefixWord ++ tailWord_2604709).sum := by decide
  have hdescent : baseEnd_2604709 < baseStart_2604709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604739 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 5]
def baseStart_2604739 : Nat := 118140960795 + 2604739 * 2 ^ 59
def prefixEnd_2604739 : Nat := 4983230072969 + 3 ^ 40 * 2604739 * 2
def baseEnd_2604739 : Nat := 1337483086511589680383529

theorem tailTrace_2604739 : CollatzResearch.WordTrace tailWord_2604739 prefixEnd_2604739 1337483086511589680383529 := by
  unfold tailWord_2604739
  simp only [CollatzResearch.WordTrace]
  refine ⟨95002636110482931849673271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63335090740321954566448847 95002636110482931849673271)
  ·
    refine ⟨142503954165724397774509907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95002636110482931849673271 142503954165724397774509907)
    ·
      refine ⟨213755931248586596661764861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142503954165724397774509907 213755931248586596661764861)
      ·
        refine ⟨80158474218219973748161823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213755931248586596661764861 80158474218219973748161823)
        ·
          refine ⟨120237711327329960622242735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80158474218219973748161823 120237711327329960622242735)
          ·
            refine ⟨180356566990994940933364103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120237711327329960622242735 180356566990994940933364103)
            ·
              refine ⟨270534850486492411400046155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180356566990994940933364103 270534850486492411400046155)
              ·
                refine ⟨405802275729738617100069233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270534850486492411400046155 405802275729738617100069233)
                ·
                  refine ⟨304351706797303962825051925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405802275729738617100069233 304351706797303962825051925)
                  ·
                    refine ⟨14266486256123623257424309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 304351706797303962825051925 14266486256123623257424309)
                    ·
                      refine ⟨1337483086511589680383529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14266486256123623257424309 1337483086511589680383529)
                      ·
                        rfl

theorem cell23_2604739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_2604739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604739 prefixEnd_2604739 := by exact prefixLift 2604739
  have htrace : WordTrace (prefixWord ++ tailWord_2604739) baseStart_2604739 baseEnd_2604739 := by
    simpa [prefixWord, tailWord_2604739, baseEnd_2604739] using wordTrace_append hprefix tailTrace_2604739
  have hstable : (prefixWord ++ tailWord_2604739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604739).length < 2 ^ (prefixWord ++ tailWord_2604739).sum := by decide
  have hdescent : baseEnd_2604739 < baseStart_2604739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604783 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 2, 4, 2]
def baseStart_2604783 : Nat := 118140960795 + 2604783 * 2 ^ 59
def prefixEnd_2604783 : Nat := 4983230072969 + 3 ^ 40 * 2604783 * 2
def baseEnd_2604783 : Nat := 1337505679660387508233327

theorem tailTrace_2604783 : CollatzResearch.WordTrace tailWord_2604783 prefixEnd_2604783 1337505679660387508233327 := by
  unfold tailWord_2604783
  simp only [CollatzResearch.WordTrace]
  refine ⟨95004240922323527364275003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63336160614882351576183335 95004240922323527364275003)
  ·
    refine ⟨142506361383485291046412505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95004240922323527364275003 142506361383485291046412505)
    ·
      refine ⟨106879771037613968284809379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142506361383485291046412505 106879771037613968284809379)
      ·
        refine ⟨160319656556420952427214069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106879771037613968284809379 160319656556420952427214069)
        ·
          refine ⟨15029967802164464290051319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160319656556420952427214069 15029967802164464290051319)
          ·
            refine ⟨22544951703246696435076979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15029967802164464290051319 22544951703246696435076979)
            ·
              refine ⟨33817427554870044652615469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22544951703246696435076979 33817427554870044652615469)
              ·
                refine ⟨12681535333076266744730801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33817427554870044652615469 12681535333076266744730801)
                ·
                  refine ⟨9511151499807200058548101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12681535333076266744730801 9511151499807200058548101)
                  ·
                    refine ⟨1783340906213850010977769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9511151499807200058548101 1783340906213850010977769)
                    ·
                      refine ⟨1337505679660387508233327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783340906213850010977769 1337505679660387508233327)
                      ·
                        rfl

theorem cell23_2604783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 4, 2].length) (baseStart_2604783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604783 prefixEnd_2604783 := by exact prefixLift 2604783
  have htrace : WordTrace (prefixWord ++ tailWord_2604783) baseStart_2604783 baseEnd_2604783 := by
    simpa [prefixWord, tailWord_2604783, baseEnd_2604783] using wordTrace_append hprefix tailTrace_2604783
  have hstable : (prefixWord ++ tailWord_2604783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604783).length < 2 ^ (prefixWord ++ tailWord_2604783).sum := by decide
  have hdescent : baseEnd_2604783 < baseStart_2604783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604796 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_2604796 : Nat := 118140960795 + 2604796 * 2 ^ 59
def prefixEnd_2604796 : Nat := 4983230072969 + 3 ^ 40 * 2604796 * 2
def baseEnd_2604796 : Nat := 1337512354908895957370767

theorem tailTrace_2604796 : CollatzResearch.WordTrace tailWord_2604796 prefixEnd_2604796 1337512354908895957370767 := by
  unfold tailWord_2604796
  simp only [CollatzResearch.WordTrace]
  refine ⟨47502357535638215292249121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63336476714184287056332161 47502357535638215292249121)
  ·
    refine ⟨35626768151728661469186841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47502357535638215292249121 35626768151728661469186841)
    ·
      refine ⟨26720076113796496101890131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35626768151728661469186841 26720076113796496101890131)
      ·
        refine ⟨40080114170694744152835197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26720076113796496101890131 40080114170694744152835197)
        ·
          refine ⟨15030042814010529057313199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40080114170694744152835197 15030042814010529057313199)
          ·
            refine ⟨22545064221015793585969799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15030042814010529057313199 22545064221015793585969799)
            ·
              refine ⟨33817596331523690378954699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22545064221015793585969799 33817596331523690378954699)
              ·
                refine ⟨50726394497285535568432049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33817596331523690378954699 50726394497285535568432049)
                ·
                  refine ⟨38044795872964151676324037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50726394497285535568432049 38044795872964151676324037)
                  ·
                    refine ⟨7133399226180778439310757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38044795872964151676324037 7133399226180778439310757)
                    ·
                      refine ⟨1337512354908895957370767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7133399226180778439310757 1337512354908895957370767)
                      ·
                        rfl

theorem cell23_2604796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_2604796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604796 prefixEnd_2604796 := by exact prefixLift 2604796
  have htrace : WordTrace (prefixWord ++ tailWord_2604796) baseStart_2604796 baseEnd_2604796 := by
    simpa [prefixWord, tailWord_2604796, baseEnd_2604796] using wordTrace_append hprefix tailTrace_2604796
  have hstable : (prefixWord ++ tailWord_2604796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604796).length < 2 ^ (prefixWord ++ tailWord_2604796).sum := by decide
  have hdescent : baseEnd_2604796 < baseStart_2604796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604840 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 6]
def baseStart_2604840 : Nat := 118140960795 + 2604840 * 2 ^ 59
def prefixEnd_2604840 : Nat := 4983230072969 + 3 ^ 40 * 2604840 * 2
def baseEnd_2604840 : Nat := 148614994228632642802285

theorem tailTrace_2604840 : CollatzResearch.WordTrace tailWord_2604840 prefixEnd_2604840 148614994228632642802285 := by
  unfold tailWord_2604840
  simp only [CollatzResearch.WordTrace]
  refine ⟨47503159941558513049549987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63337546588744684066066649 47503159941558513049549987)
  ·
    refine ⟨71254739912337769574324981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47503159941558513049549987 71254739912337769574324981)
    ·
      refine ⟨6680131866781665897592967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71254739912337769574324981 6680131866781665897592967)
      ·
        refine ⟨10020197800172498846389451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6680131866781665897592967 10020197800172498846389451)
        ·
          refine ⟨15030296700258748269584177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10020197800172498846389451 15030296700258748269584177)
          ·
            refine ⟨11272722525194061202188133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15030296700258748269584177 11272722525194061202188133)
            ·
              refine ⟨2113635473473886475410275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11272722525194061202188133 2113635473473886475410275)
              ·
                refine ⟨3170453210210829713115413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113635473473886475410275 3170453210210829713115413)
                ·
                  refine ⟨148614994228632642802285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3170453210210829713115413 148614994228632642802285)
                  ·
                    rfl

theorem cell23_2604840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 6].length) (baseStart_2604840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604840 prefixEnd_2604840 := by exact prefixLift 2604840
  have htrace : WordTrace (prefixWord ++ tailWord_2604840) baseStart_2604840 baseEnd_2604840 := by
    simpa [prefixWord, tailWord_2604840, baseEnd_2604840] using wordTrace_append hprefix tailTrace_2604840
  have hstable : (prefixWord ++ tailWord_2604840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604840).length < 2 ^ (prefixWord ++ tailWord_2604840).sum := by decide
  have hdescent : baseEnd_2604840 < baseStart_2604840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604860 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_2604860 : Nat := 118140960795 + 2604860 * 2 ^ 59
def prefixEnd_2604860 : Nat := 4983230072969 + 3 ^ 40 * 2604860 * 2
def baseEnd_2604860 : Nat := 1337545217670783706970473

theorem tailTrace_2604860 : CollatzResearch.WordTrace tailWord_2604860 prefixEnd_2604860 1337545217670783706970473 := by
  unfold tailWord_2604860
  simp only [CollatzResearch.WordTrace]
  refine ⟨47503524671522284757414017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63338032895363046343218689 47503524671522284757414017)
  ·
    refine ⟨35627643503641713568060513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47503524671522284757414017 35627643503641713568060513)
    ·
      refine ⟨26720732627731285176045385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35627643503641713568060513 26720732627731285176045385)
      ·
        refine ⟨20040549470798463882034039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26720732627731285176045385 20040549470798463882034039)
        ·
          refine ⟨30060824206197695823051059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20040549470798463882034039 30060824206197695823051059)
          ·
            refine ⟨45091236309296543734576589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30060824206197695823051059 45091236309296543734576589)
            ·
              refine ⟨16909213615986203900466221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45091236309296543734576589 16909213615986203900466221)
              ·
                refine ⟨6340955105994826462674833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16909213615986203900466221 6340955105994826462674833)
                ·
                  refine ⟨4755716329496119847006125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6340955105994826462674833 4755716329496119847006125)
                  ·
                    refine ⟨1783393623561044942627297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4755716329496119847006125 1783393623561044942627297)
                    ·
                      refine ⟨1337545217670783706970473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783393623561044942627297 1337545217670783706970473)
                      ·
                        rfl

theorem cell23_2604860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_2604860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604860 prefixEnd_2604860 := by exact prefixLift 2604860
  have htrace : WordTrace (prefixWord ++ tailWord_2604860) baseStart_2604860 baseEnd_2604860 := by
    simpa [prefixWord, tailWord_2604860, baseEnd_2604860] using wordTrace_append hprefix tailTrace_2604860
  have hstable : (prefixWord ++ tailWord_2604860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604860).length < 2 ^ (prefixWord ++ tailWord_2604860).sum := by decide
  have hdescent : baseEnd_2604860 < baseStart_2604860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604884 : List Nat := [2, 4, 1, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_2604884 : Nat := 118140960795 + 2604884 * 2 ^ 59
def prefixEnd_2604884 : Nat := 4983230072969 + 3 ^ 40 * 2604884 * 2
def baseEnd_2604884 : Nat := 1337557541206491613070363

theorem tailTrace_2604884 : CollatzResearch.WordTrace tailWord_2604884 prefixEnd_2604884 1337557541206491613070363 := by
  unfold tailWord_2604884
  simp only [CollatzResearch.WordTrace]
  refine ⟨47503962347478810806850853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63338616463305081075801137 47503962347478810806850853)
  ·
    refine ⟨8906992940152277026284535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47503962347478810806850853 8906992940152277026284535)
    ·
      refine ⟨13360489410228415539426803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8906992940152277026284535 13360489410228415539426803)
      ·
        refine ⟨20040734115342623309140205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13360489410228415539426803 20040734115342623309140205)
        ·
          refine ⟨7515275293253483740927577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20040734115342623309140205 7515275293253483740927577)
          ·
            refine ⟨5636456469940112805695683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7515275293253483740927577 5636456469940112805695683)
            ·
              refine ⟨8454684704910169208543525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5636456469940112805695683 8454684704910169208543525)
              ·
                refine ⟨1585253382170656726601911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8454684704910169208543525 1585253382170656726601911)
                ·
                  refine ⟨2377880073255985089902867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585253382170656726601911 2377880073255985089902867)
                  ·
                    refine ⟨3566820109883977634854301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2377880073255985089902867 3566820109883977634854301)
                    ·
                      refine ⟨1337557541206491613070363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3566820109883977634854301 1337557541206491613070363)
                      ·
                        rfl

theorem cell23_2604884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_2604884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604884 prefixEnd_2604884 := by exact prefixLift 2604884
  have htrace : WordTrace (prefixWord ++ tailWord_2604884) baseStart_2604884 baseEnd_2604884 := by
    simpa [prefixWord, tailWord_2604884, baseEnd_2604884] using wordTrace_append hprefix tailTrace_2604884
  have hstable : (prefixWord ++ tailWord_2604884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604884).length < 2 ^ (prefixWord ++ tailWord_2604884).sum := by decide
  have hdescent : baseEnd_2604884 < baseStart_2604884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604900 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_2604900 : Nat := 118140960795 + 2604900 * 2 ^ 59
def prefixEnd_2604900 : Nat := 4983230072969 + 3 ^ 40 * 2604900 * 2
def baseEnd_2604900 : Nat := 445855252298987850156763

theorem tailTrace_2604900 : CollatzResearch.WordTrace tailWord_2604900 prefixEnd_2604900 445855252298987850156763 := by
  unfold tailWord_2604900
  simp only [CollatzResearch.WordTrace]
  refine ⟨47504254131449828173142077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63339005508599770897522769 47504254131449828173142077)
  ·
    refine ⟨17814095299293685564928279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47504254131449828173142077 17814095299293685564928279)
    ·
      refine ⟨26721142948940528347392419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17814095299293685564928279 26721142948940528347392419)
      ·
        refine ⟨40081714423410792521088629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26721142948940528347392419 40081714423410792521088629)
        ·
          refine ⟨3757660727194761798852059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40081714423410792521088629 3757660727194761798852059)
          ·
            refine ⟨5636491090792142698278089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757660727194761798852059 5636491090792142698278089)
            ·
              refine ⟨4227368318094107023708567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5636491090792142698278089 4227368318094107023708567)
              ·
                refine ⟨6341052477141160535562851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4227368318094107023708567 6341052477141160535562851)
                ·
                  refine ⟨9511578715711740803344277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6341052477141160535562851 9511578715711740803344277)
                  ·
                    refine ⟨445855252298987850156763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9511578715711740803344277 445855252298987850156763)
                    ·
                      rfl

theorem cell23_2604900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_2604900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604900 prefixEnd_2604900 := by exact prefixLift 2604900
  have htrace : WordTrace (prefixWord ++ tailWord_2604900) baseStart_2604900 baseEnd_2604900 := by
    simpa [prefixWord, tailWord_2604900, baseEnd_2604900] using wordTrace_append hprefix tailTrace_2604900
  have hstable : (prefixWord ++ tailWord_2604900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604900).length < 2 ^ (prefixWord ++ tailWord_2604900).sum := by decide
  have hdescent : baseEnd_2604900 < baseStart_2604900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604913 : List Nat := [1, 2, 2, 2, 1, 3, 5, 7]
def baseStart_2604913 : Nat := 118140960795 + 2604913 * 2 ^ 59
def prefixEnd_2604913 : Nat := 4983230072969 + 3 ^ 40 * 2604913 * 2
def baseEnd_2604913 : Nat := 49539719709091555541027

theorem tailTrace_2604913 : CollatzResearch.WordTrace tailWord_2604913 prefixEnd_2604913 49539719709091555541027 := by
  unfold tailWord_2604913
  simp only [CollatzResearch.WordTrace]
  refine ⟨95008982411852559566507393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63339321607901706377671595 95008982411852559566507393)
  ·
    refine ⟨71256736808889419674880545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95008982411852559566507393 71256736808889419674880545)
    ·
      refine ⟨53442552606667064756160409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71256736808889419674880545 53442552606667064756160409)
      ·
        refine ⟨40081914455000298567120307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53442552606667064756160409 40081914455000298567120307)
        ·
          refine ⟨60122871682500447850680461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40081914455000298567120307 60122871682500447850680461)
          ·
            refine ⟨22546076880937667944005173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60122871682500447850680461 22546076880937667944005173)
            ·
              refine ⟨2113694707587906369750485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22546076880937667944005173 2113694707587906369750485)
              ·
                refine ⟨49539719709091555541027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2113694707587906369750485 49539719709091555541027)
                ·
                  rfl

theorem cell23_2604913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 7].length) (baseStart_2604913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604913 prefixEnd_2604913 := by exact prefixLift 2604913
  have htrace : WordTrace (prefixWord ++ tailWord_2604913) baseStart_2604913 baseEnd_2604913 := by
    simpa [prefixWord, tailWord_2604913, baseEnd_2604913] using wordTrace_append hprefix tailTrace_2604913
  have hstable : (prefixWord ++ tailWord_2604913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604913).length < 2 ^ (prefixWord ++ tailWord_2604913).sum := by decide
  have hdescent : baseEnd_2604913 < baseStart_2604913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604957 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_2604957 : Nat := 118140960795 + 2604957 * 2 ^ 59
def prefixEnd_2604957 : Nat := 4983230072969 + 3 ^ 40 * 2604957 * 2
def baseEnd_2604957 : Nat := 1337595025294269827457527

theorem tailTrace_2604957 : CollatzResearch.WordTrace tailWord_2604957 prefixEnd_2604957 1337595025294269827457527 := by
  unfold tailWord_2604957
  simp only [CollatzResearch.WordTrace]
  refine ⟨95010587223693155081109125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63340391482462103387406083 95010587223693155081109125)
  ·
    refine ⟨17814485104442466577707961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95010587223693155081109125 17814485104442466577707961)
    ·
      refine ⟨13360863828331849933280971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17814485104442466577707961 13360863828331849933280971)
      ·
        refine ⟨20041295742497774899921457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13360863828331849933280971 20041295742497774899921457)
        ·
          refine ⟨15030971806873331174941093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20041295742497774899921457 15030971806873331174941093)
          ·
            refine ⟨2818307213788749595301455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15030971806873331174941093 2818307213788749595301455)
            ·
              refine ⟨4227460820683124392952183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818307213788749595301455 4227460820683124392952183)
              ·
                refine ⟨6341191231024686589428275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4227460820683124392952183 6341191231024686589428275)
                ·
                  refine ⟨9511786846537029884142413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6341191231024686589428275 9511786846537029884142413)
                  ·
                    refine ⟨3566920067451386206553405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9511786846537029884142413 3566920067451386206553405)
                    ·
                      refine ⟨1337595025294269827457527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3566920067451386206553405 1337595025294269827457527)
                      ·
                        rfl

theorem cell23_2604957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_2604957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604957 prefixEnd_2604957 := by exact prefixLift 2604957
  have htrace : WordTrace (prefixWord ++ tailWord_2604957) baseStart_2604957 baseEnd_2604957 := by
    simpa [prefixWord, tailWord_2604957, baseEnd_2604957] using wordTrace_append hprefix tailTrace_2604957
  have hstable : (prefixWord ++ tailWord_2604957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604957).length < 2 ^ (prefixWord ++ tailWord_2604957).sum := by decide
  have hdescent : baseEnd_2604957 < baseStart_2604957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604983 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_2604983 : Nat := 118140960795 + 2604983 * 2 ^ 59
def prefixEnd_2604983 : Nat := 4983230072969 + 3 ^ 40 * 2604983 * 2
def baseEnd_2604983 : Nat := 1337608375791286725732407

theorem tailTrace_2604983 : CollatzResearch.WordTrace tailWord_2604983 prefixEnd_2604983 1337608375791286725732407 := by
  unfold tailWord_2604983
  simp only [CollatzResearch.WordTrace]
  refine ⟨95011535521598961521555603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63341023681065974347703735 95011535521598961521555603)
  ·
    refine ⟨142517303282398442282333405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95011535521598961521555603 142517303282398442282333405)
    ·
      refine ⟨53443988730899415855875027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142517303282398442282333405 53443988730899415855875027)
      ·
        refine ⟨80165983096349123783812541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53443988730899415855875027 80165983096349123783812541)
        ·
          refine ⟨30062243661130921418929703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80165983096349123783812541 30062243661130921418929703)
          ·
            refine ⟨45093365491696382128394555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30062243661130921418929703 45093365491696382128394555)
            ·
              refine ⟨67640048237544573192591833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45093365491696382128394555 67640048237544573192591833)
              ·
                refine ⟨50730036178158429894443875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67640048237544573192591833 50730036178158429894443875)
                ·
                  refine ⟨76095054267237644841665813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50730036178158429894443875 76095054267237644841665813)
                  ·
                    refine ⟨3566955668776764601953085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76095054267237644841665813 3566955668776764601953085)
                    ·
                      refine ⟨1337608375791286725732407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3566955668776764601953085 1337608375791286725732407)
                      ·
                        rfl

theorem cell23_2604983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_2604983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2604983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2604983 prefixEnd_2604983 := by exact prefixLift 2604983
  have htrace : WordTrace (prefixWord ++ tailWord_2604983) baseStart_2604983 baseEnd_2604983 := by
    simpa [prefixWord, tailWord_2604983, baseEnd_2604983] using wordTrace_append hprefix tailTrace_2604983
  have hstable : (prefixWord ++ tailWord_2604983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604983).length < 2 ^ (prefixWord ++ tailWord_2604983).sum := by decide
  have hdescent : baseEnd_2604983 < baseStart_2604983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605054 : List Nat := [4, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_2605054 : Nat := 118140960795 + 2605054 * 2 ^ 59
def prefixEnd_2605054 : Nat := 4983230072969 + 3 ^ 40 * 2605054 * 2
def baseEnd_2605054 : Nat := 148627203657528438660509

theorem tailTrace_2605054 : CollatzResearch.WordTrace tailWord_2605054 prefixEnd_2605054 148627203657528438660509 := by
  unfold tailWord_2605054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11876765638042717580923777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63342750069561160431593477 11876765638042717580923777)
  ·
    refine ⟨8907574228532038185692833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11876765638042717580923777 8907574228532038185692833)
    ·
      refine ⟨6680680671399028639269625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8907574228532038185692833 6680680671399028639269625)
      ·
        refine ⟨5010510503549271479452219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6680680671399028639269625 5010510503549271479452219)
        ·
          refine ⟨7515765755323907219178329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5010510503549271479452219 7515765755323907219178329)
          ·
            refine ⟨5636824316492930414383747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7515765755323907219178329 5636824316492930414383747)
            ·
              refine ⟨8455236474739395621575621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5636824316492930414383747 8455236474739395621575621)
              ·
                refine ⟨1585356839013636679045429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8455236474739395621575621 1585356839013636679045429)
                ·
                  refine ⟨148627203657528438660509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1585356839013636679045429 148627203657528438660509)
                  ·
                    rfl

theorem cell23_2605054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_2605054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605054 prefixEnd_2605054 := by exact prefixLift 2605054
  have htrace : WordTrace (prefixWord ++ tailWord_2605054) baseStart_2605054 baseEnd_2605054 := by
    simpa [prefixWord, tailWord_2605054, baseEnd_2605054] using wordTrace_append hprefix tailTrace_2605054
  have hstable : (prefixWord ++ tailWord_2605054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605054).length < 2 ^ (prefixWord ++ tailWord_2605054).sum := by decide
  have hdescent : baseEnd_2605054 < baseStart_2605054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605070 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2605070 : Nat := 118140960795 + 2605070 * 2 ^ 59
def prefixEnd_2605070 : Nat := 4983230072969 + 3 ^ 40 * 2605070 * 2
def baseEnd_2605070 : Nat := 1337653048608227885344507

theorem tailTrace_2605070 : CollatzResearch.WordTrace tailWord_2605070 prefixEnd_2605070 1337653048608227885344507 := by
  unfold tailWord_2605070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11876838584035471922496583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63343139114855850253315109 11876838584035471922496583)
  ·
    refine ⟨17815257876053207883744875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11876838584035471922496583 17815257876053207883744875)
    ·
      refine ⟨26722886814079811825617313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17815257876053207883744875 26722886814079811825617313)
      ·
        refine ⟨20042165110559858869212985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26722886814079811825617313 20042165110559858869212985)
        ·
          refine ⟨15031623832919894151909739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20042165110559858869212985 15031623832919894151909739)
          ·
            refine ⟨22547435749379841227864609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15031623832919894151909739 22547435749379841227864609)
            ·
              refine ⟨16910576812034880920898457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22547435749379841227864609 16910576812034880920898457)
              ·
                refine ⟨12682932609026160690673843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16910576812034880920898457 12682932609026160690673843)
                ·
                  refine ⟨19024398913539241036010765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12682932609026160690673843 19024398913539241036010765)
                  ·
                    refine ⟨7134149592577215388504037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19024398913539241036010765 7134149592577215388504037)
                    ·
                      refine ⟨1337653048608227885344507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7134149592577215388504037 1337653048608227885344507)
                      ·
                        rfl

theorem cell23_2605070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2605070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605070 prefixEnd_2605070 := by exact prefixLift 2605070
  have htrace : WordTrace (prefixWord ++ tailWord_2605070) baseStart_2605070 baseEnd_2605070 := by
    simpa [prefixWord, tailWord_2605070, baseEnd_2605070] using wordTrace_append hprefix tailTrace_2605070
  have hstable : (prefixWord ++ tailWord_2605070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605070).length < 2 ^ (prefixWord ++ tailWord_2605070).sum := by decide
  have hdescent : baseEnd_2605070 < baseStart_2605070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605083 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 4]
def baseStart_2605083 : Nat := 118140960795 + 2605083 * 2 ^ 59
def prefixEnd_2605083 : Nat := 4983230072969 + 3 ^ 40 * 2605083 * 2
def baseEnd_2605083 : Nat := 1337659723856736334481947

theorem tailTrace_2605083 : CollatzResearch.WordTrace tailWord_2605083 prefixEnd_2605083 1337659723856736334481947 := by
  unfold tailWord_2605083
  simp only [CollatzResearch.WordTrace]
  refine ⟨95015182821236678600195903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63343455214157785733463935 95015182821236678600195903)
  ·
    refine ⟨142522774231855017900293855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95015182821236678600195903 142522774231855017900293855)
    ·
      refine ⟨213784161347782526850440783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142522774231855017900293855 213784161347782526850440783)
      ·
        refine ⟨320676242021673790275661175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213784161347782526850440783 320676242021673790275661175)
        ·
          refine ⟨481014363032510685413491763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320676242021673790275661175 481014363032510685413491763)
          ·
            refine ⟨721521544548766028120237645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481014363032510685413491763 721521544548766028120237645)
            ·
              refine ⟨270570579205787260545089117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 721521544548766028120237645 270570579205787260545089117)
              ·
                refine ⟨101463967202170222704408419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270570579205787260545089117 101463967202170222704408419)
                ·
                  refine ⟨152195950803255334056612629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101463967202170222704408419 152195950803255334056612629)
                  ·
                    refine ⟨7134185193902593783903717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 152195950803255334056612629 7134185193902593783903717)
                    ·
                      refine ⟨1337659723856736334481947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7134185193902593783903717 1337659723856736334481947)
                      ·
                        rfl

theorem cell23_2605083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 4].length) (baseStart_2605083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605083 prefixEnd_2605083 := by exact prefixLift 2605083
  have htrace : WordTrace (prefixWord ++ tailWord_2605083) baseStart_2605083 baseEnd_2605083 := by
    simpa [prefixWord, tailWord_2605083, baseEnd_2605083] using wordTrace_append hprefix tailTrace_2605083
  have hstable : (prefixWord ++ tailWord_2605083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605083).length < 2 ^ (prefixWord ++ tailWord_2605083).sum := by decide
  have hdescent : baseEnd_2605083 < baseStart_2605083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605123 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 2, 9]
def baseStart_2605123 : Nat := 118140960795 + 2605123 * 2 ^ 59
def prefixEnd_2605123 : Nat := 4983230072969 + 3 ^ 40 * 2605123 * 2
def baseEnd_2605123 : Nat := 445893421027638725993921

theorem tailTrace_2605123 : CollatzResearch.WordTrace tailWord_2605123 prefixEnd_2605123 445893421027638725993921 := by
  unfold tailWord_2605123
  simp only [CollatzResearch.WordTrace]
  refine ⟨95016641741091765431652023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63344427827394510287768015 95016641741091765431652023)
  ·
    refine ⟨142524962611637648147478035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95016641741091765431652023 142524962611637648147478035)
    ·
      refine ⟨213787443917456472221217053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142524962611637648147478035 213787443917456472221217053)
      ·
        refine ⟨80170291469046177082956395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213787443917456472221217053 80170291469046177082956395)
        ·
          refine ⟨120255437203569265624434593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80170291469046177082956395 120255437203569265624434593)
          ·
            refine ⟨90191577902676949218325945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120255437203569265624434593 90191577902676949218325945)
            ·
              refine ⟨67643683427007711913744459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90191577902676949218325945 67643683427007711913744459)
              ·
                refine ⟨101465525140511567870616689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67643683427007711913744459 101465525140511567870616689)
                ·
                  refine ⟨76099143855383675902962517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101465525140511567870616689 76099143855383675902962517)
                  ·
                    refine ⟨445893421027638725993921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 76099143855383675902962517 445893421027638725993921)
                    ·
                      rfl

theorem cell23_2605123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 9].length) (baseStart_2605123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605123 prefixEnd_2605123 := by exact prefixLift 2605123
  have htrace : WordTrace (prefixWord ++ tailWord_2605123) baseStart_2605123 baseEnd_2605123 := by
    simpa [prefixWord, tailWord_2605123, baseEnd_2605123] using wordTrace_append hprefix tailTrace_2605123
  have hstable : (prefixWord ++ tailWord_2605123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605123).length < 2 ^ (prefixWord ++ tailWord_2605123).sum := by decide
  have hdescent : baseEnd_2605123 < baseStart_2605123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605127 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 6]
def baseStart_2605127 : Nat := 118140960795 + 2605127 * 2 ^ 59
def prefixEnd_2605127 : Nat := 4983230072969 + 3 ^ 40 * 2605127 * 2
def baseEnd_2605127 : Nat := 148631368556170462481305

theorem tailTrace_2605127 : CollatzResearch.WordTrace tailWord_2605127 prefixEnd_2605127 148631368556170462481305 := by
  unfold tailWord_2605127
  simp only [CollatzResearch.WordTrace]
  refine ⟨95016787633077274114797635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63344525088718182743198423 95016787633077274114797635)
  ·
    refine ⟨142525181449615911172196453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95016787633077274114797635 142525181449615911172196453)
    ·
      refine ⟨26723471521802983344786835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142525181449615911172196453 26723471521802983344786835)
      ·
        refine ⟨40085207282704475017180253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26723471521802983344786835 40085207282704475017180253)
        ·
          refine ⟨15031952731014178131442595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40085207282704475017180253 15031952731014178131442595)
          ·
            refine ⟨22547929096521267197163893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15031952731014178131442595 22547929096521267197163893)
            ·
              refine ⟨2113868352798868799734115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22547929096521267197163893 2113868352798868799734115)
              ·
                refine ⟨3170802529198303199601173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113868352798868799734115 3170802529198303199601173)
                ·
                  refine ⟨148631368556170462481305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3170802529198303199601173 148631368556170462481305)
                  ·
                    rfl

theorem cell23_2605127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 6].length) (baseStart_2605127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605127 prefixEnd_2605127 := by exact prefixLift 2605127
  have htrace : WordTrace (prefixWord ++ tailWord_2605127) baseStart_2605127 baseEnd_2605127 := by
    simpa [prefixWord, tailWord_2605127, baseEnd_2605127] using wordTrace_append hprefix tailTrace_2605127
  have hstable : (prefixWord ++ tailWord_2605127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605127).length < 2 ^ (prefixWord ++ tailWord_2605127).sum := by decide
  have hdescent : baseEnd_2605127 < baseStart_2605127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605157 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_2605157 : Nat := 118140960795 + 2605157 * 2 ^ 59
def prefixEnd_2605157 : Nat := 4983230072969 + 3 ^ 40 * 2605157 * 2
def baseEnd_2605157 : Nat := 445899240475056348318869

theorem tailTrace_2605157 : CollatzResearch.WordTrace tailWord_2605157 prefixEnd_2605157 445899240475056348318869 := by
  unfold tailWord_2605157
  simp only [CollatzResearch.WordTrace]
  refine ⟨95017881822968589238389725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63345254548645726158926483 95017881822968589238389725)
  ·
    refine ⟨35631705683613220964396147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95017881822968589238389725 35631705683613220964396147)
    ·
      refine ⟨53447558525419831446594221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35631705683613220964396147 53447558525419831446594221)
      ·
        refine ⟨20042834447032436792472833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53447558525419831446594221 20042834447032436792472833)
        ·
          refine ⟨15032125835274327594354625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20042834447032436792472833 15032125835274327594354625)
          ·
            refine ⟨11274094376455745695765969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15032125835274327594354625 11274094376455745695765969)
            ·
              refine ⟨8455570782341809271824477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11274094376455745695765969 8455570782341809271824477)
              ·
                refine ⟨3170839043378178476934179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8455570782341809271824477 3170839043378178476934179)
                ·
                  refine ⟨4756258565067267715401269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3170839043378178476934179 4756258565067267715401269)
                  ·
                    refine ⟨445899240475056348318869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4756258565067267715401269 445899240475056348318869)
                    ·
                      rfl

theorem cell23_2605157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_2605157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605157 prefixEnd_2605157 := by exact prefixLift 2605157
  have htrace : WordTrace (prefixWord ++ tailWord_2605157) baseStart_2605157 baseEnd_2605157 := by
    simpa [prefixWord, tailWord_2605157, baseEnd_2605157] using wordTrace_append hprefix tailTrace_2605157
  have hstable : (prefixWord ++ tailWord_2605157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605157).length < 2 ^ (prefixWord ++ tailWord_2605157).sum := by decide
  have hdescent : baseEnd_2605157 < baseStart_2605157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605164 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 2, 3, 2]
def baseStart_2605164 : Nat := 118140960795 + 2605164 * 2 ^ 59
def prefixEnd_2605164 : Nat := 4983230072969 + 3 ^ 40 * 2605164 * 2
def baseEnd_2605164 : Nat := 1337701315789750517569075

theorem tailTrace_2605164 : CollatzResearch.WordTrace tailWord_2605164 prefixEnd_2605164 1337701315789750517569075 := by
  unfold tailWord_2605164
  simp only [CollatzResearch.WordTrace]
  refine ⟨47509068566971614716947273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63345424755962152955929697 47509068566971614716947273)
  ·
    refine ⟨35631801425228711037710455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47509068566971614716947273 35631801425228711037710455)
    ·
      refine ⟨53447702137843066556565683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35631801425228711037710455 53447702137843066556565683)
      ·
        refine ⟨80171553206764599834848525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53447702137843066556565683 80171553206764599834848525)
        ·
          refine ⟨30064332452536724938068197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80171553206764599834848525 30064332452536724938068197)
          ·
            refine ⟨5637062334850635925887787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30064332452536724938068197 5637062334850635925887787)
            ·
              refine ⟨8455593502275953888831681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5637062334850635925887787 8455593502275953888831681)
              ·
                refine ⟨6341695126706965416623761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8455593502275953888831681 6341695126706965416623761)
                ·
                  refine ⟨4756271345030224062467821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6341695126706965416623761 4756271345030224062467821)
                  ·
                    refine ⟨1783601754386334023425433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4756271345030224062467821 1783601754386334023425433)
                    ·
                      refine ⟨1337701315789750517569075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783601754386334023425433 1337701315789750517569075)
                      ·
                        rfl

theorem cell23_2605164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_2605164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605164 prefixEnd_2605164 := by exact prefixLift 2605164
  have htrace : WordTrace (prefixWord ++ tailWord_2605164) baseStart_2605164 baseEnd_2605164 := by
    simpa [prefixWord, tailWord_2605164, baseEnd_2605164] using wordTrace_append hprefix tailTrace_2605164
  have hstable : (prefixWord ++ tailWord_2605164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605164).length < 2 ^ (prefixWord ++ tailWord_2605164).sum := by decide
  have hdescent : baseEnd_2605164 < baseStart_2605164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605194 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_2605194 : Nat := 118140960795 + 2605194 * 2 ^ 59
def prefixEnd_2605194 : Nat := 4983230072969 + 3 ^ 40 * 2605194 * 2
def baseEnd_2605194 : Nat := 1337716720209385400193937

theorem tailTrace_2605194 : CollatzResearch.WordTrace tailWord_2605194 prefixEnd_2605194 1337716720209385400193937 := by
  unfold tailWord_2605194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23754807830958636139371659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63346154215889696371657757 23754807830958636139371659)
  ·
    refine ⟨35632211746437954209057489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23754807830958636139371659 35632211746437954209057489)
    ·
      refine ⟨26724158809828465656793117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35632211746437954209057489 26724158809828465656793117)
      ·
        refine ⟨10021559553685674621297419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26724158809828465656793117 10021559553685674621297419)
        ·
          refine ⟨15032339330528511931946129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10021559553685674621297419 15032339330528511931946129)
          ·
            refine ⟨11274254497896383948959597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15032339330528511931946129 11274254497896383948959597)
            ·
              refine ⟨4227845436711143980859849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11274254497896383948959597 4227845436711143980859849)
              ·
                refine ⟨3170884077533357985644887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4227845436711143980859849 3170884077533357985644887)
                ·
                  refine ⟨4756326116300036978467331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3170884077533357985644887 4756326116300036978467331)
                  ·
                    refine ⟨7134489174450055467700997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4756326116300036978467331 7134489174450055467700997)
                    ·
                      refine ⟨1337716720209385400193937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7134489174450055467700997 1337716720209385400193937)
                      ·
                        rfl

theorem cell23_2605194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_2605194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605194 prefixEnd_2605194 := by exact prefixLift 2605194
  have htrace : WordTrace (prefixWord ++ tailWord_2605194) baseStart_2605194 baseEnd_2605194 := by
    simpa [prefixWord, tailWord_2605194, baseEnd_2605194] using wordTrace_append hprefix tailTrace_2605194
  have hstable : (prefixWord ++ tailWord_2605194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605194).length < 2 ^ (prefixWord ++ tailWord_2605194).sum := by decide
  have hdescent : baseEnd_2605194 < baseStart_2605194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605227 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 3]
def baseStart_2605227 : Nat := 118140960795 + 2605227 * 2 ^ 59
def prefixEnd_2605227 : Nat := 4983230072969 + 3 ^ 40 * 2605227 * 2
def baseEnd_2605227 : Nat := 1337733665070983771081285

theorem tailTrace_2605227 : CollatzResearch.WordTrace tailWord_2605227 prefixEnd_2605227 1337733665070983771081285 := by
  unfold tailWord_2605227
  simp only [CollatzResearch.WordTrace]
  refine ⟨95020434932714991193437935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63346956621809994128958623 95020434932714991193437935)
  ·
    refine ⟨142530652399072486790156903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95020434932714991193437935 142530652399072486790156903)
    ·
      refine ⟨213795978598608730185235355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142530652399072486790156903 213795978598608730185235355)
      ·
        refine ⟨320693967897913095277853033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213795978598608730185235355 320693967897913095277853033)
        ·
          refine ⟨240520475923434821458389775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320693967897913095277853033 240520475923434821458389775)
          ·
            refine ⟨360780713885152232187584663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240520475923434821458389775 360780713885152232187584663)
            ·
              refine ⟨541171070827728348281376995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360780713885152232187584663 541171070827728348281376995)
              ·
                refine ⟨811756606241592522422065493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541171070827728348281376995 811756606241592522422065493)
                ·
                  refine ⟨2378193182348415593033395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 811756606241592522422065493 2378193182348415593033395)
                  ·
                    refine ⟨3567289773522623389550093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2378193182348415593033395 3567289773522623389550093)
                    ·
                      refine ⟨1337733665070983771081285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3567289773522623389550093 1337733665070983771081285)
                      ·
                        rfl

theorem cell23_2605227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 3].length) (baseStart_2605227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605227 prefixEnd_2605227 := by exact prefixLift 2605227
  have htrace : WordTrace (prefixWord ++ tailWord_2605227) baseStart_2605227 baseEnd_2605227 := by
    simpa [prefixWord, tailWord_2605227, baseEnd_2605227] using wordTrace_append hprefix tailTrace_2605227
  have hstable : (prefixWord ++ tailWord_2605227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605227).length < 2 ^ (prefixWord ++ tailWord_2605227).sum := by decide
  have hdescent : baseEnd_2605227 < baseStart_2605227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605297 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_2605297 : Nat := 118140960795 + 2605297 * 2 ^ 59
def prefixEnd_2605297 : Nat := 4983230072969 + 3 ^ 40 * 2605297 * 2
def baseEnd_2605297 : Nat := 1337769608716798497205963

theorem tailTrace_2605297 : CollatzResearch.WordTrace tailWord_2605297 prefixEnd_2605297 1337769608716798497205963 := by
  unfold tailWord_2605297
  simp only [CollatzResearch.WordTrace]
  refine ⟨95022988042461393148486145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63348658694974262098990763 95022988042461393148486145)
  ·
    refine ⟨71267241031846044861364609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95022988042461393148486145 71267241031846044861364609)
    ·
      refine ⟨53450430773884533646023457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71267241031846044861364609 53450430773884533646023457)
      ·
        refine ⟨40087823080413400234517593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53450430773884533646023457 40087823080413400234517593)
        ·
          refine ⟨30065867310310050175888195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40087823080413400234517593 30065867310310050175888195)
          ·
            refine ⟨45098800965465075263832293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30065867310310050175888195 45098800965465075263832293)
            ·
              refine ⟨8456025181024701611968555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45098800965465075263832293 8456025181024701611968555)
              ·
                refine ⟨12684037771537052417952833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8456025181024701611968555 12684037771537052417952833)
                ·
                  refine ⟨9513028328652789313464625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12684037771537052417952833 9513028328652789313464625)
                  ·
                    refine ⟨7134771246489591985098469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9513028328652789313464625 7134771246489591985098469)
                    ·
                      refine ⟨1337769608716798497205963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7134771246489591985098469 1337769608716798497205963)
                      ·
                        rfl

theorem cell23_2605297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_2605297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605297 prefixEnd_2605297 := by exact prefixLift 2605297
  have htrace : WordTrace (prefixWord ++ tailWord_2605297) baseStart_2605297 baseEnd_2605297 := by
    simpa [prefixWord, tailWord_2605297, baseEnd_2605297] using wordTrace_append hprefix tailTrace_2605297
  have hstable : (prefixWord ++ tailWord_2605297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605297).length < 2 ^ (prefixWord ++ tailWord_2605297).sum := by decide
  have hdescent : baseEnd_2605297 < baseStart_2605297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605317 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_2605317 : Nat := 118140960795 + 2605317 * 2 ^ 59
def prefixEnd_2605317 : Nat := 4983230072969 + 3 ^ 40 * 2605317 * 2
def baseEnd_2605317 : Nat := 1337779878329888418955871

theorem tailTrace_2605317 : CollatzResearch.WordTrace tailWord_2605317 prefixEnd_2605317 1337779878329888418955871 := by
  unfold tailWord_2605317
  simp only [CollatzResearch.WordTrace]
  refine ⟨95023717502388936564214205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63349145001592624376142803 95023717502388936564214205)
  ·
    refine ⟨35633894063395851211580327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95023717502388936564214205 35633894063395851211580327)
    ·
      refine ⟨53450841095093776817370491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35633894063395851211580327 53450841095093776817370491)
      ·
        refine ⟨80176261642640665226055737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53450841095093776817370491 80176261642640665226055737)
        ·
          refine ⟨60132196231980498919541803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80176261642640665226055737 60132196231980498919541803)
          ·
            refine ⟨90198294347970748379312705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60132196231980498919541803 90198294347970748379312705)
            ·
              refine ⟨67648720760978061284484529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90198294347970748379312705 67648720760978061284484529)
              ·
                refine ⟨50736540570733545963363397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67648720760978061284484529 50736540570733545963363397)
                ·
                  refine ⟨9513101357012539868130637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50736540570733545963363397 9513101357012539868130637)
                  ·
                    refine ⟨3567413008879702450548989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9513101357012539868130637 3567413008879702450548989)
                    ·
                      refine ⟨1337779878329888418955871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3567413008879702450548989 1337779878329888418955871)
                      ·
                        rfl

theorem cell23_2605317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_2605317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605317 prefixEnd_2605317 := by exact prefixLift 2605317
  have htrace : WordTrace (prefixWord ++ tailWord_2605317) baseStart_2605317 baseEnd_2605317 := by
    simpa [prefixWord, tailWord_2605317, baseEnd_2605317] using wordTrace_append hprefix tailTrace_2605317
  have hstable : (prefixWord ++ tailWord_2605317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605317).length < 2 ^ (prefixWord ++ tailWord_2605317).sum := by decide
  have hdescent : baseEnd_2605317 < baseStart_2605317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605341 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 7]
def baseStart_2605341 : Nat := 118140960795 + 2605341 * 2 ^ 59
def prefixEnd_2605341 : Nat := 4983230072969 + 3 ^ 40 * 2605341 * 2
def baseEnd_2605341 : Nat := 148643577985066258339529

theorem tailTrace_2605341 : CollatzResearch.WordTrace tailWord_2605341 prefixEnd_2605341 148643577985066258339529 := by
  unfold tailWord_2605341
  simp only [CollatzResearch.WordTrace]
  refine ⟨95024592854301988663087877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63349728569534659108725251 95024592854301988663087877)
  ·
    refine ⟨17817111160181622874328977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95024592854301988663087877 17817111160181622874328977)
    ·
      refine ⟨13362833370136217155746733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17817111160181622874328977 13362833370136217155746733)
      ·
        refine ⟨5011062513801081433405025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13362833370136217155746733 5011062513801081433405025)
        ·
          refine ⟨3758296885350811075053769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5011062513801081433405025 3758296885350811075053769)
          ·
            refine ⟨2818722664013108306290327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3758296885350811075053769 2818722664013108306290327)
            ·
              refine ⟨4228083996019662459435491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818722664013108306290327 4228083996019662459435491)
              ·
                refine ⟨6342125994029493689153237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228083996019662459435491 6342125994029493689153237)
                ·
                  refine ⟨148643577985066258339529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6342125994029493689153237 148643577985066258339529)
                  ·
                    rfl

theorem cell23_2605341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_2605341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605341 prefixEnd_2605341 := by exact prefixLift 2605341
  have htrace : WordTrace (prefixWord ++ tailWord_2605341) baseStart_2605341 baseEnd_2605341 := by
    simpa [prefixWord, tailWord_2605341, baseEnd_2605341] using wordTrace_append hprefix tailTrace_2605341
  have hstable : (prefixWord ++ tailWord_2605341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605341).length < 2 ^ (prefixWord ++ tailWord_2605341).sum := by decide
  have hdescent : baseEnd_2605341 < baseStart_2605341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605347 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 5]
def baseStart_2605347 : Nat := 118140960795 + 2605347 * 2 ^ 59
def prefixEnd_2605347 : Nat := 4983230072969 + 3 ^ 40 * 2605347 * 2
def baseEnd_2605347 : Nat := 1337795282749523301580733

theorem tailTrace_2605347 : CollatzResearch.WordTrace tailWord_2605347 prefixEnd_2605347 1337795282749523301580733 := by
  unfold tailWord_2605347
  simp only [CollatzResearch.WordTrace]
  refine ⟨95024811692280251687806295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63349874461520167791870863 95024811692280251687806295)
  ·
    refine ⟨142537217538420377531709443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95024811692280251687806295 142537217538420377531709443)
    ·
      refine ⟨213805826307630566297564165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142537217538420377531709443 213805826307630566297564165)
      ·
        refine ⟨40088592432680731180793281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213805826307630566297564165 40088592432680731180793281)
        ·
          refine ⟨30066444324510548385594961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40088592432680731180793281 30066444324510548385594961)
          ·
            refine ⟨22549833243382911289196221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30066444324510548385594961 22549833243382911289196221)
            ·
              refine ⟨8456187466268591733448583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22549833243382911289196221 8456187466268591733448583)
              ·
                refine ⟨12684281199402887600172875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8456187466268591733448583 12684281199402887600172875)
                ·
                  refine ⟨19026421799104331400259313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12684281199402887600172875 19026421799104331400259313)
                  ·
                    refine ⟨14269816349328248550194485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19026421799104331400259313 14269816349328248550194485)
                    ·
                      refine ⟨1337795282749523301580733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14269816349328248550194485 1337795282749523301580733)
                      ·
                        rfl

theorem cell23_2605347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_2605347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605347 prefixEnd_2605347 := by exact prefixLift 2605347
  have htrace : WordTrace (prefixWord ++ tailWord_2605347) baseStart_2605347 baseEnd_2605347 := by
    simpa [prefixWord, tailWord_2605347, baseEnd_2605347] using wordTrace_append hprefix tailTrace_2605347
  have hstable : (prefixWord ++ tailWord_2605347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605347).length < 2 ^ (prefixWord ++ tailWord_2605347).sum := by decide
  have hdescent : baseEnd_2605347 < baseStart_2605347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605352 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_2605352 : Nat := 118140960795 + 2605352 * 2 ^ 59
def prefixEnd_2605352 : Nat := 4983230072969 + 3 ^ 40 * 2605352 * 2
def baseEnd_2605352 : Nat := 1337797850152795782018211

theorem tailTrace_2605352 : CollatzResearch.WordTrace tailWord_2605352 prefixEnd_2605352 1337797850152795782018211 := by
  unfold tailWord_2605352
  simp only [CollatzResearch.WordTrace]
  refine ⟨47512497028631068770869155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63349996038174758361158873 47512497028631068770869155)
  ·
    refine ⟨71268745542946603156303733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47512497028631068770869155 71268745542946603156303733)
    ·
      refine ⟨6681444894651244045903475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71268745542946603156303733 6681444894651244045903475)
      ·
        refine ⟨10022167341976866068855213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6681444894651244045903475 10022167341976866068855213)
        ·
          refine ⟨3758312753241324775820705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10022167341976866068855213 3758312753241324775820705)
          ·
            refine ⟨2818734564930993581865529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3758312753241324775820705 2818734564930993581865529)
            ·
              refine ⟨2114050923698245186399147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2818734564930993581865529 2114050923698245186399147)
              ·
                refine ⟨3171076385547367779598721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114050923698245186399147 3171076385547367779598721)
                ·
                  refine ⟨2378307289160525834699041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3171076385547367779598721 2378307289160525834699041)
                  ·
                    refine ⟨1783730466870394376024281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2378307289160525834699041 1783730466870394376024281)
                    ·
                      refine ⟨1337797850152795782018211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783730466870394376024281 1337797850152795782018211)
                      ·
                        rfl

theorem cell23_2605352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_2605352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605352 prefixEnd_2605352 := by exact prefixLift 2605352
  have htrace : WordTrace (prefixWord ++ tailWord_2605352) baseStart_2605352 baseEnd_2605352 := by
    simpa [prefixWord, tailWord_2605352, baseEnd_2605352] using wordTrace_append hprefix tailTrace_2605352
  have hstable : (prefixWord ++ tailWord_2605352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605352).length < 2 ^ (prefixWord ++ tailWord_2605352).sum := by decide
  have hdescent : baseEnd_2605352 < baseStart_2605352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605501 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_2605501 : Nat := 118140960795 + 2605501 * 2 ^ 59
def prefixEnd_2605501 : Nat := 4983230072969 + 3 ^ 40 * 2605501 * 2
def baseEnd_2605501 : Nat := 1337874358770315699055025

theorem tailTrace_2605501 : CollatzResearch.WordTrace tailWord_2605501 prefixEnd_2605501 1337874358770315699055025 := by
  unfold tailWord_2605501
  simp only [CollatzResearch.WordTrace]
  refine ⟨95030428533722335988912357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63353619022481557325941571 95030428533722335988912357)
  ·
    refine ⟨17818205350072937997921067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95030428533722335988912357 17818205350072937997921067)
    ·
      refine ⟨26727308025109406996881601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17818205350072937997921067 26727308025109406996881601)
      ·
        refine ⟨20045481018832055247661201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26727308025109406996881601 20045481018832055247661201)
        ·
          refine ⟨15034110764124041435745901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20045481018832055247661201 15034110764124041435745901)
          ·
            refine ⟨5637791536546515538404713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15034110764124041435745901 5637791536546515538404713)
            ·
              refine ⟨4228343652409886653803535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5637791536546515538404713 4228343652409886653803535)
              ·
                refine ⟨6342515478614829980705303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228343652409886653803535 6342515478614829980705303)
                ·
                  refine ⟨9513773217922244971057955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6342515478614829980705303 9513773217922244971057955)
                  ·
                    refine ⟨14270659826883367456586933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9513773217922244971057955 14270659826883367456586933)
                    ·
                      refine ⟨1337874358770315699055025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14270659826883367456586933 1337874358770315699055025)
                      ·
                        rfl

theorem cell23_2605501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_2605501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605501 prefixEnd_2605501 := by exact prefixLift 2605501
  have htrace : WordTrace (prefixWord ++ tailWord_2605501) baseStart_2605501 baseEnd_2605501 := by
    simpa [prefixWord, tailWord_2605501, baseEnd_2605501] using wordTrace_append hprefix tailTrace_2605501
  have hstable : (prefixWord ++ tailWord_2605501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605501).length < 2 ^ (prefixWord ++ tailWord_2605501).sum := by decide
  have hdescent : baseEnd_2605501 < baseStart_2605501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605525 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_2605525 : Nat := 118140960795 + 2605525 * 2 ^ 59
def prefixEnd_2605525 : Nat := 4983230072969 + 3 ^ 40 * 2605525 * 2
def baseEnd_2605525 : Nat := 445962227435341201718305

theorem tailTrace_2605525 : CollatzResearch.WordTrace tailWord_2605525 prefixEnd_2605525 445962227435341201718305 := by
  unfold tailWord_2605525
  simp only [CollatzResearch.WordTrace]
  refine ⟨95031303885635388087786029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63354202590423592058524019 95031303885635388087786029)
  ·
    refine ⟨35636738957113270532919761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95031303885635388087786029 35636738957113270532919761)
    ·
      refine ⟨26727554217834952899689821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35636738957113270532919761 26727554217834952899689821)
      ·
        refine ⟨10022832831688107337383683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26727554217834952899689821 10022832831688107337383683)
        ·
          refine ⟨15034249247532161006075525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10022832831688107337383683 15034249247532161006075525)
          ·
            refine ⟨2818921733912280188639161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15034249247532161006075525 2818921733912280188639161)
            ·
              refine ⟨2114191300434210141479371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2818921733912280188639161 2114191300434210141479371)
              ·
                refine ⟨3171286950651315212219057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114191300434210141479371 3171286950651315212219057)
                ·
                  refine ⟨2378465212988486409164293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3171286950651315212219057 2378465212988486409164293)
                  ·
                    refine ⟨445962227435341201718305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2378465212988486409164293 445962227435341201718305)
                    ·
                      rfl

theorem cell23_2605525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_2605525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605525 prefixEnd_2605525 := by exact prefixLift 2605525
  have htrace : WordTrace (prefixWord ++ tailWord_2605525) baseStart_2605525 baseEnd_2605525 := by
    simpa [prefixWord, tailWord_2605525, baseEnd_2605525] using wordTrace_append hprefix tailTrace_2605525
  have hstable : (prefixWord ++ tailWord_2605525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605525).length < 2 ^ (prefixWord ++ tailWord_2605525).sum := by decide
  have hdescent : baseEnd_2605525 < baseStart_2605525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605564 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_2605564 : Nat := 118140960795 + 2605564 * 2 ^ 59
def prefixEnd_2605564 : Nat := 4983230072969 + 3 ^ 40 * 2605564 * 2
def baseEnd_2605564 : Nat := 445968902683849650855745

theorem tailTrace_2605564 : CollatzResearch.WordTrace tailWord_2605564 prefixEnd_2605564 445968902683849650855745 := by
  unfold tailWord_2605564
  simp only [CollatzResearch.WordTrace]
  refine ⟨47516363166247048874227873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63355150888329398498970497 47516363166247048874227873)
  ·
    refine ⟨35637272374685286655670905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47516363166247048874227873 35637272374685286655670905)
    ·
      refine ⟨26727954281013964991753179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35637272374685286655670905 26727954281013964991753179)
      ·
        refine ⟨40091931421520947487629769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26727954281013964991753179 40091931421520947487629769)
        ·
          refine ⟨30068948566140710615722327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40091931421520947487629769 30068948566140710615722327)
          ·
            refine ⟨45103422849211065923583491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30068948566140710615722327 45103422849211065923583491)
            ·
              refine ⟨67655134273816598885375237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45103422849211065923583491 67655134273816598885375237)
              ·
                refine ⟨12685337676340612291007857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67655134273816598885375237 12685337676340612291007857)
                ·
                  refine ⟨9514003257255459218255893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12685337676340612291007857 9514003257255459218255893)
                  ·
                    refine ⟨445968902683849650855745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9514003257255459218255893 445968902683849650855745)
                    ·
                      rfl

theorem cell23_2605564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_2605564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605564 prefixEnd_2605564 := by exact prefixLift 2605564
  have htrace : WordTrace (prefixWord ++ tailWord_2605564) baseStart_2605564 baseEnd_2605564 := by
    simpa [prefixWord, tailWord_2605564, baseEnd_2605564] using wordTrace_append hprefix tailTrace_2605564
  have hstable : (prefixWord ++ tailWord_2605564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605564).length < 2 ^ (prefixWord ++ tailWord_2605564).sum := by decide
  have hdescent : baseEnd_2605564 < baseStart_2605564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605571 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 3, 4, 2]
def baseStart_2605571 : Nat := 118140960795 + 2605571 * 2 ^ 59
def prefixEnd_2605571 : Nat := 4983230072969 + 3 ^ 40 * 2605571 * 2
def baseEnd_2605571 : Nat := 1337910302416130425179703

theorem tailTrace_2605571 : CollatzResearch.WordTrace tailWord_2605571 prefixEnd_2605571 1337910302416130425179703 := by
  unfold tailWord_2605571
  simp only [CollatzResearch.WordTrace]
  refine ⟨95032981643468737943960567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63355321095645825295973711 95032981643468737943960567)
  ·
    refine ⟨142549472465203106915940851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95032981643468737943960567 142549472465203106915940851)
    ·
      refine ⟨213824208697804660373911277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142549472465203106915940851 213824208697804660373911277)
      ·
        refine ⟨80184078261676747640216729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213824208697804660373911277 80184078261676747640216729)
        ·
          refine ⟨60138058696257560730162547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80184078261676747640216729 60138058696257560730162547)
          ·
            refine ⟨90207088044386341095243821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60138058696257560730162547 90207088044386341095243821)
            ·
              refine ⟨33827658016644877910716433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90207088044386341095243821 33827658016644877910716433)
              ·
                refine ⟨25370743512483658433037325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33827658016644877910716433 25370743512483658433037325)
                ·
                  refine ⟨9514028817181371912388997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25370743512483658433037325 9514028817181371912388997)
                  ·
                    refine ⟨1783880403221507233572937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9514028817181371912388997 1783880403221507233572937)
                    ·
                      refine ⟨1337910302416130425179703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783880403221507233572937 1337910302416130425179703)
                      ·
                        rfl

theorem cell23_2605571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_2605571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605571 prefixEnd_2605571 := by exact prefixLift 2605571
  have htrace : WordTrace (prefixWord ++ tailWord_2605571) baseStart_2605571 baseEnd_2605571 := by
    simpa [prefixWord, tailWord_2605571, baseEnd_2605571] using wordTrace_append hprefix tailTrace_2605571
  have hstable : (prefixWord ++ tailWord_2605571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605571).length < 2 ^ (prefixWord ++ tailWord_2605571).sum := by decide
  have hdescent : baseEnd_2605571 < baseStart_2605571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605594 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 9]
def baseStart_2605594 : Nat := 118140960795 + 2605594 * 2 ^ 59
def prefixEnd_2605594 : Nat := 4983230072969 + 3 ^ 40 * 2605594 * 2
def baseEnd_2605594 : Nat := 148658012496798203910233

theorem tailTrace_2605594 : CollatzResearch.WordTrace tailWord_2605594 prefixEnd_2605594 148658012496798203910233 := by
  unfold tailWord_2605594
  simp only [CollatzResearch.WordTrace]
  refine ⟨23758455130596353218011959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63355880348256941914698557 23758455130596353218011959)
  ·
    refine ⟨35637682695894529827017939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23758455130596353218011959 35637682695894529827017939)
    ·
      refine ⟨53456524043841794740526909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35637682695894529827017939 53456524043841794740526909)
      ·
        refine ⟨20046196516440673027697591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53456524043841794740526909 20046196516440673027697591)
        ·
          refine ⟨30069294774661009541546387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20046196516440673027697591 30069294774661009541546387)
          ·
            refine ⟨45103942161991514312319581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30069294774661009541546387 45103942161991514312319581)
            ·
              refine ⟨16913978310746817867119843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45103942161991514312319581 16913978310746817867119843)
              ·
                refine ⟨25370967466120226800679765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16913978310746817867119843 25370967466120226800679765)
                ·
                  refine ⟨148658012496798203910233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25370967466120226800679765 148658012496798203910233)
                  ·
                    rfl

theorem cell23_2605594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_2605594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605594 prefixEnd_2605594 := by exact prefixLift 2605594
  have htrace : WordTrace (prefixWord ++ tailWord_2605594) baseStart_2605594 baseEnd_2605594 := by
    simpa [prefixWord, tailWord_2605594, baseEnd_2605594] using wordTrace_append hprefix tailTrace_2605594
  have hstable : (prefixWord ++ tailWord_2605594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605594).length < 2 ^ (prefixWord ++ tailWord_2605594).sum := by decide
  have hdescent : baseEnd_2605594 < baseStart_2605594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605621 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_2605621 : Nat := 118140960795 + 2605621 * 2 ^ 59
def prefixEnd_2605621 : Nat := 4983230072969 + 3 ^ 40 * 2605621 * 2
def baseEnd_2605621 : Nat := 1337935976448855229554473

theorem tailTrace_2605621 : CollatzResearch.WordTrace tailWord_2605621 prefixEnd_2605621 1337935976448855229554473 := by
  unfold tailWord_2605621
  simp only [CollatzResearch.WordTrace]
  refine ⟨95034805293287596483280717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63356536862191730988853811 95034805293287596483280717)
  ·
    refine ⟨35638051984982848681230269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95034805293287596483280717 35638051984982848681230269)
    ·
      refine ⟨13364269494368568255461351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35638051984982848681230269 13364269494368568255461351)
      ·
        refine ⟨20046404241552852383192027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13364269494368568255461351 20046404241552852383192027)
        ·
          refine ⟨30069606362329278574788041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20046404241552852383192027 30069606362329278574788041)
          ·
            refine ⟨22552204771746958931091031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30069606362329278574788041 22552204771746958931091031)
            ·
              refine ⟨33828307157620438396636547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22552204771746958931091031 33828307157620438396636547)
              ·
                refine ⟨50742460736430657594954821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33828307157620438396636547 50742460736430657594954821)
                ·
                  refine ⟨9514211388080748299054029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50742460736430657594954821 9514211388080748299054029)
                  ·
                    refine ⟨3567829270530280612145261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9514211388080748299054029 3567829270530280612145261)
                    ·
                      refine ⟨1337935976448855229554473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3567829270530280612145261 1337935976448855229554473)
                      ·
                        rfl

theorem cell23_2605621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_2605621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605621 prefixEnd_2605621 := by exact prefixLift 2605621
  have htrace : WordTrace (prefixWord ++ tailWord_2605621) baseStart_2605621 baseEnd_2605621 := by
    simpa [prefixWord, tailWord_2605621, baseEnd_2605621] using wordTrace_append hprefix tailTrace_2605621
  have hstable : (prefixWord ++ tailWord_2605621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605621).length < 2 ^ (prefixWord ++ tailWord_2605621).sum := by decide
  have hdescent : baseEnd_2605621 < baseStart_2605621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605622 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_2605622 : Nat := 118140960795 + 2605622 * 2 ^ 59
def prefixEnd_2605622 : Nat := 4983230072969 + 3 ^ 40 * 2605622 * 2
def baseEnd_2605622 : Nat := 1337936489929509725641969

theorem tailTrace_2605622 : CollatzResearch.WordTrace tailWord_2605622 prefixEnd_2605622 1337936489929509725641969 := by
  unfold tailWord_2605622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5939677610392748353379195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63356561177522649102711413 5939677610392748353379195)
  ·
    refine ⟨8909516415589122530068793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5939677610392748353379195 8909516415589122530068793)
    ·
      refine ⟨6682137311691841897551595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8909516415589122530068793 6682137311691841897551595)
      ·
        refine ⟨10023205967537762846327393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6682137311691841897551595 10023205967537762846327393)
        ·
          refine ⟨7517404475653322134745545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10023205967537762846327393 7517404475653322134745545)
          ·
            refine ⟨5638053356739991601059159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7517404475653322134745545 5638053356739991601059159)
            ·
              refine ⟨8457080035109987401588739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638053356739991601059159 8457080035109987401588739)
              ·
                refine ⟨12685620052664981102383109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8457080035109987401588739 12685620052664981102383109)
                ·
                  refine ⟨2378553759874683956696833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12685620052664981102383109 2378553759874683956696833)
                  ·
                    refine ⟨1783915319906012967522625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2378553759874683956696833 1783915319906012967522625)
                    ·
                      refine ⟨1337936489929509725641969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1783915319906012967522625 1337936489929509725641969)
                      ·
                        rfl

theorem cell23_2605622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_2605622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605622 prefixEnd_2605622 := by exact prefixLift 2605622
  have htrace : WordTrace (prefixWord ++ tailWord_2605622) baseStart_2605622 baseEnd_2605622 := by
    simpa [prefixWord, tailWord_2605622, baseEnd_2605622] using wordTrace_append hprefix tailTrace_2605622
  have hstable : (prefixWord ++ tailWord_2605622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605622).length < 2 ^ (prefixWord ++ tailWord_2605622).sum := by decide
  have hdescent : baseEnd_2605622 < baseStart_2605622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605628 : List Nat := [2, 2, 2, 2, 3, 1, 2, 4, 5]
def baseStart_2605628 : Nat := 118140960795 + 2605628 * 2 ^ 59
def prefixEnd_2605628 : Nat := 4983230072969 + 3 ^ 40 * 2605628 * 2
def baseEnd_2605628 : Nat := 148659952312604078018549

theorem tailTrace_2605628 : CollatzResearch.WordTrace tailWord_2605628 prefixEnd_2605628 148659952312604078018549 := by
  unfold tailWord_2605628
  simp only [CollatzResearch.WordTrace]
  refine ⟨47517530302131118339392769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63356707069508157785857025 47517530302131118339392769)
  ·
    refine ⟨35638147726598338754544577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47517530302131118339392769 35638147726598338754544577)
    ·
      refine ⟨26728610794948754065908433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35638147726598338754544577 26728610794948754065908433)
      ·
        refine ⟨20046458096211565549431325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26728610794948754065908433 20046458096211565549431325)
        ·
          refine ⟨7517421786079337081036747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20046458096211565549431325 7517421786079337081036747)
          ·
            refine ⟨11276132679119005621555121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7517421786079337081036747 11276132679119005621555121)
            ·
              refine ⟨8457099509339254216166341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11276132679119005621555121 8457099509339254216166341)
              ·
                refine ⟨1585706158001110165531189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8457099509339254216166341 1585706158001110165531189)
                ·
                  refine ⟨148659952312604078018549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1585706158001110165531189 148659952312604078018549)
                  ·
                    rfl

theorem cell23_2605628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_2605628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605628 prefixEnd_2605628 := by exact prefixLift 2605628
  have htrace : WordTrace (prefixWord ++ tailWord_2605628) baseStart_2605628 baseEnd_2605628 := by
    simpa [prefixWord, tailWord_2605628, baseEnd_2605628] using wordTrace_append hprefix tailTrace_2605628
  have hstable : (prefixWord ++ tailWord_2605628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605628).length < 2 ^ (prefixWord ++ tailWord_2605628).sum := by decide
  have hdescent : baseEnd_2605628 < baseStart_2605628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605678 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2605678 : Nat := 118140960795 + 2605678 * 2 ^ 59
def prefixEnd_2605678 : Nat := 4983230072969 + 3 ^ 40 * 2605678 * 2
def baseEnd_2605678 : Nat := 1337965244846161506541711

theorem tailTrace_2605678 : CollatzResearch.WordTrace tailWord_2605678 prefixEnd_2605678 1337965244846161506541711 := by
  unfold tailWord_2605678
  simp only [CollatzResearch.WordTrace]
  refine ⟨11879610531760136902263211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63357922836054063478737125 11879610531760136902263211)
  ·
    refine ⟨17819415797640205353394817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11879610531760136902263211 17819415797640205353394817)
    ·
      refine ⟨13364561848230154015046113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17819415797640205353394817 13364561848230154015046113)
      ·
        refine ⟨10023421386172615511284585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13364561848230154015046113 10023421386172615511284585)
        ·
          refine ⟨7517566039629461633463439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10023421386172615511284585 7517566039629461633463439)
          ·
            refine ⟨11276349059444192450195159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7517566039629461633463439 11276349059444192450195159)
            ·
              refine ⟨16914523589166288675292739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11276349059444192450195159 16914523589166288675292739)
              ·
                refine ⟨25371785383749433012939109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16914523589166288675292739 25371785383749433012939109)
                ·
                  refine ⟨4757209759453018689926083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25371785383749433012939109 4757209759453018689926083)
                  ·
                    refine ⟨7135814639179528034889125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4757209759453018689926083 7135814639179528034889125)
                    ·
                      refine ⟨1337965244846161506541711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7135814639179528034889125 1337965244846161506541711)
                      ·
                        rfl

theorem cell23_2605678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2605678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605678 prefixEnd_2605678 := by exact prefixLift 2605678
  have htrace : WordTrace (prefixWord ++ tailWord_2605678) baseStart_2605678 baseEnd_2605678 := by
    simpa [prefixWord, tailWord_2605678, baseEnd_2605678] using wordTrace_append hprefix tailTrace_2605678
  have hstable : (prefixWord ++ tailWord_2605678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605678).length < 2 ^ (prefixWord ++ tailWord_2605678).sum := by decide
  have hdescent : baseEnd_2605678 < baseStart_2605678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605766 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2605766 : Nat := 118140960795 + 2605766 * 2 ^ 59
def prefixEnd_2605766 : Nat := 4983230072969 + 3 ^ 40 * 2605766 * 2
def baseEnd_2605766 : Nat := 1338010431143757162241307

theorem tailTrace_2605766 : CollatzResearch.WordTrace tailWord_2605766 prefixEnd_2605766 1338010431143757162241307 := by
  unfold tailWord_2605766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2970002933680071445228411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63360062585174857498206101 2970002933680071445228411)
  ·
    refine ⟨4455004400520107167842617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2970002933680071445228411 4455004400520107167842617)
    ·
      refine ⟨3341253300390080375881963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4455004400520107167842617 3341253300390080375881963)
      ·
        refine ⟨5011879950585120563822945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341253300390080375881963 5011879950585120563822945)
        ·
          refine ⟨3758909962938840422867209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5011879950585120563822945 3758909962938840422867209)
          ·
            refine ⟨2819182472204130317150407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3758909962938840422867209 2819182472204130317150407)
            ·
              refine ⟨4228773708306195475725611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819182472204130317150407 4228773708306195475725611)
              ·
                refine ⟨6343160562459293213588417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228773708306195475725611 6343160562459293213588417)
                ·
                  refine ⟨4757370421844469910191313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6343160562459293213588417 4757370421844469910191313)
                  ·
                    refine ⟨3568027816383352432643485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4757370421844469910191313 3568027816383352432643485)
                    ·
                      refine ⟨1338010431143757162241307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3568027816383352432643485 1338010431143757162241307)
                      ·
                        rfl

theorem cell23_2605766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2605766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605766 prefixEnd_2605766 := by exact prefixLift 2605766
  have htrace : WordTrace (prefixWord ++ tailWord_2605766) baseStart_2605766 baseEnd_2605766 := by
    simpa [prefixWord, tailWord_2605766, baseEnd_2605766] using wordTrace_append hprefix tailTrace_2605766
  have hstable : (prefixWord ++ tailWord_2605766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605766).length < 2 ^ (prefixWord ++ tailWord_2605766).sum := by decide
  have hdescent : baseEnd_2605766 < baseStart_2605766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605768 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_2605768 : Nat := 118140960795 + 2605768 * 2 ^ 59
def prefixEnd_2605768 : Nat := 4983230072969 + 3 ^ 40 * 2605768 * 2
def baseEnd_2605768 : Nat := 1338011458105066154416297

theorem tailTrace_2605768 : CollatzResearch.WordTrace tailWord_2605768 prefixEnd_2605768 1338011458105066154416297 := by
  unfold tailWord_2605768
  simp only [CollatzResearch.WordTrace]
  refine ⟨47520083411877520294440979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63360111215836693725921305 47520083411877520294440979)
  ·
    refine ⟨71280125117816280441661469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47520083411877520294440979 71280125117816280441661469)
    ·
      refine ⟨26730046919181105165623051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71280125117816280441661469 26730046919181105165623051)
      ·
        refine ⟨40095070378771657748434577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26730046919181105165623051 40095070378771657748434577)
        ·
          refine ⟨30071302784078743311325933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40095070378771657748434577 30071302784078743311325933)
          ·
            refine ⟨11276738544029528741747225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30071302784078743311325933 11276738544029528741747225)
            ·
              refine ⟨8457553908022146556310419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11276738544029528741747225 8457553908022146556310419)
              ·
                refine ⟨12686330862033219834465629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8457553908022146556310419 12686330862033219834465629)
                ·
                  refine ⟨4757374073262457437924611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12686330862033219834465629 4757374073262457437924611)
                  ·
                    refine ⟨7136061109893686156886917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4757374073262457437924611 7136061109893686156886917)
                    ·
                      refine ⟨1338011458105066154416297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7136061109893686156886917 1338011458105066154416297)
                      ·
                        rfl

theorem cell23_2605768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_2605768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605768 prefixEnd_2605768 := by exact prefixLift 2605768
  have htrace : WordTrace (prefixWord ++ tailWord_2605768) baseStart_2605768 baseEnd_2605768 := by
    simpa [prefixWord, tailWord_2605768, baseEnd_2605768] using wordTrace_append hprefix tailTrace_2605768
  have hstable : (prefixWord ++ tailWord_2605768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605768).length < 2 ^ (prefixWord ++ tailWord_2605768).sum := by decide
  have hdescent : baseEnd_2605768 < baseStart_2605768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605772 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2605772 : Nat := 118140960795 + 2605772 * 2 ^ 59
def prefixEnd_2605772 : Nat := 4983230072969 + 3 ^ 40 * 2605772 * 2
def baseEnd_2605772 : Nat := 1338013512027684138766279

theorem tailTrace_2605772 : CollatzResearch.WordTrace tailWord_2605772 prefixEnd_2605772 1338013512027684138766279 := by
  unfold tailWord_2605772
  simp only [CollatzResearch.WordTrace]
  refine ⟨47520156357870274636013785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63360208477160366181351713 47520156357870274636013785)
  ·
    refine ⟨35640117268402705977010339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47520156357870274636013785 35640117268402705977010339)
    ·
      refine ⟨53460175902604058965515509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35640117268402705977010339 53460175902604058965515509)
      ·
        refine ⟨5011891490869130528017079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53460175902604058965515509 5011891490869130528017079)
        ·
          refine ⟨7517837236303695792025619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011891490869130528017079 7517837236303695792025619)
          ·
            refine ⟨11276755854455543688038429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7517837236303695792025619 11276755854455543688038429)
            ·
              refine ⟨4228783445420828883014411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11276755854455543688038429 4228783445420828883014411)
              ·
                refine ⟨6343175168131243324521617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228783445420828883014411 6343175168131243324521617)
                ·
                  refine ⟨4757381376098432493391213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6343175168131243324521617 4757381376098432493391213)
                  ·
                    refine ⟨1784018016036912185021705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4757381376098432493391213 1784018016036912185021705)
                    ·
                      refine ⟨1338013512027684138766279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784018016036912185021705 1338013512027684138766279)
                      ·
                        rfl

theorem cell23_2605772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2605772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605772 prefixEnd_2605772 := by exact prefixLift 2605772
  have htrace : WordTrace (prefixWord ++ tailWord_2605772) baseStart_2605772 baseEnd_2605772 := by
    simpa [prefixWord, tailWord_2605772, baseEnd_2605772] using wordTrace_append hprefix tailTrace_2605772
  have hstable : (prefixWord ++ tailWord_2605772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605772).length < 2 ^ (prefixWord ++ tailWord_2605772).sum := by decide
  have hdescent : baseEnd_2605772 < baseStart_2605772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605785 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 5, 2, 2]
def baseStart_2605785 : Nat := 118140960795 + 2605785 * 2 ^ 59
def prefixEnd_2605785 : Nat := 4983230072969 + 3 ^ 40 * 2605785 * 2
def baseEnd_2605785 : Nat := 1338020187276192587903719

theorem tailTrace_2605785 : CollatzResearch.WordTrace tailWord_2605785 prefixEnd_2605785 1338020187276192587903719 := by
  unfold tailWord_2605785
  simp only [CollatzResearch.WordTrace]
  refine ⟨95040786864693452492250809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63360524576462301661500539 95040786864693452492250809)
  ·
    refine ⟨71280590148520089369188107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95040786864693452492250809 71280590148520089369188107)
    ·
      refine ⟨106920885222780134053782161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71280590148520089369188107 106920885222780134053782161)
      ·
        refine ⟨80190663917085100540336621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106920885222780134053782161 80190663917085100540336621)
        ·
          refine ⟨30071498968906912702626233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80190663917085100540336621 30071498968906912702626233)
          ·
            refine ⟨22553624226680184526969675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30071498968906912702626233 22553624226680184526969675)
            ·
              refine ⟨33830436340020276790454513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22553624226680184526969675 33830436340020276790454513)
              ·
                refine ⟨25372827255015207592840885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33830436340020276790454513 25372827255015207592840885)
                ·
                  refine ⟨2378702555157675711828833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25372827255015207592840885 2378702555157675711828833)
                  ·
                    refine ⟨1784026916368256783871625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2378702555157675711828833 1784026916368256783871625)
                    ·
                      refine ⟨1338020187276192587903719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784026916368256783871625 1338020187276192587903719)
                      ·
                        rfl

theorem cell23_2605785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_2605785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605785 prefixEnd_2605785 := by exact prefixLift 2605785
  have htrace : WordTrace (prefixWord ++ tailWord_2605785) baseStart_2605785 baseEnd_2605785 := by
    simpa [prefixWord, tailWord_2605785, baseEnd_2605785] using wordTrace_append hprefix tailTrace_2605785
  have hstable : (prefixWord ++ tailWord_2605785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605785).length < 2 ^ (prefixWord ++ tailWord_2605785).sum := by decide
  have hdescent : baseEnd_2605785 < baseStart_2605785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605791 : List Nat := [1, 1, 2, 3, 2, 4, 10]
def baseStart_2605791 : Nat := 118140960795 + 2605791 * 2 ^ 59
def prefixEnd_2605791 : Nat := 4983230072969 + 3 ^ 40 * 2605791 * 2
def baseEnd_2605791 : Nat := 16518805779754562523811

theorem tailTrace_2605791 : CollatzResearch.WordTrace tailWord_2605791 prefixEnd_2605791 16518805779754562523811 := by
  unfold tailWord_2605791
  simp only [CollatzResearch.WordTrace]
  refine ⟨95041005702671715516969227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63360670468447810344646151 95041005702671715516969227)
  ·
    refine ⟨142561508554007573275453841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95041005702671715516969227 142561508554007573275453841)
    ·
      refine ⟨106921131415505679956590381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142561508554007573275453841 106921131415505679956590381)
      ·
        refine ⟨40095424280814629983721393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106921131415505679956590381 40095424280814629983721393)
        ·
          refine ⟨30071568210610972487791045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40095424280814629983721393 30071568210610972487791045)
          ·
            refine ⟨5638419039489557341460821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30071568210610972487791045 5638419039489557341460821)
            ·
              refine ⟨16518805779754562523811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5638419039489557341460821 16518805779754562523811)
              ·
                rfl

theorem cell23_2605791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 10].length) (baseStart_2605791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605791 prefixEnd_2605791 := by exact prefixLift 2605791
  have htrace : WordTrace (prefixWord ++ tailWord_2605791) baseStart_2605791 baseEnd_2605791 := by
    simpa [prefixWord, tailWord_2605791, baseEnd_2605791] using wordTrace_append hprefix tailTrace_2605791
  have hstable : (prefixWord ++ tailWord_2605791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605791).length < 2 ^ (prefixWord ++ tailWord_2605791).sum := by decide
  have hdescent : baseEnd_2605791 < baseStart_2605791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605795 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 4, 4]
def baseStart_2605795 : Nat := 118140960795 + 2605795 * 2 ^ 59
def prefixEnd_2605795 : Nat := 4983230072969 + 3 ^ 40 * 2605795 * 2
def baseEnd_2605795 : Nat := 446008440694245849592891

theorem tailTrace_2605795 : CollatzResearch.WordTrace tailWord_2605795 prefixEnd_2605795 446008440694245849592891 := by
  unfold tailWord_2605795
  simp only [CollatzResearch.WordTrace]
  refine ⟨95041151594657224200114839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63360767729771482800076559 95041151594657224200114839)
  ·
    refine ⟨142561727391985836300172259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95041151594657224200114839 142561727391985836300172259)
    ·
      refine ⟨213842591087978754450258389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142561727391985836300172259 213842591087978754450258389)
      ·
        refine ⟨5011935728624502057427931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 213842591087978754450258389 5011935728624502057427931)
        ·
          refine ⟨7517903592936753086141897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011935728624502057427931 7517903592936753086141897)
          ·
            refine ⟨5638427694702564814606423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7517903592936753086141897 5638427694702564814606423)
            ·
              refine ⟨8457641542053847221909635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638427694702564814606423 8457641542053847221909635)
              ·
                refine ⟨12686462313080770832864453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8457641542053847221909635 12686462313080770832864453)
                ·
                  refine ⟨2378711683702644531162085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12686462313080770832864453 2378711683702644531162085)
                  ·
                    refine ⟨446008440694245849592891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2378711683702644531162085 446008440694245849592891)
                    ·
                      rfl

theorem cell23_2605795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 4].length) (baseStart_2605795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605795 prefixEnd_2605795 := by exact prefixLift 2605795
  have htrace : WordTrace (prefixWord ++ tailWord_2605795) baseStart_2605795 baseEnd_2605795 := by
    simpa [prefixWord, tailWord_2605795, baseEnd_2605795] using wordTrace_append hprefix tailTrace_2605795
  have hstable : (prefixWord ++ tailWord_2605795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605795).length < 2 ^ (prefixWord ++ tailWord_2605795).sum := by decide
  have hdescent : baseEnd_2605795 < baseStart_2605795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605822 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2605822 : Nat := 118140960795 + 2605822 * 2 ^ 59
def prefixEnd_2605822 : Nat := 4983230072969 + 3 ^ 40 * 2605822 * 2
def baseEnd_2605822 : Nat := 1338039186060408943141049

theorem tailTrace_2605822 : CollatzResearch.WordTrace tailWord_2605822 prefixEnd_2605822 1338039186060408943141049 := by
  unfold tailWord_2605822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11880267045694925976418465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63361424243706271874231813 11880267045694925976418465)
  ·
    refine ⟨8910200284271194482313849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11880267045694925976418465 8910200284271194482313849)
    ·
      refine ⟨6682650213203395861735387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8910200284271194482313849 6682650213203395861735387)
      ·
        refine ⟨10023975319805093792603081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6682650213203395861735387 10023975319805093792603081)
        ·
          refine ⟨7517981489853820344452311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10023975319805093792603081 7517981489853820344452311)
          ·
            refine ⟨11276972234780730516678467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7517981489853820344452311 11276972234780730516678467)
            ·
              refine ⟨16915458352171095775017701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11276972234780730516678467 16915458352171095775017701)
              ·
                refine ⟨3171648441032080457815819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16915458352171095775017701 3171648441032080457815819)
                ·
                  refine ⟨4757472661548120686723729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171648441032080457815819 4757472661548120686723729)
                  ·
                    refine ⟨3568104496161090515042797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4757472661548120686723729 3568104496161090515042797)
                    ·
                      refine ⟨1338039186060408943141049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3568104496161090515042797 1338039186060408943141049)
                      ·
                        rfl

theorem cell23_2605822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2605822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605822 prefixEnd_2605822 := by exact prefixLift 2605822
  have htrace : WordTrace (prefixWord ++ tailWord_2605822) baseStart_2605822 baseEnd_2605822 := by
    simpa [prefixWord, tailWord_2605822, baseEnd_2605822] using wordTrace_append hprefix tailTrace_2605822
  have hstable : (prefixWord ++ tailWord_2605822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605822).length < 2 ^ (prefixWord ++ tailWord_2605822).sum := by decide
  have hdescent : baseEnd_2605822 < baseStart_2605822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605842 : List Nat := [3, 2, 4, 1, 3, 1, 9]
def baseStart_2605842 : Nat := 118140960795 + 2605842 * 2 ^ 59
def prefixEnd_2605842 : Nat := 4983230072969 + 3 ^ 40 * 2605842 * 2
def baseEnd_2605842 : Nat := 16519129082388874875197

theorem tailTrace_2605842 : CollatzResearch.WordTrace tailWord_2605842 prefixEnd_2605842 16519129082388874875197 := by
  unfold tailWord_2605842
  simp only [CollatzResearch.WordTrace]
  refine ⟨23760716456371737806768945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63361910550324634151383853 23760716456371737806768945)
  ·
    refine ⟨17820537342278803355076709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23760716456371737806768945 17820537342278803355076709)
    ·
      refine ⟨3341350751677275629076883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17820537342278803355076709 3341350751677275629076883)
      ·
        refine ⟨5012026127515913443615325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341350751677275629076883 5012026127515913443615325)
        ·
          refine ⟨1879509797818467541355747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5012026127515913443615325 1879509797818467541355747)
          ·
            refine ⟨2819264696727701312033621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879509797818467541355747 2819264696727701312033621)
            ·
              refine ⟨16519129082388874875197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2819264696727701312033621 16519129082388874875197)
              ·
                rfl

theorem cell23_2605842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 9].length) (baseStart_2605842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605842 prefixEnd_2605842 := by exact prefixLift 2605842
  have htrace : WordTrace (prefixWord ++ tailWord_2605842) baseStart_2605842 baseEnd_2605842 := by
    simpa [prefixWord, tailWord_2605842, baseEnd_2605842] using wordTrace_append hprefix tailTrace_2605842
  have hstable : (prefixWord ++ tailWord_2605842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605842).length < 2 ^ (prefixWord ++ tailWord_2605842).sum := by decide
  have hdescent : baseEnd_2605842 < baseStart_2605842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605853 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_2605853 : Nat := 118140960795 + 2605853 * 2 ^ 59
def prefixEnd_2605853 : Nat := 4983230072969 + 3 ^ 40 * 2605853 * 2
def baseEnd_2605853 : Nat := 1338055103960698321853407

theorem tailTrace_2605853 : CollatzResearch.WordTrace tailWord_2605853 prefixEnd_2605853 1338055103960698321853407 := by
  unfold tailWord_2605853
  simp only [CollatzResearch.WordTrace]
  refine ⟨95043267028447100105726213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63362178018964733403817475 95043267028447100105726213)
  ·
    refine ⟨17820612567833831269823665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95043267028447100105726213 17820612567833831269823665)
    ·
      refine ⟨13365459425875373452367749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17820612567833831269823665 13365459425875373452367749)
      ·
        refine ⟨2506023642351632522318953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13365459425875373452367749 2506023642351632522318953)
        ·
          refine ⟨1879517731763724391739215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2506023642351632522318953 1879517731763724391739215)
          ·
            refine ⟨2819276597645586587608823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879517731763724391739215 2819276597645586587608823)
            ·
              refine ⟨4228914896468379881413235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819276597645586587608823 4228914896468379881413235)
              ·
                refine ⟨6343372344702569822119853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228914896468379881413235 6343372344702569822119853)
                ·
                  refine ⟨2378764629263463683294945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6343372344702569822119853 2378764629263463683294945)
                  ·
                    refine ⟨1784073471947597762471209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2378764629263463683294945 1784073471947597762471209)
                    ·
                      refine ⟨1338055103960698321853407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784073471947597762471209 1338055103960698321853407)
                      ·
                        rfl

theorem cell23_2605853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_2605853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605853 prefixEnd_2605853 := by exact prefixLift 2605853
  have htrace : WordTrace (prefixWord ++ tailWord_2605853) baseStart_2605853 baseEnd_2605853 := by
    simpa [prefixWord, tailWord_2605853, baseEnd_2605853] using wordTrace_append hprefix tailTrace_2605853
  have hstable : (prefixWord ++ tailWord_2605853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605853).length < 2 ^ (prefixWord ++ tailWord_2605853).sum := by decide
  have hdescent : baseEnd_2605853 < baseStart_2605853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605909 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_2605909 : Nat := 118140960795 + 2605909 * 2 ^ 59
def prefixEnd_2605909 : Nat := 4983230072969 + 3 ^ 40 * 2605909 * 2
def baseEnd_2605909 : Nat := 1338083858877350102753149

theorem tailTrace_2605909 : CollatzResearch.WordTrace tailWord_2605909 prefixEnd_2605909 1338083858877350102753149 := by
  unfold tailWord_2605909
  simp only [CollatzResearch.WordTrace]
  refine ⟨95045309516244221669764781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63363539677496147779843187 95045309516244221669764781)
  ·
    refine ⟨35641991068591583126161793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95045309516244221669764781 35641991068591583126161793)
    ·
      refine ⟨26731493301443687344621345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35641991068591583126161793 26731493301443687344621345)
      ·
        refine ⟨20048619976082765508466009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26731493301443687344621345 20048619976082765508466009)
        ·
          refine ⟨15036464982062074131349507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20048619976082765508466009 15036464982062074131349507)
          ·
            refine ⟨22554697473093111197024261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15036464982062074131349507 22554697473093111197024261)
            ·
              refine ⟨4229005776204958349442049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22554697473093111197024261 4229005776204958349442049)
              ·
                refine ⟨3171754332153718762081537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4229005776204958349442049 3171754332153718762081537)
                ·
                  refine ⟨2378815749115289071561153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3171754332153718762081537 2378815749115289071561153)
                  ·
                    refine ⟨1784111811836466803670865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2378815749115289071561153 1784111811836466803670865)
                    ·
                      refine ⟨1338083858877350102753149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784111811836466803670865 1338083858877350102753149)
                      ·
                        rfl

theorem cell23_2605909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_2605909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605909 prefixEnd_2605909 := by exact prefixLift 2605909
  have htrace : WordTrace (prefixWord ++ tailWord_2605909) baseStart_2605909 baseEnd_2605909 := by
    simpa [prefixWord, tailWord_2605909, baseEnd_2605909] using wordTrace_append hprefix tailTrace_2605909
  have hstable : (prefixWord ++ tailWord_2605909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605909).length < 2 ^ (prefixWord ++ tailWord_2605909).sum := by decide
  have hdescent : baseEnd_2605909 < baseStart_2605909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605922 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2605922 : Nat := 118140960795 + 2605922 * 2 ^ 59
def prefixEnd_2605922 : Nat := 4983230072969 + 3 ^ 40 * 2605922 * 2
def baseEnd_2605922 : Nat := 1338090534125858551890589

theorem tailTrace_2605922 : CollatzResearch.WordTrace tailWord_2605922 prefixEnd_2605922 1338090534125858551890589 := by
  unfold tailWord_2605922
  simp only [CollatzResearch.WordTrace]
  refine ⟨23761445916299281222497005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63363855776798083259992013 23761445916299281222497005)
  ·
    refine ⟨8910542218612230458436377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23761445916299281222497005 8910542218612230458436377)
    ·
      refine ⟨6682906663959172843827283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8910542218612230458436377 6682906663959172843827283)
      ·
        refine ⟨10024359995938759265740925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6682906663959172843827283 10024359995938759265740925)
        ·
          refine ⟨3759134998477034724652847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10024359995938759265740925 3759134998477034724652847)
          ·
            refine ⟨5638702497715552086979271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759134998477034724652847 5638702497715552086979271)
            ·
              refine ⟨8458053746573328130468907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638702497715552086979271 8458053746573328130468907)
              ·
                refine ⟨12687080619859992195703361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8458053746573328130468907 12687080619859992195703361)
                ·
                  refine ⟨9515310464894994146777521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12687080619859992195703361 9515310464894994146777521)
                  ·
                    refine ⟨7136482848671245610083141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9515310464894994146777521 7136482848671245610083141)
                    ·
                      refine ⟨1338090534125858551890589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7136482848671245610083141 1338090534125858551890589)
                      ·
                        rfl

theorem cell23_2605922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2605922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605922 prefixEnd_2605922 := by exact prefixLift 2605922
  have htrace : WordTrace (prefixWord ++ tailWord_2605922) baseStart_2605922 baseEnd_2605922 := by
    simpa [prefixWord, tailWord_2605922, baseEnd_2605922] using wordTrace_append hprefix tailTrace_2605922
  have hstable : (prefixWord ++ tailWord_2605922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605922).length < 2 ^ (prefixWord ++ tailWord_2605922).sum := by decide
  have hdescent : baseEnd_2605922 < baseStart_2605922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605938 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2605938 : Nat := 118140960795 + 2605938 * 2 ^ 59
def prefixEnd_2605938 : Nat := 4983230072969 + 3 ^ 40 * 2605938 * 2
def baseEnd_2605938 : Nat := 1338098749816330489290515

theorem tailTrace_2605938 : CollatzResearch.WordTrace tailWord_2605938 prefixEnd_2605938 1338098749816330489290515 := by
  unfold tailWord_2605938
  simp only [CollatzResearch.WordTrace]
  refine ⟨23761591808284789905642617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63364244822092773081713645 23761591808284789905642617)
  ·
    refine ⟨17821193856213592429231963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23761591808284789905642617 17821193856213592429231963)
    ·
      refine ⟨26731790784320388643847945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17821193856213592429231963 26731790784320388643847945)
      ·
        refine ⟨20048843088240291482885959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26731790784320388643847945 20048843088240291482885959)
        ·
          refine ⟨30073264632360437224328939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20048843088240291482885959 30073264632360437224328939)
          ·
            refine ⟨45109896948540655836493409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30073264632360437224328939 45109896948540655836493409)
            ·
              refine ⟨33832422711405491877370057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45109896948540655836493409 33832422711405491877370057)
              ·
                refine ⟨25374317033554118908027543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33832422711405491877370057 25374317033554118908027543)
                ·
                  refine ⟨38061475550331178362041315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25374317033554118908027543 38061475550331178362041315)
                  ·
                    refine ⟨57092213325496767543061973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38061475550331178362041315 57092213325496767543061973)
                    ·
                      refine ⟨1338098749816330489290515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57092213325496767543061973 1338098749816330489290515)
                      ·
                        rfl

theorem cell23_2605938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2605938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605938 prefixEnd_2605938 := by exact prefixLift 2605938
  have htrace : WordTrace (prefixWord ++ tailWord_2605938) baseStart_2605938 baseEnd_2605938 := by
    simpa [prefixWord, tailWord_2605938, baseEnd_2605938] using wordTrace_append hprefix tailTrace_2605938
  have hstable : (prefixWord ++ tailWord_2605938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605938).length < 2 ^ (prefixWord ++ tailWord_2605938).sum := by decide
  have hdescent : baseEnd_2605938 < baseStart_2605938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605945 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 2, 5]
def baseStart_2605945 : Nat := 118140960795 + 2605945 * 2 ^ 59
def prefixEnd_2605945 : Nat := 4983230072969 + 3 ^ 40 * 2605945 * 2
def baseEnd_2605945 : Nat := 446034114726970653967661

theorem tailTrace_2605945 : CollatzResearch.WordTrace tailWord_2605945 prefixEnd_2605945 446034114726970653967661 := by
  unfold tailWord_2605945
  simp only [CollatzResearch.WordTrace]
  refine ⟨95046622544113799818075289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63364415029409199878716859 95046622544113799818075289)
  ·
    refine ⟨71284966908085349863556467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95046622544113799818075289 71284966908085349863556467)
    ·
      refine ⟨106927450362128024795334701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71284966908085349863556467 106927450362128024795334701)
      ·
        refine ⟨40097793885798009298250513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106927450362128024795334701 40097793885798009298250513)
        ·
          refine ⟨30073345414348506973687885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40097793885798009298250513 30073345414348506973687885)
          ·
            refine ⟨11277504530380690115132957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30073345414348506973687885 11277504530380690115132957)
            ·
              refine ⟨4229064198892758793174859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11277504530380690115132957 4229064198892758793174859)
              ·
                refine ⟨6343596298339138189762289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4229064198892758793174859 6343596298339138189762289)
                ·
                  refine ⟨4757697223754353642321717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6343596298339138189762289 4757697223754353642321717)
                  ·
                    refine ⟨446034114726970653967661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4757697223754353642321717 446034114726970653967661)
                    ·
                      rfl

theorem cell23_2605945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_2605945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2605945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2605945 prefixEnd_2605945 := by exact prefixLift 2605945
  have htrace : WordTrace (prefixWord ++ tailWord_2605945) baseStart_2605945 baseEnd_2605945 := by
    simpa [prefixWord, tailWord_2605945, baseEnd_2605945] using wordTrace_append hprefix tailTrace_2605945
  have hstable : (prefixWord ++ tailWord_2605945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605945).length < 2 ^ (prefixWord ++ tailWord_2605945).sum := by decide
  have hdescent : baseEnd_2605945 < baseStart_2605945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606009 : List Nat := [1, 2, 1, 4, 2, 2, 3, 3, 1, 4]
def baseStart_2606009 : Nat := 118140960795 + 2606009 * 2 ^ 59
def prefixEnd_2606009 : Nat := 4983230072969 + 3 ^ 40 * 2606009 * 2
def baseEnd_2606009 : Nat := 446045068980933237167563

theorem tailTrace_2606009 : CollatzResearch.WordTrace tailWord_2606009 prefixEnd_2606009 446045068980933237167563 := by
  unfold tailWord_2606009
  simp only [CollatzResearch.WordTrace]
  refine ⟨95048956815881938748405081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63365971210587959165603387 95048956815881938748405081)
  ·
    refine ⟨71286717611911454061303811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95048956815881938748405081 71286717611911454061303811)
    ·
      refine ⟨106930076417867181091955717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71286717611911454061303811 106930076417867181091955717)
      ·
        refine ⟨20049389328350096454741697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106930076417867181091955717 20049389328350096454741697)
        ·
          refine ⟨15037041996262572341056273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20049389328350096454741697 15037041996262572341056273)
          ·
            refine ⟨11277781497196929255792205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15037041996262572341056273 11277781497196929255792205)
            ·
              refine ⟨4229168061448848470922077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11277781497196929255792205 4229168061448848470922077)
              ·
                refine ⟨1585938023043318176595779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4229168061448848470922077 1585938023043318176595779)
                ·
                  refine ⟨2378907034564977264893669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585938023043318176595779 2378907034564977264893669)
                  ·
                    refine ⟨446045068980933237167563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2378907034564977264893669 446045068980933237167563)
                    ·
                      rfl

theorem cell23_2606009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 4].length) (baseStart_2606009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606009 prefixEnd_2606009 := by exact prefixLift 2606009
  have htrace : WordTrace (prefixWord ++ tailWord_2606009) baseStart_2606009 baseEnd_2606009 := by
    simpa [prefixWord, tailWord_2606009, baseEnd_2606009] using wordTrace_append hprefix tailTrace_2606009
  have hstable : (prefixWord ++ tailWord_2606009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606009).length < 2 ^ (prefixWord ++ tailWord_2606009).sum := by decide
  have hdescent : baseEnd_2606009 < baseStart_2606009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606065 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 3, 6]
def baseStart_2606065 : Nat := 118140960795 + 2606065 * 2 ^ 59
def prefixEnd_2606065 : Nat := 4983230072969 + 3 ^ 40 * 2606065 * 2
def baseEnd_2606065 : Nat := 446054653953150497467477

theorem tailTrace_2606065 : CollatzResearch.WordTrace tailWord_2606065 prefixEnd_2606065 446054653953150497467477 := by
  unfold tailWord_2606065
  simp only [CollatzResearch.WordTrace]
  refine ⟨95050999303679060312443649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63367332869119373541629099 95050999303679060312443649)
  ·
    refine ⟨71288249477759295234332737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95050999303679060312443649 71288249477759295234332737)
    ·
      refine ⟨53466187108319471425749553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71288249477759295234332737 53466187108319471425749553)
      ·
        refine ⟨40099640331239603569312165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53466187108319471425749553 40099640331239603569312165)
        ·
          refine ⟨7518682562107425669246031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40099640331239603569312165 7518682562107425669246031)
          ·
            refine ⟨11278023843161138503869047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7518682562107425669246031 11278023843161138503869047)
            ·
              refine ⟨16917035764741707755803571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11278023843161138503869047 16917035764741707755803571)
              ·
                refine ⟨25375553647112561633705357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16917035764741707755803571 25375553647112561633705357)
                ·
                  refine ⟨9515832617667210612639509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25375553647112561633705357 9515832617667210612639509)
                  ·
                    refine ⟨446054653953150497467477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9515832617667210612639509 446054653953150497467477)
                    ·
                      rfl

theorem cell23_2606065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_2606065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606065 prefixEnd_2606065 := by exact prefixLift 2606065
  have htrace : WordTrace (prefixWord ++ tailWord_2606065) baseStart_2606065 baseEnd_2606065 := by
    simpa [prefixWord, tailWord_2606065, baseEnd_2606065] using wordTrace_append hprefix tailTrace_2606065
  have hstable : (prefixWord ++ tailWord_2606065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606065).length < 2 ^ (prefixWord ++ tailWord_2606065).sum := by decide
  have hdescent : baseEnd_2606065 < baseStart_2606065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606085 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_2606085 : Nat := 118140960795 + 2606085 * 2 ^ 59
def prefixEnd_2606085 : Nat := 4983230072969 + 3 ^ 40 * 2606085 * 2
def baseEnd_2606085 : Nat := 1338174231472541414152339

theorem tailTrace_2606085 : CollatzResearch.WordTrace tailWord_2606085 prefixEnd_2606085 1338174231472541414152339 := by
  unfold tailWord_2606085
  simp only [CollatzResearch.WordTrace]
  refine ⟨95051728763606603728171709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63367819175737735818781139 95051728763606603728171709)
  ·
    refine ⟨35644398286352476398064391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95051728763606603728171709 35644398286352476398064391)
    ·
      refine ⟨53466597429528714597096587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35644398286352476398064391 53466597429528714597096587)
      ·
        refine ⟨80199896144293071895644881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53466597429528714597096587 80199896144293071895644881)
        ·
          refine ⟨60149922108219803921733661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80199896144293071895644881 60149922108219803921733661)
          ·
            refine ⟨22556220790582426470650123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60149922108219803921733661 22556220790582426470650123)
            ·
              refine ⟨33834331185873639705975185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22556220790582426470650123 33834331185873639705975185)
              ·
                refine ⟨25375748389405229779481389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33834331185873639705975185 25375748389405229779481389)
                ·
                  refine ⟨9515905646026961167305521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25375748389405229779481389 9515905646026961167305521)
                  ·
                    refine ⟨7136929234520220875479141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9515905646026961167305521 7136929234520220875479141)
                    ·
                      refine ⟨1338174231472541414152339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7136929234520220875479141 1338174231472541414152339)
                      ·
                        rfl

theorem cell23_2606085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_2606085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606085 prefixEnd_2606085 := by exact prefixLift 2606085
  have htrace : WordTrace (prefixWord ++ tailWord_2606085) baseStart_2606085 baseEnd_2606085 := by
    simpa [prefixWord, tailWord_2606085, baseEnd_2606085] using wordTrace_append hprefix tailTrace_2606085
  have hstable : (prefixWord ++ tailWord_2606085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606085).length < 2 ^ (prefixWord ++ tailWord_2606085).sum := by decide
  have hdescent : baseEnd_2606085 < baseStart_2606085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606092 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_2606092 : Nat := 118140960795 + 2606092 * 2 ^ 59
def prefixEnd_2606092 : Nat := 4983230072969 + 3 ^ 40 * 2606092 * 2
def baseEnd_2606092 : Nat := 1338177825837122886764807

theorem tailTrace_2606092 : CollatzResearch.WordTrace tailWord_2606092 prefixEnd_2606092 1338177825837122886764807 := by
  unfold tailWord_2606092
  simp only [CollatzResearch.WordTrace]
  refine ⟨47525992037290621961838265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63367989383054162615784353 47525992037290621961838265)
  ·
    refine ⟨35644494027967966471378699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47525992037290621961838265 35644494027967966471378699)
    ·
      refine ⟨53466741041951949707068049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35644494027967966471378699 53466741041951949707068049)
      ·
        refine ⟨40100055781463962280301037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53466741041951949707068049 40100055781463962280301037)
        ·
          refine ⟨15037520918048985855112889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40100055781463962280301037 15037520918048985855112889)
          ·
            refine ⟨11278140688536739391334667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15037520918048985855112889 11278140688536739391334667)
            ·
              refine ⟨16917211032805109087002001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11278140688536739391334667 16917211032805109087002001)
              ·
                refine ⟨12687908274603831815251501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16917211032805109087002001 12687908274603831815251501)
                ·
                  refine ⟨4757965602976436930719313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12687908274603831815251501 4757965602976436930719313)
                  ·
                    refine ⟨3568474202232327698039485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4757965602976436930719313 3568474202232327698039485)
                    ·
                      refine ⟨1338177825837122886764807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3568474202232327698039485 1338177825837122886764807)
                      ·
                        rfl

theorem cell23_2606092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_2606092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606092 prefixEnd_2606092 := by exact prefixLift 2606092
  have htrace : WordTrace (prefixWord ++ tailWord_2606092) baseStart_2606092 baseEnd_2606092 := by
    simpa [prefixWord, tailWord_2606092, baseEnd_2606092] using wordTrace_append hprefix tailTrace_2606092
  have hstable : (prefixWord ++ tailWord_2606092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606092).length < 2 ^ (prefixWord ++ tailWord_2606092).sum := by decide
  have hdescent : baseEnd_2606092 < baseStart_2606092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606119 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2606119 : Nat := 118140960795 + 2606119 * 2 ^ 59
def prefixEnd_2606119 : Nat := 4983230072969 + 3 ^ 40 * 2606119 * 2
def baseEnd_2606119 : Nat := 1338191689814794281127183

theorem tailTrace_2606119 : CollatzResearch.WordTrace tailWord_2606119 prefixEnd_2606119 1338191689814794281127183 := by
  unfold tailWord_2606119
  simp only [CollatzResearch.WordTrace]
  refine ⟨95052968845483427534909411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63368645896988951689939607 95052968845483427534909411)
  ·
    refine ⟨142579453268225141302364117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95052968845483427534909411 142579453268225141302364117)
    ·
      refine ⟨3341705935974026749274159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 142579453268225141302364117 3341705935974026749274159)
      ·
        refine ⟨5012558903961040123911239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341705935974026749274159 5012558903961040123911239)
        ·
          refine ⟨7518838355941560185866859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012558903961040123911239 7518838355941560185866859)
          ·
            refine ⟨11278257533912340278800289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7518838355941560185866859 11278257533912340278800289)
            ·
              refine ⟨8458693150434255209100217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11278257533912340278800289 8458693150434255209100217)
              ·
                refine ⟨6344019862825691406825163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8458693150434255209100217 6344019862825691406825163)
                ·
                  refine ⟨9516029794238537110237745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6344019862825691406825163 9516029794238537110237745)
                  ·
                    refine ⟨7137022345678902832678309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9516029794238537110237745 7137022345678902832678309)
                    ·
                      refine ⟨1338191689814794281127183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7137022345678902832678309 1338191689814794281127183)
                      ·
                        rfl

theorem cell23_2606119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2606119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606119 prefixEnd_2606119 := by exact prefixLift 2606119
  have htrace : WordTrace (prefixWord ++ tailWord_2606119) baseStart_2606119 baseEnd_2606119 := by
    simpa [prefixWord, tailWord_2606119, baseEnd_2606119] using wordTrace_append hprefix tailTrace_2606119
  have hstable : (prefixWord ++ tailWord_2606119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606119).length < 2 ^ (prefixWord ++ tailWord_2606119).sum := by decide
  have hdescent : baseEnd_2606119 < baseStart_2606119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606174 : List Nat := [4, 4, 1, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_2606174 : Nat := 118140960795 + 2606174 * 2 ^ 59
def prefixEnd_2606174 : Nat := 4983230072969 + 3 ^ 40 * 2606174 * 2
def baseEnd_2606174 : Nat := 1338219931250791565939431

theorem tailTrace_2606174 : CollatzResearch.WordTrace tailWord_2606174 prefixEnd_2606174 1338219931250791565939431 := by
  unfold tailWord_2606174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11881871857535521491020197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63369983240189447952107717 11881871857535521491020197)
  ·
    refine ⟨2227850973287910279566287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11881871857535521491020197 2227850973287910279566287)
    ·
      refine ⟨3341776459931865419349431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2227850973287910279566287 3341776459931865419349431)
      ·
        refine ⟨5012664689897798129024147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341776459931865419349431 5012664689897798129024147)
        ·
          refine ⟨7518997034846697193536221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012664689897798129024147 7518997034846697193536221)
          ·
            refine ⟨2819623888067511447576083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7518997034846697193536221 2819623888067511447576083)
            ·
              refine ⟨4229435832101267171364125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819623888067511447576083 4229435832101267171364125)
              ·
                refine ⟨1586038437037975189261547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4229435832101267171364125 1586038437037975189261547)
                ·
                  refine ⟨2379057655556962783892321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586038437037975189261547 2379057655556962783892321)
                  ·
                    refine ⟨1784293241667722087919241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2379057655556962783892321 1784293241667722087919241)
                    ·
                      refine ⟨1338219931250791565939431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784293241667722087919241 1338219931250791565939431)
                      ·
                        rfl

theorem cell23_2606174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_2606174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606174 prefixEnd_2606174 := by exact prefixLift 2606174
  have htrace : WordTrace (prefixWord ++ tailWord_2606174) baseStart_2606174 baseEnd_2606174 := by
    simpa [prefixWord, tailWord_2606174, baseEnd_2606174] using wordTrace_append hprefix tailTrace_2606174
  have hstable : (prefixWord ++ tailWord_2606174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606174).length < 2 ^ (prefixWord ++ tailWord_2606174).sum := by decide
  have hdescent : baseEnd_2606174 < baseStart_2606174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606213 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 2, 2, 2]
def baseStart_2606213 : Nat := 118140960795 + 2606213 * 2 ^ 59
def prefixEnd_2606213 : Nat := 4983230072969 + 3 ^ 40 * 2606213 * 2
def baseEnd_2606213 : Nat := 1338239956996316913351751

theorem tailTrace_2606213 : CollatzResearch.WordTrace tailWord_2606213 prefixEnd_2606213 1338239956996316913351751 := by
  unfold tailWord_2606213
  simp only [CollatzResearch.WordTrace]
  refine ⟨95056397307142881588831293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63370931538095254392554195 95056397307142881588831293)
  ·
    refine ⟨35646148990178580595811735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95056397307142881588831293 35646148990178580595811735)
    ·
      refine ⟨53469223485267870893717603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35646148990178580595811735 53469223485267870893717603)
      ·
        refine ⟨80203835227901806340576405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53469223485267870893717603 80203835227901806340576405)
        ·
          refine ⟨3759554776307897172214519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80203835227901806340576405 3759554776307897172214519)
          ·
            refine ⟨5639332164461845758321779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759554776307897172214519 5639332164461845758321779)
            ·
              refine ⟨8458998246692768637482669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639332164461845758321779 8458998246692768637482669)
              ·
                refine ⟨3172124342509788239056001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8458998246692768637482669 3172124342509788239056001)
                ·
                  refine ⟨2379093256882341179292001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3172124342509788239056001 2379093256882341179292001)
                  ·
                    refine ⟨1784319942661755884469001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2379093256882341179292001 1784319942661755884469001)
                    ·
                      refine ⟨1338239956996316913351751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784319942661755884469001 1338239956996316913351751)
                      ·
                        rfl

theorem cell23_2606213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_2606213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606213 prefixEnd_2606213 := by exact prefixLift 2606213
  have htrace : WordTrace (prefixWord ++ tailWord_2606213) baseStart_2606213 baseEnd_2606213 := by
    simpa [prefixWord, tailWord_2606213, baseEnd_2606213] using wordTrace_append hprefix tailTrace_2606213
  have hstable : (prefixWord ++ tailWord_2606213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606213).length < 2 ^ (prefixWord ++ tailWord_2606213).sum := by decide
  have hdescent : baseEnd_2606213 < baseStart_2606213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606252 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_2606252 : Nat := 118140960795 + 2606252 * 2 ^ 59
def prefixEnd_2606252 : Nat := 4983230072969 + 3 ^ 40 * 2606252 * 2
def baseEnd_2606252 : Nat := 1338259982741842260764071

theorem tailTrace_2606252 : CollatzResearch.WordTrace tailWord_2606252 prefixEnd_2606252 1338259982741842260764071 := by
  unfold tailWord_2606252
  simp only [CollatzResearch.WordTrace]
  refine ⟨47528909877000795624750505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63371879836001060833000673 47528909877000795624750505)
  ·
    refine ⟨35646682407750596718562879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47528909877000795624750505 35646682407750596718562879)
    ·
      refine ⟨53470023611625895077844319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35646682407750596718562879 53470023611625895077844319)
      ·
        refine ⟨80205035417438842616766479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53470023611625895077844319 80205035417438842616766479)
        ·
          refine ⟨120307553126158263925149719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80205035417438842616766479 120307553126158263925149719)
          ·
            refine ⟨180461329689237395887724579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120307553126158263925149719 180461329689237395887724579)
            ·
              refine ⟨270691994533856093831586869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180461329689237395887724579 270691994533856093831586869)
              ·
                refine ⟨25377374487549008796711269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270691994533856093831586869 25377374487549008796711269)
                ·
                  refine ⟨4758257716415439149383363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25377374487549008796711269 4758257716415439149383363)
                  ·
                    refine ⟨7137386574623158724075045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4758257716415439149383363 7137386574623158724075045)
                    ·
                      refine ⟨1338259982741842260764071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7137386574623158724075045 1338259982741842260764071)
                      ·
                        rfl

theorem cell23_2606252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_2606252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606252 prefixEnd_2606252 := by exact prefixLift 2606252
  have htrace : WordTrace (prefixWord ++ tailWord_2606252) baseStart_2606252 baseEnd_2606252 := by
    simpa [prefixWord, tailWord_2606252, baseEnd_2606252] using wordTrace_append hprefix tailTrace_2606252
  have hstable : (prefixWord ++ tailWord_2606252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606252).length < 2 ^ (prefixWord ++ tailWord_2606252).sum := by decide
  have hdescent : baseEnd_2606252 < baseStart_2606252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606269 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_2606269 : Nat := 118140960795 + 2606269 * 2 ^ 59
def prefixEnd_2606269 : Nat := 4983230072969 + 3 ^ 40 * 2606269 * 2
def baseEnd_2606269 : Nat := 1338268711912968694251493

theorem tailTrace_2606269 : CollatzResearch.WordTrace tailWord_2606269 prefixEnd_2606269 1338268711912968694251493 := by
  unfold tailWord_2606269
  simp only [CollatzResearch.WordTrace]
  refine ⟨95058439794940003152869861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63372293196626668768579907 95058439794940003152869861)
  ·
    refine ⟨17823457461551250591163099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95058439794940003152869861 17823457461551250591163099)
    ·
      refine ⟨26735186192326875886744649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17823457461551250591163099 26735186192326875886744649)
      ·
        refine ⟨20051389644245156915058487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26735186192326875886744649 20051389644245156915058487)
        ·
          refine ⟨30077084466367735372587731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20051389644245156915058487 30077084466367735372587731)
          ·
            refine ⟨45115626699551603058881597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30077084466367735372587731 45115626699551603058881597)
            ·
              refine ⟨16918360012331851147080599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45115626699551603058881597 16918360012331851147080599)
              ·
                refine ⟨25377540018497776720620899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16918360012331851147080599 25377540018497776720620899)
                ·
                  refine ⟨38066310027746665080931349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25377540018497776720620899 38066310027746665080931349)
                  ·
                    refine ⟨1784358282550624925668657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38066310027746665080931349 1784358282550624925668657)
                    ·
                      refine ⟨1338268711912968694251493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784358282550624925668657 1338268711912968694251493)
                      ·
                        rfl

theorem cell23_2606269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_2606269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606269 prefixEnd_2606269 := by exact prefixLift 2606269
  have htrace : WordTrace (prefixWord ++ tailWord_2606269) baseStart_2606269 baseEnd_2606269 := by
    simpa [prefixWord, tailWord_2606269, baseEnd_2606269] using wordTrace_append hprefix tailTrace_2606269
  have hstable : (prefixWord ++ tailWord_2606269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606269).length < 2 ^ (prefixWord ++ tailWord_2606269).sum := by decide
  have hdescent : baseEnd_2606269 < baseStart_2606269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606309 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 8]
def baseStart_2606309 : Nat := 118140960795 + 2606309 * 2 ^ 59
def prefixEnd_2606309 : Nat := 4983230072969 + 3 ^ 40 * 2606309 * 2
def baseEnd_2606309 : Nat := 148698805682127615305701

theorem tailTrace_2606309 : CollatzResearch.WordTrace tailWord_2606309 prefixEnd_2606309 148698805682127615305701 := by
  unfold tailWord_2606309
  simp only [CollatzResearch.WordTrace]
  refine ⟨95059898714795089984325981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63373265809863393322883987 95059898714795089984325981)
  ·
    refine ⟨35647462018048158744122243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95059898714795089984325981 35647462018048158744122243)
    ·
      refine ⟨53471193027072238116183365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35647462018048158744122243 53471193027072238116183365)
      ·
        refine ⟨10025848692576044646784381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53471193027072238116183365 10025848692576044646784381)
        ·
          refine ⟨3759693259716016742544143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10025848692576044646784381 3759693259716016742544143)
          ·
            refine ⟨5639539889574025113816215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759693259716016742544143 5639539889574025113816215)
            ·
              refine ⟨8459309834361037670724323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639539889574025113816215 8459309834361037670724323)
              ·
                refine ⟨12688964751541556506086485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8459309834361037670724323 12688964751541556506086485)
                ·
                  refine ⟨148698805682127615305701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12688964751541556506086485 148698805682127615305701)
                  ·
                    rfl

theorem cell23_2606309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_2606309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606309 prefixEnd_2606309 := by exact prefixLift 2606309
  have htrace : WordTrace (prefixWord ++ tailWord_2606309) baseStart_2606309 baseEnd_2606309 := by
    simpa [prefixWord, tailWord_2606309, baseEnd_2606309] using wordTrace_append hprefix tailTrace_2606309
  have hstable : (prefixWord ++ tailWord_2606309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606309).length < 2 ^ (prefixWord ++ tailWord_2606309).sum := by decide
  have hdescent : baseEnd_2606309 < baseStart_2606309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606312 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2606312 : Nat := 118140960795 + 2606312 * 2 ^ 59
def prefixEnd_2606312 : Nat := 4983230072969 + 3 ^ 40 * 2606312 * 2
def baseEnd_2606312 : Nat := 1338290791581112026013795

theorem tailTrace_2606312 : CollatzResearch.WordTrace tailWord_2606312 prefixEnd_2606312 1338290791581112026013795 := by
  unfold tailWord_2606312
  simp only [CollatzResearch.WordTrace]
  refine ⟨47530004066892110748342595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63373338755856147664456793 47530004066892110748342595)
  ·
    refine ⟨71295006100338166122513893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47530004066892110748342595 71295006100338166122513893)
    ·
      refine ⟨13367813643813406147971355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71295006100338166122513893 13367813643813406147971355)
      ·
        refine ⟨20051720465720109221957033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13367813643813406147971355 20051720465720109221957033)
        ·
          refine ⟨15038790349290081916467775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20051720465720109221957033 15038790349290081916467775)
          ·
            refine ⟨22558185523935122874701663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15038790349290081916467775 22558185523935122874701663)
            ·
              refine ⟨33837278285902684312052495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22558185523935122874701663 33837278285902684312052495)
              ·
                refine ⟨50755917428854026468078743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33837278285902684312052495 50755917428854026468078743)
                ·
                  refine ⟨76133876143281039702118115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50755917428854026468078743 76133876143281039702118115)
                  ·
                    refine ⟨114200814214921559553177173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76133876143281039702118115 114200814214921559553177173)
                    ·
                      refine ⟨1338290791581112026013795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 114200814214921559553177173 1338290791581112026013795)
                      ·
                        rfl

theorem cell23_2606312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2606312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606312 prefixEnd_2606312 := by exact prefixLift 2606312
  have htrace : WordTrace (prefixWord ++ tailWord_2606312) baseStart_2606312 baseEnd_2606312 := by
    simpa [prefixWord, tailWord_2606312, baseEnd_2606312] using wordTrace_append hprefix tailTrace_2606312
  have hstable : (prefixWord ++ tailWord_2606312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606312).length < 2 ^ (prefixWord ++ tailWord_2606312).sum := by decide
  have hdescent : baseEnd_2606312 < baseStart_2606312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606329 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 3, 5, 2]
def baseStart_2606329 : Nat := 118140960795 + 2606329 * 2 ^ 59
def prefixEnd_2606329 : Nat := 4983230072969 + 3 ^ 40 * 2606329 * 2
def baseEnd_2606329 : Nat := 1338299520752238459501217

theorem tailTrace_2606329 : CollatzResearch.WordTrace tailWord_2606329 prefixEnd_2606329 1338299520752238459501217 := by
  unfold tailWord_2606329
  simp only [CollatzResearch.WordTrace]
  refine ⟨95060628174722633400054041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63373752116481755600036027 95060628174722633400054041)
  ·
    refine ⟨71295471131041975050040531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95060628174722633400054041 71295471131041975050040531)
    ·
      refine ⟨106943206696562962575060797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71295471131041975050040531 106943206696562962575060797)
      ·
        refine ⟨40103702511211110965647799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106943206696562962575060797 40103702511211110965647799)
        ·
          refine ⟨60155553766816666448471699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40103702511211110965647799 60155553766816666448471699)
          ·
            refine ⟨90233330650224999672707549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60155553766816666448471699 90233330650224999672707549)
            ·
              refine ⟨33837498993834374877265331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90233330650224999672707549 33837498993834374877265331)
              ·
                refine ⟨50756248490751562315897997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33837498993834374877265331 50756248490751562315897997)
                ·
                  refine ⟨19033593184031835868461749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50756248490751562315897997 19033593184031835868461749)
                  ·
                    refine ⟨1784399361002984612668289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19033593184031835868461749 1784399361002984612668289)
                    ·
                      refine ⟨1338299520752238459501217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784399361002984612668289 1338299520752238459501217)
                      ·
                        rfl

theorem cell23_2606329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_2606329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606329 prefixEnd_2606329 := by exact prefixLift 2606329
  have htrace : WordTrace (prefixWord ++ tailWord_2606329) baseStart_2606329 baseEnd_2606329 := by
    simpa [prefixWord, tailWord_2606329, baseEnd_2606329] using wordTrace_append hprefix tailTrace_2606329
  have hstable : (prefixWord ++ tailWord_2606329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606329).length < 2 ^ (prefixWord ++ tailWord_2606329).sum := by decide
  have hdescent : baseEnd_2606329 < baseStart_2606329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606339 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 1, 5]
def baseStart_2606339 : Nat := 118140960795 + 2606339 * 2 ^ 59
def prefixEnd_2606339 : Nat := 4983230072969 + 3 ^ 40 * 2606339 * 2
def baseEnd_2606339 : Nat := 446101551852927806792057

theorem tailTrace_2606339 : CollatzResearch.WordTrace tailWord_2606339 prefixEnd_2606339 446101551852927806792057 := by
  unfold tailWord_2606339
  simp only [CollatzResearch.WordTrace]
  refine ⟨95060992904686405107918071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63373995269790936738612047 95060992904686405107918071)
  ·
    refine ⟨142591489357029607661877107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95060992904686405107918071 142591489357029607661877107)
    ·
      refine ⟨213887234035544411492815661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142591489357029607661877107 213887234035544411492815661)
      ·
        refine ⟨80207712763329154309805873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213887234035544411492815661 80207712763329154309805873)
        ·
          refine ⟨60155784572496865732354405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80207712763329154309805873 60155784572496865732354405)
          ·
            refine ⟨11279209607343162324816451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60155784572496865732354405 11279209607343162324816451)
            ·
              refine ⟨16918814411014743487224677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11279209607343162324816451 16918814411014743487224677)
              ·
                refine ⟨3172277702065264403854627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16918814411014743487224677 3172277702065264403854627)
                ·
                  refine ⟨4758416553097896605781941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172277702065264403854627 4758416553097896605781941)
                  ·
                    refine ⟨446101551852927806792057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4758416553097896605781941 446101551852927806792057)
                    ·
                      rfl

theorem cell23_2606339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 5].length) (baseStart_2606339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606339 prefixEnd_2606339 := by exact prefixLift 2606339
  have htrace : WordTrace (prefixWord ++ tailWord_2606339) baseStart_2606339 baseEnd_2606339 := by
    simpa [prefixWord, tailWord_2606339, baseEnd_2606339] using wordTrace_append hprefix tailTrace_2606339
  have hstable : (prefixWord ++ tailWord_2606339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606339).length < 2 ^ (prefixWord ++ tailWord_2606339).sum := by decide
  have hdescent : baseEnd_2606339 < baseStart_2606339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606346 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_2606346 : Nat := 118140960795 + 2606346 * 2 ^ 59
def prefixEnd_2606346 : Nat := 4983230072969 + 3 ^ 40 * 2606346 * 2
def baseEnd_2606346 : Nat := 1338308249923364892988639

theorem tailTrace_2606346 : CollatzResearch.WordTrace tailWord_2606346 prefixEnd_2606346 1338308249923364892988639 := by
  unfold tailWord_2606346
  simp only [CollatzResearch.WordTrace]
  refine ⟨23765312053915261325855723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63374165477107363535615261 23765312053915261325855723)
  ·
    refine ⟨35647968080872891988783585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23765312053915261325855723 35647968080872891988783585)
    ·
      refine ⟨26735976060654668991587689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35647968080872891988783585 26735976060654668991587689)
      ·
        refine ⟨20051982045491001743690767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26735976060654668991587689 20051982045491001743690767)
        ·
          refine ⟨30077973068236502615536151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20051982045491001743690767 30077973068236502615536151)
          ·
            refine ⟨45116959602354753923304227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30077973068236502615536151 45116959602354753923304227)
            ·
              refine ⟨67675439403532130884956341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45116959602354753923304227 67675439403532130884956341)
              ·
                refine ⟨6344572444081137270464657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67675439403532130884956341 6344572444081137270464657)
                ·
                  refine ⟨4758429333060852952848493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6344572444081137270464657 4758429333060852952848493)
                  ·
                    refine ⟨1784410999897819857318185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4758429333060852952848493 1784410999897819857318185)
                    ·
                      refine ⟨1338308249923364892988639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784410999897819857318185 1338308249923364892988639)
                      ·
                        rfl

theorem cell23_2606346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_2606346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606346 prefixEnd_2606346 := by exact prefixLift 2606346
  have htrace : WordTrace (prefixWord ++ tailWord_2606346) baseStart_2606346 baseEnd_2606346 := by
    simpa [prefixWord, tailWord_2606346, baseEnd_2606346] using wordTrace_append hprefix tailTrace_2606346
  have hstable : (prefixWord ++ tailWord_2606346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606346).length < 2 ^ (prefixWord ++ tailWord_2606346).sum := by decide
  have hdescent : baseEnd_2606346 < baseStart_2606346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606370 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_2606370 : Nat := 118140960795 + 2606370 * 2 ^ 59
def prefixEnd_2606370 : Nat := 4983230072969 + 3 ^ 40 * 2606370 * 2
def baseEnd_2606370 : Nat := 1338320573459072799088529

theorem tailTrace_2606370 : CollatzResearch.WordTrace tailWord_2606370 prefixEnd_2606370 1338320573459072799088529 := by
  unfold tailWord_2606370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23765530891893524350574141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63374749045049398268197709 23765530891893524350574141)
  ·
    refine ⟨8912074084460071631465303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23765530891893524350574141 8912074084460071631465303)
    ·
      refine ⟨13368111126690107447197955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8912074084460071631465303 13368111126690107447197955)
      ·
        refine ⟨20052166690035161170796933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13368111126690107447197955 20052166690035161170796933)
        ·
          refine ⟨3759781254381592719524425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20052166690035161170796933 3759781254381592719524425)
          ·
            refine ⟨2819835940786194539643319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3759781254381592719524425 2819835940786194539643319)
            ·
              refine ⟨4229753911179291809464979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819835940786194539643319 4229753911179291809464979)
              ·
                refine ⟨6344630866768937714197469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4229753911179291809464979 6344630866768937714197469)
                ·
                  refine ⟨2379236575038351642824051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6344630866768937714197469 2379236575038351642824051)
                  ·
                    refine ⟨3568854862557527464236077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2379236575038351642824051 3568854862557527464236077)
                    ·
                      refine ⟨1338320573459072799088529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3568854862557527464236077 1338320573459072799088529)
                      ·
                        rfl

theorem cell23_2606370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_2606370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606370 prefixEnd_2606370 := by exact prefixLift 2606370
  have htrace : WordTrace (prefixWord ++ tailWord_2606370) baseStart_2606370 baseEnd_2606370 := by
    simpa [prefixWord, tailWord_2606370, baseEnd_2606370] using wordTrace_append hprefix tailTrace_2606370
  have hstable : (prefixWord ++ tailWord_2606370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606370).length < 2 ^ (prefixWord ++ tailWord_2606370).sum := by decide
  have hdescent : baseEnd_2606370 < baseStart_2606370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606389 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2606389 : Nat := 118140960795 + 2606389 * 2 ^ 59
def prefixEnd_2606389 : Nat := 4983230072969 + 3 ^ 40 * 2606389 * 2
def baseEnd_2606389 : Nat := 1338330329591508224750941

theorem tailTrace_2606389 : CollatzResearch.WordTrace tailWord_2606389 prefixEnd_2606389 1338330329591508224750941 := by
  unfold tailWord_2606389
  simp only [CollatzResearch.WordTrace]
  refine ⟨95062816554505263647238221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63375211036336842431492147 95062816554505263647238221)
  ·
    refine ⟨35648556207939473867714333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95062816554505263647238221 35648556207939473867714333)
    ·
      refine ⟨13368208577977302700392875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35648556207939473867714333 13368208577977302700392875)
      ·
        refine ⟨20052312866965954050589313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13368208577977302700392875 20052312866965954050589313)
        ·
          refine ⟨15039234650224465537941985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20052312866965954050589313 15039234650224465537941985)
          ·
            refine ⟨11279425987668349153456489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15039234650224465537941985 11279425987668349153456489)
            ·
              refine ⟨8459569490751261865092367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11279425987668349153456489 8459569490751261865092367)
              ·
                refine ⟨12689354236126892797638551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8459569490751261865092367 12689354236126892797638551)
                ·
                  refine ⟨19034031354190339196457827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12689354236126892797638551 19034031354190339196457827)
                  ·
                    refine ⟨28551047031285508794686741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19034031354190339196457827 28551047031285508794686741)
                    ·
                      refine ⟨1338330329591508224750941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28551047031285508794686741 1338330329591508224750941)
                      ·
                        rfl

theorem cell23_2606389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2606389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606389 prefixEnd_2606389 := by exact prefixLift 2606389
  have htrace : WordTrace (prefixWord ++ tailWord_2606389) baseStart_2606389 baseEnd_2606389 := by
    simpa [prefixWord, tailWord_2606389, baseEnd_2606389] using wordTrace_append hprefix tailTrace_2606389
  have hstable : (prefixWord ++ tailWord_2606389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606389).length < 2 ^ (prefixWord ++ tailWord_2606389).sum := by decide
  have hdescent : baseEnd_2606389 < baseStart_2606389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606396 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_2606396 : Nat := 118140960795 + 2606396 * 2 ^ 59
def prefixEnd_2606396 : Nat := 4983230072969 + 3 ^ 40 * 2606396 * 2
def baseEnd_2606396 : Nat := 1338333923956089697363409

theorem tailTrace_2606396 : CollatzResearch.WordTrace tailWord_2606396 prefixEnd_2606396 1338333923956089697363409 := by
  unfold tailWord_2606396
  simp only [CollatzResearch.WordTrace]
  refine ⟨47531535932739951921371521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63375381243653269228495361 47531535932739951921371521)
  ·
    refine ⟨35648651949554963941028641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47531535932739951921371521 35648651949554963941028641)
    ·
      refine ⟨26736488962166222955771481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35648651949554963941028641 26736488962166222955771481)
      ·
        refine ⟨20052366721624667216828611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26736488962166222955771481 20052366721624667216828611)
        ·
          refine ⟨30078550082437000825242917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20052366721624667216828611 30078550082437000825242917)
          ·
            refine ⟨5639728140456937654733047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30078550082437000825242917 5639728140456937654733047)
            ·
              refine ⟨8459592210685406482099571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639728140456937654733047 8459592210685406482099571)
              ·
                refine ⟨12689388316028109723149357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8459592210685406482099571 12689388316028109723149357)
                ·
                  refine ⟨4758520618510541146181009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12689388316028109723149357 4758520618510541146181009)
                  ·
                    refine ⟨3568890463882905859635757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4758520618510541146181009 3568890463882905859635757)
                    ·
                      refine ⟨1338333923956089697363409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3568890463882905859635757 1338333923956089697363409)
                      ·
                        rfl

theorem cell23_2606396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_2606396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606396 prefixEnd_2606396 := by exact prefixLift 2606396
  have htrace : WordTrace (prefixWord ++ tailWord_2606396) baseStart_2606396 baseEnd_2606396 := by
    simpa [prefixWord, tailWord_2606396, baseEnd_2606396] using wordTrace_append hprefix tailTrace_2606396
  have hstable : (prefixWord ++ tailWord_2606396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606396).length < 2 ^ (prefixWord ++ tailWord_2606396).sum := by decide
  have hdescent : baseEnd_2606396 < baseStart_2606396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606409 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 3]
def baseStart_2606409 : Nat := 118140960795 + 2606409 * 2 ^ 59
def prefixEnd_2606409 : Nat := 4983230072969 + 3 ^ 40 * 2606409 * 2
def baseEnd_2606409 : Nat := 1338340599204598146500849

theorem tailTrace_2606409 : CollatzResearch.WordTrace tailWord_2606409 prefixEnd_2606409 1338340599204598146500849 := by
  unfold tailWord_2606409
  simp only [CollatzResearch.WordTrace]
  refine ⟨95063546014432807062966281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63375697342955204708644187 95063546014432807062966281)
  ·
    refine ⟨71297659510824605297224711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95063546014432807062966281 71297659510824605297224711)
    ·
      refine ⟨106946489266236907945837067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71297659510824605297224711 106946489266236907945837067)
      ·
        refine ⟨160419733899355361918755601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106946489266236907945837067 160419733899355361918755601)
        ·
          refine ⟨120314800424516521439066701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160419733899355361918755601 120314800424516521439066701)
          ·
            refine ⟨45118050159193695539650013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120314800424516521439066701 45118050159193695539650013)
            ·
              refine ⟨16919268809697635827368755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45118050159193695539650013 16919268809697635827368755)
              ·
                refine ⟨25378903214546453741053133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16919268809697635827368755 25378903214546453741053133)
                ·
                  refine ⟨9517088705454920152894925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25378903214546453741053133 9517088705454920152894925)
                  ·
                    refine ⟨3568908264545595057335597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9517088705454920152894925 3568908264545595057335597)
                    ·
                      refine ⟨1338340599204598146500849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3568908264545595057335597 1338340599204598146500849)
                      ·
                        rfl

theorem cell23_2606409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_2606409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606409 prefixEnd_2606409 := by exact prefixLift 2606409
  have htrace : WordTrace (prefixWord ++ tailWord_2606409) baseStart_2606409 baseEnd_2606409 := by
    simpa [prefixWord, tailWord_2606409, baseEnd_2606409] using wordTrace_append hprefix tailTrace_2606409
  have hstable : (prefixWord ++ tailWord_2606409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606409).length < 2 ^ (prefixWord ++ tailWord_2606409).sum := by decide
  have hdescent : baseEnd_2606409 < baseStart_2606409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606426 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3]
def baseStart_2606426 : Nat := 118140960795 + 2606426 * 2 ^ 59
def prefixEnd_2606426 : Nat := 4983230072969 + 3 ^ 40 * 2606426 * 2
def baseEnd_2606426 : Nat := 1338349328375724579988271

theorem tailTrace_2606426 : CollatzResearch.WordTrace tailWord_2606426 prefixEnd_2606426 1338349328375724579988271 := by
  unfold tailWord_2606426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23766041513842804741583783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63376110703580812644223421 23766041513842804741583783)
  ·
    refine ⟨35649062270764207112375675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23766041513842804741583783 35649062270764207112375675)
    ·
      refine ⟨53473593406146310668563513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35649062270764207112375675 53473593406146310668563513)
      ·
        refine ⟨40105195054609733001422635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53473593406146310668563513 40105195054609733001422635)
        ·
          refine ⟨60157792581914599502133953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40105195054609733001422635 60157792581914599502133953)
          ·
            refine ⟨45118344436435949626600465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60157792581914599502133953 45118344436435949626600465)
            ·
              refine ⟨33838758327326962219950349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45118344436435949626600465 33838758327326962219950349)
              ·
                refine ⟨12689534372747610832481381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33838758327326962219950349 12689534372747610832481381)
                ·
                  refine ⟨2379287694890177031090259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12689534372747610832481381 2379287694890177031090259)
                  ·
                    refine ⟨3568931542335265546635389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2379287694890177031090259 3568931542335265546635389)
                    ·
                      refine ⟨1338349328375724579988271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3568931542335265546635389 1338349328375724579988271)
                      ·
                        rfl

theorem cell23_2606426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_2606426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606426 prefixEnd_2606426 := by exact prefixLift 2606426
  have htrace : WordTrace (prefixWord ++ tailWord_2606426) baseStart_2606426 baseEnd_2606426 := by
    simpa [prefixWord, tailWord_2606426, baseEnd_2606426] using wordTrace_append hprefix tailTrace_2606426
  have hstable : (prefixWord ++ tailWord_2606426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606426).length < 2 ^ (prefixWord ++ tailWord_2606426).sum := by decide
  have hdescent : baseEnd_2606426 < baseStart_2606426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606469 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_2606469 : Nat := 118140960795 + 2606469 * 2 ^ 59
def prefixEnd_2606469 : Nat := 4983230072969 + 3 ^ 40 * 2606469 * 2
def baseEnd_2606469 : Nat := 1338371408043867911750573

theorem tailTrace_2606469 : CollatzResearch.WordTrace tailWord_2606469 prefixEnd_2606469 1338371408043867911750573 := by
  unfold tailWord_2606469
  simp only [CollatzResearch.WordTrace]
  refine ⟨95065734394215437310150461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63377156262810291540100307 95065734394215437310150461)
  ·
    refine ⟨35649650397830788991306423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95065734394215437310150461 35649650397830788991306423)
    ·
      refine ⟨53474475596746183486959635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35649650397830788991306423 53474475596746183486959635)
      ·
        refine ⟨80211713395119275230439453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53474475596746183486959635 80211713395119275230439453)
        ·
          refine ⟨30079392523169728211414795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80211713395119275230439453 30079392523169728211414795)
          ·
            refine ⟨45119088784754592317122193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30079392523169728211414795 45119088784754592317122193)
            ·
              refine ⟨33839316588565944237841645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45119088784754592317122193 33839316588565944237841645)
              ·
                refine ⟨12689743720712229089190617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33839316588565944237841645 12689743720712229089190617)
                ·
                  refine ⟨9517307790534171816892963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12689743720712229089190617 9517307790534171816892963)
                  ·
                    refine ⟨14275961685801257725339445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9517307790534171816892963 14275961685801257725339445)
                    ·
                      refine ⟨1338371408043867911750573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14275961685801257725339445 1338371408043867911750573)
                      ·
                        rfl

theorem cell23_2606469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_2606469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606469 prefixEnd_2606469 := by exact prefixLift 2606469
  have htrace : WordTrace (prefixWord ++ tailWord_2606469) baseStart_2606469 baseEnd_2606469 := by
    simpa [prefixWord, tailWord_2606469, baseEnd_2606469] using wordTrace_append hprefix tailTrace_2606469
  have hstable : (prefixWord ++ tailWord_2606469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606469).length < 2 ^ (prefixWord ++ tailWord_2606469).sum := by decide
  have hdescent : baseEnd_2606469 < baseStart_2606469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606489 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 7]
def baseStart_2606489 : Nat := 118140960795 + 2606489 * 2 ^ 59
def prefixEnd_2606489 : Nat := 4983230072969 + 3 ^ 40 * 2606489 * 2
def baseEnd_2606489 : Nat := 148709075295217537055609

theorem tailTrace_2606489 : CollatzResearch.WordTrace tailWord_2606489 prefixEnd_2606489 148709075295217537055609 := by
  unfold tailWord_2606489
  simp only [CollatzResearch.WordTrace]
  refine ⟨95066463854142980725878521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63377642569428653817252347 95066463854142980725878521)
  ·
    refine ⟨71299847890607235544408891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95066463854142980725878521 71299847890607235544408891)
    ·
      refine ⟨106949771835910853316613337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71299847890607235544408891 106949771835910853316613337)
      ·
        refine ⟨80212328876933139987460003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106949771835910853316613337 80212328876933139987460003)
        ·
          refine ⟨120318493315399709981190005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80212328876933139987460003 120318493315399709981190005)
          ·
            refine ⟨11279858748318722810736563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120318493315399709981190005 11279858748318722810736563)
            ·
              refine ⟨16919788122478084216104845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11279858748318722810736563 16919788122478084216104845)
              ·
                refine ⟨6344920545929281581039317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16919788122478084216104845 6344920545929281581039317)
                ·
                  refine ⟨148709075295217537055609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6344920545929281581039317 148709075295217537055609)
                  ·
                    rfl

theorem cell23_2606489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 7].length) (baseStart_2606489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606489 prefixEnd_2606489 := by exact prefixLift 2606489
  have htrace : WordTrace (prefixWord ++ tailWord_2606489) baseStart_2606489 baseEnd_2606489 := by
    simpa [prefixWord, tailWord_2606489, baseEnd_2606489] using wordTrace_append hprefix tailTrace_2606489
  have hstable : (prefixWord ++ tailWord_2606489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606489).length < 2 ^ (prefixWord ++ tailWord_2606489).sum := by decide
  have hdescent : baseEnd_2606489 < baseStart_2606489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606494 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2606494 : Nat := 118140960795 + 2606494 * 2 ^ 59
def prefixEnd_2606494 : Nat := 4983230072969 + 3 ^ 40 * 2606494 * 2
def baseEnd_2606494 : Nat := 1338384245060230313937959

theorem tailTrace_2606494 : CollatzResearch.WordTrace tailWord_2606494 prefixEnd_2606494 1338384245060230313937959 := by
  unfold tailWord_2606494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11883330777390608322476317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63377764146083244386540357 11883330777390608322476317)
  ·
    refine ⟨4456249041521478120928619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11883330777390608322476317 4456249041521478120928619)
    ·
      refine ⟨6684373562282217181392929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4456249041521478120928619 6684373562282217181392929)
      ·
        refine ⟨5013280171711662886044697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6684373562282217181392929 5013280171711662886044697)
        ·
          refine ⟨3759960128783747164533523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5013280171711662886044697 3759960128783747164533523)
          ·
            refine ⟨5639940193175620746800285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759960128783747164533523 5639940193175620746800285)
            ·
              refine ⟨2114977572440857780050107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5639940193175620746800285 2114977572440857780050107)
              ·
                refine ⟨3172466358661286670075161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114977572440857780050107 3172466358661286670075161)
                ·
                  refine ⟨2379349768995965002556371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3172466358661286670075161 2379349768995965002556371)
                  ·
                    refine ⟨3569024653493947503834557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2379349768995965002556371 3569024653493947503834557)
                    ·
                      refine ⟨1338384245060230313937959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3569024653493947503834557 1338384245060230313937959)
                      ·
                        rfl

theorem cell23_2606494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2606494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606494 prefixEnd_2606494 := by exact prefixLift 2606494
  have htrace : WordTrace (prefixWord ++ tailWord_2606494) baseStart_2606494 baseEnd_2606494 := by
    simpa [prefixWord, tailWord_2606494, baseEnd_2606494] using wordTrace_append hprefix tailTrace_2606494
  have hstable : (prefixWord ++ tailWord_2606494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606494).length < 2 ^ (prefixWord ++ tailWord_2606494).sum := by decide
  have hdescent : baseEnd_2606494 < baseStart_2606494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606519 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 1, 7]
def baseStart_2606519 : Nat := 118140960795 + 2606519 * 2 ^ 59
def prefixEnd_2606519 : Nat := 4983230072969 + 3 ^ 40 * 2606519 * 2
def baseEnd_2606519 : Nat := 446132360692197572041781

theorem tailTrace_2606519 : CollatzResearch.WordTrace tailWord_2606519 prefixEnd_2606519 446132360692197572041781 := by
  unfold tailWord_2606519
  simp only [CollatzResearch.WordTrace]
  refine ⟨95067558044034295849470611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63378372029356197232980407 95067558044034295849470611)
  ·
    refine ⟨142601337066051443774205917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95067558044034295849470611 142601337066051443774205917)
    ·
      refine ⟨53475501399769291415327219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142601337066051443774205917 53475501399769291415327219)
      ·
        refine ⟨80213252099653937122990829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53475501399769291415327219 80213252099653937122990829)
        ·
          refine ⟨30079969537370226421121561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80213252099653937122990829 30079969537370226421121561)
          ·
            refine ⟨22559977153027669815841171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30079969537370226421121561 22559977153027669815841171)
            ·
              refine ⟨33839965729541504723761757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22559977153027669815841171 33839965729541504723761757)
              ·
                refine ⟨12689987148578064271410659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33839965729541504723761757 12689987148578064271410659)
                ·
                  refine ⟨19034980722867096407115989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12689987148578064271410659 19034980722867096407115989)
                  ·
                    refine ⟨446132360692197572041781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19034980722867096407115989 446132360692197572041781)
                    ·
                      rfl

theorem cell23_2606519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_2606519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606519 prefixEnd_2606519 := by exact prefixLift 2606519
  have htrace : WordTrace (prefixWord ++ tailWord_2606519) baseStart_2606519 baseEnd_2606519 := by
    simpa [prefixWord, tailWord_2606519, baseEnd_2606519] using wordTrace_append hprefix tailTrace_2606519
  have hstable : (prefixWord ++ tailWord_2606519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606519).length < 2 ^ (prefixWord ++ tailWord_2606519).sum := by decide
  have hdescent : baseEnd_2606519 < baseStart_2606519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606536 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 2, 5]
def baseStart_2606536 : Nat := 118140960795 + 2606536 * 2 ^ 59
def prefixEnd_2606536 : Nat := 4983230072969 + 3 ^ 40 * 2606536 * 2
def baseEnd_2606536 : Nat := 446135270415906383204255

theorem tailTrace_2606536 : CollatzResearch.WordTrace tailWord_2606536 prefixEnd_2606536 446135270415906383204255 := by
  unfold tailWord_2606536
  simp only [CollatzResearch.WordTrace]
  refine ⟨47534089042486353876419731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63378785389981805168559641 47534089042486353876419731)
  ·
    refine ⟨71301133563729530814629597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47534089042486353876419731 71301133563729530814629597)
    ·
      refine ⟨26737925086398574055486099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71301133563729530814629597 26737925086398574055486099)
      ·
        refine ⟨40106887629597861083229149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26737925086398574055486099 40106887629597861083229149)
        ·
          refine ⟨15040082861099197906210931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40106887629597861083229149 15040082861099197906210931)
          ·
            refine ⟨22560124291648796859316397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15040082861099197906210931 22560124291648796859316397)
            ·
              refine ⟨8460046609368298822243649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22560124291648796859316397 8460046609368298822243649)
              ·
                refine ⟨6345034957026224116682737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8460046609368298822243649 6345034957026224116682737)
                ·
                  refine ⟨4758776217769668087512053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6345034957026224116682737 4758776217769668087512053)
                  ·
                    refine ⟨446135270415906383204255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4758776217769668087512053 446135270415906383204255)
                    ·
                      rfl

theorem cell23_2606536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_2606536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606536 prefixEnd_2606536 := by exact prefixLift 2606536
  have htrace : WordTrace (prefixWord ++ tailWord_2606536) baseStart_2606536 baseEnd_2606536 := by
    simpa [prefixWord, tailWord_2606536, baseEnd_2606536] using wordTrace_append hprefix tailTrace_2606536
  have hstable : (prefixWord ++ tailWord_2606536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606536).length < 2 ^ (prefixWord ++ tailWord_2606536).sum := by decide
  have hdescent : baseEnd_2606536 < baseStart_2606536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606540 : List Nat := [2, 2, 1, 4, 2, 2, 3, 2, 5]
def baseStart_2606540 : Nat := 118140960795 + 2606540 * 2 ^ 59
def prefixEnd_2606540 : Nat := 4983230072969 + 3 ^ 40 * 2606540 * 2
def baseEnd_2606540 : Nat := 148711985018926348218083

theorem tailTrace_2606540 : CollatzResearch.WordTrace tailWord_2606540 prefixEnd_2606540 148711985018926348218083 := by
  unfold tailWord_2606540
  simp only [CollatzResearch.WordTrace]
  refine ⟨47534161988479108217992537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63378882651305477623990049 47534161988479108217992537)
  ·
    refine ⟨35650621491359331163494403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47534161988479108217992537 35650621491359331163494403)
    ·
      refine ⟨53475932237038996745241605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35650621491359331163494403 53475932237038996745241605)
      ·
        refine ⟨10026737294444811889732801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53475932237038996745241605 10026737294444811889732801)
        ·
          refine ⟨7520052970833608917299601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10026737294444811889732801 7520052970833608917299601)
          ·
            refine ⟨5640039728125206687974701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7520052970833608917299601 5640039728125206687974701)
            ·
              refine ⟨2115014898046952507990513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5640039728125206687974701 2115014898046952507990513)
              ·
                refine ⟨1586261173535214380992885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2115014898046952507990513 1586261173535214380992885)
                ·
                  refine ⟨148711985018926348218083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1586261173535214380992885 148711985018926348218083)
                  ·
                    rfl

theorem cell23_2606540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_2606540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606540 prefixEnd_2606540 := by exact prefixLift 2606540
  have htrace : WordTrace (prefixWord ++ tailWord_2606540) baseStart_2606540 baseEnd_2606540 := by
    simpa [prefixWord, tailWord_2606540, baseEnd_2606540] using wordTrace_append hprefix tailTrace_2606540
  have hstable : (prefixWord ++ tailWord_2606540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606540).length < 2 ^ (prefixWord ++ tailWord_2606540).sum := by decide
  have hdescent : baseEnd_2606540 < baseStart_2606540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606579 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 8]
def baseStart_2606579 : Nat := 118140960795 + 2606579 * 2 ^ 59
def prefixEnd_2606579 : Nat := 4983230072969 + 3 ^ 40 * 2606579 * 2
def baseEnd_2606579 : Nat := 148714210101762497930563

theorem tailTrace_2606579 : CollatzResearch.WordTrace tailWord_2606579 prefixEnd_2606579 148714210101762497930563 := by
  unfold tailWord_2606579
  simp only [CollatzResearch.WordTrace]
  refine ⟨95069746423816926096654791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63379830949211284064436527 95069746423816926096654791)
  ·
    refine ⟨142604619635725389144982187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95069746423816926096654791 142604619635725389144982187)
    ·
      refine ⟨213906929453588083717473281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142604619635725389144982187 213906929453588083717473281)
      ·
        refine ⟨160430197090191062788104961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213906929453588083717473281 160430197090191062788104961)
        ·
          refine ⟨120322647817643297091078721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160430197090191062788104961 120322647817643297091078721)
          ·
            refine ⟨90241985863232472818309041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120322647817643297091078721 90241985863232472818309041)
            ·
              refine ⟨67681489397424354613731781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90241985863232472818309041 67681489397424354613731781)
              ·
                refine ⟨12690279262017066490074709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67681489397424354613731781 12690279262017066490074709)
                ·
                  refine ⟨148714210101762497930563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12690279262017066490074709 148714210101762497930563)
                  ·
                    rfl

theorem cell23_2606579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 8].length) (baseStart_2606579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606579 prefixEnd_2606579 := by exact prefixLift 2606579
  have htrace : WordTrace (prefixWord ++ tailWord_2606579) baseStart_2606579 baseEnd_2606579 := by
    simpa [prefixWord, tailWord_2606579, baseEnd_2606579] using wordTrace_append hprefix tailTrace_2606579
  have hstable : (prefixWord ++ tailWord_2606579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606579).length < 2 ^ (prefixWord ++ tailWord_2606579).sum := by decide
  have hdescent : baseEnd_2606579 < baseStart_2606579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606623 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 3]
def baseStart_2606623 : Nat := 118140960795 + 2606623 * 2 ^ 59
def prefixEnd_2606623 : Nat := 4983230072969 + 3 ^ 40 * 2606623 * 2
def baseEnd_2606623 : Nat := 1338450484064660309224865

theorem tailTrace_2606623 : CollatzResearch.WordTrace tailWord_2606623 prefixEnd_2606623 1338450484064660309224865 := by
  unfold tailWord_2606623
  simp only [CollatzResearch.WordTrace]
  refine ⟨95071351235657521611256523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63380900823771681074171015 95071351235657521611256523)
  ·
    refine ⟨142607026853486282416884785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95071351235657521611256523 142607026853486282416884785)
    ·
      refine ⟨106955270140114711812663589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142607026853486282416884785 106955270140114711812663589)
      ·
        refine ⟨20054113151271508464874423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106955270140114711812663589 20054113151271508464874423)
        ·
          refine ⟨30081169726907262697311635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20054113151271508464874423 30081169726907262697311635)
          ·
            refine ⟨45121754590360894045967453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30081169726907262697311635 45121754590360894045967453)
            ·
              refine ⟨16920657971385335267237795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45121754590360894045967453 16920657971385335267237795)
              ·
                refine ⟨25380986957078002900856693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16920657971385335267237795 25380986957078002900856693)
                ·
                  refine ⟨2379467527226062771955315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25380986957078002900856693 2379467527226062771955315)
                  ·
                    refine ⟨3569201290839094157932973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2379467527226062771955315 3569201290839094157932973)
                    ·
                      refine ⟨1338450484064660309224865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3569201290839094157932973 1338450484064660309224865)
                      ·
                        rfl

theorem cell23_2606623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_2606623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606623 prefixEnd_2606623 := by exact prefixLift 2606623
  have htrace : WordTrace (prefixWord ++ tailWord_2606623) baseStart_2606623 baseEnd_2606623 := by
    simpa [prefixWord, tailWord_2606623, baseEnd_2606623] using wordTrace_append hprefix tailTrace_2606623
  have hstable : (prefixWord ++ tailWord_2606623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606623).length < 2 ^ (prefixWord ++ tailWord_2606623).sum := by decide
  have hdescent : baseEnd_2606623 < baseStart_2606623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606627 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 2, 2, 3]
def baseStart_2606627 : Nat := 118140960795 + 2606627 * 2 ^ 59
def prefixEnd_2606627 : Nat := 4983230072969 + 3 ^ 40 * 2606627 * 2
def baseEnd_2606627 : Nat := 1338452537987278293574847

theorem tailTrace_2606627 : CollatzResearch.WordTrace tailWord_2606627 prefixEnd_2606627 1338452537987278293574847 := by
  unfold tailWord_2606627
  simp only [CollatzResearch.WordTrace]
  refine ⟨95071497127643030294402135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63380998085095353529601423 95071497127643030294402135)
  ·
    refine ⟨142607245691464545441603203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95071497127643030294402135 142607245691464545441603203)
    ·
      refine ⟨213910868537196818162404805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142607245691464545441603203 213910868537196818162404805)
      ·
        refine ⟨40108287850724403405450901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213910868537196818162404805 40108287850724403405450901)
        ·
          refine ⟨1880075993002706409630511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40108287850724403405450901 1880075993002706409630511)
          ·
            refine ⟨2820113989504059614445767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880075993002706409630511 2820113989504059614445767)
            ·
              refine ⟨4230170984256089421668651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820113989504059614445767 4230170984256089421668651)
              ·
                refine ⟨6345256476384134132502977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4230170984256089421668651 6345256476384134132502977)
                ·
                  refine ⟨4758942357288100599377233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6345256476384134132502977 4758942357288100599377233)
                  ·
                    refine ⟨3569206767966075449532925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4758942357288100599377233 3569206767966075449532925)
                    ·
                      refine ⟨1338452537987278293574847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3569206767966075449532925 1338452537987278293574847)
                      ·
                        rfl

theorem cell23_2606627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_2606627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606627 prefixEnd_2606627 := by exact prefixLift 2606627
  have htrace : WordTrace (prefixWord ++ tailWord_2606627) baseStart_2606627 baseEnd_2606627 := by
    simpa [prefixWord, tailWord_2606627, baseEnd_2606627] using wordTrace_append hprefix tailTrace_2606627
  have hstable : (prefixWord ++ tailWord_2606627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606627).length < 2 ^ (prefixWord ++ tailWord_2606627).sum := by decide
  have hdescent : baseEnd_2606627 < baseStart_2606627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606643 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 1, 5]
def baseStart_2606643 : Nat := 118140960795 + 2606643 * 2 ^ 59
def prefixEnd_2606643 : Nat := 4983230072969 + 3 ^ 40 * 2606643 * 2
def baseEnd_2606643 : Nat := 446153584559250076991591

theorem tailTrace_2606643 : CollatzResearch.WordTrace tailWord_2606643 prefixEnd_2606643 446153584559250076991591 := by
  unfold tailWord_2606643
  simp only [CollatzResearch.WordTrace]
  refine ⟨95072080695585065026984583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63381387130390043351323055 95072080695585065026984583)
  ·
    refine ⟨142608121043377597540476875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95072080695585065026984583 142608121043377597540476875)
    ·
      refine ⟨213912181565066396310715313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142608121043377597540476875 213912181565066396310715313)
      ·
        refine ⟨160434136173799797233036485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213912181565066396310715313 160434136173799797233036485)
        ·
          refine ⟨30081400532587461981194341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160434136173799797233036485 30081400532587461981194341)
          ·
            refine ⟨5640262599860149121473939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30081400532587461981194341 5640262599860149121473939)
            ·
              refine ⟨8460393899790223682210909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5640262599860149121473939 8460393899790223682210909)
              ·
                refine ⟨3172647712421333880829091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8460393899790223682210909 3172647712421333880829091)
                ·
                  refine ⟨4758971568632000821243637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172647712421333880829091 4758971568632000821243637)
                  ·
                    refine ⟨446153584559250076991591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4758971568632000821243637 446153584559250076991591)
                    ·
                      rfl

theorem cell23_2606643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 5].length) (baseStart_2606643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606643 prefixEnd_2606643 := by exact prefixLift 2606643
  have htrace : WordTrace (prefixWord ++ tailWord_2606643) baseStart_2606643 baseEnd_2606643 := by
    simpa [prefixWord, tailWord_2606643, baseEnd_2606643] using wordTrace_append hprefix tailTrace_2606643
  have hstable : (prefixWord ++ tailWord_2606643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606643).length < 2 ^ (prefixWord ++ tailWord_2606643).sum := by decide
  have hdescent : baseEnd_2606643 < baseStart_2606643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606657 : List Nat := [1, 2, 5, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_2606657 : Nat := 118140960795 + 2606657 * 2 ^ 59
def prefixEnd_2606657 : Nat := 4983230072969 + 3 ^ 40 * 2606657 * 2
def baseEnd_2606657 : Nat := 1338467942406913176199709

theorem tailTrace_2606657 : CollatzResearch.WordTrace tailWord_2606657 prefixEnd_2606657 1338467942406913176199709 := by
  unfold tailWord_2606657
  simp only [CollatzResearch.WordTrace]
  refine ⟨95072591317534345417994225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63381727545022896945329483 95072591317534345417994225)
  ·
    refine ⟨71304443488150759063495669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95072591317534345417994225 71304443488150759063495669)
    ·
      refine ⟨6684791577014133662202719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71304443488150759063495669 6684791577014133662202719)
      ·
        refine ⟨10027187365521200493304079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6684791577014133662202719 10027187365521200493304079)
        ·
          refine ⟨15040781048281800739956119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10027187365521200493304079 15040781048281800739956119)
          ·
            refine ⟨22561171572422701109934179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15040781048281800739956119 22561171572422701109934179)
            ·
              refine ⟨33841757358634051664901269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22561171572422701109934179 33841757358634051664901269)
              ·
                refine ⟨1586332376185971171792247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33841757358634051664901269 1586332376185971171792247)
                ·
                  refine ⟨2379498564278956757688371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586332376185971171792247 2379498564278956757688371)
                  ·
                    refine ⟨3569247846418435136532557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2379498564278956757688371 3569247846418435136532557)
                    ·
                      refine ⟨1338467942406913176199709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3569247846418435136532557 1338467942406913176199709)
                      ·
                        rfl

theorem cell23_2606657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_2606657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606657 prefixEnd_2606657 := by exact prefixLift 2606657
  have htrace : WordTrace (prefixWord ++ tailWord_2606657) baseStart_2606657 baseEnd_2606657 := by
    simpa [prefixWord, tailWord_2606657, baseEnd_2606657] using wordTrace_append hprefix tailTrace_2606657
  have hstable : (prefixWord ++ tailWord_2606657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606657).length < 2 ^ (prefixWord ++ tailWord_2606657).sum := by decide
  have hdescent : baseEnd_2606657 < baseStart_2606657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606716 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_2606716 : Nat := 118140960795 + 2606716 * 2 ^ 59
def prefixEnd_2606716 : Nat := 4983230072969 + 3 ^ 40 * 2606716 * 2
def baseEnd_2606716 : Nat := 446166079255176148453979

theorem tailTrace_2606716 : CollatzResearch.WordTrace tailWord_2606716 prefixEnd_2606716 446166079255176148453979 := by
  unfold tailWord_2606716
  simp only [CollatzResearch.WordTrace]
  refine ⟨47537371612160299247196001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63383162149547065662928001 47537371612160299247196001)
  ·
    refine ⟨35653028709120224435397001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47537371612160299247196001 35653028709120224435397001)
    ·
      refine ⟨26739771531840168326547751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35653028709120224435397001 26739771531840168326547751)
      ·
        refine ⟨40109657297760252489821627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26739771531840168326547751 40109657297760252489821627)
        ·
          refine ⟨60164485946640378734732441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40109657297760252489821627 60164485946640378734732441)
          ·
            refine ⟨45123364459980284051049331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60164485946640378734732441 45123364459980284051049331)
            ·
              refine ⟨67685046689970426076573997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45123364459980284051049331 67685046689970426076573997)
              ·
                refine ⟨25381892508738909778715249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67685046689970426076573997 25381892508738909778715249)
                ·
                  refine ⟨19036419381554182334036437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25381892508738909778715249 19036419381554182334036437)
                  ·
                    refine ⟨446166079255176148453979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19036419381554182334036437 446166079255176148453979)
                    ·
                      rfl

theorem cell23_2606716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_2606716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606716 prefixEnd_2606716 := by exact prefixLift 2606716
  have htrace : WordTrace (prefixWord ++ tailWord_2606716) baseStart_2606716 baseEnd_2606716 := by
    simpa [prefixWord, tailWord_2606716, baseEnd_2606716] using wordTrace_append hprefix tailTrace_2606716
  have hstable : (prefixWord ++ tailWord_2606716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606716).length < 2 ^ (prefixWord ++ tailWord_2606716).sum := by decide
  have hdescent : baseEnd_2606716 < baseStart_2606716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606723 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 2, 7, 2]
def baseStart_2606723 : Nat := 118140960795 + 2606723 * 2 ^ 59
def prefixEnd_2606723 : Nat := 4983230072969 + 3 ^ 40 * 2606723 * 2
def baseEnd_2606723 : Nat := 1338501832130109917974405

theorem tailTrace_2606723 : CollatzResearch.WordTrace tailWord_2606723 prefixEnd_2606723 1338501832130109917974405 := by
  unfold tailWord_2606723
  simp only [CollatzResearch.WordTrace]
  refine ⟨95074998535295238689896823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63383332356863492459931215 95074998535295238689896823)
  ·
    refine ⟨142612497802942858034845235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95074998535295238689896823 142612497802942858034845235)
    ·
      refine ⟨213918746704414287052267853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142612497802942858034845235 213918746704414287052267853)
      ·
        refine ⟨80219530014155357644600445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213918746704414287052267853 80219530014155357644600445)
        ·
          refine ⟨30082323755308259116725167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80219530014155357644600445 30082323755308259116725167)
          ·
            refine ⟨45123485632962388675087751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30082323755308259116725167 45123485632962388675087751)
            ·
              refine ⟨67685228449443583012631627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45123485632962388675087751 67685228449443583012631627)
              ·
                refine ⟨101527842674165374518947441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67685228449443583012631627 101527842674165374518947441)
                ·
                  refine ⟨76145882005624030889210581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101527842674165374518947441 76145882005624030889210581)
                  ·
                    refine ⟨1784669109506813223965873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 76145882005624030889210581 1784669109506813223965873)
                    ·
                      refine ⟨1338501832130109917974405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784669109506813223965873 1338501832130109917974405)
                      ·
                        rfl

theorem cell23_2606723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_2606723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606723 prefixEnd_2606723 := by exact prefixLift 2606723
  have htrace : WordTrace (prefixWord ++ tailWord_2606723) baseStart_2606723 baseEnd_2606723 := by
    simpa [prefixWord, tailWord_2606723, baseEnd_2606723] using wordTrace_append hprefix tailTrace_2606723
  have hstable : (prefixWord ++ tailWord_2606723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606723).length < 2 ^ (prefixWord ++ tailWord_2606723).sum := by decide
  have hdescent : baseEnd_2606723 < baseStart_2606723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606724 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_2606724 : Nat := 118140960795 + 2606724 * 2 ^ 59
def prefixEnd_2606724 : Nat := 4983230072969 + 3 ^ 40 * 2606724 * 2
def baseEnd_2606724 : Nat := 446167448536921471353967

theorem tailTrace_2606724 : CollatzResearch.WordTrace tailWord_2606724 prefixEnd_2606724 446167448536921471353967 := by
  unfold tailWord_2606724
  simp only [CollatzResearch.WordTrace]
  refine ⟨47537517504145807930341613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63383356672194410573788817 47537517504145807930341613)
  ·
    refine ⟨17826569064054677973878105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47537517504145807930341613 17826569064054677973878105)
    ·
      refine ⟨13369926798041008480408579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17826569064054677973878105 13369926798041008480408579)
      ·
        refine ⟨20054890197061512720612869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13369926798041008480408579 20054890197061512720612869)
        ·
          refine ⟨3760291911949033635114913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20054890197061512720612869 3760291911949033635114913)
          ·
            refine ⟨2820218933961775226336185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3760291911949033635114913 2820218933961775226336185)
            ·
              refine ⟨2115164200471331419752139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2820218933961775226336185 2115164200471331419752139)
              ·
                refine ⟨3172746300706997129628209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115164200471331419752139 3172746300706997129628209)
                ·
                  refine ⟨2379559725530247847221157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3172746300706997129628209 2379559725530247847221157)
                  ·
                    refine ⟨446167448536921471353967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2379559725530247847221157 446167448536921471353967)
                    ·
                      rfl

theorem cell23_2606724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_2606724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606724 prefixEnd_2606724 := by exact prefixLift 2606724
  have htrace : WordTrace (prefixWord ++ tailWord_2606724) baseStart_2606724 baseEnd_2606724 := by
    simpa [prefixWord, tailWord_2606724, baseEnd_2606724] using wordTrace_append hprefix tailTrace_2606724
  have hstable : (prefixWord ++ tailWord_2606724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606724).length < 2 ^ (prefixWord ++ tailWord_2606724).sum := by decide
  have hdescent : baseEnd_2606724 < baseStart_2606724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606774 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_2606774 : Nat := 118140960795 + 2606774 * 2 ^ 59
def prefixEnd_2606774 : Nat := 4983230072969 + 3 ^ 40 * 2606774 * 2
def baseEnd_2606774 : Nat := 1338528019643489218436671

theorem tailTrace_2606774 : CollatzResearch.WordTrace tailWord_2606774 prefixEnd_2606774 1338528019643489218436671 := by
  unfold tailWord_2606774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5942303666131904650000211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63384572438740316266668917 5942303666131904650000211)
  ·
    refine ⟨8913455499197856975000317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5942303666131904650000211 8913455499197856975000317)
    ·
      refine ⟨3342545812199196365625119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8913455499197856975000317 3342545812199196365625119)
      ·
        refine ⟨5013818718298794548437679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342545812199196365625119 5013818718298794548437679)
        ·
          refine ⟨7520728077448191822656519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5013818718298794548437679 7520728077448191822656519)
          ·
            refine ⟨11281092116172287733984779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7520728077448191822656519 11281092116172287733984779)
            ·
              refine ⟨16921638174258431600977169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11281092116172287733984779 16921638174258431600977169)
              ·
                refine ⟨12691228630693823700732877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16921638174258431600977169 12691228630693823700732877)
                ·
                  refine ⟨4759210736510183887774829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12691228630693823700732877 4759210736510183887774829)
                  ·
                    refine ⟨1784704026191318957915561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4759210736510183887774829 1784704026191318957915561)
                    ·
                      refine ⟨1338528019643489218436671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784704026191318957915561 1338528019643489218436671)
                      ·
                        rfl

theorem cell23_2606774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_2606774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606774 prefixEnd_2606774 := by exact prefixLift 2606774
  have htrace : WordTrace (prefixWord ++ tailWord_2606774) baseStart_2606774 baseEnd_2606774 := by
    simpa [prefixWord, tailWord_2606774, baseEnd_2606774] using wordTrace_append hprefix tailTrace_2606774
  have hstable : (prefixWord ++ tailWord_2606774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606774).length < 2 ^ (prefixWord ++ tailWord_2606774).sum := by decide
  have hdescent : baseEnd_2606774 < baseStart_2606774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606776 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 11]
def baseStart_2606776 : Nat := 118140960795 + 2606776 * 2 ^ 59
def prefixEnd_2606776 : Nat := 4983230072969 + 3 ^ 40 * 2606776 * 2
def baseEnd_2606776 : Nat := 148725449622755356734629

theorem tailTrace_2606776 : CollatzResearch.WordTrace tailWord_2606776 prefixEnd_2606776 148725449622755356734629 := by
  unfold tailWord_2606776
  simp only [CollatzResearch.WordTrace]
  refine ⟨47538465802051614370788091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63384621069402152494384121 47538465802051614370788091)
  ·
    refine ⟨71307698703077421556182137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47538465802051614370788091 71307698703077421556182137)
    ·
      refine ⟨53480774027308066167136603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71307698703077421556182137 53480774027308066167136603)
      ·
        refine ⟨80221161040962099250704905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53480774027308066167136603 80221161040962099250704905)
        ·
          refine ⟨60165870780721574438028679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80221161040962099250704905 60165870780721574438028679)
          ·
            refine ⟨90248806171082361657043019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60165870780721574438028679 90248806171082361657043019)
            ·
              refine ⟨135373209256623542485564529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90248806171082361657043019 135373209256623542485564529)
              ·
                refine ⟨101529906942467656864173397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135373209256623542485564529 101529906942467656864173397)
                ·
                  refine ⟨148725449622755356734629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 101529906942467656864173397 148725449622755356734629)
                  ·
                    rfl

theorem cell23_2606776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 11].length) (baseStart_2606776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606776 prefixEnd_2606776 := by exact prefixLift 2606776
  have htrace : WordTrace (prefixWord ++ tailWord_2606776) baseStart_2606776 baseEnd_2606776 := by
    simpa [prefixWord, tailWord_2606776, baseEnd_2606776] using wordTrace_append hprefix tailTrace_2606776
  have hstable : (prefixWord ++ tailWord_2606776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606776).length < 2 ^ (prefixWord ++ tailWord_2606776).sum := by decide
  have hdescent : baseEnd_2606776 < baseStart_2606776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606783 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_2606783 : Nat := 118140960795 + 2606783 * 2 ^ 59
def prefixEnd_2606783 : Nat := 4983230072969 + 3 ^ 40 * 2606783 * 2
def baseEnd_2606783 : Nat := 1338532640969379683224129

theorem tailTrace_2606783 : CollatzResearch.WordTrace tailWord_2606783 prefixEnd_2606783 1338532640969379683224129 := by
  unfold tailWord_2606783
  simp only [CollatzResearch.WordTrace]
  refine ⟨95077186915077868937081003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63384791276718579291387335 95077186915077868937081003)
  ·
    refine ⟨142615780372616803405621505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95077186915077868937081003 142615780372616803405621505)
    ·
      refine ⟨106961835279462602554216129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142615780372616803405621505 106961835279462602554216129)
      ·
        refine ⟨80221376459596951915662097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106961835279462602554216129 80221376459596951915662097)
        ·
          refine ⟨60166032344697713936746573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80221376459596951915662097 60166032344697713936746573)
          ·
            refine ⟨22562262129261642726279965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60166032344697713936746573 22562262129261642726279965)
            ·
              refine ⟨8460848298473116022354987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22562262129261642726279965 8460848298473116022354987)
              ·
                refine ⟨12691272447709674033532481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8460848298473116022354987 12691272447709674033532481)
                ·
                  refine ⟨9518454335782255525149361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12691272447709674033532481 9518454335782255525149361)
                  ·
                    refine ⟨7138840751836691643862021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9518454335782255525149361 7138840751836691643862021)
                    ·
                      refine ⟨1338532640969379683224129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7138840751836691643862021 1338532640969379683224129)
                      ·
                        rfl

theorem cell23_2606783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_2606783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606783 prefixEnd_2606783 := by exact prefixLift 2606783
  have htrace : WordTrace (prefixWord ++ tailWord_2606783) baseStart_2606783 baseEnd_2606783 := by
    simpa [prefixWord, tailWord_2606783, baseEnd_2606783] using wordTrace_append hprefix tailTrace_2606783
  have hstable : (prefixWord ++ tailWord_2606783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606783).length < 2 ^ (prefixWord ++ tailWord_2606783).sum := by decide
  have hdescent : baseEnd_2606783 < baseStart_2606783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606810 : List Nat := [3, 1, 1, 2, 2, 3, 1, 5, 5]
def baseStart_2606810 : Nat := 118140960795 + 2606810 * 2 ^ 59
def prefixEnd_2606810 : Nat := 4983230072969 + 3 ^ 40 * 2606810 * 2
def baseEnd_2606810 : Nat := 148727389438561230842945

theorem tailTrace_2606810 : CollatzResearch.WordTrace tailWord_2606810 prefixEnd_2606810 148727389438561230842945 := by
  unfold tailWord_2606810
  simp only [CollatzResearch.WordTrace]
  refine ⟨23769542921495013137078471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63385447790653368365542589 23769542921495013137078471)
  ·
    refine ⟨35654314382242519705617707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23769542921495013137078471 35654314382242519705617707)
    ·
      refine ⟨53481471573363779558426561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35654314382242519705617707 53481471573363779558426561)
      ·
        refine ⟨40111103680022834668819921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53481471573363779558426561 40111103680022834668819921)
        ·
          refine ⟨30083327760017126001614941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40111103680022834668819921 30083327760017126001614941)
          ·
            refine ⟨11281247910006422250605603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30083327760017126001614941 11281247910006422250605603)
            ·
              refine ⟨16921871865009633375908405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11281247910006422250605603 16921871865009633375908405)
              ·
                refine ⟨1586425487344653128991413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16921871865009633375908405 1586425487344653128991413)
                ·
                  refine ⟨148727389438561230842945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1586425487344653128991413 148727389438561230842945)
                  ·
                    rfl

theorem cell23_2606810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_2606810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606810 prefixEnd_2606810 := by exact prefixLift 2606810
  have htrace : WordTrace (prefixWord ++ tailWord_2606810) baseStart_2606810 baseEnd_2606810 := by
    simpa [prefixWord, tailWord_2606810, baseEnd_2606810] using wordTrace_append hprefix tailTrace_2606810
  have hstable : (prefixWord ++ tailWord_2606810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606810).length < 2 ^ (prefixWord ++ tailWord_2606810).sum := by decide
  have hdescent : baseEnd_2606810 < baseStart_2606810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606843 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 4]
def baseStart_2606843 : Nat := 118140960795 + 2606843 * 2 ^ 59
def prefixEnd_2606843 : Nat := 4983230072969 + 3 ^ 40 * 2606843 * 2
def baseEnd_2606843 : Nat := 1338563449808649448473853

theorem tailTrace_2606843 : CollatzResearch.WordTrace tailWord_2606843 prefixEnd_2606843 1338563449808649448473853 := by
  unfold tailWord_2606843
  simp only [CollatzResearch.WordTrace]
  refine ⟨95079375294860499184265183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63386250196573666122843455 95079375294860499184265183)
  ·
    refine ⟨142619062942290748776397775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95079375294860499184265183 142619062942290748776397775)
    ·
      refine ⟨213928594413436123164596663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142619062942290748776397775 213928594413436123164596663)
      ·
        refine ⟨320892891620154184746894995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213928594413436123164596663 320892891620154184746894995)
        ·
          refine ⟨481339337430231277120342493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320892891620154184746894995 481339337430231277120342493)
          ·
            refine ⟨180502251536336728920128435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 481339337430231277120342493 180502251536336728920128435)
            ·
              refine ⟨270753377304505093380192653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180502251536336728920128435 270753377304505093380192653)
              ·
                refine ⟨101532516489189410017572245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270753377304505093380192653 101532516489189410017572245)
                ·
                  refine ⟨4759336710430753594573699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101532516489189410017572245 4759336710430753594573699)
                  ·
                    refine ⟨7139005065646130391860549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4759336710430753594573699 7139005065646130391860549)
                    ·
                      refine ⟨1338563449808649448473853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7139005065646130391860549 1338563449808649448473853)
                      ·
                        rfl

theorem cell23_2606843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 4].length) (baseStart_2606843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606843 prefixEnd_2606843 := by exact prefixLift 2606843
  have htrace : WordTrace (prefixWord ++ tailWord_2606843) baseStart_2606843 baseEnd_2606843 := by
    simpa [prefixWord, tailWord_2606843, baseEnd_2606843] using wordTrace_append hprefix tailTrace_2606843
  have hstable : (prefixWord ++ tailWord_2606843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606843).length < 2 ^ (prefixWord ++ tailWord_2606843).sum := by decide
  have hdescent : baseEnd_2606843 < baseStart_2606843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606860 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 1, 6, 2]
def baseStart_2606860 : Nat := 118140960795 + 2606860 * 2 ^ 59
def prefixEnd_2606860 : Nat := 4983230072969 + 3 ^ 40 * 2606860 * 2
def baseEnd_2606860 : Nat := 1338572178979775881961275

theorem tailTrace_2606860 : CollatzResearch.WordTrace tailWord_2606860 prefixEnd_2606860 1338572178979775881961275 := by
  unfold tailWord_2606860
  simp only [CollatzResearch.WordTrace]
  refine ⟨47539997667899455543817017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63386663557199274058422689 47539997667899455543817017)
  ·
    refine ⟨35654998250924591657862763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47539997667899455543817017 35654998250924591657862763)
    ·
      refine ⟨53482497376386887486794145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35654998250924591657862763 53482497376386887486794145)
      ·
        refine ⟨40111873032290165615095609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53482497376386887486794145 40111873032290165615095609)
        ·
          refine ⟨30083904774217624211321707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40111873032290165615095609 30083904774217624211321707)
          ·
            refine ⟨45125857161326436316982561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30083904774217624211321707 45125857161326436316982561)
            ·
              refine ⟨33844392870994827237736921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45125857161326436316982561 33844392870994827237736921)
              ·
                refine ⟨25383294653246120428302691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33844392870994827237736921 25383294653246120428302691)
                ·
                  refine ⟨38074941979869180642454037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25383294653246120428302691 38074941979869180642454037)
                  ·
                    refine ⟨1784762905306367842615033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38074941979869180642454037 1784762905306367842615033)
                    ·
                      refine ⟨1338572178979775881961275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784762905306367842615033 1338572178979775881961275)
                      ·
                        rfl

theorem cell23_2606860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_2606860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606860 prefixEnd_2606860 := by exact prefixLift 2606860
  have htrace : WordTrace (prefixWord ++ tailWord_2606860) baseStart_2606860 baseEnd_2606860 := by
    simpa [prefixWord, tailWord_2606860, baseEnd_2606860] using wordTrace_append hprefix tailTrace_2606860
  have hstable : (prefixWord ++ tailWord_2606860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606860).length < 2 ^ (prefixWord ++ tailWord_2606860).sum := by decide
  have hdescent : baseEnd_2606860 < baseStart_2606860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606878 : List Nat := [4, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2606878 : Nat := 118140960795 + 2606878 * 2 ^ 59
def prefixEnd_2606878 : Nat := 4983230072969 + 3 ^ 40 * 2606878 * 2
def baseEnd_2606878 : Nat := 148731269070172979059577

theorem tailTrace_2606878 : CollatzResearch.WordTrace tailWord_2606878 prefixEnd_2606878 148731269070172979059577 := by
  unfold tailWord_2606878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11885081481216712520223661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63387101233155800107859525 11885081481216712520223661)
  ·
    refine ⟨4456905555456267195083873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11885081481216712520223661 4456905555456267195083873)
    ·
      refine ⟨3342679166592200396312905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4456905555456267195083873 3342679166592200396312905)
      ·
        refine ⟨2507009374944150297234679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3342679166592200396312905 2507009374944150297234679)
        ·
          refine ⟨3760514062416225445852019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507009374944150297234679 3760514062416225445852019)
          ·
            refine ⟨5640771093624338168778029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760514062416225445852019 5640771093624338168778029)
            ·
              refine ⟨2115289160109126813291761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5640771093624338168778029 2115289160109126813291761)
              ·
                refine ⟨1586466870081845109968821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2115289160109126813291761 1586466870081845109968821)
                ·
                  refine ⟨148731269070172979059577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1586466870081845109968821 148731269070172979059577)
                  ·
                    rfl

theorem cell23_2606878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2606878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606878 prefixEnd_2606878 := by exact prefixLift 2606878
  have htrace : WordTrace (prefixWord ++ tailWord_2606878) baseStart_2606878 baseEnd_2606878 := by
    simpa [prefixWord, tailWord_2606878, baseEnd_2606878] using wordTrace_append hprefix tailTrace_2606878
  have hstable : (prefixWord ++ tailWord_2606878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606878).length < 2 ^ (prefixWord ++ tailWord_2606878).sum := by decide
  have hdescent : baseEnd_2606878 < baseStart_2606878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606883 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 8]
def baseStart_2606883 : Nat := 118140960795 + 2606883 * 2 ^ 59
def prefixEnd_2606883 : Nat := 4983230072969 + 3 ^ 40 * 2606883 * 2
def baseEnd_2606883 : Nat := 148731554337203254663741

theorem tailTrace_2606883 : CollatzResearch.WordTrace tailWord_2606883 prefixEnd_2606883 148731554337203254663741 := by
  unfold tailWord_2606883
  simp only [CollatzResearch.WordTrace]
  refine ⟨95080834214715586015721303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63387222809810390677147535 95080834214715586015721303)
  ·
    refine ⟨142621251322073379023581955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95080834214715586015721303 142621251322073379023581955)
    ·
      refine ⟨213931876983110068535372933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142621251322073379023581955 213931876983110068535372933)
      ·
        refine ⟨40112226934333137850382425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213931876983110068535372933 40112226934333137850382425)
        ·
          refine ⟨30084170200749853387786819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40112226934333137850382425 30084170200749853387786819)
          ·
            refine ⟨45126255301124780081680229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30084170200749853387786819 45126255301124780081680229)
            ·
              refine ⟨8461172868960896265315043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45126255301124780081680229 8461172868960896265315043)
              ·
                refine ⟨12691759303441344397972565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8461172868960896265315043 12691759303441344397972565)
                ·
                  refine ⟨148731554337203254663741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12691759303441344397972565 148731554337203254663741)
                  ·
                    rfl

theorem cell23_2606883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 8].length) (baseStart_2606883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606883 prefixEnd_2606883 := by exact prefixLift 2606883
  have htrace : WordTrace (prefixWord ++ tailWord_2606883) baseStart_2606883 baseEnd_2606883 := by
    simpa [prefixWord, tailWord_2606883, baseEnd_2606883] using wordTrace_append hprefix tailTrace_2606883
  have hstable : (prefixWord ++ tailWord_2606883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606883).length < 2 ^ (prefixWord ++ tailWord_2606883).sum := by decide
  have hdescent : baseEnd_2606883 < baseStart_2606883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606937 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 2, 3, 2]
def baseStart_2606937 : Nat := 118140960795 + 2606937 * 2 ^ 59
def prefixEnd_2606937 : Nat := 4983230072969 + 3 ^ 40 * 2606937 * 2
def baseEnd_2606937 : Nat := 1338611716990172080698421

theorem tailTrace_2606937 : CollatzResearch.WordTrace tailWord_2606937 prefixEnd_2606937 1338611716990172080698421 := by
  unfold tailWord_2606937
  simp only [CollatzResearch.WordTrace]
  refine ⟨95082803756519953238187065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63388535837679968825458043 95082803756519953238187065)
  ·
    refine ⟨71312102817389964928640299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95082803756519953238187065 71312102817389964928640299)
    ·
      refine ⟨106968154226084947392960449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71312102817389964928640299 106968154226084947392960449)
      ·
        refine ⟨80226115669563710544720337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106968154226084947392960449 80226115669563710544720337)
        ·
          refine ⟨60169586752172782908540253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80226115669563710544720337 60169586752172782908540253)
          ·
            refine ⟨22563595032064793590702595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60169586752172782908540253 22563595032064793590702595)
            ·
              refine ⟨33845392548097190386053893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22563595032064793590702595 33845392548097190386053893)
              ·
                refine ⟨6346011102768223197385105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33845392548097190386053893 6346011102768223197385105)
                ·
                  refine ⟨4759508327076167398038829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6346011102768223197385105 4759508327076167398038829)
                  ·
                    refine ⟨1784815622653562774264561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4759508327076167398038829 1784815622653562774264561)
                    ·
                      refine ⟨1338611716990172080698421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784815622653562774264561 1338611716990172080698421)
                      ·
                        rfl

theorem cell23_2606937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_2606937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606937 prefixEnd_2606937 := by exact prefixLift 2606937
  have htrace : WordTrace (prefixWord ++ tailWord_2606937) baseStart_2606937 baseEnd_2606937 := by
    simpa [prefixWord, tailWord_2606937, baseEnd_2606937] using wordTrace_append hprefix tailTrace_2606937
  have hstable : (prefixWord ++ tailWord_2606937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606937).length < 2 ^ (prefixWord ++ tailWord_2606937).sum := by decide
  have hdescent : baseEnd_2606937 < baseStart_2606937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606960 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 6, 4]
def baseStart_2606960 : Nat := 118140960795 + 2606960 * 2 ^ 59
def prefixEnd_2606960 : Nat := 4983230072969 + 3 ^ 40 * 2606960 * 2
def baseEnd_2606960 : Nat := 446207842348408496903605

theorem tailTrace_2606960 : CollatzResearch.WordTrace tailWord_2606960 prefixEnd_2606960 446207842348408496903605 := by
  unfold tailWord_2606960
  simp only [CollatzResearch.WordTrace]
  refine ⟨47541821317718314083137167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63389095090291085444182889 47541821317718314083137167)
  ·
    refine ⟨71312731976577471124705751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47541821317718314083137167 71312731976577471124705751)
    ·
      refine ⟨106969097964866206687058627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71312731976577471124705751 106969097964866206687058627)
      ·
        refine ⟨160453646947299310030587941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106969097964866206687058627 160453646947299310030587941)
        ·
          refine ⟨30085058802618620630735239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160453646947299310030587941 30085058802618620630735239)
          ·
            refine ⟨45127588203927930946102859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30085058802618620630735239 45127588203927930946102859)
            ·
              refine ⟨67691382305891896419154289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45127588203927930946102859 67691382305891896419154289)
              ·
                refine ⟨50768536729418922314365717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67691382305891896419154289 50768536729418922314365717)
                ·
                  refine ⟨2379775159191511983485893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50768536729418922314365717 2379775159191511983485893)
                  ·
                    refine ⟨446207842348408496903605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2379775159191511983485893 446207842348408496903605)
                    ·
                      rfl

theorem cell23_2606960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 4].length) (baseStart_2606960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606960 prefixEnd_2606960 := by exact prefixLift 2606960
  have htrace : WordTrace (prefixWord ++ tailWord_2606960) baseStart_2606960 baseEnd_2606960 := by
    simpa [prefixWord, tailWord_2606960, baseEnd_2606960] using wordTrace_append hprefix tailTrace_2606960
  have hstable : (prefixWord ++ tailWord_2606960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606960).length < 2 ^ (prefixWord ++ tailWord_2606960).sum := by decide
  have hdescent : baseEnd_2606960 < baseStart_2606960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606984 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2606984 : Nat := 118140960795 + 2606984 * 2 ^ 59
def prefixEnd_2606984 : Nat := 4983230072969 + 3 ^ 40 * 2606984 * 2
def baseEnd_2606984 : Nat := 1338635850580933396810705

theorem tailTrace_2606984 : CollatzResearch.WordTrace tailWord_2606984 prefixEnd_2606984 1338635850580933396810705 := by
  unfold tailWord_2606984
  simp only [CollatzResearch.WordTrace]
  refine ⟨47542258993674840132574003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63389678658233120176765337 47542258993674840132574003)
  ·
    refine ⟨71313388490512260198861005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47542258993674840132574003 71313388490512260198861005)
    ·
      refine ⟨26742520683942097574572877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71313388490512260198861005 26742520683942097574572877)
      ·
        refine ⟨10028445256478286590464829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26742520683942097574572877 10028445256478286590464829)
        ·
          refine ⟨3760666971179357471424311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10028445256478286590464829 3760666971179357471424311)
          ·
            refine ⟨5641000456769036207136467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760666971179357471424311 5641000456769036207136467)
            ·
              refine ⟨8461500685153554310704701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641000456769036207136467 8461500685153554310704701)
              ·
                refine ⟨3173062756932582866514263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8461500685153554310704701 3173062756932582866514263)
                ·
                  refine ⟨4759594135398874299771395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173062756932582866514263 4759594135398874299771395)
                  ·
                    refine ⟨7139391203098311449657093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4759594135398874299771395 7139391203098311449657093)
                    ·
                      refine ⟨1338635850580933396810705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7139391203098311449657093 1338635850580933396810705)
                      ·
                        rfl

theorem cell23_2606984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2606984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606984 prefixEnd_2606984 := by exact prefixLift 2606984
  have htrace : WordTrace (prefixWord ++ tailWord_2606984) baseStart_2606984 baseEnd_2606984 := by
    simpa [prefixWord, tailWord_2606984, baseEnd_2606984] using wordTrace_append hprefix tailTrace_2606984
  have hstable : (prefixWord ++ tailWord_2606984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606984).length < 2 ^ (prefixWord ++ tailWord_2606984).sum := by decide
  have hdescent : baseEnd_2606984 < baseStart_2606984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606994 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2606994 : Nat := 118140960795 + 2606994 * 2 ^ 59
def prefixEnd_2606994 : Nat := 4983230072969 + 3 ^ 40 * 2606994 * 2
def baseEnd_2606994 : Nat := 446213661795826119228553

theorem tailTrace_2606994 : CollatzResearch.WordTrace tailWord_2606994 prefixEnd_2606994 446213661795826119228553 := by
  unfold tailWord_2606994
  simp only [CollatzResearch.WordTrace]
  refine ⟨23771220679328362993253009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63389921811542301315341357 23771220679328362993253009)
  ·
    refine ⟨17828415509496272244939757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23771220679328362993253009 17828415509496272244939757)
    ·
      refine ⟨6685655816061102091852409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17828415509496272244939757 6685655816061102091852409)
      ·
        refine ⟨5014241862045826568889307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6685655816061102091852409 5014241862045826568889307)
        ·
          refine ⟨7521362793068739853333961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5014241862045826568889307 7521362793068739853333961)
          ·
            refine ⟨5641022094801554890000471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7521362793068739853333961 5641022094801554890000471)
            ·
              refine ⟨8461533142202332335000707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641022094801554890000471 8461533142202332335000707)
              ·
                refine ⟨12692299713303498502501061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8461533142202332335000707 12692299713303498502501061)
                ·
                  refine ⟨2379806196244405969218949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12692299713303498502501061 2379806196244405969218949)
                  ·
                    refine ⟨446213661795826119228553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2379806196244405969218949 446213661795826119228553)
                    ·
                      rfl

theorem cell23_2606994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2606994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2606994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2606994 prefixEnd_2606994 := by exact prefixLift 2606994
  have htrace : WordTrace (prefixWord ++ tailWord_2606994) baseStart_2606994 baseEnd_2606994 := by
    simpa [prefixWord, tailWord_2606994, baseEnd_2606994] using wordTrace_append hprefix tailTrace_2606994
  have hstable : (prefixWord ++ tailWord_2606994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606994).length < 2 ^ (prefixWord ++ tailWord_2606994).sum := by decide
  have hdescent : baseEnd_2606994 < baseStart_2606994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607001 : List Nat := [1, 2, 1, 2, 1, 3, 4, 4, 1, 2, 2]
def baseStart_2607001 : Nat := 118140960795 + 2607001 * 2 ^ 59
def prefixEnd_2607001 : Nat := 4983230072969 + 3 ^ 40 * 2607001 * 2
def baseEnd_2607001 : Nat := 1338644579752059830298127

theorem tailTrace_2607001 : CollatzResearch.WordTrace tailWord_2607001 prefixEnd_2607001 1338644579752059830298127 := by
  unfold tailWord_2607001
  simp only [CollatzResearch.WordTrace]
  refine ⟨95085138028288092168516857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63390092018858728112344571 95085138028288092168516857)
  ·
    refine ⟨71313853521216069126387643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95085138028288092168516857 71313853521216069126387643)
    ·
      refine ⟨106970780281824103689581465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71313853521216069126387643 106970780281824103689581465)
      ·
        refine ⟨80228085211368077767186099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106970780281824103689581465 80228085211368077767186099)
        ·
          refine ⟨120342127817052116650779149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80228085211368077767186099 120342127817052116650779149)
          ·
            refine ⟨45128297931394543744042181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120342127817052116650779149 45128297931394543744042181)
            ·
              refine ⟨8461555862136476952007909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45128297931394543744042181 8461555862136476952007909)
              ·
                refine ⟨1586541724150589428501483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8461555862136476952007909 1586541724150589428501483)
                ·
                  refine ⟨2379812586225884142752225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586541724150589428501483 2379812586225884142752225)
                  ·
                    refine ⟨1784859439669413107064169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2379812586225884142752225 1784859439669413107064169)
                    ·
                      refine ⟨1338644579752059830298127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784859439669413107064169 1338644579752059830298127)
                      ·
                        rfl

theorem cell23_2607001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 2, 2].length) (baseStart_2607001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607001 prefixEnd_2607001 := by exact prefixLift 2607001
  have htrace : WordTrace (prefixWord ++ tailWord_2607001) baseStart_2607001 baseEnd_2607001 := by
    simpa [prefixWord, tailWord_2607001, baseEnd_2607001] using wordTrace_append hprefix tailTrace_2607001
  have hstable : (prefixWord ++ tailWord_2607001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607001).length < 2 ^ (prefixWord ++ tailWord_2607001).sum := by decide
  have hdescent : baseEnd_2607001 < baseStart_2607001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607050 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_2607050 : Nat := 118140960795 + 2607050 * 2 ^ 59
def prefixEnd_2607050 : Nat := 4983230072969 + 3 ^ 40 * 2607050 * 2
def baseEnd_2607050 : Nat := 446223246768043379528467

theorem tailTrace_2607050 : CollatzResearch.WordTrace tailWord_2607050 prefixEnd_2607050 446223246768043379528467 := by
  unfold tailWord_2607050
  simp only [CollatzResearch.WordTrace]
  refine ⟨23771731301277643384262651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63391283470073715691367069 23771731301277643384262651)
  ·
    refine ⟨35657596951916465076393977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23771731301277643384262651 35657596951916465076393977)
    ·
      refine ⟨26743197713937348807295483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35657596951916465076393977 26743197713937348807295483)
      ·
        refine ⟨40114796570906023210943225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26743197713937348807295483 40114796570906023210943225)
        ·
          refine ⟨30086097428179517408207419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40114796570906023210943225 30086097428179517408207419)
          ·
            refine ⟨45129146142269276112311129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30086097428179517408207419 45129146142269276112311129)
            ·
              refine ⟨33846859606701957084233347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45129146142269276112311129 33846859606701957084233347)
              ·
                refine ⟨50770289410052935626350021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33846859606701957084233347 50770289410052935626350021)
                ·
                  refine ⟨9519429264384925429940629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50770289410052935626350021 9519429264384925429940629)
                  ·
                    refine ⟨446223246768043379528467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9519429264384925429940629 446223246768043379528467)
                    ·
                      rfl

theorem cell23_2607050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_2607050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607050 prefixEnd_2607050 := by exact prefixLift 2607050
  have htrace : WordTrace (prefixWord ++ tailWord_2607050) baseStart_2607050 baseEnd_2607050 := by
    simpa [prefixWord, tailWord_2607050, baseEnd_2607050] using wordTrace_append hprefix tailTrace_2607050
  have hstable : (prefixWord ++ tailWord_2607050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607050).length < 2 ^ (prefixWord ++ tailWord_2607050).sum := by decide
  have hdescent : baseEnd_2607050 < baseStart_2607050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607057 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 5, 4, 2]
def baseStart_2607057 : Nat := 118140960795 + 2607057 * 2 ^ 59
def prefixEnd_2607057 : Nat := 4983230072969 + 3 ^ 40 * 2607057 * 2
def baseEnd_2607057 : Nat := 1338673334668711611197869

theorem tailTrace_2607057 : CollatzResearch.WordTrace tailWord_2607057 prefixEnd_2607057 1338673334668711611197869 := by
  unfold tailWord_2607057
  simp only [CollatzResearch.WordTrace]
  refine ⟨95087180516085213732555425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63391453677390142488370283 95087180516085213732555425)
  ·
    refine ⟨71315385387063910299416569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95087180516085213732555425 71315385387063910299416569)
    ·
      refine ⟨53486539040297932724562427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71315385387063910299416569 53486539040297932724562427)
      ·
        refine ⟨80229808560446899086843641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53486539040297932724562427 80229808560446899086843641)
        ·
          refine ⟨60172356420335174315132731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80229808560446899086843641 60172356420335174315132731)
          ·
            refine ⟨90258534630502761472699097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60172356420335174315132731 90258534630502761472699097)
            ·
              refine ⟨67693900972877071104524323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90258534630502761472699097 67693900972877071104524323)
              ·
                refine ⟨101540851459315606656786485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67693900972877071104524323 101540851459315606656786485)
                ·
                  refine ⟨9519454824310838124073733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101540851459315606656786485 9519454824310838124073733)
                  ·
                    refine ⟨1784897779558282148263825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9519454824310838124073733 1784897779558282148263825)
                    ·
                      refine ⟨1338673334668711611197869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784897779558282148263825 1338673334668711611197869)
                      ·
                        rfl

theorem cell23_2607057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_2607057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607057 prefixEnd_2607057 := by exact prefixLift 2607057
  have htrace : WordTrace (prefixWord ++ tailWord_2607057) baseStart_2607057 baseEnd_2607057 := by
    simpa [prefixWord, tailWord_2607057, baseEnd_2607057] using wordTrace_append hprefix tailTrace_2607057
  have hstable : (prefixWord ++ tailWord_2607057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607057).length < 2 ^ (prefixWord ++ tailWord_2607057).sum := by decide
  have hdescent : baseEnd_2607057 < baseStart_2607057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607080 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 9]
def baseStart_2607080 : Nat := 118140960795 + 2607080 * 2 ^ 59
def prefixEnd_2607080 : Nat := 4983230072969 + 3 ^ 40 * 2607080 * 2
def baseEnd_2607080 : Nat := 148742793858196113467807

theorem tailTrace_2607080 : CollatzResearch.WordTrace tailWord_2607080 prefixEnd_2607080 148742793858196113467807 := by
  unfold tailWord_2607080
  simp only [CollatzResearch.WordTrace]
  refine ⟨47544009697500944330321347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63392012930001259107095129 47544009697500944330321347)
  ·
    refine ⟨71316014546251416495482021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47544009697500944330321347 71316014546251416495482021)
    ·
      refine ⟨13371752727422140592902879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71316014546251416495482021 13371752727422140592902879)
      ·
        refine ⟨20057629091133210889354319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13371752727422140592902879 20057629091133210889354319)
        ·
          refine ⟨30086443636699816334031479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20057629091133210889354319 30086443636699816334031479)
          ·
            refine ⟨45129665455049724501047219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30086443636699816334031479 45129665455049724501047219)
            ·
              refine ⟨67694498182574586751570829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45129665455049724501047219 67694498182574586751570829)
              ·
                refine ⟨25385436818465470031839061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67694498182574586751570829 25385436818465470031839061)
                ·
                  refine ⟨148742793858196113467807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25385436818465470031839061 148742793858196113467807)
                  ·
                    rfl

theorem cell23_2607080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 9].length) (baseStart_2607080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607080 prefixEnd_2607080 := by exact prefixLift 2607080
  have htrace : WordTrace (prefixWord ++ tailWord_2607080) baseStart_2607080 baseEnd_2607080 := by
    simpa [prefixWord, tailWord_2607080, baseEnd_2607080] using wordTrace_append hprefix tailTrace_2607080
  have hstable : (prefixWord ++ tailWord_2607080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607080).length < 2 ^ (prefixWord ++ tailWord_2607080).sum := by decide
  have hdescent : baseEnd_2607080 < baseStart_2607080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607147 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 4]
def baseStart_2607147 : Nat := 118140960795 + 2607147 * 2 ^ 59
def prefixEnd_2607147 : Nat := 4983230072969 + 3 ^ 40 * 2607147 * 2
def baseEnd_2607147 : Nat := 1338719547927616259072455

theorem tailTrace_2607147 : CollatzResearch.WordTrace tailWord_2607147 prefixEnd_2607147 1338719547927616259072455 := by
  unfold tailWord_2607147
  simp only [CollatzResearch.WordTrace]
  refine ⟨95090463085759159103331695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63393642057172772735554463 95090463085759159103331695)
  ·
    refine ⟨142635694628638738654997543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95090463085759159103331695 142635694628638738654997543)
    ·
      refine ⟨213953541942958107982496315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142635694628638738654997543 213953541942958107982496315)
      ·
        refine ⟨320930312914437161973744473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213953541942958107982496315 320930312914437161973744473)
        ·
          refine ⟨240697734685827871480308355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320930312914437161973744473 240697734685827871480308355)
          ·
            refine ⟨361046602028741807220462533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240697734685827871480308355 361046602028741807220462533)
            ·
              refine ⟨67696237880389088853836725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 361046602028741807220462533 67696237880389088853836725)
              ·
                refine ⟨6346522301286477080047193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67696237880389088853836725 6346522301286477080047193)
                ·
                  refine ⟨4759891725964857810035395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6346522301286477080047193 4759891725964857810035395)
                  ·
                    refine ⟨7139837588947286715053093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4759891725964857810035395 7139837588947286715053093)
                    ·
                      refine ⟨1338719547927616259072455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7139837588947286715053093 1338719547927616259072455)
                      ·
                        rfl

theorem cell23_2607147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 4].length) (baseStart_2607147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607147 prefixEnd_2607147 := by exact prefixLift 2607147
  have htrace : WordTrace (prefixWord ++ tailWord_2607147) baseStart_2607147 baseEnd_2607147 := by
    simpa [prefixWord, tailWord_2607147, baseEnd_2607147] using wordTrace_append hprefix tailTrace_2607147
  have hstable : (prefixWord ++ tailWord_2607147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607147).length < 2 ^ (prefixWord ++ tailWord_2607147).sum := by decide
  have hdescent : baseEnd_2607147 < baseStart_2607147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607164 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_2607164 : Nat := 118140960795 + 2607164 * 2 ^ 59
def prefixEnd_2607164 : Nat := 4983230072969 + 3 ^ 40 * 2607164 * 2
def baseEnd_2607164 : Nat := 1338728277098742692559877

theorem tailTrace_2607164 : CollatzResearch.WordTrace tailWord_2607164 prefixEnd_2607164 1338728277098742692559877 := by
  unfold tailWord_2607164
  simp only [CollatzResearch.WordTrace]
  refine ⟨47545541563348785503350273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63394055417798380671133697 47545541563348785503350273)
  ·
    refine ⟨35659156172511589127512705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47545541563348785503350273 35659156172511589127512705)
    ·
      refine ⟨26744367129383691845634529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35659156172511589127512705 26744367129383691845634529)
      ·
        refine ⟨20058275347037768884225897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26744367129383691845634529 20058275347037768884225897)
        ·
          refine ⟨15043706510278326663169423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20058275347037768884225897 15043706510278326663169423)
          ·
            refine ⟨22565559765417489994754135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15043706510278326663169423 22565559765417489994754135)
            ·
              refine ⟨33848339648126234992131203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22565559765417489994754135 33848339648126234992131203)
              ·
                refine ⟨50772509472189352488196805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33848339648126234992131203 50772509472189352488196805)
                ·
                  refine ⟨9519845526035503591536901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50772509472189352488196805 9519845526035503591536901)
                  ·
                    refine ⟨1784971036131656923413169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9519845526035503591536901 1784971036131656923413169)
                    ·
                      refine ⟨1338728277098742692559877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784971036131656923413169 1338728277098742692559877)
                      ·
                        rfl

theorem cell23_2607164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_2607164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607164 prefixEnd_2607164 := by exact prefixLift 2607164
  have htrace : WordTrace (prefixWord ++ tailWord_2607164) baseStart_2607164 baseEnd_2607164 := by
    simpa [prefixWord, tailWord_2607164, baseEnd_2607164] using wordTrace_append hprefix tailTrace_2607164
  have hstable : (prefixWord ++ tailWord_2607164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607164).length < 2 ^ (prefixWord ++ tailWord_2607164).sum := by decide
  have hdescent : baseEnd_2607164 < baseStart_2607164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607181 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_2607181 : Nat := 118140960795 + 2607181 * 2 ^ 59
def prefixEnd_2607181 : Nat := 4983230072969 + 3 ^ 40 * 2607181 * 2
def baseEnd_2607181 : Nat := 1338737006269869126047299

theorem tailTrace_2607181 : CollatzResearch.WordTrace tailWord_2607181 prefixEnd_2607181 1338737006269869126047299 := by
  unfold tailWord_2607181
  simp only [CollatzResearch.WordTrace]
  refine ⟨95091703167635982910069397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63394468778423988606712931 95091703167635982910069397)
  ·
    refine ⟨4457423585982936698909503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95091703167635982910069397 4457423585982936698909503)
    ·
      refine ⟨6686135378974405048364255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4457423585982936698909503 6686135378974405048364255)
      ·
        refine ⟨10029203068461607572546383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6686135378974405048364255 10029203068461607572546383)
        ·
          refine ⟨15043804602692411358819575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10029203068461607572546383 15043804602692411358819575)
          ·
            refine ⟨22565706904038617038229363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15043804602692411358819575 22565706904038617038229363)
            ·
              refine ⟨33848560356057925557344045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22565706904038617038229363 33848560356057925557344045)
              ·
                refine ⟨12693210133521722084004017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33848560356057925557344045 12693210133521722084004017)
                ·
                  refine ⟨9519907600141291563003013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12693210133521722084004017 9519907600141291563003013)
                  ·
                    refine ⟨1784982675026492168063065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9519907600141291563003013 1784982675026492168063065)
                    ·
                      refine ⟨1338737006269869126047299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1784982675026492168063065 1338737006269869126047299)
                      ·
                        rfl

theorem cell23_2607181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_2607181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607181 prefixEnd_2607181 := by exact prefixLift 2607181
  have htrace : WordTrace (prefixWord ++ tailWord_2607181) baseStart_2607181 baseEnd_2607181 := by
    simpa [prefixWord, tailWord_2607181, baseEnd_2607181] using wordTrace_append hprefix tailTrace_2607181
  have hstable : (prefixWord ++ tailWord_2607181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607181).length < 2 ^ (prefixWord ++ tailWord_2607181).sum := by decide
  have hdescent : baseEnd_2607181 < baseStart_2607181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607257 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_2607257 : Nat := 118140960795 + 2607257 * 2 ^ 59
def prefixEnd_2607257 : Nat := 4983230072969 + 3 ^ 40 * 2607257 * 2
def baseEnd_2607257 : Nat := 1338776030799610828696949

theorem tailTrace_2607257 : CollatzResearch.WordTrace tailWord_2607257 prefixEnd_2607257 1338776030799610828696949 := by
  unfold tailWord_2607257
  simp only [CollatzResearch.WordTrace]
  refine ⟨95094475115360647889836025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63396316743573765259890683 95094475115360647889836025)
  ·
    refine ⟨71320856336520485917377019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95094475115360647889836025 71320856336520485917377019)
    ·
      refine ⟨106981284504780728876065529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71320856336520485917377019 106981284504780728876065529)
      ·
        refine ⟨80235963378585546657049147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106981284504780728876065529 80235963378585546657049147)
        ·
          refine ⟨120353945067878319985573721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80235963378585546657049147 120353945067878319985573721)
          ·
            refine ⟨90265458800908739989180291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120353945067878319985573721 90265458800908739989180291)
            ·
              refine ⟨135398188201363109983770437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90265458800908739989180291 135398188201363109983770437)
              ·
                refine ⟨25387160287755583121956957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135398188201363109983770437 25387160287755583121956957)
                ·
                  refine ⟨9520185107908343670733859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25387160287755583121956957 9520185107908343670733859)
                  ·
                    refine ⟨14280277661862515506100789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9520185107908343670733859 14280277661862515506100789)
                    ·
                      refine ⟨1338776030799610828696949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14280277661862515506100789 1338776030799610828696949)
                      ·
                        rfl

theorem cell23_2607257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_2607257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607257 prefixEnd_2607257 := by exact prefixLift 2607257
  have htrace : WordTrace (prefixWord ++ tailWord_2607257) baseStart_2607257 baseEnd_2607257 := by
    simpa [prefixWord, tailWord_2607257, baseEnd_2607257] using wordTrace_append hprefix tailTrace_2607257
  have hstable : (prefixWord ++ tailWord_2607257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607257).length < 2 ^ (prefixWord ++ tailWord_2607257).sum := by decide
  have hdescent : baseEnd_2607257 < baseStart_2607257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607264 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 1, 6]
def baseStart_2607264 : Nat := 118140960795 + 2607264 * 2 ^ 59
def prefixEnd_2607264 : Nat := 4983230072969 + 3 ^ 40 * 2607264 * 2
def baseEnd_2607264 : Nat := 446259875054730767103139

theorem tailTrace_2607264 : CollatzResearch.WordTrace tailWord_2607264 prefixEnd_2607264 446259875054730767103139 := by
  unfold tailWord_2607264
  simp only [CollatzResearch.WordTrace]
  refine ⟨47547365213167644042670423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63396486950890192056893897 47547365213167644042670423)
  ·
    refine ⟨71321047819751466064005635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47547365213167644042670423 71321047819751466064005635)
    ·
      refine ⟨106981571729627199096008453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71321047819751466064005635 106981571729627199096008453)
      ·
        refine ⟨20059044699305099830501585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106981571729627199096008453 20059044699305099830501585)
        ·
          refine ⟨15044283524478824872876189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20059044699305099830501585 15044283524478824872876189)
          ·
            refine ⟨5641606321679559327328571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15044283524478824872876189 5641606321679559327328571)
            ·
              refine ⟨8462409482519338990992857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641606321679559327328571 8462409482519338990992857)
              ·
                refine ⟨6346807111889504243244643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8462409482519338990992857 6346807111889504243244643)
                ·
                  refine ⟨9520210667834256364866965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6346807111889504243244643 9520210667834256364866965)
                  ·
                    refine ⟨446259875054730767103139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9520210667834256364866965 446259875054730767103139)
                    ·
                      rfl

theorem cell23_2607264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_2607264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607264 prefixEnd_2607264 := by exact prefixLift 2607264
  have htrace : WordTrace (prefixWord ++ tailWord_2607264) baseStart_2607264 baseEnd_2607264 := by
    simpa [prefixWord, tailWord_2607264, baseEnd_2607264] using wordTrace_append hprefix tailTrace_2607264
  have hstable : (prefixWord ++ tailWord_2607264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607264).length < 2 ^ (prefixWord ++ tailWord_2607264).sum := by decide
  have hdescent : baseEnd_2607264 < baseStart_2607264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607268 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_2607268 : Nat := 118140960795 + 2607268 * 2 ^ 59
def prefixEnd_2607268 : Nat := 4983230072969 + 3 ^ 40 * 2607268 * 2
def baseEnd_2607268 : Nat := 446260559695603428553133

theorem tailTrace_2607268 : CollatzResearch.WordTrace tailWord_2607268 prefixEnd_2607268 446260559695603428553133 := by
  unfold tailWord_2607268
  simp only [CollatzResearch.WordTrace]
  refine ⟨47547438159160398384243229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63396584212213864512324305 47547438159160398384243229)
  ·
    refine ⟨17830289309685149394091211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47547438159160398384243229 17830289309685149394091211)
    ·
      refine ⟨26745433964527724091136817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17830289309685149394091211 26745433964527724091136817)
      ·
        refine ⟨20059075473395793068352613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26745433964527724091136817 20059075473395793068352613)
        ·
          refine ⟨3761076651261711200316115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20059075473395793068352613 3761076651261711200316115)
          ·
            refine ⟨5641614976892566800474173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761076651261711200316115 5641614976892566800474173)
            ·
              refine ⟨2115605616334712550177815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5641614976892566800474173 2115605616334712550177815)
              ·
                refine ⟨3173408424502068825266723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115605616334712550177815 3173408424502068825266723)
                ·
                  refine ⟨4760112636753103237900085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173408424502068825266723 4760112636753103237900085)
                  ·
                    refine ⟨446260559695603428553133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4760112636753103237900085 446260559695603428553133)
                    ·
                      rfl

theorem cell23_2607268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_2607268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607268 prefixEnd_2607268 := by exact prefixLift 2607268
  have htrace : WordTrace (prefixWord ++ tailWord_2607268) baseStart_2607268 baseEnd_2607268 := by
    simpa [prefixWord, tailWord_2607268, baseEnd_2607268] using wordTrace_append hprefix tailTrace_2607268
  have hstable : (prefixWord ++ tailWord_2607268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607268).length < 2 ^ (prefixWord ++ tailWord_2607268).sum := by decide
  have hdescent : baseEnd_2607268 < baseStart_2607268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607298 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2607298 : Nat := 118140960795 + 2607298 * 2 ^ 59
def prefixEnd_2607298 : Nat := 4983230072969 + 3 ^ 40 * 2607298 * 2
def baseEnd_2607298 : Nat := 446265694502148389428087

theorem tailTrace_2607298 : CollatzResearch.WordTrace tailWord_2607298 prefixEnd_2607298 446265694502148389428087 := by
  unfold tailWord_2607298
  simp only [CollatzResearch.WordTrace]
  refine ⟨23773992627053027973019637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63397313672141407928052365 23773992627053027973019637)
  ·
    refine ⟨2228811808786221372470591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23773992627053027973019637 2228811808786221372470591)
    ·
      refine ⟨3343217713179332058705887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228811808786221372470591 3343217713179332058705887)
      ·
        refine ⟨5014826569768998088058831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3343217713179332058705887 5014826569768998088058831)
        ·
          refine ⟨7522239854653497132088247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5014826569768998088058831 7522239854653497132088247)
          ·
            refine ⟨11283359781980245698132371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7522239854653497132088247 11283359781980245698132371)
            ·
              refine ⟨16925039672970368547198557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11283359781980245698132371 16925039672970368547198557)
              ·
                refine ⟨6346889877363888205199459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16925039672970368547198557 6346889877363888205199459)
                ·
                  refine ⟨9520334816045832307799189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6346889877363888205199459 9520334816045832307799189)
                  ·
                    refine ⟨446265694502148389428087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9520334816045832307799189 446265694502148389428087)
                    ·
                      rfl

theorem cell23_2607298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2607298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607298 prefixEnd_2607298 := by exact prefixLift 2607298
  have htrace : WordTrace (prefixWord ++ tailWord_2607298) baseStart_2607298 baseEnd_2607298 := by
    simpa [prefixWord, tailWord_2607298, baseEnd_2607298] using wordTrace_append hprefix tailTrace_2607298
  have hstable : (prefixWord ++ tailWord_2607298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607298).length < 2 ^ (prefixWord ++ tailWord_2607298).sum := by decide
  have hdescent : baseEnd_2607298 < baseStart_2607298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607307 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 2, 7]
def baseStart_2607307 : Nat := 118140960795 + 2607307 * 2 ^ 59
def prefixEnd_2607307 : Nat := 4983230072969 + 3 ^ 40 * 2607307 * 2
def baseEnd_2607307 : Nat := 446267234944111877690573

theorem tailTrace_2607307 : CollatzResearch.WordTrace tailWord_2607307 prefixEnd_2607307 446267234944111877690573 := by
  unfold tailWord_2607307
  simp only [CollatzResearch.WordTrace]
  refine ⟨95096298765179506429156175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63397532510119670952770783 95096298765179506429156175)
  ·
    refine ⟨142644448147769259643734263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95096298765179506429156175 142644448147769259643734263)
    ·
      refine ⟨213966672221653889465601395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142644448147769259643734263 213966672221653889465601395)
      ·
        refine ⟨320950008332480834198402093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213966672221653889465601395 320950008332480834198402093)
        ·
          refine ⟨120356253124680312824400785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320950008332480834198402093 120356253124680312824400785)
          ·
            refine ⟨90267189843510234618300589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120356253124680312824400785 90267189843510234618300589)
            ·
              refine ⟨33850196191316337981862721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90267189843510234618300589 33850196191316337981862721)
              ·
                refine ⟨25387647143487253486397041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33850196191316337981862721 25387647143487253486397041)
                ·
                  refine ⟨19040735357615440114797781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25387647143487253486397041 19040735357615440114797781)
                  ·
                    refine ⟨446267234944111877690573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19040735357615440114797781 446267234944111877690573)
                    ·
                      rfl

theorem cell23_2607307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 7].length) (baseStart_2607307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607307 prefixEnd_2607307 := by exact prefixLift 2607307
  have htrace : WordTrace (prefixWord ++ tailWord_2607307) baseStart_2607307 baseEnd_2607307 := by
    simpa [prefixWord, tailWord_2607307, baseEnd_2607307] using wordTrace_append hprefix tailTrace_2607307
  have hstable : (prefixWord ++ tailWord_2607307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607307).length < 2 ^ (prefixWord ++ tailWord_2607307).sum := by decide
  have hdescent : baseEnd_2607307 < baseStart_2607307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607318 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2607318 : Nat := 118140960795 + 2607318 * 2 ^ 59
def prefixEnd_2607318 : Nat := 4983230072969 + 3 ^ 40 * 2607318 * 2
def baseEnd_2607318 : Nat := 1338807353119535090034169

theorem tailTrace_2607318 : CollatzResearch.WordTrace tailWord_2607318 prefixEnd_2607318 1338807353119535090034169 := by
  unfold tailWord_2607318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943543748008728456737913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63397799978759770205204405 5943543748008728456737913)
  ·
    refine ⟨4457657811006546342553435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5943543748008728456737913 4457657811006546342553435)
    ·
      refine ⟨6686486716509819513830153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4457657811006546342553435 6686486716509819513830153)
      ·
        refine ⟨5014865037382364635372615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6686486716509819513830153 5014865037382364635372615)
        ·
          refine ⟨7522297556073546953058923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5014865037382364635372615 7522297556073546953058923)
          ·
            refine ⟨11283446334110320429588385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7522297556073546953058923 11283446334110320429588385)
            ·
              refine ⟨8462584750582740322191289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11283446334110320429588385 8462584750582740322191289)
              ·
                refine ⟨6346938562937055241643467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8462584750582740322191289 6346938562937055241643467)
                ·
                  refine ⟨9520407844405582862465201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6346938562937055241643467 9520407844405582862465201)
                  ·
                    refine ⟨7140305883304187146848901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9520407844405582862465201 7140305883304187146848901)
                    ·
                      refine ⟨1338807353119535090034169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7140305883304187146848901 1338807353119535090034169)
                      ·
                        rfl

theorem cell23_2607318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2607318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607318 prefixEnd_2607318 := by exact prefixLift 2607318
  have htrace : WordTrace (prefixWord ++ tailWord_2607318) baseStart_2607318 baseEnd_2607318 := by
    simpa [prefixWord, tailWord_2607318, baseEnd_2607318] using wordTrace_append hprefix tailTrace_2607318
  have hstable : (prefixWord ++ tailWord_2607318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607318).length < 2 ^ (prefixWord ++ tailWord_2607318).sum := by decide
  have hdescent : baseEnd_2607318 < baseStart_2607318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607325 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2607325 : Nat := 118140960795 + 2607325 * 2 ^ 59
def prefixEnd_2607325 : Nat := 4983230072969 + 3 ^ 40 * 2607325 * 2
def baseEnd_2607325 : Nat := 1338810947484116562646637

theorem tailTrace_2607325 : CollatzResearch.WordTrace tailWord_2607325 prefixEnd_2607325 1338810947484116562646637 := by
  unfold tailWord_2607325
  simp only [CollatzResearch.WordTrace]
  refine ⟨95096955279114295503311429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63397970186076197002207619 95096955279114295503311429)
  ·
    refine ⟨17830679114833930406870893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95096955279114295503311429 17830679114833930406870893)
    ·
      refine ⟨6686504668062723902576585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17830679114833930406870893 6686504668062723902576585)
      ·
        refine ⟨5014878501047042926932439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6686504668062723902576585 5014878501047042926932439)
        ·
          refine ⟨7522317751570564390398659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5014878501047042926932439 7522317751570564390398659)
          ·
            refine ⟨11283476627355846585597989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7522317751570564390398659 11283476627355846585597989)
            ·
              refine ⟨2115651867629221234799623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11283476627355846585597989 2115651867629221234799623)
              ·
                refine ⟨3173477801443831852199435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115651867629221234799623 3173477801443831852199435)
                ·
                  refine ⟨4760216702165747778299153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173477801443831852199435 4760216702165747778299153)
                  ·
                    refine ⟨3570162526624310833724365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4760216702165747778299153 3570162526624310833724365)
                    ·
                      refine ⟨1338810947484116562646637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3570162526624310833724365 1338810947484116562646637)
                      ·
                        rfl

theorem cell23_2607325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2607325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607325 prefixEnd_2607325 := by exact prefixLift 2607325
  have htrace : WordTrace (prefixWord ++ tailWord_2607325) baseStart_2607325 baseEnd_2607325 := by
    simpa [prefixWord, tailWord_2607325, baseEnd_2607325] using wordTrace_append hprefix tailTrace_2607325
  have hstable : (prefixWord ++ tailWord_2607325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607325).length < 2 ^ (prefixWord ++ tailWord_2607325).sum := by decide
  have hdescent : baseEnd_2607325 < baseStart_2607325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607337 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 3, 8]
def baseStart_2607337 : Nat := 118140960795 + 2607337 * 2 ^ 59
def prefixEnd_2607337 : Nat := 4983230072969 + 3 ^ 40 * 2607337 * 2
def baseEnd_2607337 : Nat := 446272369750656838565527

theorem tailTrace_2607337 : CollatzResearch.WordTrace tailWord_2607337 prefixEnd_2607337 446272369750656838565527 := by
  unfold tailWord_2607337
  simp only [CollatzResearch.WordTrace]
  refine ⟨95097392955070821552748265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63398261970047214368498843 95097392955070821552748265)
  ·
    refine ⟨71323044716303116164561199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95097392955070821552748265 71323044716303116164561199)
    ·
      refine ⟨106984567074454674246841799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71323044716303116164561199 106984567074454674246841799)
      ·
        refine ⟨160476850611682011370262699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106984567074454674246841799 160476850611682011370262699)
        ·
          refine ⟨240715275917523017055394049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160476850611682011370262699 240715275917523017055394049)
          ·
            refine ⟨180536456938142262791545537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240715275917523017055394049 180536456938142262791545537)
            ·
              refine ⟨135402342703606697093659153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180536456938142262791545537 135402342703606697093659153)
              ·
                refine ⟨101551757027705022820244365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135402342703606697093659153 101551757027705022820244365)
                ·
                  refine ⟨38081908885389383557591637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101551757027705022820244365 38081908885389383557591637)
                  ·
                    refine ⟨446272369750656838565527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38081908885389383557591637 446272369750656838565527)
                    ·
                      rfl

theorem cell23_2607337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_2607337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607337 prefixEnd_2607337 := by exact prefixLift 2607337
  have htrace : WordTrace (prefixWord ++ tailWord_2607337) baseStart_2607337 baseEnd_2607337 := by
    simpa [prefixWord, tailWord_2607337, baseEnd_2607337] using wordTrace_append hprefix tailTrace_2607337
  have hstable : (prefixWord ++ tailWord_2607337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607337).length < 2 ^ (prefixWord ++ tailWord_2607337).sum := by decide
  have hdescent : baseEnd_2607337 < baseStart_2607337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607354 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_2607354 : Nat := 118140960795 + 2607354 * 2 ^ 59
def prefixEnd_2607354 : Nat := 4983230072969 + 3 ^ 40 * 2607354 * 2
def baseEnd_2607354 : Nat := 446275279474365649728001

theorem tailTrace_2607354 : CollatzResearch.WordTrace tailWord_2607354 prefixEnd_2607354 446275279474365649728001 := by
  unfold tailWord_2607354
  simp only [CollatzResearch.WordTrace]
  refine ⟨23774503249002308364029279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63398675330672822304078077 23774503249002308364029279)
  ·
    refine ⟨35661754873503462546043919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23774503249002308364029279 35661754873503462546043919)
    ·
      refine ⟨53492632310255193819065879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35661754873503462546043919 53492632310255193819065879)
      ·
        refine ⟨80238948465382790728598819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53492632310255193819065879 80238948465382790728598819)
        ·
          refine ⟨120358422698074186092898229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80238948465382790728598819 120358422698074186092898229)
          ·
            refine ⟨11283602127944454946209209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120358422698074186092898229 11283602127944454946209209)
            ·
              refine ⟨8462701595958341209656907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11283602127944454946209209 8462701595958341209656907)
              ·
                refine ⟨12694052393937511814485361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462701595958341209656907 12694052393937511814485361)
                ·
                  refine ⟨9520539295453133860864021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12694052393937511814485361 9520539295453133860864021)
                  ·
                    refine ⟨446275279474365649728001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9520539295453133860864021 446275279474365649728001)
                    ·
                      rfl

theorem cell23_2607354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_2607354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607354 prefixEnd_2607354 := by exact prefixLift 2607354
  have htrace : WordTrace (prefixWord ++ tailWord_2607354) baseStart_2607354 baseEnd_2607354 := by
    simpa [prefixWord, tailWord_2607354, baseEnd_2607354] using wordTrace_append hprefix tailTrace_2607354
  have hstable : (prefixWord ++ tailWord_2607354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607354).length < 2 ^ (prefixWord ++ tailWord_2607354).sum := by decide
  have hdescent : baseEnd_2607354 < baseStart_2607354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
