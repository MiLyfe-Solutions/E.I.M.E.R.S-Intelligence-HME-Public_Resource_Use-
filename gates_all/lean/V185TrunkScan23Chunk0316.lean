import V185TrunkScan23Chunk0315

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1868954 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1868954 : Nat := 118140960795 + 1868954 * 2 ^ 59
def prefixEnd_1868954 : Nat := 4983230072969 + 3 ^ 40 * 1868954 * 2
def baseEnd_1868954 : Nat := 959671723143185942579843

theorem tailTrace_1868954 : CollatzResearch.WordTrace tailWord_1868954 prefixEnd_1868954 959671723143185942579843 := by
  unfold tailWord_1868954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17041588117776581194035479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45444234980737549850761277 17041588117776581194035479)
  ·
    refine ⟨25562382176664871791053219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17041588117776581194035479 25562382176664871791053219)
    ·
      refine ⟨38343573264997307686579829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25562382176664871791053219 38343573264997307686579829)
      ·
        refine ⟨3594709993593497595616859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38343573264997307686579829 3594709993593497595616859)
        ·
          refine ⟨5392064990390246393425289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594709993593497595616859 5392064990390246393425289)
          ·
            refine ⟨4044048742792684795068967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5392064990390246393425289 4044048742792684795068967)
            ·
              refine ⟨6066073114189027192603451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044048742792684795068967 6066073114189027192603451)
              ·
                refine ⟨9099109671283540788905177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066073114189027192603451 9099109671283540788905177)
                ·
                  refine ⟨6824332253462655591678883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9099109671283540788905177 6824332253462655591678883)
                  ·
                    refine ⟨10236498380193983387518325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6824332253462655591678883 10236498380193983387518325)
                    ·
                      refine ⟨959671723143185942579843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10236498380193983387518325 959671723143185942579843)
                      ·
                        rfl

theorem cell23_1868954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1868954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868954 prefixEnd_1868954 := by exact prefixLift 1868954
  have htrace : WordTrace (prefixWord ++ tailWord_1868954) baseStart_1868954 baseEnd_1868954 := by
    simpa [prefixWord, tailWord_1868954, baseEnd_1868954] using wordTrace_append hprefix tailTrace_1868954
  have hstable : (prefixWord ++ tailWord_1868954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868954).length < 2 ^ (prefixWord ++ tailWord_1868954).sum := by decide
  have hdescent : baseEnd_1868954 < baseStart_1868954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868985 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 2, 2, 2]
def baseStart_1868985 : Nat := 118140960795 + 1868985 * 2 ^ 59
def prefixEnd_1868985 : Nat := 4983230072969 + 3 ^ 40 * 1868985 * 2
def baseEnd_1868985 : Nat := 959687641043475321292201

theorem tailTrace_1868985 : CollatzResearch.WordTrace tailWord_1868985 prefixEnd_1868985 959687641043475321292201 := by
  unfold tailWord_1868985
  simp only [CollatzResearch.WordTrace]
  refine ⟨68167483133994017070520409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45444988755996011380346939 68167483133994017070520409)
  ·
    refine ⟨51125612350495512802890307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68167483133994017070520409 51125612350495512802890307)
    ·
      refine ⟨76688418525743269204335461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51125612350495512802890307 76688418525743269204335461)
      ·
        refine ⟨14379078473576862975812899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76688418525743269204335461 14379078473576862975812899)
        ·
          refine ⟨21568617710365294463719349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14379078473576862975812899 21568617710365294463719349)
          ·
            refine ⟨2022057910346746355973689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21568617710365294463719349 2022057910346746355973689)
            ·
              refine ⟨1516543432760059766980267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022057910346746355973689 1516543432760059766980267)
              ·
                refine ⟨2274815149140089650470401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516543432760059766980267 2274815149140089650470401)
                ·
                  refine ⟨1706111361855067237852801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2274815149140089650470401 1706111361855067237852801)
                  ·
                    refine ⟨1279583521391300428389601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1706111361855067237852801 1279583521391300428389601)
                    ·
                      refine ⟨959687641043475321292201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1279583521391300428389601 959687641043475321292201)
                      ·
                        rfl

theorem cell23_1868985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_1868985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1868985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1868985 prefixEnd_1868985 := by exact prefixLift 1868985
  have htrace : WordTrace (prefixWord ++ tailWord_1868985) baseStart_1868985 baseEnd_1868985 := by
    simpa [prefixWord, tailWord_1868985, baseEnd_1868985] using wordTrace_append hprefix tailTrace_1868985
  have hstable : (prefixWord ++ tailWord_1868985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868985).length < 2 ^ (prefixWord ++ tailWord_1868985).sum := by decide
  have hdescent : baseEnd_1868985 < baseStart_1868985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869024 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1869024 : Nat := 118140960795 + 1869024 * 2 ^ 59
def prefixEnd_1869024 : Nat := 4983230072969 + 3 ^ 40 * 1869024 * 2
def baseEnd_1869024 : Nat := 959707666789000668704521

theorem tailTrace_1869024 : CollatzResearch.WordTrace tailWord_1869024 prefixEnd_1869024 959707666789000668704521 := by
  unfold tailWord_1869024
  simp only [CollatzResearch.WordTrace]
  refine ⟨34084452790426363365595063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45445937053901817820793417 34084452790426363365595063)
  ·
    refine ⟨51126679185639545048392595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34084452790426363365595063 51126679185639545048392595)
    ·
      refine ⟨76690018778459317572588893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51126679185639545048392595 76690018778459317572588893)
      ·
        refine ⟨28758757041922244089720835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76690018778459317572588893 28758757041922244089720835)
        ·
          refine ⟨43138135562883366134581253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28758757041922244089720835 43138135562883366134581253)
          ·
            refine ⟨8088400418040631150233985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43138135562883366134581253 8088400418040631150233985)
            ·
              refine ⟨6066300313530473362675489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8088400418040631150233985 6066300313530473362675489)
              ·
                refine ⟨4549725235147855022006617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6066300313530473362675489 4549725235147855022006617)
                ·
                  refine ⟨3412293926360891266504963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4549725235147855022006617 3412293926360891266504963)
                  ·
                    refine ⟨5118440889541336899757445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3412293926360891266504963 5118440889541336899757445)
                    ·
                      refine ⟨959707666789000668704521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5118440889541336899757445 959707666789000668704521)
                      ·
                        rfl

theorem cell23_1869024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1869024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869024 prefixEnd_1869024 := by exact prefixLift 1869024
  have htrace : WordTrace (prefixWord ++ tailWord_1869024) baseStart_1869024 baseEnd_1869024 := by
    simpa [prefixWord, tailWord_1869024, baseEnd_1869024] using wordTrace_append hprefix tailTrace_1869024
  have hstable : (prefixWord ++ tailWord_1869024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869024).length < 2 ^ (prefixWord ++ tailWord_1869024).sum := by decide
  have hdescent : baseEnd_1869024 < baseStart_1869024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869068 : List Nat := [2, 2, 1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_1869068 : Nat := 118140960795 + 1869068 * 2 ^ 59
def prefixEnd_1869068 : Nat := 4983230072969 + 3 ^ 40 * 1869068 * 2
def baseEnd_1869068 : Nat := 319910086645932832184773

theorem tailTrace_1869068 : CollatzResearch.WordTrace tailWord_1869068 prefixEnd_1869068 319910086645932832184773 := by
  unfold tailWord_1869068
  simp only [CollatzResearch.WordTrace]
  refine ⟨34085255196346661122895929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45447006928462214830527905 34085255196346661122895929)
  ·
    refine ⟨25563941397259995842171947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34085255196346661122895929 25563941397259995842171947)
    ·
      refine ⟨38345912095889993763257921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25563941397259995842171947 38345912095889993763257921)
      ·
        refine ⟨28759434071917495322443441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38345912095889993763257921 28759434071917495322443441)
        ·
          refine ⟨21569575553938121491832581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28759434071917495322443441 21569575553938121491832581)
          ·
            refine ⟨4044295416363397779718609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21569575553938121491832581 4044295416363397779718609)
            ·
              refine ⟨3033221562272548334788957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4044295416363397779718609 3033221562272548334788957)
              ·
                refine ⟨1137458085852205625545859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3033221562272548334788957 1137458085852205625545859)
                ·
                  refine ⟨1706187128778308438318789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137458085852205625545859 1706187128778308438318789)
                  ·
                    refine ⟨319910086645932832184773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1706187128778308438318789 319910086645932832184773)
                    ·
                      rfl

theorem cell23_1869068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_1869068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869068 prefixEnd_1869068 := by exact prefixLift 1869068
  have htrace : WordTrace (prefixWord ++ tailWord_1869068) baseStart_1869068 baseEnd_1869068 := by
    simpa [prefixWord, tailWord_1869068, baseEnd_1869068] using wordTrace_append hprefix tailTrace_1869068
  have hstable : (prefixWord ++ tailWord_1869068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869068).length < 2 ^ (prefixWord ++ tailWord_1869068).sum := by decide
  have hdescent : baseEnd_1869068 < baseStart_1869068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869091 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 3]
def baseStart_1869091 : Nat := 118140960795 + 1869091 * 2 ^ 59
def prefixEnd_1869091 : Nat := 4983230072969 + 3 ^ 40 * 1869091 * 2
def baseEnd_1869091 : Nat := 959742069992851906566713

theorem tailTrace_1869091 : CollatzResearch.WordTrace tailWord_1869091 prefixEnd_1869091 959742069992851906566713 := by
  unfold tailWord_1869091
  simp only [CollatzResearch.WordTrace]
  refine ⟨68171349271609997173879127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45447566181073331449252751 68171349271609997173879127)
  ·
    refine ⟨102257023907414995760818691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68171349271609997173879127 102257023907414995760818691)
    ·
      refine ⟨153385535861122493641228037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102257023907414995760818691 153385535861122493641228037)
      ·
        refine ⟨28759787973960467557730257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153385535861122493641228037 28759787973960467557730257)
        ·
          refine ⟨21569840980470350668297693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28759787973960467557730257 21569840980470350668297693)
          ·
            refine ⟨8088690367676381500611635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21569840980470350668297693 8088690367676381500611635)
            ·
              refine ⟨12133035551514572250917453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088690367676381500611635 12133035551514572250917453)
              ·
                refine ⟨4549888331817964594094045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12133035551514572250917453 4549888331817964594094045)
                ·
                  refine ⟨1706208124431736722785267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4549888331817964594094045 1706208124431736722785267)
                  ·
                    refine ⟨2559312186647605084177901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1706208124431736722785267 2559312186647605084177901)
                    ·
                      refine ⟨959742069992851906566713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2559312186647605084177901 959742069992851906566713)
                      ·
                        rfl

theorem cell23_1869091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_1869091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869091 prefixEnd_1869091 := by exact prefixLift 1869091
  have htrace : WordTrace (prefixWord ++ tailWord_1869091) baseStart_1869091 baseEnd_1869091 := by
    simpa [prefixWord, tailWord_1869091, baseEnd_1869091] using wordTrace_append hprefix tailTrace_1869091
  have hstable : (prefixWord ++ tailWord_1869091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869091).length < 2 ^ (prefixWord ++ tailWord_1869091).sum := by decide
  have hdescent : baseEnd_1869091 < baseStart_1869091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869098 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 6]
def baseStart_1869098 : Nat := 118140960795 + 1869098 * 2 ^ 59
def prefixEnd_1869098 : Nat := 4983230072969 + 3 ^ 40 * 1869098 * 2
def baseEnd_1869098 : Nat := 106638407150825931019909

theorem tailTrace_1869098 : CollatzResearch.WordTrace tailWord_1869098 prefixEnd_1869098 106638407150825931019909 := by
  unfold tailWord_1869098
  simp only [CollatzResearch.WordTrace]
  refine ⟨17042901145646159342345987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45447736388389758246255965 17042901145646159342345987)
  ·
    refine ⟨25564351718469239013518981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17042901145646159342345987 25564351718469239013518981)
    ·
      refine ⟨4793315947212982315034809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25564351718469239013518981 4793315947212982315034809)
      ·
        refine ⟨3594986960409736736276107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4793315947212982315034809 3594986960409736736276107)
        ·
          refine ⟨5392480440614605104414161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594986960409736736276107 5392480440614605104414161)
          ·
            refine ⟨4044360330460953828310621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5392480440614605104414161 4044360330460953828310621)
            ·
              refine ⟨1516635123922857685616483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4044360330460953828310621 1516635123922857685616483)
              ·
                refine ⟨2274952685884286528424725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516635123922857685616483 2274952685884286528424725)
                ·
                  refine ⟨106638407150825931019909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2274952685884286528424725 106638407150825931019909)
                  ·
                    rfl

theorem cell23_1869098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_1869098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869098 prefixEnd_1869098 := by exact prefixLift 1869098
  have htrace : WordTrace (prefixWord ++ tailWord_1869098) baseStart_1869098 baseEnd_1869098 := by
    simpa [prefixWord, tailWord_1869098, baseEnd_1869098] using wordTrace_append hprefix tailTrace_1869098
  have hstable : (prefixWord ++ tailWord_1869098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869098).length < 2 ^ (prefixWord ++ tailWord_1869098).sum := by decide
  have hdescent : baseEnd_1869098 < baseStart_1869098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869108 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_1869108 : Nat := 118140960795 + 1869108 * 2 ^ 59
def prefixEnd_1869108 : Nat := 4983230072969 + 3 ^ 40 * 1869108 * 2
def baseEnd_1869108 : Nat := 959750799163978340054135

theorem tailTrace_1869108 : CollatzResearch.WordTrace tailWord_1869108 prefixEnd_1869108 959750799163978340054135 := by
  unfold tailWord_1869108
  simp only [CollatzResearch.WordTrace]
  refine ⟨34085984656274204538623989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45447979541698939384831985 34085984656274204538623989)
  ·
    refine ⟨3195561061525706675495999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34085984656274204538623989 3195561061525706675495999)
    ·
      refine ⟨4793341592288560013243999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3195561061525706675495999 4793341592288560013243999)
      ·
        refine ⟨7190012388432840019865999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793341592288560013243999 7190012388432840019865999)
        ·
          refine ⟨10785018582649260029798999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7190012388432840019865999 10785018582649260029798999)
          ·
            refine ⟨16177527873973890044698499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10785018582649260029798999 16177527873973890044698499)
            ·
              refine ⟨24266291810960835067047749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16177527873973890044698499 24266291810960835067047749)
              ·
                refine ⟨4549929714555156575071453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24266291810960835067047749 4549929714555156575071453)
                ·
                  refine ⟨1706223642958183715651795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4549929714555156575071453 1706223642958183715651795)
                  ·
                    refine ⟨2559335464437275573477693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1706223642958183715651795 2559335464437275573477693)
                    ·
                      refine ⟨959750799163978340054135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2559335464437275573477693 959750799163978340054135)
                      ·
                        rfl

theorem cell23_1869108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_1869108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869108 prefixEnd_1869108 := by exact prefixLift 1869108
  have htrace : WordTrace (prefixWord ++ tailWord_1869108) baseStart_1869108 baseEnd_1869108 := by
    simpa [prefixWord, tailWord_1869108, baseEnd_1869108] using wordTrace_append hprefix tailTrace_1869108
  have hstable : (prefixWord ++ tailWord_1869108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869108).length < 2 ^ (prefixWord ++ tailWord_1869108).sum := by decide
  have hdescent : baseEnd_1869108 < baseStart_1869108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869118 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_1869118 : Nat := 118140960795 + 1869118 * 2 ^ 59
def prefixEnd_1869118 : Nat := 4983230072969 + 3 ^ 40 * 1869118 * 2
def baseEnd_1869118 : Nat := 959755933970523300929089

theorem tailTrace_1869118 : CollatzResearch.WordTrace tailWord_1869118 prefixEnd_1869118 959755933970523300929089 := by
  unfold tailWord_1869118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8521541755314022598139001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45448222695008120523408005 8521541755314022598139001)
  ·
    refine ⟨6391156316485516948604251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8521541755314022598139001 6391156316485516948604251)
    ·
      refine ⟨9586734474728275422906377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6391156316485516948604251 9586734474728275422906377)
      ·
        refine ⟨7190050856046206567179783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9586734474728275422906377 7190050856046206567179783)
        ·
          refine ⟨10785076284069309850769675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7190050856046206567179783 10785076284069309850769675)
          ·
            refine ⟨16177614426103964776154513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10785076284069309850769675 16177614426103964776154513)
            ·
              refine ⟨12133210819577973582115885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16177614426103964776154513 12133210819577973582115885)
              ·
                refine ⟨4549954057341740093293457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12133210819577973582115885 4549954057341740093293457)
                ·
                  refine ⟨3412465543006305069970093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4549954057341740093293457 3412465543006305069970093)
                  ·
                    refine ⟨1279674578627364401238785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412465543006305069970093 1279674578627364401238785)
                    ·
                      refine ⟨959755933970523300929089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1279674578627364401238785 959755933970523300929089)
                      ·
                        rfl

theorem cell23_1869118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_1869118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869118 prefixEnd_1869118 := by exact prefixLift 1869118
  have htrace : WordTrace (prefixWord ++ tailWord_1869118) baseStart_1869118 baseEnd_1869118 := by
    simpa [prefixWord, tailWord_1869118, baseEnd_1869118] using wordTrace_append hprefix tailTrace_1869118
  have hstable : (prefixWord ++ tailWord_1869118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869118).length < 2 ^ (prefixWord ++ tailWord_1869118).sum := by decide
  have hdescent : baseEnd_1869118 < baseStart_1869118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869141 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_1869141 : Nat := 118140960795 + 1869141 * 2 ^ 59
def prefixEnd_1869141 : Nat := 4983230072969 + 3 ^ 40 * 1869141 * 2
def baseEnd_1869141 : Nat := 319922581341858903647161

theorem tailTrace_1869141 : CollatzResearch.WordTrace tailWord_1869141 prefixEnd_1869141 319922581341858903647161 := by
  unfold tailWord_1869141
  simp only [CollatzResearch.WordTrace]
  refine ⟨68173172921428855713199277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45448781947619237142132851 68173172921428855713199277)
  ·
    refine ⟨25564939845535820892449729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68173172921428855713199277 25564939845535820892449729)
    ·
      refine ⟨19173704884151865669337297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25564939845535820892449729 19173704884151865669337297)
      ·
        refine ⟨14380278663113899252002973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19173704884151865669337297 14380278663113899252002973)
        ·
          refine ⟨5392604498667712219501115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14380278663113899252002973 5392604498667712219501115)
          ·
            refine ⟨8088906748001568329251673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392604498667712219501115 8088906748001568329251673)
            ·
              refine ⟨6066680061001176246938755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8088906748001568329251673 6066680061001176246938755)
              ·
                refine ⟨9100020091501764370408133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066680061001176246938755 9100020091501764370408133)
                ·
                  refine ⟨1706253767156580819451525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9100020091501764370408133 1706253767156580819451525)
                  ·
                    refine ⟨319922581341858903647161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1706253767156580819451525 319922581341858903647161)
                    ·
                      rfl

theorem cell23_1869141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_1869141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869141 prefixEnd_1869141 := by exact prefixLift 1869141
  have htrace : WordTrace (prefixWord ++ tailWord_1869141) baseStart_1869141 baseEnd_1869141 := by
    simpa [prefixWord, tailWord_1869141, baseEnd_1869141] using wordTrace_append hprefix tailTrace_1869141
  have hstable : (prefixWord ++ tailWord_1869141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869141).length < 2 ^ (prefixWord ++ tailWord_1869141).sum := by decide
  have hdescent : baseEnd_1869141 < baseStart_1869141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869149 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 6]
def baseStart_1869149 : Nat := 118140960795 + 1869149 * 2 ^ 59
def prefixEnd_1869149 : Nat := 4983230072969 + 3 ^ 40 * 1869149 * 2
def baseEnd_1869149 : Nat := 106641316874534742182383

theorem tailTrace_1869149 : CollatzResearch.WordTrace tailWord_1869149 prefixEnd_1869149 106641316874534742182383 := by
  unfold tailWord_1869149
  simp only [CollatzResearch.WordTrace]
  refine ⟨68173464705399873079490501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45448976470266582052993667 68173464705399873079490501)
  ·
    refine ⟨12782524632262476202404469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68173464705399873079490501 12782524632262476202404469)
    ·
      refine ⟨1198361684274607143975419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12782524632262476202404469 1198361684274607143975419)
      ·
        refine ⟨1797542526411910715963129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1198361684274607143975419 1797542526411910715963129)
        ·
          refine ⟨1348156894808933036972347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1797542526411910715963129 1348156894808933036972347)
          ·
            refine ⟨2022235342213399555458521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348156894808933036972347 2022235342213399555458521)
            ·
              refine ⟨1516676506660049666593891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022235342213399555458521 1516676506660049666593891)
              ·
                refine ⟨2275014759990074499890837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516676506660049666593891 2275014759990074499890837)
                ·
                  refine ⟨106641316874534742182383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2275014759990074499890837 106641316874534742182383)
                  ·
                    rfl

theorem cell23_1869149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_1869149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869149 prefixEnd_1869149 := by exact prefixLift 1869149
  have htrace : WordTrace (prefixWord ++ tailWord_1869149) baseStart_1869149 baseEnd_1869149 := by
    simpa [prefixWord, tailWord_1869149, baseEnd_1869149] using wordTrace_append hprefix tailTrace_1869149
  have hstable : (prefixWord ++ tailWord_1869149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869149).length < 2 ^ (prefixWord ++ tailWord_1869149).sum := by decide
  have hdescent : baseEnd_1869149 < baseStart_1869149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869181 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_1869181 : Nat := 118140960795 + 1869181 * 2 ^ 59
def prefixEnd_1869181 : Nat := 4983230072969 + 3 ^ 40 * 1869181 * 2
def baseEnd_1869181 : Nat := 959788283251756554441299

theorem tailTrace_1869181 : CollatzResearch.WordTrace tailWord_1869181 prefixEnd_1869181 959788283251756554441299 := by
  unfold tailWord_1869181
  simp only [CollatzResearch.WordTrace]
  refine ⟨68174631841283942544655397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45449754560855961696436931 68174631841283942544655397)
  ·
    refine ⟨12782743470240739227122887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68174631841283942544655397 12782743470240739227122887)
    ·
      refine ⟨19174115205361108840684331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12782743470240739227122887 19174115205361108840684331)
      ·
        refine ⟨28761172808041663261026497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19174115205361108840684331 28761172808041663261026497)
        ·
          refine ⟨21570879606031247445769873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28761172808041663261026497 21570879606031247445769873)
          ·
            refine ⟨16178159704523435584327405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21570879606031247445769873 16178159704523435584327405)
            ·
              refine ⟨6066809889196288344122777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16178159704523435584327405 6066809889196288344122777)
              ·
                refine ⟨4550107416897216258092083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6066809889196288344122777 4550107416897216258092083)
                ·
                  refine ⟨6825161125345824387138125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550107416897216258092083 6825161125345824387138125)
                  ·
                    refine ⟨2559435422004684145176797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6825161125345824387138125 2559435422004684145176797)
                    ·
                      refine ⟨959788283251756554441299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2559435422004684145176797 959788283251756554441299)
                      ·
                        rfl

theorem cell23_1869181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_1869181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869181 prefixEnd_1869181 := by exact prefixLift 1869181
  have htrace : WordTrace (prefixWord ++ tailWord_1869181) baseStart_1869181 baseEnd_1869181 := by
    simpa [prefixWord, tailWord_1869181, baseEnd_1869181] using wordTrace_append hprefix tailTrace_1869181
  have hstable : (prefixWord ++ tailWord_1869181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869181).length < 2 ^ (prefixWord ++ tailWord_1869181).sum := by decide
  have hdescent : baseEnd_1869181 < baseStart_1869181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869185 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_1869185 : Nat := 118140960795 + 1869185 * 2 ^ 59
def prefixEnd_1869185 : Nat := 4983230072969 + 3 ^ 40 * 1869185 * 2
def baseEnd_1869185 : Nat := 959790337174374538791281

theorem tailTrace_1869185 : CollatzResearch.WordTrace tailWord_1869185 prefixEnd_1869185 959790337174374538791281 := by
  unfold tailWord_1869185
  simp only [CollatzResearch.WordTrace]
  refine ⟨68174777733269451227801009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45449851822179634151867339 68174777733269451227801009)
  ·
    refine ⟨51131083299952088420850757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68174777733269451227801009 51131083299952088420850757)
    ·
      refine ⟨9587078118741016578909517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51131083299952088420850757 9587078118741016578909517)
      ·
        refine ⟨3595154294527881217091069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9587078118741016578909517 3595154294527881217091069)
        ·
          refine ⟨1348182860447955456409151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3595154294527881217091069 1348182860447955456409151)
          ·
            refine ⟨2022274290671933184613727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348182860447955456409151 2022274290671933184613727)
            ·
              refine ⟨3033411436007899776920591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022274290671933184613727 3033411436007899776920591)
              ·
                refine ⟨4550117154011849665380887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033411436007899776920591 4550117154011849665380887)
                ·
                  refine ⟨6825175731017774498071331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550117154011849665380887 6825175731017774498071331)
                  ·
                    refine ⟨10237763596526661747106997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6825175731017774498071331 10237763596526661747106997)
                    ·
                      refine ⟨959790337174374538791281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10237763596526661747106997 959790337174374538791281)
                      ·
                        rfl

theorem cell23_1869185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_1869185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869185 prefixEnd_1869185 := by exact prefixLift 1869185
  have htrace : WordTrace (prefixWord ++ tailWord_1869185) baseStart_1869185 baseEnd_1869185 := by
    simpa [prefixWord, tailWord_1869185, baseEnd_1869185] using wordTrace_append hprefix tailTrace_1869185
  have hstable : (prefixWord ++ tailWord_1869185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869185).length < 2 ^ (prefixWord ++ tailWord_1869185).sum := by decide
  have hdescent : baseEnd_1869185 < baseStart_1869185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869368 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 6]
def baseStart_1869368 : Nat := 118140960795 + 1869368 * 2 ^ 59
def prefixEnd_1869368 : Nat := 4983230072969 + 3 ^ 40 * 1869368 * 2
def baseEnd_1869368 : Nat := 106653811570460813644771

theorem tailTrace_1869368 : CollatzResearch.WordTrace tailWord_1869368 prefixEnd_1869368 106653811570460813644771 := by
  unfold tailWord_1869368
  simp only [CollatzResearch.WordTrace]
  refine ⟨34090726145803236740856379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45454301527737648987808505 34090726145803236740856379)
  ·
    refine ⟨51136089218704855111284569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34090726145803236740856379 51136089218704855111284569)
    ·
      refine ⟨38352066914028641333463427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51136089218704855111284569 38352066914028641333463427)
      ·
        refine ⟨57528100371042962000195141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38352066914028641333463427 57528100371042962000195141)
        ·
          refine ⟨10786518819570555375036589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57528100371042962000195141 10786518819570555375036589)
          ·
            refine ⟨4044944557338958265638721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10786518819570555375036589 4044944557338958265638721)
            ·
              refine ⟨3033708418004218699229041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4044944557338958265638721 3033708418004218699229041)
              ·
                refine ⟨2275281313503164024421781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033708418004218699229041 2275281313503164024421781)
                ·
                  refine ⟨106653811570460813644771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2275281313503164024421781 106653811570460813644771)
                  ·
                    rfl

theorem cell23_1869368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 6].length) (baseStart_1869368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869368 prefixEnd_1869368 := by exact prefixLift 1869368
  have htrace : WordTrace (prefixWord ++ tailWord_1869368) baseStart_1869368 baseEnd_1869368 := by
    simpa [prefixWord, tailWord_1869368, baseEnd_1869368] using wordTrace_append hprefix tailTrace_1869368
  have hstable : (prefixWord ++ tailWord_1869368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869368).length < 2 ^ (prefixWord ++ tailWord_1869368).sum := by decide
  have hdescent : baseEnd_1869368 < baseStart_1869368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869372 : List Nat := [2, 2, 2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_1869372 : Nat := 118140960795 + 1869372 * 2 ^ 59
def prefixEnd_1869372 : Nat := 4983230072969 + 3 ^ 40 * 1869372 * 2
def baseEnd_1869372 : Nat := 319962119352255102384307

theorem tailTrace_1869372 : CollatzResearch.WordTrace tailWord_1869372 prefixEnd_1869372 319962119352255102384307 := by
  unfold tailWord_1869372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34090799091795991082429185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45454398789061321443238913 34090799091795991082429185)
  ·
    refine ⟨25568099318846993311821889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34090799091795991082429185 25568099318846993311821889)
    ·
      refine ⟨19176074489135244983866417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25568099318846993311821889 19176074489135244983866417)
      ·
        refine ⟨14382055866851433737899813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19176074489135244983866417 14382055866851433737899813)
        ·
          refine ⟨2696635475034643825856215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14382055866851433737899813 2696635475034643825856215)
          ·
            refine ⟨4044953212551965738784323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696635475034643825856215 4044953212551965738784323)
            ·
              refine ⟨6067429818827948608176485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044953212551965738784323 6067429818827948608176485)
              ·
                refine ⟨1137643091030240364033091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6067429818827948608176485 1137643091030240364033091)
                ·
                  refine ⟨1706464636545360546049637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137643091030240364033091 1706464636545360546049637)
                  ·
                    refine ⟨319962119352255102384307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1706464636545360546049637 319962119352255102384307)
                    ·
                      rfl

theorem cell23_1869372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_1869372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869372 prefixEnd_1869372 := by exact prefixLift 1869372
  have htrace : WordTrace (prefixWord ++ tailWord_1869372) baseStart_1869372 baseEnd_1869372 := by
    simpa [prefixWord, tailWord_1869372, baseEnd_1869372] using wordTrace_append hprefix tailTrace_1869372
  have hstable : (prefixWord ++ tailWord_1869372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869372).length < 2 ^ (prefixWord ++ tailWord_1869372).sum := by decide
  have hdescent : baseEnd_1869372 < baseStart_1869372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869381 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_1869381 : Nat := 118140960795 + 1869381 * 2 ^ 59
def prefixEnd_1869381 : Nat := 4983230072969 + 3 ^ 40 * 1869381 * 2
def baseEnd_1869381 : Nat := 319963659794218590646793

theorem tailTrace_1869381 : CollatzResearch.WordTrace tailWord_1869381 prefixEnd_1869381 319963659794218590646793 := by
  unfold tailWord_1869381
  simp only [CollatzResearch.WordTrace]
  refine ⟨68181926440559376701935997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45454617627039584467957331 68181926440559376701935997)
  ·
    refine ⟨25568222415209766263225999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68181926440559376701935997 25568222415209766263225999)
    ·
      refine ⟨38352333622814649394838999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25568222415209766263225999 38352333622814649394838999)
      ·
        refine ⟨57528500434221974092258499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38352333622814649394838999 57528500434221974092258499)
        ·
          refine ⟨86292750651332961138387749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57528500434221974092258499 86292750651332961138387749)
          ·
            refine ⟨16179890747124930213447703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86292750651332961138387749 16179890747124930213447703)
            ·
              refine ⟨24269836120687395320171555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16179890747124930213447703 24269836120687395320171555)
              ·
                refine ⟨36404754181031092980257333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24269836120687395320171555 36404754181031092980257333)
                ·
                  refine ⟨3412945704471664966899125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36404754181031092980257333 3412945704471664966899125)
                  ·
                    refine ⟨319963659794218590646793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3412945704471664966899125 319963659794218590646793)
                    ·
                      rfl

theorem cell23_1869381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_1869381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869381 prefixEnd_1869381 := by exact prefixLift 1869381
  have htrace : WordTrace (prefixWord ++ tailWord_1869381) baseStart_1869381 baseEnd_1869381 := by
    simpa [prefixWord, tailWord_1869381, baseEnd_1869381] using wordTrace_append hprefix tailTrace_1869381
  have hstable : (prefixWord ++ tailWord_1869381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869381).length < 2 ^ (prefixWord ++ tailWord_1869381).sum := by decide
  have hdescent : baseEnd_1869381 < baseStart_1869381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869412 : List Nat := [2, 3, 1, 1, 2, 3, 1, 5, 1, 1, 3]
def baseStart_1869412 : Nat := 118140960795 + 1869412 * 2 ^ 59
def prefixEnd_1869412 : Nat := 4983230072969 + 3 ^ 40 * 1869412 * 2
def baseEnd_1869412 : Nat := 959906897282945150652737

theorem tailTrace_1869412 : CollatzResearch.WordTrace tailWord_1869412 prefixEnd_1869412 959906897282945150652737 := by
  unfold tailWord_1869412
  simp only [CollatzResearch.WordTrace]
  refine ⟨34091528551723534498157245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45455371402298045997542993 34091528551723534498157245)
  ·
    refine ⟨12784323206896325436808967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34091528551723534498157245 12784323206896325436808967)
    ·
      refine ⟨19176484810344488155213451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12784323206896325436808967 19176484810344488155213451)
      ·
        refine ⟨28764727215516732232820177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19176484810344488155213451 28764727215516732232820177)
        ·
          refine ⟨21573545411637549174615133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28764727215516732232820177 21573545411637549174615133)
          ·
            refine ⟨8090079529364080940480675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21573545411637549174615133 8090079529364080940480675)
            ·
              refine ⟨12135119294046121410721013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8090079529364080940480675 12135119294046121410721013)
              ·
                refine ⟨1137667433816823882255095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12135119294046121410721013 1137667433816823882255095)
                ·
                  refine ⟨1706501150725235823382643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137667433816823882255095 1706501150725235823382643)
                  ·
                    refine ⟨2559751726087853735073965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1706501150725235823382643 2559751726087853735073965)
                    ·
                      refine ⟨959906897282945150652737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2559751726087853735073965 959906897282945150652737)
                      ·
                        rfl

theorem cell23_1869412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_1869412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869412 prefixEnd_1869412 := by exact prefixLift 1869412
  have htrace : WordTrace (prefixWord ++ tailWord_1869412) baseStart_1869412 baseEnd_1869412 := by
    simpa [prefixWord, tailWord_1869412, baseEnd_1869412] using wordTrace_append hprefix tailTrace_1869412
  have hstable : (prefixWord ++ tailWord_1869412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869412).length < 2 ^ (prefixWord ++ tailWord_1869412).sum := by decide
  have hdescent : baseEnd_1869412 < baseStart_1869412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869415 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 1, 5]
def baseStart_1869415 : Nat := 118140960795 + 1869415 * 2 ^ 59
def prefixEnd_1869415 : Nat := 4983230072969 + 3 ^ 40 * 1869415 * 2
def baseEnd_1869415 : Nat := 319969479241636212971741

theorem tailTrace_1869415 : CollatzResearch.WordTrace tailWord_1869415 prefixEnd_1869415 319969479241636212971741 := by
  unfold tailWord_1869415
  simp only [CollatzResearch.WordTrace]
  refine ⟨68183166522436200508673699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45455444348290800339115799 68183166522436200508673699)
  ·
    refine ⟨102274749783654300763010549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68183166522436200508673699 102274749783654300763010549)
    ·
      refine ⟨9588257792217590696532239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102274749783654300763010549 9588257792217590696532239)
      ·
        refine ⟨14382386688326386044798359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9588257792217590696532239 14382386688326386044798359)
        ·
          refine ⟨21573580032489579067197539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14382386688326386044798359 21573580032489579067197539)
          ·
            refine ⟨32360370048734368600796309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21573580032489579067197539 32360370048734368600796309)
            ·
              refine ⟨1516892346034423528162327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32360370048734368600796309 1516892346034423528162327)
              ·
                refine ⟨2275338519051635292243491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516892346034423528162327 2275338519051635292243491)
                ·
                  refine ⟨3413007778577452938365237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275338519051635292243491 3413007778577452938365237)
                  ·
                    refine ⟨319969479241636212971741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3413007778577452938365237 319969479241636212971741)
                    ·
                      rfl

theorem cell23_1869415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_1869415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869415 prefixEnd_1869415 := by exact prefixLift 1869415
  have htrace : WordTrace (prefixWord ++ tailWord_1869415) baseStart_1869415 baseEnd_1869415 := by
    simpa [prefixWord, tailWord_1869415, baseEnd_1869415] using wordTrace_append hprefix tailTrace_1869415
  have hstable : (prefixWord ++ tailWord_1869415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869415).length < 2 ^ (prefixWord ++ tailWord_1869415).sum := by decide
  have hdescent : baseEnd_1869415 < baseStart_1869415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869429 : List Nat := [1, 3, 4, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1869429 : Nat := 118140960795 + 1869429 * 2 ^ 59
def prefixEnd_1869429 : Nat := 4983230072969 + 3 ^ 40 * 1869429 * 2
def baseEnd_1869429 : Nat := 959915626454071584140159

theorem tailTrace_1869429 : CollatzResearch.WordTrace tailWord_1869429 prefixEnd_1869429 959915626454071584140159 := by
  unfold tailWord_1869429
  simp only [CollatzResearch.WordTrace]
  refine ⟨68183677144385480899683341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45455784762923653933122227 68183677144385480899683341)
  ·
    refine ⟨25568878929144555337381253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68183677144385480899683341 25568878929144555337381253)
    ·
      refine ⟨4794164799214604125758985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25568878929144555337381253 4794164799214604125758985)
      ·
        refine ⟨3595623599410953094319239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4794164799214604125758985 3595623599410953094319239)
        ·
          refine ⟨5393435399116429641478859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595623599410953094319239 5393435399116429641478859)
          ·
            refine ⟨8090153098674644462218289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393435399116429641478859 8090153098674644462218289)
            ·
              refine ⟨6067614824005983346663717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8090153098674644462218289 6067614824005983346663717)
              ·
                refine ⟨1137677779501121877499447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6067614824005983346663717 1137677779501121877499447)
                ·
                  refine ⟨1706516669251682816249171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137677779501121877499447 1706516669251682816249171)
                  ·
                    refine ⟨2559775003877524224373757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1706516669251682816249171 2559775003877524224373757)
                    ·
                      refine ⟨959915626454071584140159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2559775003877524224373757 959915626454071584140159)
                      ·
                        rfl

theorem cell23_1869429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1869429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869429 prefixEnd_1869429 := by exact prefixLift 1869429
  have htrace : WordTrace (prefixWord ++ tailWord_1869429) baseStart_1869429 baseEnd_1869429 := by
    simpa [prefixWord, tailWord_1869429, baseEnd_1869429] using wordTrace_append hprefix tailTrace_1869429
  have hstable : (prefixWord ++ tailWord_1869429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869429).length < 2 ^ (prefixWord ++ tailWord_1869429).sum := by decide
  have hdescent : baseEnd_1869429 < baseStart_1869429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869431 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_1869431 : Nat := 118140960795 + 1869431 * 2 ^ 59
def prefixEnd_1869431 : Nat := 4983230072969 + 3 ^ 40 * 1869431 * 2
def baseEnd_1869431 : Nat := 959916653415380576315149

theorem tailTrace_1869431 : CollatzResearch.WordTrace tailWord_1869431 prefixEnd_1869431 959916653415380576315149 := by
  unfold tailWord_1869431
  simp only [CollatzResearch.WordTrace]
  refine ⟨68183750090378235241256147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45455833393585490160837431 68183750090378235241256147)
  ·
    refine ⟨102275625135567352861884221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68183750090378235241256147 102275625135567352861884221)
    ·
      refine ⟨38353359425837757323206583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102275625135567352861884221 38353359425837757323206583)
      ·
        refine ⟨57530039138756635984809875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38353359425837757323206583 57530039138756635984809875)
        ·
          refine ⟨86295058708134953977214813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57530039138756635984809875 86295058708134953977214813)
          ·
            refine ⟨32360647015550607741455555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86295058708134953977214813 32360647015550607741455555)
            ·
              refine ⟨48540970523325911612183333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32360647015550607741455555 48540970523325911612183333)
              ·
                refine ⟨9101431973123608427284375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48540970523325911612183333 9101431973123608427284375)
                ·
                  refine ⟨13652147959685412640926563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9101431973123608427284375 13652147959685412640926563)
                  ·
                    refine ⟨20478221939528118961389845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13652147959685412640926563 20478221939528118961389845)
                    ·
                      refine ⟨959916653415380576315149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20478221939528118961389845 959916653415380576315149)
                      ·
                        rfl

theorem cell23_1869431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_1869431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869431 prefixEnd_1869431 := by exact prefixLift 1869431
  have htrace : WordTrace (prefixWord ++ tailWord_1869431) baseStart_1869431 baseEnd_1869431 := by
    simpa [prefixWord, tailWord_1869431, baseEnd_1869431] using wordTrace_append hprefix tailTrace_1869431
  have hstable : (prefixWord ++ tailWord_1869431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869431).length < 2 ^ (prefixWord ++ tailWord_1869431).sum := by decide
  have hdescent : baseEnd_1869431 < baseStart_1869431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869461 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1869461 : Nat := 118140960795 + 1869461 * 2 ^ 59
def prefixEnd_1869461 : Nat := 4983230072969 + 3 ^ 40 * 1869461 * 2
def baseEnd_1869461 : Nat := 959932057835015458940011

theorem tailTrace_1869461 : CollatzResearch.WordTrace tailWord_1869461 prefixEnd_1869461 959932057835015458940011 := by
  unfold tailWord_1869461
  simp only [CollatzResearch.WordTrace]
  refine ⟨68184844280269550364848237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45456562853513033576565491 68184844280269550364848237)
  ·
    refine ⟨25569316605101081386818089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68184844280269550364848237 25569316605101081386818089)
    ·
      refine ⟨19176987453825811040113567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25569316605101081386818089 19176987453825811040113567)
      ·
        refine ⟨28765481180738716560170351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19176987453825811040113567 28765481180738716560170351)
        ·
          refine ⟨43148221771108074840255527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28765481180738716560170351 43148221771108074840255527)
          ·
            refine ⟨64722332656662112260383291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43148221771108074840255527 64722332656662112260383291)
            ·
              refine ⟨97083498984993168390574937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64722332656662112260383291 97083498984993168390574937)
              ·
                refine ⟨72812624238744876292931203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97083498984993168390574937 72812624238744876292931203)
                ·
                  refine ⟨109218936358117314439396805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72812624238744876292931203 109218936358117314439396805)
                  ·
                    refine ⟨20478550567146996457386901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109218936358117314439396805 20478550567146996457386901)
                    ·
                      refine ⟨959932057835015458940011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20478550567146996457386901 959932057835015458940011)
                      ·
                        rfl

theorem cell23_1869461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1869461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869461 prefixEnd_1869461 := by exact prefixLift 1869461
  have htrace : WordTrace (prefixWord ++ tailWord_1869461) baseStart_1869461 baseEnd_1869461 := by
    simpa [prefixWord, tailWord_1869461, baseEnd_1869461] using wordTrace_append hprefix tailTrace_1869461
  have hstable : (prefixWord ++ tailWord_1869461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869461).length < 2 ^ (prefixWord ++ tailWord_1869461).sum := by decide
  have hdescent : baseEnd_1869461 < baseStart_1869461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869480 : List Nat := [2, 1, 7, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1869480 : Nat := 118140960795 + 1869480 * 2 ^ 59
def prefixEnd_1869480 : Nat := 4983230072969 + 3 ^ 40 * 1869480 * 2
def baseEnd_1869480 : Nat := 959941813967450884602425

theorem tailTrace_1869480 : CollatzResearch.WordTrace tailWord_1869480 prefixEnd_1869480 959941813967450884602425 := by
  unfold tailWord_1869480
  simp only [CollatzResearch.WordTrace]
  refine ⟨34092768633600358304894947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45457024844800477739859929 34092768633600358304894947)
  ·
    refine ⟨51139152950400537457342421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34092768633600358304894947 51139152950400537457342421)
    ·
      refine ⟨1198573897275012596656463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 51139152950400537457342421 1198573897275012596656463)
      ·
        refine ⟨1797860845912518894984695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1198573897275012596656463 1797860845912518894984695)
        ·
          refine ⟨2696791268868778342477043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797860845912518894984695 2696791268868778342477043)
          ·
            refine ⟨4045186903303167513715565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696791268868778342477043 4045186903303167513715565)
            ·
              refine ⟨1516945088738687817643337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4045186903303167513715565 1516945088738687817643337)
              ·
                refine ⟨1137708816554015863232503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516945088738687817643337 1137708816554015863232503)
                ·
                  refine ⟨1706563224831023794848755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137708816554015863232503 1706563224831023794848755)
                  ·
                    refine ⟨2559844837246535692273133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1706563224831023794848755 2559844837246535692273133)
                    ·
                      refine ⟨959941813967450884602425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2559844837246535692273133 959941813967450884602425)
                      ·
                        rfl

theorem cell23_1869480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1869480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869480 prefixEnd_1869480 := by exact prefixLift 1869480
  have htrace : WordTrace (prefixWord ++ tailWord_1869480) baseStart_1869480 baseEnd_1869480 := by
    simpa [prefixWord, tailWord_1869480, baseEnd_1869480] using wordTrace_append hprefix tailTrace_1869480
  have hstable : (prefixWord ++ tailWord_1869480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869480).length < 2 ^ (prefixWord ++ tailWord_1869480).sum := by decide
  have hdescent : baseEnd_1869480 < baseStart_1869480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869481 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_1869481 : Nat := 118140960795 + 1869481 * 2 ^ 59
def prefixEnd_1869481 : Nat := 4983230072969 + 3 ^ 40 * 1869481 * 2
def baseEnd_1869481 : Nat := 959942327448105380689919

theorem tailTrace_1869481 : CollatzResearch.WordTrace tailWord_1869481 prefixEnd_1869481 959942327448105380689919 := by
  unfold tailWord_1869481
  simp only [CollatzResearch.WordTrace]
  refine ⟨68185573740197093780576297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45457049160131395853717531 68185573740197093780576297)
  ·
    refine ⟨51139180305147820335432223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68185573740197093780576297 51139180305147820335432223)
    ·
      refine ⟨76708770457721730503148335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51139180305147820335432223 76708770457721730503148335)
      ·
        refine ⟨115063155686582595754722503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76708770457721730503148335 115063155686582595754722503)
        ·
          refine ⟨172594733529873893632083755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115063155686582595754722503 172594733529873893632083755)
          ·
            refine ⟨258892100294810840448125633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172594733529873893632083755 258892100294810840448125633)
            ·
              refine ⟨194169075221108130336094225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258892100294810840448125633 194169075221108130336094225)
              ·
                refine ⟨145626806415831097752070669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194169075221108130336094225 145626806415831097752070669)
                ·
                  refine ⟨54610052405936661657026501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145626806415831097752070669 54610052405936661657026501)
                  ·
                    refine ⟨10239384826113124060692469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54610052405936661657026501 10239384826113124060692469)
                    ·
                      refine ⟨959942327448105380689919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10239384826113124060692469 959942327448105380689919)
                      ·
                        rfl

theorem cell23_1869481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_1869481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869481 prefixEnd_1869481 := by exact prefixLift 1869481
  have htrace : WordTrace (prefixWord ++ tailWord_1869481) baseStart_1869481 baseEnd_1869481 := by
    simpa [prefixWord, tailWord_1869481, baseEnd_1869481] using wordTrace_append hprefix tailTrace_1869481
  have hstable : (prefixWord ++ tailWord_1869481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869481).length < 2 ^ (prefixWord ++ tailWord_1869481).sum := by decide
  have hdescent : baseEnd_1869481 < baseStart_1869481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869506 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1869506 : Nat := 118140960795 + 1869506 * 2 ^ 59
def prefixEnd_1869506 : Nat := 4983230072969 + 3 ^ 40 * 1869506 * 2
def baseEnd_1869506 : Nat := 959955164464467782877305

theorem tailTrace_1869506 : CollatzResearch.WordTrace tailWord_1869506 prefixEnd_1869506 959955164464467782877305 := by
  unfold tailWord_1869506
  simp only [CollatzResearch.WordTrace]
  refine ⟨17046621391276630762559093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45457657043404348700157581 17046621391276630762559093)
  ·
    refine ⟨1598120755432184133989915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17046621391276630762559093 1598120755432184133989915)
    ·
      refine ⟨2397181133148276200984873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1598120755432184133989915 2397181133148276200984873)
      ·
        refine ⟨1797885849861207150738655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2397181133148276200984873 1797885849861207150738655)
        ·
          refine ⟨2696828774791810726107983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797885849861207150738655 2696828774791810726107983)
          ·
            refine ⟨4045243162187716089161975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696828774791810726107983 4045243162187716089161975)
            ·
              refine ⟨6067864743281574133742963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045243162187716089161975 6067864743281574133742963)
              ·
                refine ⟨9101797114922361200614445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067864743281574133742963 9101797114922361200614445)
                ·
                  refine ⟨3413173918095885450230417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9101797114922361200614445 3413173918095885450230417)
                  ·
                    refine ⟨2559880438571914087672813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3413173918095885450230417 2559880438571914087672813)
                    ·
                      refine ⟨959955164464467782877305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2559880438571914087672813 959955164464467782877305)
                      ·
                        rfl

theorem cell23_1869506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1869506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869506 prefixEnd_1869506 := by exact prefixLift 1869506
  have htrace : WordTrace (prefixWord ++ tailWord_1869506) baseStart_1869506 baseEnd_1869506 := by
    simpa [prefixWord, tailWord_1869506, baseEnd_1869506] using wordTrace_append hprefix tailTrace_1869506
  have hstable : (prefixWord ++ tailWord_1869506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869506).length < 2 ^ (prefixWord ++ tailWord_1869506).sum := by decide
  have hdescent : baseEnd_1869506 < baseStart_1869506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869528 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1869528 : Nat := 118140960795 + 1869528 * 2 ^ 59
def prefixEnd_1869528 : Nat := 4983230072969 + 3 ^ 40 * 1869528 * 2
def baseEnd_1869528 : Nat := 959966461038866696802203

theorem tailTrace_1869528 : CollatzResearch.WordTrace tailWord_1869528 prefixEnd_1869528 959966461038866696802203 := by
  unfold tailWord_1869528
  simp only [CollatzResearch.WordTrace]
  refine ⟨34093643985513410403768619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45458191980684547205024825 34093643985513410403768619)
  ·
    refine ⟨51140465978270115605652929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34093643985513410403768619 51140465978270115605652929)
    ·
      refine ⟨38355349483702586704239697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51140465978270115605652929 38355349483702586704239697)
      ·
        refine ⟨28766512112776940028179773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38355349483702586704239697 28766512112776940028179773)
        ·
          refine ⟨10787442042291352510567415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28766512112776940028179773 10787442042291352510567415)
          ·
            refine ⟨16181163063437028765851123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10787442042291352510567415 16181163063437028765851123)
            ·
              refine ⟨24271744595155543148776685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16181163063437028765851123 24271744595155543148776685)
              ·
                refine ⟨9101904223183328680791257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24271744595155543148776685 9101904223183328680791257)
                ·
                  refine ⟨6826428167387496510593443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9101904223183328680791257 6826428167387496510593443)
                  ·
                    refine ⟨10239642251081244765890165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6826428167387496510593443 10239642251081244765890165)
                    ·
                      refine ⟨959966461038866696802203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10239642251081244765890165 959966461038866696802203)
                      ·
                        rfl

theorem cell23_1869528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1869528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869528 prefixEnd_1869528 := by exact prefixLift 1869528
  have htrace : WordTrace (prefixWord ++ tailWord_1869528) baseStart_1869528 baseEnd_1869528 := by
    simpa [prefixWord, tailWord_1869528, baseEnd_1869528] using wordTrace_append hprefix tailTrace_1869528
  have hstable : (prefixWord ++ tailWord_1869528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869528).length < 2 ^ (prefixWord ++ tailWord_1869528).sum := by decide
  have hdescent : baseEnd_1869528 < baseStart_1869528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869529 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 1, 3, 2]
def baseStart_1869529 : Nat := 118140960795 + 1869529 * 2 ^ 59
def prefixEnd_1869529 : Nat := 4983230072969 + 3 ^ 40 * 1869529 * 2
def baseEnd_1869529 : Nat := 959966974519521192889699

theorem tailTrace_1869529 : CollatzResearch.WordTrace tailWord_1869529 prefixEnd_1869529 959966974519521192889699 := by
  unfold tailWord_1869529
  simp only [CollatzResearch.WordTrace]
  refine ⟨68187324444023197978323641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45458216296015465318882427 68187324444023197978323641)
  ·
    refine ⟨51140493333017398483742731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68187324444023197978323641 51140493333017398483742731)
    ·
      refine ⟨76710739999526097725614097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51140493333017398483742731 76710739999526097725614097)
      ·
        refine ⟨57533054999644573294210573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76710739999526097725614097 57533054999644573294210573)
        ·
          refine ⟨21574895624866714985328965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57533054999644573294210573 21574895624866714985328965)
          ·
            refine ⟨4045292929662509059749181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21574895624866714985328965 4045292929662509059749181)
            ·
              refine ⟨1516984848623440897405943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4045292929662509059749181 1516984848623440897405943)
              ·
                refine ⟨2275477272935161346108915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516984848623440897405943 2275477272935161346108915)
                ·
                  refine ⟨3413215909402742019163373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275477272935161346108915 3413215909402742019163373)
                  ·
                    refine ⟨1279955966026028257186265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413215909402742019163373 1279955966026028257186265)
                    ·
                      refine ⟨959966974519521192889699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1279955966026028257186265 959966974519521192889699)
                      ·
                        rfl

theorem cell23_1869529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_1869529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869529 prefixEnd_1869529 := by exact prefixLift 1869529
  have htrace : WordTrace (prefixWord ++ tailWord_1869529) baseStart_1869529 baseEnd_1869529 := by
    simpa [prefixWord, tailWord_1869529, baseEnd_1869529] using wordTrace_append hprefix tailTrace_1869529
  have hstable : (prefixWord ++ tailWord_1869529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869529).length < 2 ^ (prefixWord ++ tailWord_1869529).sum := by decide
  have hdescent : baseEnd_1869529 < baseStart_1869529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869574 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1869574 : Nat := 118140960795 + 1869574 * 2 ^ 59
def prefixEnd_1869574 : Nat := 4983230072969 + 3 ^ 40 * 1869574 * 2
def baseEnd_1869574 : Nat := 959990081148973516826993

theorem tailTrace_1869574 : CollatzResearch.WordTrace tailWord_1869574 prefixEnd_1869574 959990081148973516826993 := by
  unfold tailWord_1869574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130905179026880333240993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45459310485906780442474517 2130905179026880333240993)
  ·
    refine ⟨1598178884270160249930745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2130905179026880333240993 1598178884270160249930745)
    ·
      refine ⟨1198634163202620187448059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1598178884270160249930745 1198634163202620187448059)
      ·
        refine ⟨1797951244803930281172089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1198634163202620187448059 1797951244803930281172089)
        ·
          refine ⟨1348463433602947710879067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1797951244803930281172089 1348463433602947710879067)
          ·
            refine ⟨2022695150404421566318601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348463433602947710879067 2022695150404421566318601)
            ·
              refine ⟨1517021362803316174738951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022695150404421566318601 1517021362803316174738951)
              ·
                refine ⟨2275532044204974262108427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517021362803316174738951 2275532044204974262108427)
                ·
                  refine ⟨3413298066307461393162641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275532044204974262108427 3413298066307461393162641)
                  ·
                    refine ⟨2559973549730596044871981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3413298066307461393162641 2559973549730596044871981)
                    ·
                      refine ⟨959990081148973516826993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2559973549730596044871981 959990081148973516826993)
                      ·
                        rfl

theorem cell23_1869574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1869574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869574 prefixEnd_1869574 := by exact prefixLift 1869574
  have htrace : WordTrace (prefixWord ++ tailWord_1869574) baseStart_1869574 baseEnd_1869574 := by
    simpa [prefixWord, tailWord_1869574, baseEnd_1869574] using wordTrace_append hprefix tailTrace_1869574
  have hstable : (prefixWord ++ tailWord_1869574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869574).length < 2 ^ (prefixWord ++ tailWord_1869574).sum := by decide
  have hdescent : baseEnd_1869574 < baseStart_1869574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869635 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 3]
def baseStart_1869635 : Nat := 118140960795 + 1869635 * 2 ^ 59
def prefixEnd_1869635 : Nat := 4983230072969 + 3 ^ 40 * 1869635 * 2
def baseEnd_1869635 : Nat := 960021403468897778164211

theorem tailTrace_1869635 : CollatzResearch.WordTrace tailWord_1869635 prefixEnd_1869635 960021403468897778164211 := by
  unfold tailWord_1869635
  simp only [CollatzResearch.WordTrace]
  refine ⟨68191190581639178081682359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45460793721092785387788239 68191190581639178081682359)
  ·
    refine ⟨102286785872458767122523539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68191190581639178081682359 102286785872458767122523539)
    ·
      refine ⟨153430178808688150683785309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102286785872458767122523539 153430178808688150683785309)
      ·
        refine ⟨57536317053258056506419491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153430178808688150683785309 57536317053258056506419491)
        ·
          refine ⟨86304475579887084759629237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57536317053258056506419491 86304475579887084759629237)
          ·
            refine ⟨8091044585614414196215241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86304475579887084759629237 8091044585614414196215241)
            ·
              refine ⟨6068283439210810647161431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8091044585614414196215241 6068283439210810647161431)
              ·
                refine ⟨9102425158816215970742147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068283439210810647161431 9102425158816215970742147)
                ·
                  refine ⟨13653637738224323956113221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9102425158816215970742147 13653637738224323956113221)
                  ·
                    refine ⟨2560057075917060741771229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13653637738224323956113221 2560057075917060741771229)
                    ·
                      refine ⟨960021403468897778164211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2560057075917060741771229 960021403468897778164211)
                      ·
                        rfl

theorem cell23_1869635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_1869635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869635 prefixEnd_1869635 := by exact prefixLift 1869635
  have htrace : WordTrace (prefixWord ++ tailWord_1869635) baseStart_1869635 baseEnd_1869635 := by
    simpa [prefixWord, tailWord_1869635, baseEnd_1869635] using wordTrace_append hprefix tailTrace_1869635
  have hstable : (prefixWord ++ tailWord_1869635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869635).length < 2 ^ (prefixWord ++ tailWord_1869635).sum := by decide
  have hdescent : baseEnd_1869635 < baseStart_1869635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869652 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_1869652 : Nat := 118140960795 + 1869652 * 2 ^ 59
def prefixEnd_1869652 : Nat := 4983230072969 + 3 ^ 40 * 1869652 * 2
def baseEnd_1869652 : Nat := 960030132640024211651633

theorem tailTrace_1869652 : CollatzResearch.WordTrace tailWord_1869652 prefixEnd_1869652 960030132640024211651633 := by
  unfold tailWord_1869652
  simp only [CollatzResearch.WordTrace]
  refine ⟨34095905311288794992525605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45461207081718393323367473 34095905311288794992525605)
  ·
    refine ⟨6392982245866649061098551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34095905311288794992525605 6392982245866649061098551)
    ·
      refine ⟨9589473368799973591647827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6392982245866649061098551 9589473368799973591647827)
      ·
        refine ⟨14384210053199960387471741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9589473368799973591647827 14384210053199960387471741)
        ·
          refine ⟨5394078769949985145301903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14384210053199960387471741 5394078769949985145301903)
          ·
            refine ⟨8091118154924977717952855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394078769949985145301903 8091118154924977717952855)
            ·
              refine ⟨12136677232387466576929283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8091118154924977717952855 12136677232387466576929283)
              ·
                refine ⟨18205015848581199865393925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12136677232387466576929283 18205015848581199865393925)
                ·
                  refine ⟨3413440471608974974761361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18205015848581199865393925 3413440471608974974761361)
                  ·
                    refine ⟨2560080353706731231071021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3413440471608974974761361 2560080353706731231071021)
                    ·
                      refine ⟨960030132640024211651633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2560080353706731231071021 960030132640024211651633)
                      ·
                        rfl

theorem cell23_1869652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_1869652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869652 prefixEnd_1869652 := by exact prefixLift 1869652
  have htrace : WordTrace (prefixWord ++ tailWord_1869652) baseStart_1869652 baseEnd_1869652 := by
    simpa [prefixWord, tailWord_1869652, baseEnd_1869652] using wordTrace_append hprefix tailTrace_1869652
  have hstable : (prefixWord ++ tailWord_1869652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869652).length < 2 ^ (prefixWord ++ tailWord_1869652).sum := by decide
  have hdescent : baseEnd_1869652 < baseStart_1869652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869682 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_1869682 : Nat := 118140960795 + 1869682 * 2 ^ 59
def prefixEnd_1869682 : Nat := 4983230072969 + 3 ^ 40 * 1869682 * 2
def baseEnd_1869682 : Nat := 960045537059659094276495

theorem tailTrace_1869682 : CollatzResearch.WordTrace tailWord_1869682 prefixEnd_1869682 960045537059659094276495 := by
  unfold tailWord_1869682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17048226203117226277160825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45461936541645936739095533 17048226203117226277160825)
  ·
    refine ⟨12786169652337919707870619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17048226203117226277160825 12786169652337919707870619)
    ·
      refine ⟨19179254478506879561805929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12786169652337919707870619 19179254478506879561805929)
      ·
        refine ⟨14384440858880159671354447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19179254478506879561805929 14384440858880159671354447)
        ·
          refine ⟨21576661288320239507031671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14384440858880159671354447 21576661288320239507031671)
          ·
            refine ⟨32364991932480359260547507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21576661288320239507031671 32364991932480359260547507)
            ·
              refine ⟨48547487898720538890821261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32364991932480359260547507 48547487898720538890821261)
              ·
                refine ⟨18205307962020202084057973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48547487898720538890821261 18205307962020202084057973)
                ·
                  refine ⟨1706747621439393945380435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18205307962020202084057973 1706747621439393945380435)
                  ·
                    refine ⟨2560121432159090918070653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1706747621439393945380435 2560121432159090918070653)
                    ·
                      refine ⟨960045537059659094276495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2560121432159090918070653 960045537059659094276495)
                      ·
                        rfl

theorem cell23_1869682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_1869682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869682 prefixEnd_1869682 := by exact prefixLift 1869682
  have htrace : WordTrace (prefixWord ++ tailWord_1869682) baseStart_1869682 baseEnd_1869682 := by
    simpa [prefixWord, tailWord_1869682, baseEnd_1869682] using wordTrace_append hprefix tailTrace_1869682
  have hstable : (prefixWord ++ tailWord_1869682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869682).length < 2 ^ (prefixWord ++ tailWord_1869682).sum := by decide
  have hdescent : baseEnd_1869682 < baseStart_1869682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869686 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1869686 : Nat := 118140960795 + 1869686 * 2 ^ 59
def prefixEnd_1869686 : Nat := 4983230072969 + 3 ^ 40 * 1869686 * 2
def baseEnd_1869686 : Nat := 960047590982277078626477

theorem tailTrace_1869686 : CollatzResearch.WordTrace tailWord_1869686 prefixEnd_1869686 960047590982277078626477 := by
  unfold tailWord_1869686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262065669028400861986807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45462033802969609194525941 4262065669028400861986807)
  ·
    refine ⟨6393098503542601292980211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4262065669028400861986807 6393098503542601292980211)
    ·
      refine ⟨9589647755313901939470317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6393098503542601292980211 9589647755313901939470317)
      ·
        refine ⟨3596117908242713227301369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9589647755313901939470317 3596117908242713227301369)
        ·
          refine ⟨2697088431182034920476027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596117908242713227301369 2697088431182034920476027)
          ·
            refine ⟨4045632646773052380714041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697088431182034920476027 4045632646773052380714041)
            ·
              refine ⟨3034224485079789285535531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4045632646773052380714041 3034224485079789285535531)
              ·
                refine ⟨4551336727619683928303297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034224485079789285535531 4551336727619683928303297)
                ·
                  refine ⟨3413502545714762946227473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4551336727619683928303297 3413502545714762946227473)
                  ·
                    refine ⟨2560126909286072209670605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3413502545714762946227473 2560126909286072209670605)
                    ·
                      refine ⟨960047590982277078626477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2560126909286072209670605 960047590982277078626477)
                      ·
                        rfl

theorem cell23_1869686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1869686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869686 prefixEnd_1869686 := by exact prefixLift 1869686
  have htrace : WordTrace (prefixWord ++ tailWord_1869686) baseStart_1869686 baseEnd_1869686 := by
    simpa [prefixWord, tailWord_1869686, baseEnd_1869686] using wordTrace_append hprefix tailTrace_1869686
  have hstable : (prefixWord ++ tailWord_1869686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869686).length < 2 ^ (prefixWord ++ tailWord_1869686).sum := by decide
  have hdescent : baseEnd_1869686 < baseStart_1869686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869710 : List Nat := [4, 1, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_1869710 : Nat := 118140960795 + 1869710 * 2 ^ 59
def prefixEnd_1869710 : Nat := 4983230072969 + 3 ^ 40 * 1869710 * 2
def baseEnd_1869710 : Nat := 320019971505994994908789

theorem tailTrace_1869710 : CollatzResearch.WordTrace tailWord_1869710 prefixEnd_1869710 320019971505994994908789 := by
  unfold tailWord_1869710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8524240757045933236332823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45462617370911643927108389 8524240757045933236332823)
  ·
    refine ⟨12786361135568899854499235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8524240757045933236332823 12786361135568899854499235)
    ·
      refine ⟨19179541703353349781748853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12786361135568899854499235 19179541703353349781748853)
      ·
        refine ⟨1798082034689376542038955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19179541703353349781748853 1798082034689376542038955)
        ·
          refine ⟨2697123052034064813058433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798082034689376542038955 2697123052034064813058433)
          ·
            refine ⟨2022842289025548609793825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2697123052034064813058433 2022842289025548609793825)
            ·
              refine ⟨1517131716769161457345369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022842289025548609793825 1517131716769161457345369)
              ·
                refine ⟨1137848787576871093009027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517131716769161457345369 1137848787576871093009027)
                ·
                  refine ⟨1706773181365306639513541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137848787576871093009027 1706773181365306639513541)
                  ·
                    refine ⟨320019971505994994908789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1706773181365306639513541 320019971505994994908789)
                    ·
                      rfl

theorem cell23_1869710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_1869710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869710 prefixEnd_1869710 := by exact prefixLift 1869710
  have htrace : WordTrace (prefixWord ++ tailWord_1869710) baseStart_1869710 baseEnd_1869710 := by
    simpa [prefixWord, tailWord_1869710, baseEnd_1869710] using wordTrace_append hprefix tailTrace_1869710
  have hstable : (prefixWord ++ tailWord_1869710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869710).length < 2 ^ (prefixWord ++ tailWord_1869710).sum := by decide
  have hdescent : baseEnd_1869710 < baseStart_1869710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869715 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 8, 4]
def baseStart_1869715 : Nat := 118140960795 + 1869715 * 2 ^ 59
def prefixEnd_1869715 : Nat := 4983230072969 + 3 ^ 40 * 1869715 * 2
def baseEnd_1869715 : Nat := 320020827307085821721281

theorem tailTrace_1869715 : CollatzResearch.WordTrace tailWord_1869715 prefixEnd_1869715 320020827307085821721281 := by
  unfold tailWord_1869715
  simp only [CollatzResearch.WordTrace]
  refine ⟨68194108421349351744594599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45462738947566234496396399 68194108421349351744594599)
  ·
    refine ⟨102291162632024027616891899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68194108421349351744594599 102291162632024027616891899)
    ·
      refine ⟨153436743948036041425337849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102291162632024027616891899 153436743948036041425337849)
      ·
        refine ⟨115077557961027031069003387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153436743948036041425337849 115077557961027031069003387)
        ·
          refine ⟨172616336941540546603505081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115077557961027031069003387 172616336941540546603505081)
          ·
            refine ⟨129462252706155409952628811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172616336941540546603505081 129462252706155409952628811)
            ·
              refine ⟨194193379059233114928943217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129462252706155409952628811 194193379059233114928943217)
              ·
                refine ⟨145645034294424836196707413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194193379059233114928943217 145645034294424836196707413)
                ·
                  refine ⟨1706777745637791049180165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 145645034294424836196707413 1706777745637791049180165)
                  ·
                    refine ⟨320020827307085821721281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1706777745637791049180165 320020827307085821721281)
                    ·
                      rfl

theorem cell23_1869715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 4].length) (baseStart_1869715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869715 prefixEnd_1869715 := by exact prefixLift 1869715
  have htrace : WordTrace (prefixWord ++ tailWord_1869715) baseStart_1869715 baseEnd_1869715 := by
    simpa [prefixWord, tailWord_1869715, baseEnd_1869715] using wordTrace_append hprefix tailTrace_1869715
  have hstable : (prefixWord ++ tailWord_1869715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869715).length < 2 ^ (prefixWord ++ tailWord_1869715).sum := by decide
  have hdescent : baseEnd_1869715 < baseStart_1869715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869722 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1869722 : Nat := 118140960795 + 1869722 * 2 ^ 59
def prefixEnd_1869722 : Nat := 4983230072969 + 3 ^ 40 * 1869722 * 2
def baseEnd_1869722 : Nat := 960066076285838937776311

theorem tailTrace_1869722 : CollatzResearch.WordTrace tailWord_1869722 prefixEnd_1869722 960066076285838937776311 := by
  unfold tailWord_1869722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17048590933080997985024855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45462909154882661293399613 17048590933080997985024855)
  ·
    refine ⟨25572886399621496977537283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17048590933080997985024855 25572886399621496977537283)
    ·
      refine ⟨38359329599432245466305925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25572886399621496977537283 38359329599432245466305925)
      ·
        refine ⟨7192374299893546024932361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38359329599432245466305925 7192374299893546024932361)
        ·
          refine ⟨5394280724920159518699271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7192374299893546024932361 5394280724920159518699271)
          ·
            refine ⟨8091421087380239278048907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394280724920159518699271 8091421087380239278048907)
            ·
              refine ⟨12137131631070358917073361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8091421087380239278048907 12137131631070358917073361)
              ·
                refine ⟨9102848723302769187805021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12137131631070358917073361 9102848723302769187805021)
                ·
                  refine ⟨3413568271238538445426883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9102848723302769187805021 3413568271238538445426883)
                  ·
                    refine ⟨5120352406857807668140325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3413568271238538445426883 5120352406857807668140325)
                    ·
                      refine ⟨960066076285838937776311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5120352406857807668140325 960066076285838937776311)
                      ·
                        rfl

theorem cell23_1869722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1869722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869722 prefixEnd_1869722 := by exact prefixLift 1869722
  have htrace : WordTrace (prefixWord ++ tailWord_1869722) baseStart_1869722 baseEnd_1869722 := by
    simpa [prefixWord, tailWord_1869722, baseEnd_1869722] using wordTrace_append hprefix tailTrace_1869722
  have hstable : (prefixWord ++ tailWord_1869722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869722).length < 2 ^ (prefixWord ++ tailWord_1869722).sum := by decide
  have hdescent : baseEnd_1869722 < baseStart_1869722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869732 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_1869732 : Nat := 118140960795 + 1869732 * 2 ^ 59
def prefixEnd_1869732 : Nat := 4983230072969 + 3 ^ 40 * 1869732 * 2
def baseEnd_1869732 : Nat := 320023737030794632883755

theorem tailTrace_1869732 : CollatzResearch.WordTrace tailWord_1869732 prefixEnd_1869732 320023737030794632883755 := by
  unfold tailWord_1869732
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097364231143881823981725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45463152308191842431975633 34097364231143881823981725)
  ·
    refine ⟨12786511586678955683993147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34097364231143881823981725 12786511586678955683993147)
    ·
      refine ⟨19179767380018433525989721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12786511586678955683993147 19179767380018433525989721)
      ·
        refine ⟨14384825535013825144492291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19179767380018433525989721 14384825535013825144492291)
        ·
          refine ⟨21577238302520737716738437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14384825535013825144492291 21577238302520737716738437)
          ·
            refine ⟨4045732181722638321888457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21577238302520737716738437 4045732181722638321888457)
            ·
              refine ⟨3034299136291978741416343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4045732181722638321888457 3034299136291978741416343)
              ·
                refine ⟨4551448704437968112124515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034299136291978741416343 4551448704437968112124515)
                ·
                  refine ⟨6827173056656952168186773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551448704437968112124515 6827173056656952168186773)
                  ·
                    refine ⟨320023737030794632883755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6827173056656952168186773 320023737030794632883755)
                    ·
                      rfl

theorem cell23_1869732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_1869732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869732 prefixEnd_1869732 := by exact prefixLift 1869732
  have htrace : WordTrace (prefixWord ++ tailWord_1869732) baseStart_1869732 baseEnd_1869732 := by
    simpa [prefixWord, tailWord_1869732, baseEnd_1869732] using wordTrace_append hprefix tailTrace_1869732
  have hstable : (prefixWord ++ tailWord_1869732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869732).length < 2 ^ (prefixWord ++ tailWord_1869732).sum := by decide
  have hdescent : baseEnd_1869732 < baseStart_1869732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869756 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1869756 : Nat := 118140960795 + 1869756 * 2 ^ 59
def prefixEnd_1869756 : Nat := 4983230072969 + 3 ^ 40 * 1869756 * 2
def baseEnd_1869756 : Nat := 960083534628091804751155

theorem tailTrace_1869756 : CollatzResearch.WordTrace tailWord_1869756 prefixEnd_1869756 960083534628091804751155 := by
  unfold tailWord_1869756
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097801907100407873418561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45463735876133877164558081 34097801907100407873418561)
  ·
    refine ⟨25573351430325305905063921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34097801907100407873418561 25573351430325305905063921)
    ·
      refine ⟨19180013572743979428797941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25573351430325305905063921 19180013572743979428797941)
      ·
        refine ⟨1798126272444748071449807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19180013572743979428797941 1798126272444748071449807)
        ·
          refine ⟨2697189408667122107174711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798126272444748071449807 2697189408667122107174711)
          ·
            refine ⟨4045784113000683160762067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697189408667122107174711 4045784113000683160762067)
            ·
              refine ⟨6068676169501024741143101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045784113000683160762067 6068676169501024741143101)
              ·
                refine ⟨2275753563562884277928663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6068676169501024741143101 2275753563562884277928663)
                ·
                  refine ⟨3413630345344326416892995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275753563562884277928663 3413630345344326416892995)
                  ·
                    refine ⟨5120445518016489625339493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3413630345344326416892995 5120445518016489625339493)
                    ·
                      refine ⟨960083534628091804751155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5120445518016489625339493 960083534628091804751155)
                      ·
                        rfl

theorem cell23_1869756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1869756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869756 prefixEnd_1869756 := by exact prefixLift 1869756
  have htrace : WordTrace (prefixWord ++ tailWord_1869756) baseStart_1869756 baseEnd_1869756 := by
    simpa [prefixWord, tailWord_1869756, baseEnd_1869756] using wordTrace_append hprefix tailTrace_1869756
  have hstable : (prefixWord ++ tailWord_1869756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869756).length < 2 ^ (prefixWord ++ tailWord_1869756).sum := by decide
  have hdescent : baseEnd_1869756 < baseStart_1869756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869786 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4]
def baseStart_1869786 : Nat := 118140960795 + 1869786 * 2 ^ 59
def prefixEnd_1869786 : Nat := 4983230072969 + 3 ^ 40 * 1869786 * 2
def baseEnd_1869786 : Nat := 960098939047726687376017

theorem tailTrace_1869786 : CollatzResearch.WordTrace tailWord_1869786 prefixEnd_1869786 960098939047726687376017 := by
  unfold tailWord_1869786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17049174501023032717607303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45464465336061420580286141 17049174501023032717607303)
  ·
    refine ⟨25573761751534549076410955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17049174501023032717607303 25573761751534549076410955)
    ·
      refine ⟨38360642627301823614616433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25573761751534549076410955 38360642627301823614616433)
      ·
        refine ⟨28770481970476367710962325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38360642627301823614616433 28770481970476367710962325)
        ·
          refine ⟨1348616342366079736451359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28770481970476367710962325 1348616342366079736451359)
          ·
            refine ⟨2022924513549119604677039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348616342366079736451359 2022924513549119604677039)
            ·
              refine ⟨3034386770323679407015559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022924513549119604677039 3034386770323679407015559)
              ·
                refine ⟨4551580155485519110523339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034386770323679407015559 4551580155485519110523339)
                ·
                  refine ⟨6827370233228278665785009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551580155485519110523339 6827370233228278665785009)
                  ·
                    refine ⟨5120527674921208999338757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6827370233228278665785009 5120527674921208999338757)
                    ·
                      refine ⟨960098939047726687376017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5120527674921208999338757 960098939047726687376017)
                      ·
                        rfl

theorem cell23_1869786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_1869786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869786 prefixEnd_1869786 := by exact prefixLift 1869786
  have htrace : WordTrace (prefixWord ++ tailWord_1869786) baseStart_1869786 baseEnd_1869786 := by
    simpa [prefixWord, tailWord_1869786, baseEnd_1869786] using wordTrace_append hprefix tailTrace_1869786
  have hstable : (prefixWord ++ tailWord_1869786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869786).length < 2 ^ (prefixWord ++ tailWord_1869786).sum := by decide
  have hdescent : baseEnd_1869786 < baseStart_1869786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869832 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1869832 : Nat := 118140960795 + 1869832 * 2 ^ 59
def prefixEnd_1869832 : Nat := 4983230072969 + 3 ^ 40 * 1869832 * 2
def baseEnd_1869832 : Nat := 960122559157833507400805

theorem tailTrace_1869832 : CollatzResearch.WordTrace tailWord_1869832 prefixEnd_1869832 960122559157833507400805 := by
  unfold tailWord_1869832
  simp only [CollatzResearch.WordTrace]
  refine ⟨34099187880962740363301875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45465583841283653817735833 34099187880962740363301875)
  ·
    refine ⟨51148781821444110544952813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34099187880962740363301875 51148781821444110544952813)
    ·
      refine ⟨19180793183041541454357305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51148781821444110544952813 19180793183041541454357305)
      ·
        refine ⟨14385594887281156090767979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19180793183041541454357305 14385594887281156090767979)
        ·
          refine ⟨21578392330921734136151969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14385594887281156090767979 21578392330921734136151969)
          ·
            refine ⟨16183794248191300602113977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21578392330921734136151969 16183794248191300602113977)
            ·
              refine ⟨12137845686143475451585483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16183794248191300602113977 12137845686143475451585483)
              ·
                refine ⟨18206768529215213177378225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12137845686143475451585483 18206768529215213177378225)
                ·
                  refine ⟨13655076396911409883033669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18206768529215213177378225 13655076396911409883033669)
                  ·
                    refine ⟨2560326824420889353068813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13655076396911409883033669 2560326824420889353068813)
                    ·
                      refine ⟨960122559157833507400805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2560326824420889353068813 960122559157833507400805)
                      ·
                        rfl

theorem cell23_1869832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1869832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869832 prefixEnd_1869832 := by exact prefixLift 1869832
  have htrace : WordTrace (prefixWord ++ tailWord_1869832) baseStart_1869832 baseEnd_1869832 := by
    simpa [prefixWord, tailWord_1869832, baseEnd_1869832] using wordTrace_append hprefix tailTrace_1869832
  have hstable : (prefixWord ++ tailWord_1869832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869832).length < 2 ^ (prefixWord ++ tailWord_1869832).sum := by decide
  have hdescent : baseEnd_1869832 < baseStart_1869832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869863 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_1869863 : Nat := 118140960795 + 1869863 * 2 ^ 59
def prefixEnd_1869863 : Nat := 4983230072969 + 3 ^ 40 * 1869863 * 2
def baseEnd_1869863 : Nat := 960138477058122886113163

theorem tailTrace_1869863 : CollatzResearch.WordTrace tailWord_1869863 prefixEnd_1869863 960138477058122886113163 := by
  unfold tailWord_1869863
  simp only [CollatzResearch.WordTrace]
  refine ⟨68199506424813173020982243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45466337616542115347321495 68199506424813173020982243)
  ·
    refine ⟨102299259637219759531473365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68199506424813173020982243 102299259637219759531473365)
    ·
      refine ⟨2397638897747338114018907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102299259637219759531473365 2397638897747338114018907)
      ·
        refine ⟨3596458346621007171028361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397638897747338114018907 3596458346621007171028361)
        ·
          refine ⟨2697343759965755378271271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596458346621007171028361 2697343759965755378271271)
          ·
            refine ⟨4046015639948633067406907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697343759965755378271271 4046015639948633067406907)
            ·
              refine ⟨6069023459922949601110361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046015639948633067406907 6069023459922949601110361)
              ·
                refine ⟨4551767594942212200832771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6069023459922949601110361 4551767594942212200832771)
                ·
                  refine ⟨6827651392413318301249157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4551767594942212200832771 6827651392413318301249157)
                  ·
                    refine ⟨1280184636077497181484217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6827651392413318301249157 1280184636077497181484217)
                    ·
                      refine ⟨960138477058122886113163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280184636077497181484217 960138477058122886113163)
                      ·
                        rfl

theorem cell23_1869863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_1869863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869863 prefixEnd_1869863 := by exact prefixLift 1869863
  have htrace : WordTrace (prefixWord ++ tailWord_1869863) baseStart_1869863 baseEnd_1869863 := by
    simpa [prefixWord, tailWord_1869863, baseEnd_1869863] using wordTrace_append hprefix tailTrace_1869863
  have hstable : (prefixWord ++ tailWord_1869863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869863).length < 2 ^ (prefixWord ++ tailWord_1869863).sum := by decide
  have hdescent : baseEnd_1869863 < baseStart_1869863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869865 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 7, 7]
def baseStart_1869865 : Nat := 118140960795 + 1869865 * 2 ^ 59
def prefixEnd_1869865 : Nat := 4983230072969 + 3 ^ 40 * 1869865 * 2
def baseEnd_1869865 : Nat := 320046501339810626096051

theorem tailTrace_1869865 : CollatzResearch.WordTrace tailWord_1869865 prefixEnd_1869865 320046501339810626096051 := by
  unfold tailWord_1869865
  simp only [CollatzResearch.WordTrace]
  refine ⟨68199579370805927362555049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45466386247203951575036699 68199579370805927362555049)
  ·
    refine ⟨51149684528104445521916287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68199579370805927362555049 51149684528104445521916287)
    ·
      refine ⟨76724526792156668282874431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51149684528104445521916287 76724526792156668282874431)
      ·
        refine ⟨115086790188235002424311647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76724526792156668282874431 115086790188235002424311647)
        ·
          refine ⟨172630185282352503636467471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115086790188235002424311647 172630185282352503636467471)
          ·
            refine ⟨258945277923528755454701207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172630185282352503636467471 258945277923528755454701207)
            ·
              refine ⟨388417916885293133182051811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258945277923528755454701207 388417916885293133182051811)
              ·
                refine ⟨582626875327939699773077717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388417916885293133182051811 582626875327939699773077717)
                ·
                  refine ⟨13655317390498586713431509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 582626875327939699773077717 13655317390498586713431509)
                  ·
                    refine ⟨320046501339810626096051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13655317390498586713431509 320046501339810626096051)
                    ·
                      rfl

theorem cell23_1869865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_1869865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869865 prefixEnd_1869865 := by exact prefixLift 1869865
  have htrace : WordTrace (prefixWord ++ tailWord_1869865) baseStart_1869865 baseEnd_1869865 := by
    simpa [prefixWord, tailWord_1869865, baseEnd_1869865] using wordTrace_append hprefix tailTrace_1869865
  have hstable : (prefixWord ++ tailWord_1869865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869865).length < 2 ^ (prefixWord ++ tailWord_1869865).sum := by decide
  have hdescent : baseEnd_1869865 < baseStart_1869865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869916 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1869916 : Nat := 118140960795 + 1869916 * 2 ^ 59
def prefixEnd_1869916 : Nat := 4983230072969 + 3 ^ 40 * 1869916 * 2
def baseEnd_1869916 : Nat := 320055230510937059583473

theorem tailTrace_1869916 : CollatzResearch.WordTrace tailWord_1869916 prefixEnd_1869916 320055230510937059583473 := by
  unfold tailWord_1869916
  simp only [CollatzResearch.WordTrace]
  refine ⟨34100719746810581536330801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45467626329080775381774401 34100719746810581536330801)
  ·
    refine ⟨25575539810107936152248101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34100719746810581536330801 25575539810107936152248101)
    ·
      refine ⟨4795413714395238028546519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25575539810107936152248101 4795413714395238028546519)
      ·
        refine ⟨7193120571592857042819779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795413714395238028546519 7193120571592857042819779)
        ·
          refine ⟨10789680857389285564229669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7193120571592857042819779 10789680857389285564229669)
          ·
            refine ⟨2023065160760491043293063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10789680857389285564229669 2023065160760491043293063)
            ·
              refine ⟨3034597741140736564939595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023065160760491043293063 3034597741140736564939595)
              ·
                refine ⟨4551896611711104847409393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034597741140736564939595 4551896611711104847409393)
                ·
                  refine ⟨3413922458783328635557045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4551896611711104847409393 3413922458783328635557045)
                  ·
                    refine ⟨320055230510937059583473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3413922458783328635557045 320055230510937059583473)
                    ·
                      rfl

theorem cell23_1869916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1869916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869916 prefixEnd_1869916 := by exact prefixLift 1869916
  have htrace : WordTrace (prefixWord ++ tailWord_1869916) baseStart_1869916 baseEnd_1869916 := by
    simpa [prefixWord, tailWord_1869916, baseEnd_1869916] using wordTrace_append hprefix tailTrace_1869916
  have hstable : (prefixWord ++ tailWord_1869916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869916).length < 2 ^ (prefixWord ++ tailWord_1869916).sum := by decide
  have hdescent : baseEnd_1869916 < baseStart_1869916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869932 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_1869932 : Nat := 118140960795 + 1869932 * 2 ^ 59
def prefixEnd_1869932 : Nat := 4983230072969 + 3 ^ 40 * 1869932 * 2
def baseEnd_1869932 : Nat := 960173907223283116150345

theorem tailTrace_1869932 : CollatzResearch.WordTrace tailWord_1869932 prefixEnd_1869932 960173907223283116150345 := by
  unfold tailWord_1869932
  simp only [CollatzResearch.WordTrace]
  refine ⟨34101011530781598902622025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45468015374375465203496033 34101011530781598902622025)
  ·
    refine ⟨25575758648086199176966519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34101011530781598902622025 25575758648086199176966519)
    ·
      refine ⟨38363637972129298765449779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25575758648086199176966519 38363637972129298765449779)
      ·
        refine ⟨57545456958193948148174669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38363637972129298765449779 57545456958193948148174669)
        ·
          refine ⟨21579546359322730555565501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57545456958193948148174669 21579546359322730555565501)
          ·
            refine ⟨8092329884746023958337063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21579546359322730555565501 8092329884746023958337063)
            ·
              refine ⟨12138494827119035937505595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092329884746023958337063 12138494827119035937505595)
              ·
                refine ⟨18207742240678553906258393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12138494827119035937505595 18207742240678553906258393)
                ·
                  refine ⟨13655806680508915429693795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18207742240678553906258393 13655806680508915429693795)
                  ·
                    refine ⟨20483710020763373144540693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13655806680508915429693795 20483710020763373144540693)
                    ·
                      refine ⟨960173907223283116150345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20483710020763373144540693 960173907223283116150345)
                      ·
                        rfl

theorem cell23_1869932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_1869932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869932 prefixEnd_1869932 := by exact prefixLift 1869932
  have htrace : WordTrace (prefixWord ++ tailWord_1869932) baseStart_1869932 baseEnd_1869932 := by
    simpa [prefixWord, tailWord_1869932, baseEnd_1869932] using wordTrace_append hprefix tailTrace_1869932
  have hstable : (prefixWord ++ tailWord_1869932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869932).length < 2 ^ (prefixWord ++ tailWord_1869932).sum := by decide
  have hdescent : baseEnd_1869932 < baseStart_1869932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869979 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 1, 5, 2]
def baseStart_1869979 : Nat := 118140960795 + 1869979 * 2 ^ 59
def prefixEnd_1869979 : Nat := 4983230072969 + 3 ^ 40 * 1869979 * 2
def baseEnd_1869979 : Nat := 960198040814044432262629

theorem tailTrace_1869979 : CollatzResearch.WordTrace tailWord_1869979 prefixEnd_1869979 960198040814044432262629 := by
  unfold tailWord_1869979
  simp only [CollatzResearch.WordTrace]
  refine ⟨68203737292392924832204991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45469158194928616554803327 68203737292392924832204991)
  ·
    refine ⟨102305605938589387248307487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68203737292392924832204991 102305605938589387248307487)
    ·
      refine ⟨153458408907884080872461231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102305605938589387248307487 153458408907884080872461231)
      ·
        refine ⟨230187613361826121308691847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153458408907884080872461231 230187613361826121308691847)
        ·
          refine ⟨345281420042739181963037771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230187613361826121308691847 345281420042739181963037771)
          ·
            refine ⟨517922130064108772944556657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345281420042739181963037771 517922130064108772944556657)
            ·
              refine ⟨388441597548081579708417493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517922130064108772944556657 388441597548081579708417493)
              ·
                refine ⟨9104099942533162024416035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 388441597548081579708417493 9104099942533162024416035)
                ·
                  refine ⟨13656149913799743036624053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9104099942533162024416035 13656149913799743036624053)
                  ·
                    refine ⟨1280264054418725909683505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13656149913799743036624053 1280264054418725909683505)
                    ·
                      refine ⟨960198040814044432262629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280264054418725909683505 960198040814044432262629)
                      ·
                        rfl

theorem cell23_1869979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 5, 2].length) (baseStart_1869979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869979 prefixEnd_1869979 := by exact prefixLift 1869979
  have htrace : WordTrace (prefixWord ++ tailWord_1869979) baseStart_1869979 baseEnd_1869979 := by
    simpa [prefixWord, tailWord_1869979, baseEnd_1869979] using wordTrace_append hprefix tailTrace_1869979
  have hstable : (prefixWord ++ tailWord_1869979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869979).length < 2 ^ (prefixWord ++ tailWord_1869979).sum := by decide
  have hdescent : baseEnd_1869979 < baseStart_1869979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869989 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_1869989 : Nat := 118140960795 + 1869989 * 2 ^ 59
def prefixEnd_1869989 : Nat := 4983230072969 + 3 ^ 40 * 1869989 * 2
def baseEnd_1869989 : Nat := 320067725206863131045861

theorem tailTrace_1869989 : CollatzResearch.WordTrace tailWord_1869989 prefixEnd_1869989 320067725206863131045861 := by
  unfold tailWord_1869989
  simp only [CollatzResearch.WordTrace]
  refine ⟨68204102022356696540069021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45469401348237797693379347 68204102022356696540069021)
  ·
    refine ⟨25576538258383761202525883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68204102022356696540069021 25576538258383761202525883)
    ·
      refine ⟨38364807387575641803788825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25576538258383761202525883 38364807387575641803788825)
      ·
        refine ⟨28773605540681731352841619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38364807387575641803788825 28773605540681731352841619)
        ·
          refine ⟨43160408311022597029262429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28773605540681731352841619 43160408311022597029262429)
          ·
            refine ⟨16185153116633473885973411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43160408311022597029262429 16185153116633473885973411)
            ·
              refine ⟨24277729674950210828960117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16185153116633473885973411 24277729674950210828960117)
              ·
                refine ⟨2276037157026582265215011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24277729674950210828960117 2276037157026582265215011)
                ·
                  refine ⟨3414055735539873397822517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276037157026582265215011 3414055735539873397822517)
                  ·
                    refine ⟨320067725206863131045861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3414055735539873397822517 320067725206863131045861)
                    ·
                      rfl

theorem cell23_1869989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_1869989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1869989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1869989 prefixEnd_1869989 := by exact prefixLift 1869989
  have htrace : WordTrace (prefixWord ++ tailWord_1869989) baseStart_1869989 baseEnd_1869989 := by
    simpa [prefixWord, tailWord_1869989, baseEnd_1869989] using wordTrace_append hprefix tailTrace_1869989
  have hstable : (prefixWord ++ tailWord_1869989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869989).length < 2 ^ (prefixWord ++ tailWord_1869989).sum := by decide
  have hdescent : baseEnd_1869989 < baseStart_1869989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870009 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1870009 : Nat := 118140960795 + 1870009 * 2 ^ 59
def prefixEnd_1870009 : Nat := 4983230072969 + 3 ^ 40 * 1870009 * 2
def baseEnd_1870009 : Nat := 960213445233679314887491

theorem tailTrace_1870009 : CollatzResearch.WordTrace tailWord_1870009 prefixEnd_1870009 960213445233679314887491 := by
  unfold tailWord_1870009
  simp only [CollatzResearch.WordTrace]
  refine ⟨68204831482284239955797081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45469887654856159970531387 68204831482284239955797081)
  ·
    refine ⟨51153623611713179966847811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68204831482284239955797081 51153623611713179966847811)
    ·
      refine ⟨76730435417569769950271717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51153623611713179966847811 76730435417569769950271717)
      ·
        refine ⟨14386956640794331865675947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76730435417569769950271717 14386956640794331865675947)
        ·
          refine ⟨21580434961191497798513921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14386956640794331865675947 21580434961191497798513921)
          ·
            refine ⟨16185326220893623348885441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21580434961191497798513921 16185326220893623348885441)
            ·
              refine ⟨12138994665670217511664081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16185326220893623348885441 12138994665670217511664081)
              ·
                refine ⟨9104245999252663133748061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12138994665670217511664081 9104245999252663133748061)
                ·
                  refine ⟨3414092249719748675155523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9104245999252663133748061 3414092249719748675155523)
                  ·
                    refine ⟨5121138374579623012733285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3414092249719748675155523 5121138374579623012733285)
                    ·
                      refine ⟨960213445233679314887491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5121138374579623012733285 960213445233679314887491)
                      ·
                        rfl

theorem cell23_1870009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1870009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870009 prefixEnd_1870009 := by exact prefixLift 1870009
  have htrace : WordTrace (prefixWord ++ tailWord_1870009) baseStart_1870009 baseEnd_1870009 := by
    simpa [prefixWord, tailWord_1870009, baseEnd_1870009] using wordTrace_append hprefix tailTrace_1870009
  have hstable : (prefixWord ++ tailWord_1870009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870009).length < 2 ^ (prefixWord ++ tailWord_1870009).sum := by decide
  have hdescent : baseEnd_1870009 < baseStart_1870009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870053 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_1870053 : Nat := 118140960795 + 1870053 * 2 ^ 59
def prefixEnd_1870053 : Nat := 4983230072969 + 3 ^ 40 * 1870053 * 2
def baseEnd_1870053 : Nat := 320078679460825714245763

theorem tailTrace_1870053 : CollatzResearch.WordTrace tailWord_1870053 prefixEnd_1870053 320078679460825714245763 := by
  unfold tailWord_1870053
  simp only [CollatzResearch.WordTrace]
  refine ⟨68206436294124835470398813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45470957529416556980265875 68206436294124835470398813)
  ·
    refine ⟨25577413610296813301399555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68206436294124835470398813 25577413610296813301399555)
    ·
      refine ⟨38366120415445219952099333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25577413610296813301399555 38366120415445219952099333)
      ·
        refine ⟨7193647577895978741018625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38366120415445219952099333 7193647577895978741018625)
        ·
          refine ⟨5395235683421984055763969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7193647577895978741018625 5395235683421984055763969)
          ·
            refine ⟨4046426762566488041822977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5395235683421984055763969 4046426762566488041822977)
            ·
              refine ⟨3034820071924866031367233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4046426762566488041822977 3034820071924866031367233)
              ·
                refine ⟨2276115053943649523525425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034820071924866031367233 2276115053943649523525425)
                ·
                  refine ⟨1707086290457737142644069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2276115053943649523525425 1707086290457737142644069)
                  ·
                    refine ⟨320078679460825714245763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1707086290457737142644069 320078679460825714245763)
                    ·
                      rfl

theorem cell23_1870053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_1870053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870053 prefixEnd_1870053 := by exact prefixLift 1870053
  have htrace : WordTrace (prefixWord ++ tailWord_1870053) baseStart_1870053 baseEnd_1870053 := by
    simpa [prefixWord, tailWord_1870053, baseEnd_1870053] using wordTrace_append hprefix tailTrace_1870053
  have hstable : (prefixWord ++ tailWord_1870053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870053).length < 2 ^ (prefixWord ++ tailWord_1870053).sum := by decide
  have hdescent : baseEnd_1870053 < baseStart_1870053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870059 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 3]
def baseStart_1870059 : Nat := 118140960795 + 1870059 * 2 ^ 59
def prefixEnd_1870059 : Nat := 4983230072969 + 3 ^ 40 * 1870059 * 2
def baseEnd_1870059 : Nat := 960239119266404119262261

theorem tailTrace_1870059 : CollatzResearch.WordTrace tailWord_1870059 prefixEnd_1870059 960239119266404119262261 := by
  unfold tailWord_1870059
  simp only [CollatzResearch.WordTrace]
  refine ⟨68206655132103098495117231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45471103421402065663411487 68206655132103098495117231)
  ·
    refine ⟨102309982698154647742675847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68206655132103098495117231 102309982698154647742675847)
    ·
      refine ⟨153464974047231971614013771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102309982698154647742675847 153464974047231971614013771)
      ·
        refine ⟨230197461070847957421020657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153464974047231971614013771 230197461070847957421020657)
        ·
          refine ⟨172648095803135968065765493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230197461070847957421020657 172648095803135968065765493)
          ·
            refine ⟨16185758981543997006165515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172648095803135968065765493 16185758981543997006165515)
            ·
              refine ⟨24278638472315995509248273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16185758981543997006165515 24278638472315995509248273)
              ·
                refine ⟨18208978854236996631936205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24278638472315995509248273 18208978854236996631936205)
                ·
                  refine ⟨6828367070338873736976077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18208978854236996631936205 6828367070338873736976077)
                  ·
                    refine ⟨2560637651377077651366029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6828367070338873736976077 2560637651377077651366029)
                    ·
                      refine ⟨960239119266404119262261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2560637651377077651366029 960239119266404119262261)
                      ·
                        rfl

theorem cell23_1870059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 3].length) (baseStart_1870059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870059 prefixEnd_1870059 := by exact prefixLift 1870059
  have htrace : WordTrace (prefixWord ++ tailWord_1870059) baseStart_1870059 baseEnd_1870059 := by
    simpa [prefixWord, tailWord_1870059, baseEnd_1870059] using wordTrace_append hprefix tailTrace_1870059
  have hstable : (prefixWord ++ tailWord_1870059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870059).length < 2 ^ (prefixWord ++ tailWord_1870059).sum := by decide
  have hdescent : baseEnd_1870059 < baseStart_1870059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870060 : List Nat := [2, 2, 1, 1, 2, 3, 3, 4, 1, 2, 2]
def baseStart_1870060 : Nat := 118140960795 + 1870060 * 2 ^ 59
def prefixEnd_1870060 : Nat := 4983230072969 + 3 ^ 40 * 1870060 * 2
def baseEnd_1870060 : Nat := 960239632747058615349757

theorem tailTrace_1870060 : CollatzResearch.WordTrace tailWord_1870060 prefixEnd_1870060 960239632747058615349757 := by
  unfold tailWord_1870060
  simp only [CollatzResearch.WordTrace]
  refine ⟨34103345802549737832951817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45471127736732983777269089 34103345802549737832951817)
  ·
    refine ⟨25577509351912303374713863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34103345802549737832951817 25577509351912303374713863)
    ·
      refine ⟨38366264027868455062070795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25577509351912303374713863 38366264027868455062070795)
      ·
        refine ⟨57549396041802682593106193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38366264027868455062070795 57549396041802682593106193)
        ·
          refine ⟨43162047031352011944829645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57549396041802682593106193 43162047031352011944829645)
          ·
            refine ⟨16185767636757004479311117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43162047031352011944829645 16185767636757004479311117)
            ·
              refine ⟨6069662863783876679741669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16185767636757004479311117 6069662863783876679741669)
              ·
                refine ⟨1138061786959476877451563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6069662863783876679741669 1138061786959476877451563)
                ·
                  refine ⟨1707092680439215316177345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138061786959476877451563 1707092680439215316177345)
                  ·
                    refine ⟨1280319510329411487133009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1707092680439215316177345 1280319510329411487133009)
                    ·
                      refine ⟨960239632747058615349757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280319510329411487133009 960239632747058615349757)
                      ·
                        rfl

theorem cell23_1870060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 2, 2].length) (baseStart_1870060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870060 prefixEnd_1870060 := by exact prefixLift 1870060
  have htrace : WordTrace (prefixWord ++ tailWord_1870060) baseStart_1870060 baseEnd_1870060 := by
    simpa [prefixWord, tailWord_1870060, baseEnd_1870060] using wordTrace_append hprefix tailTrace_1870060
  have hstable : (prefixWord ++ tailWord_1870060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870060).length < 2 ^ (prefixWord ++ tailWord_1870060).sum := by decide
  have hdescent : baseEnd_1870060 < baseStart_1870060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870066 : List Nat := [3, 2, 1, 3, 2, 3, 1, 8]
def baseStart_1870066 : Nat := 118140960795 + 1870066 * 2 ^ 59
def prefixEnd_1870066 : Nat := 4983230072969 + 3 ^ 40 * 1870066 * 2
def baseEnd_1870066 : Nat := 35564544949295762662027

theorem tailTrace_1870066 : CollatzResearch.WordTrace tailWord_1870066 prefixEnd_1870066 35564544949295762662027 := by
  unfold tailWord_1870066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17051727610769434672655513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45471273628718492460414701 17051727610769434672655513)
  ·
    refine ⟨12788795708077076004491635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17051727610769434672655513 12788795708077076004491635)
    ·
      refine ⟨19183193562115614006737453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12788795708077076004491635 19183193562115614006737453)
      ·
        refine ⟨7193697585793355252526545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19183193562115614006737453 7193697585793355252526545)
        ·
          refine ⟨5395273189345016439394909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7193697585793355252526545 5395273189345016439394909)
          ·
            refine ⟨2023227446004381164773091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5395273189345016439394909 2023227446004381164773091)
            ·
              refine ⟨3034841169006571747159637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023227446004381164773091 3034841169006571747159637)
              ·
                refine ⟨35564544949295762662027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3034841169006571747159637 35564544949295762662027)
                ·
                  rfl

theorem cell23_1870066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 8].length) (baseStart_1870066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870066 prefixEnd_1870066 := by exact prefixLift 1870066
  have htrace : WordTrace (prefixWord ++ tailWord_1870066) baseStart_1870066 baseEnd_1870066 := by
    simpa [prefixWord, tailWord_1870066, baseEnd_1870066] using wordTrace_append hprefix tailTrace_1870066
  have hstable : (prefixWord ++ tailWord_1870066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870066).length < 2 ^ (prefixWord ++ tailWord_1870066).sum := by decide
  have hdescent : baseEnd_1870066 < baseStart_1870066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870076 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_1870076 : Nat := 118140960795 + 1870076 * 2 ^ 59
def prefixEnd_1870076 : Nat := 4983230072969 + 3 ^ 40 * 1870076 * 2
def baseEnd_1870076 : Nat := 960247848437530552749683

theorem tailTrace_1870076 : CollatzResearch.WordTrace tailWord_1870076 prefixEnd_1870076 960247848437530552749683 := by
  unfold tailWord_1870076
  simp only [CollatzResearch.WordTrace]
  refine ⟨34103637586520755199243041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45471516782027673598990721 34103637586520755199243041)
  ·
    refine ⟨25577728189890566399432281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34103637586520755199243041 25577728189890566399432281)
    ·
      refine ⟨19183296142417924799574211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25577728189890566399432281 19183296142417924799574211)
      ·
        refine ⟨28774944213626887199361317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19183296142417924799574211 28774944213626887199361317)
        ·
          refine ⟨5395302040055041349880247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28774944213626887199361317 5395302040055041349880247)
          ·
            refine ⟨8092953060082562024820371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395302040055041349880247 8092953060082562024820371)
            ·
              refine ⟨12139429590123843037230557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092953060082562024820371 12139429590123843037230557)
              ·
                refine ⟨4552286096296441138961459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12139429590123843037230557 4552286096296441138961459)
                ·
                  refine ⟨6828429144444661708442189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552286096296441138961459 6828429144444661708442189)
                  ·
                    refine ⟨2560660929166748140665821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6828429144444661708442189 2560660929166748140665821)
                    ·
                      refine ⟨960247848437530552749683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2560660929166748140665821 960247848437530552749683)
                      ·
                        rfl

theorem cell23_1870076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_1870076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870076 prefixEnd_1870076 := by exact prefixLift 1870076
  have htrace : WordTrace (prefixWord ++ tailWord_1870076) baseStart_1870076 baseEnd_1870076 := by
    simpa [prefixWord, tailWord_1870076, baseEnd_1870076] using wordTrace_append hprefix tailTrace_1870076
  have hstable : (prefixWord ++ tailWord_1870076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870076).length < 2 ^ (prefixWord ++ tailWord_1870076).sum := by decide
  have hdescent : baseEnd_1870076 < baseStart_1870076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870184 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_1870184 : Nat := 118140960795 + 1870184 * 2 ^ 59
def prefixEnd_1870184 : Nat := 4983230072969 + 3 ^ 40 * 1870184 * 2
def baseEnd_1870184 : Nat := 960303304348216130199187

theorem tailTrace_1870184 : CollatzResearch.WordTrace tailWord_1870184 prefixEnd_1870184 960303304348216130199187 := by
  unfold tailWord_1870184
  simp only [CollatzResearch.WordTrace]
  refine ⟨34105607128325122421708803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45474142837766829895611737 34105607128325122421708803)
  ·
    refine ⟨51158410692487683632563205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34105607128325122421708803 51158410692487683632563205)
    ·
      refine ⟨9592202004841440681105601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51158410692487683632563205 9592202004841440681105601)
      ·
        refine ⟨7194151503631080510829201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9592202004841440681105601 7194151503631080510829201)
        ·
          refine ⟨5395613627723310383121901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7194151503631080510829201 5395613627723310383121901)
          ·
            refine ⟨2023355110396241393670713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5395613627723310383121901 2023355110396241393670713)
            ·
              refine ⟨1517516332797181045253035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023355110396241393670713 1517516332797181045253035)
              ·
                refine ⟨2276274499195771567879553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517516332797181045253035 2276274499195771567879553)
                ·
                  refine ⟨1707205874396828675909665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2276274499195771567879553 1707205874396828675909665)
                  ·
                    refine ⟨1280404405797621506932249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1707205874396828675909665 1280404405797621506932249)
                    ·
                      refine ⟨960303304348216130199187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280404405797621506932249 960303304348216130199187)
                      ·
                        rfl

theorem cell23_1870184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_1870184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870184 prefixEnd_1870184 := by exact prefixLift 1870184
  have htrace : WordTrace (prefixWord ++ tailWord_1870184) baseStart_1870184 baseEnd_1870184 := by
    simpa [prefixWord, tailWord_1870184, baseEnd_1870184] using wordTrace_append hprefix tailTrace_1870184
  have hstable : (prefixWord ++ tailWord_1870184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870184).length < 2 ^ (prefixWord ++ tailWord_1870184).sum := by decide
  have hdescent : baseEnd_1870184 < baseStart_1870184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870283 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 4, 3, 2]
def baseStart_1870283 : Nat := 118140960795 + 1870283 * 2 ^ 59
def prefixEnd_1870283 : Nat := 4983230072969 + 3 ^ 40 * 1870283 * 2
def baseEnd_1870283 : Nat := 960354138933011242861231

theorem tailTrace_1870283 : CollatzResearch.WordTrace tailWord_1870283 prefixEnd_1870283 960354138933011242861231 := by
  unfold tailWord_1870283
  simp only [CollatzResearch.WordTrace]
  refine ⟨68214825083291584751271503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45476550055527723167514335 68214825083291584751271503)
  ·
    refine ⟨102322237624937377126907255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68214825083291584751271503 102322237624937377126907255)
    ·
      refine ⟨153483356437406065690360883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102322237624937377126907255 153483356437406065690360883)
      ·
        refine ⟨230225034656109098535541325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153483356437406065690360883 230225034656109098535541325)
        ·
          refine ⟨86334387996040911950827997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230225034656109098535541325 86334387996040911950827997)
          ·
            refine ⟨32375395498515341981560499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86334387996040911950827997 32375395498515341981560499)
            ·
              refine ⟨48563093247773012972340749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32375395498515341981560499 48563093247773012972340749)
              ·
                refine ⟨18211159967914879864627781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48563093247773012972340749 18211159967914879864627781)
                ·
                  refine ⟨3414592493984039974617709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18211159967914879864627781 3414592493984039974617709)
                  ·
                    refine ⟨1280472185244014990481641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414592493984039974617709 1280472185244014990481641)
                    ·
                      refine ⟨960354138933011242861231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280472185244014990481641 960354138933011242861231)
                      ·
                        rfl

theorem cell23_1870283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 3, 2].length) (baseStart_1870283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870283 prefixEnd_1870283 := by exact prefixLift 1870283
  have htrace : WordTrace (prefixWord ++ tailWord_1870283) baseStart_1870283 baseEnd_1870283 := by
    simpa [prefixWord, tailWord_1870283, baseEnd_1870283] using wordTrace_append hprefix tailTrace_1870283
  have hstable : (prefixWord ++ tailWord_1870283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870283).length < 2 ^ (prefixWord ++ tailWord_1870283).sum := by decide
  have hdescent : baseEnd_1870283 < baseStart_1870283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870316 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_1870316 : Nat := 118140960795 + 1870316 * 2 ^ 59
def prefixEnd_1870316 : Nat := 4983230072969 + 3 ^ 40 * 1870316 * 2
def baseEnd_1870316 : Nat := 960371083794609613748579

theorem tailTrace_1870316 : CollatzResearch.WordTrace tailWord_1870316 prefixEnd_1870316 960371083794609613748579 := by
  unfold tailWord_1870316
  simp only [CollatzResearch.WordTrace]
  refine ⟨34108014346086015693611401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45477352461448020924815201 34108014346086015693611401)
  ·
    refine ⟨25581010759564511770208551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34108014346086015693611401 25581010759564511770208551)
    ·
      refine ⟨38371516139346767655312827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25581010759564511770208551 38371516139346767655312827)
      ·
        refine ⟨57557274209020151482969241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38371516139346767655312827 57557274209020151482969241)
        ·
          refine ⟨43167955656765113612226931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57557274209020151482969241 43167955656765113612226931)
          ·
            refine ⟨64751933485147670418340397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43167955656765113612226931 64751933485147670418340397)
            ·
              refine ⟨24281975056930376406877649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64751933485147670418340397 24281975056930376406877649)
              ·
                refine ⟨18211481292697782305158237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24281975056930376406877649 18211481292697782305158237)
                ·
                  refine ⟨6829305484761668364434339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18211481292697782305158237 6829305484761668364434339)
                  ·
                    refine ⟨10243958227142502546651509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6829305484761668364434339 10243958227142502546651509)
                    ·
                      refine ⟨960371083794609613748579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10243958227142502546651509 960371083794609613748579)
                      ·
                        rfl

theorem cell23_1870316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_1870316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870316 prefixEnd_1870316 := by exact prefixLift 1870316
  have htrace : WordTrace (prefixWord ++ tailWord_1870316) baseStart_1870316 baseEnd_1870316 := by
    simpa [prefixWord, tailWord_1870316, baseEnd_1870316] using wordTrace_append hprefix tailTrace_1870316
  have hstable : (prefixWord ++ tailWord_1870316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870316).length < 2 ^ (prefixWord ++ tailWord_1870316).sum := by decide
  have hdescent : baseEnd_1870316 < baseStart_1870316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870333 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_1870333 : Nat := 118140960795 + 1870333 * 2 ^ 59
def prefixEnd_1870333 : Nat := 4983230072969 + 3 ^ 40 * 1870333 * 2
def baseEnd_1870333 : Nat := 960379812965736047236001

theorem tailTrace_1870333 : CollatzResearch.WordTrace tailWord_1870333 prefixEnd_1870333 960379812965736047236001 := by
  unfold tailWord_1870333
  simp only [CollatzResearch.WordTrace]
  refine ⟨68216648733110443290591653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45477765822073628860394435 68216648733110443290591653)
  ·
    refine ⟨12790621637458208116985935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68216648733110443290591653 12790621637458208116985935)
    ·
      refine ⟨19185932456187312175478903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12790621637458208116985935 19185932456187312175478903)
      ·
        refine ⟨28778898684280968263218355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19185932456187312175478903 28778898684280968263218355)
        ·
          refine ⟨43168348026421452394827533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28778898684280968263218355 43168348026421452394827533)
          ·
            refine ⟨16188130509908044648060325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43168348026421452394827533 16188130509908044648060325)
            ·
              refine ⟨3035274470607758371511311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16188130509908044648060325 3035274470607758371511311)
              ·
                refine ⟨4552911705911637557266967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035274470607758371511311 4552911705911637557266967)
                ·
                  refine ⟨6829367558867456335900451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4552911705911637557266967 6829367558867456335900451)
                  ·
                    refine ⟨10244051338301184503850677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6829367558867456335900451 10244051338301184503850677)
                    ·
                      refine ⟨960379812965736047236001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10244051338301184503850677 960379812965736047236001)
                      ·
                        rfl

theorem cell23_1870333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_1870333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870333 prefixEnd_1870333 := by exact prefixLift 1870333
  have htrace : WordTrace (prefixWord ++ tailWord_1870333) baseStart_1870333 baseEnd_1870333 := by
    simpa [prefixWord, tailWord_1870333, baseEnd_1870333] using wordTrace_append hprefix tailTrace_1870333
  have hstable : (prefixWord ++ tailWord_1870333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870333).length < 2 ^ (prefixWord ++ tailWord_1870333).sum := by decide
  have hdescent : baseEnd_1870333 < baseStart_1870333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870340 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_1870340 : Nat := 118140960795 + 1870340 * 2 ^ 59
def prefixEnd_1870340 : Nat := 4983230072969 + 3 ^ 40 * 1870340 * 2
def baseEnd_1870340 : Nat := 320127802443439173282823

theorem tailTrace_1870340 : CollatzResearch.WordTrace tailWord_1870340 prefixEnd_1870340 320127802443439173282823 := by
  unfold tailWord_1870340
  simp only [CollatzResearch.WordTrace]
  refine ⟨34108452022042541743048237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45477936029390055657397649 34108452022042541743048237)
  ·
    refine ⟨12790669508265953153643089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34108452022042541743048237 12790669508265953153643089)
    ·
      refine ⟨9593002131199464865232317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12790669508265953153643089 9593002131199464865232317)
      ·
        refine ⟨3597375799199799324462119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9593002131199464865232317 3597375799199799324462119)
        ·
          refine ⟨5396063698799698986693179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597375799199799324462119 5396063698799698986693179)
          ·
            refine ⟨8094095548199548480039769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396063698799698986693179 8094095548199548480039769)
            ·
              refine ⟨6070571661149661360029827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8094095548199548480039769 6070571661149661360029827)
              ·
                refine ⟨9105857491724492040044741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6070571661149661360029827 9105857491724492040044741)
                ·
                  refine ⟨1707348279698342257508389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9105857491724492040044741 1707348279698342257508389)
                  ·
                    refine ⟨320127802443439173282823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1707348279698342257508389 320127802443439173282823)
                    ·
                      rfl

theorem cell23_1870340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_1870340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870340 prefixEnd_1870340 := by exact prefixLift 1870340
  have htrace : WordTrace (prefixWord ++ tailWord_1870340) baseStart_1870340 baseEnd_1870340 := by
    simpa [prefixWord, tailWord_1870340, baseEnd_1870340] using wordTrace_append hprefix tailTrace_1870340
  have hstable : (prefixWord ++ tailWord_1870340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870340).length < 2 ^ (prefixWord ++ tailWord_1870340).sum := by decide
  have hdescent : baseEnd_1870340 < baseStart_1870340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870347 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 3, 2, 2]
def baseStart_1870347 : Nat := 118140960795 + 1870347 * 2 ^ 59
def prefixEnd_1870347 : Nat := 4983230072969 + 3 ^ 40 * 1870347 * 2
def baseEnd_1870347 : Nat := 960387001694898992460937

theorem tailTrace_1870347 : CollatzResearch.WordTrace tailWord_1870347 prefixEnd_1870347 960387001694898992460937 := by
  unfold tailWord_1870347
  simp only [CollatzResearch.WordTrace]
  refine ⟨68217159355059723681601295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45478106236706482454400863 68217159355059723681601295)
  ·
    refine ⟨102325739032589585522401943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68217159355059723681601295 102325739032589585522401943)
    ·
      refine ⟨153488608548884378283602915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102325739032589585522401943 153488608548884378283602915)
      ·
        refine ⟨230232912823326567425404373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153488608548884378283602915 230232912823326567425404373)
        ·
          refine ⟨5396083894296716424032915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 230232912823326567425404373 5396083894296716424032915)
          ·
            refine ⟨8094125841445074636049373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396083894296716424032915 8094125841445074636049373)
            ·
              refine ⟨3035297190541902988518515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8094125841445074636049373 3035297190541902988518515)
              ·
                refine ⟨4552945785812854482777773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035297190541902988518515 4552945785812854482777773)
                ·
                  refine ⟨1707354669679820431041665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4552945785812854482777773 1707354669679820431041665)
                  ·
                    refine ⟨1280516002259865323281249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1707354669679820431041665 1280516002259865323281249)
                    ·
                      refine ⟨960387001694898992460937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280516002259865323281249 960387001694898992460937)
                      ·
                        rfl

theorem cell23_1870347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 2, 2].length) (baseStart_1870347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870347 prefixEnd_1870347 := by exact prefixLift 1870347
  have htrace : WordTrace (prefixWord ++ tailWord_1870347) baseStart_1870347 baseEnd_1870347 := by
    simpa [prefixWord, tailWord_1870347, baseEnd_1870347] using wordTrace_append hprefix tailTrace_1870347
  have hstable : (prefixWord ++ tailWord_1870347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870347).length < 2 ^ (prefixWord ++ tailWord_1870347).sum := by decide
  have hdescent : baseEnd_1870347 < baseStart_1870347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870397 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1870397 : Nat := 118140960795 + 1870397 * 2 ^ 59
def prefixEnd_1870397 : Nat := 4983230072969 + 3 ^ 40 * 1870397 * 2
def baseEnd_1870397 : Nat := 960412675727623796835707

theorem tailTrace_1870397 : CollatzResearch.WordTrace tailWord_1870397 prefixEnd_1870397 960412675727623796835707 := by
  unfold tailWord_1870397
  simp only [CollatzResearch.WordTrace]
  refine ⟨68218983004878582220921445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45479322003252388147280963 68218983004878582220921445)
  ·
    refine ⟨12791059313414734166422771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68218983004878582220921445 12791059313414734166422771)
    ·
      refine ⟨19186588970122101249634157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12791059313414734166422771 19186588970122101249634157)
      ·
        refine ⟨7194970863795787968612809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19186588970122101249634157 7194970863795787968612809)
        ·
          refine ⟨5396228147846840976459607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7194970863795787968612809 5396228147846840976459607)
          ·
            refine ⟨8094342221770261464689411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396228147846840976459607 8094342221770261464689411)
            ·
              refine ⟨12141513332655392197034117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8094342221770261464689411 12141513332655392197034117)
              ·
                refine ⟨2276533749872886036943897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12141513332655392197034117 2276533749872886036943897)
                ·
                  refine ⟨1707400312404664527707923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2276533749872886036943897 1707400312404664527707923)
                  ·
                    refine ⟨2561100468606996791561885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1707400312404664527707923 2561100468606996791561885)
                    ·
                      refine ⟨960412675727623796835707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2561100468606996791561885 960412675727623796835707)
                      ·
                        rfl

theorem cell23_1870397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1870397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870397 prefixEnd_1870397 := by exact prefixLift 1870397
  have htrace : WordTrace (prefixWord ++ tailWord_1870397) baseStart_1870397 baseEnd_1870397 := by
    simpa [prefixWord, tailWord_1870397, baseEnd_1870397] using wordTrace_append hprefix tailTrace_1870397
  have hstable : (prefixWord ++ tailWord_1870397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870397).length < 2 ^ (prefixWord ++ tailWord_1870397).sum := by decide
  have hdescent : baseEnd_1870397 < baseStart_1870397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870398 : List Nat := [4, 2, 1, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_1870398 : Nat := 118140960795 + 1870398 * 2 ^ 59
def prefixEnd_1870398 : Nat := 4983230072969 + 3 ^ 40 * 1870398 * 2
def baseEnd_1870398 : Nat := 960413189208278292923203

theorem tailTrace_1870398 : CollatzResearch.WordTrace tailWord_1870398 prefixEnd_1870398 960413189208278292923203 := by
  unfold tailWord_1870398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8527377434734369923963481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45479346318583306261138565 8527377434734369923963481)
  ·
    refine ⟨6395533076050777442972611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8527377434734369923963481 6395533076050777442972611)
    ·
      refine ⟨9593299614076166164458917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6395533076050777442972611 9593299614076166164458917)
      ·
        refine ⟨1798743677639281155836047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9593299614076166164458917 1798743677639281155836047)
        ·
          refine ⟨2698115516458921733754071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798743677639281155836047 2698115516458921733754071)
          ·
            refine ⟨4047173274688382600631107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698115516458921733754071 4047173274688382600631107)
            ·
              refine ⟨6070759912032573900946661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047173274688382600631107 6070759912032573900946661)
              ·
                refine ⟨1138267483506107606427499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6070759912032573900946661 1138267483506107606427499)
                ·
                  refine ⟨1707401225259161409641249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138267483506107606427499 1707401225259161409641249)
                  ·
                    refine ⟨1280550918944371057230937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1707401225259161409641249 1280550918944371057230937)
                    ·
                      refine ⟨960413189208278292923203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280550918944371057230937 960413189208278292923203)
                      ·
                        rfl

theorem cell23_1870398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_1870398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870398 prefixEnd_1870398 := by exact prefixLift 1870398
  have htrace : WordTrace (prefixWord ++ tailWord_1870398) baseStart_1870398 baseEnd_1870398 := by
    simpa [prefixWord, tailWord_1870398, baseEnd_1870398] using wordTrace_append hprefix tailTrace_1870398
  have hstable : (prefixWord ++ tailWord_1870398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870398).length < 2 ^ (prefixWord ++ tailWord_1870398).sum := by decide
  have hdescent : baseEnd_1870398 < baseStart_1870398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870404 : List Nat := [2, 3, 5, 1, 1, 2, 1, 8]
def baseStart_1870404 : Nat := 118140960795 + 1870404 * 2 ^ 59
def prefixEnd_1870404 : Nat := 4983230072969 + 3 ^ 40 * 1870404 * 2
def baseEnd_1870404 : Nat := 35570972966377972942525

theorem tailTrace_1870404 : CollatzResearch.WordTrace tailWord_1870404 prefixEnd_1870404 35570972966377972942525 := by
  unfold tailWord_1870404
  simp only [CollatzResearch.WordTrace]
  refine ⟨34109619157926611208213133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45479492210568814944284177 34109619157926611208213133)
  ·
    refine ⟨12791107184222479203079925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34109619157926611208213133 12791107184222479203079925)
    ·
      refine ⟨1199166298520857425288743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12791107184222479203079925 1199166298520857425288743)
      ·
        refine ⟨1798749447781286137933115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199166298520857425288743 1798749447781286137933115)
        ·
          refine ⟨2698124171671929206899673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798749447781286137933115 2698124171671929206899673)
          ·
            refine ⟨2023593128753946905174755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2698124171671929206899673 2023593128753946905174755)
            ·
              refine ⟨3035389693130920357762133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023593128753946905174755 3035389693130920357762133)
              ·
                refine ⟨35570972966377972942525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3035389693130920357762133 35570972966377972942525)
                ·
                  rfl

theorem cell23_1870404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 8].length) (baseStart_1870404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870404 prefixEnd_1870404 := by exact prefixLift 1870404
  have htrace : WordTrace (prefixWord ++ tailWord_1870404) baseStart_1870404 baseEnd_1870404 := by
    simpa [prefixWord, tailWord_1870404, baseEnd_1870404] using wordTrace_append hprefix tailTrace_1870404
  have hstable : (prefixWord ++ tailWord_1870404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870404).length < 2 ^ (prefixWord ++ tailWord_1870404).sum := by decide
  have hdescent : baseEnd_1870404 < baseStart_1870404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870423 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1870423 : Nat := 118140960795 + 1870423 * 2 ^ 59
def prefixEnd_1870423 : Nat := 4983230072969 + 3 ^ 40 * 1870423 * 2
def baseEnd_1870423 : Nat := 960426026224640695110587

theorem tailTrace_1870423 : CollatzResearch.WordTrace tailWord_1870423 prefixEnd_1870423 960426026224640695110587 := by
  unfold tailWord_1870423
  simp only [CollatzResearch.WordTrace]
  refine ⟨68219931302784388661367923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45479954201856259107578615 68219931302784388661367923)
  ·
    refine ⟨102329896954176582992051885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68219931302784388661367923 102329896954176582992051885)
    ·
      refine ⟨38373711357816218622019457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102329896954176582992051885 38373711357816218622019457)
      ·
        refine ⟨28780283518362163966514593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38373711357816218622019457 28780283518362163966514593)
        ·
          refine ⟨21585212638771622974885945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28780283518362163966514593 21585212638771622974885945)
          ·
            refine ⟨16188909479078717231164459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21585212638771622974885945 16188909479078717231164459)
            ·
              refine ⟨24283364218618075846746689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16188909479078717231164459 24283364218618075846746689)
              ·
                refine ⟨18212523163963556885060017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24283364218618075846746689 18212523163963556885060017)
                ·
                  refine ⟨13659392372972667663795013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18212523163963556885060017 13659392372972667663795013)
                  ·
                    refine ⟨2561136069932375186961565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13659392372972667663795013 2561136069932375186961565)
                    ·
                      refine ⟨960426026224640695110587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2561136069932375186961565 960426026224640695110587)
                      ·
                        rfl

theorem cell23_1870423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1870423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870423 prefixEnd_1870423 := by exact prefixLift 1870423
  have htrace : WordTrace (prefixWord ++ tailWord_1870423) baseStart_1870423 baseEnd_1870423 := by
    simpa [prefixWord, tailWord_1870423, baseEnd_1870423] using wordTrace_append hprefix tailTrace_1870423
  have hstable : (prefixWord ++ tailWord_1870423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870423).length < 2 ^ (prefixWord ++ tailWord_1870423).sum := by decide
  have hdescent : baseEnd_1870423 < baseStart_1870423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870460 : List Nat := [2, 2, 2, 1, 1, 2, 4, 4, 5]
def baseStart_1870460 : Nat := 118140960795 + 1870460 * 2 ^ 59
def prefixEnd_1870460 : Nat := 4983230072969 + 3 ^ 40 * 1870460 * 2
def baseEnd_1870460 : Nat := 106716113889873005594213

theorem tailTrace_1870460 : CollatzResearch.WordTrace tailWord_1870460 prefixEnd_1870460 106716113889873005594213 := by
  unfold tailWord_1870460
  simp only [CollatzResearch.WordTrace]
  refine ⟨34110640401825171990232417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45480853869100229320309889 34110640401825171990232417)
  ·
    refine ⟨25582980301368878992674313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34110640401825171990232417 25582980301368878992674313)
    ·
      refine ⟨19187235226026659244505735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25582980301368878992674313 19187235226026659244505735)
      ·
        refine ⟨28780852839039988866758603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19187235226026659244505735 28780852839039988866758603)
        ·
          refine ⟨43171279258559983300137905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28780852839039988866758603 43171279258559983300137905)
          ·
            refine ⟨32378459443919987475103429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43171279258559983300137905 32378459443919987475103429)
            ·
              refine ⟨6070961145734997651581893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32378459443919987475103429 6070961145734997651581893)
              ·
                refine ⟨1138305214825312059671605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6070961145734997651581893 1138305214825312059671605)
                ·
                  refine ⟨106716113889873005594213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1138305214825312059671605 106716113889873005594213)
                  ·
                    rfl

theorem cell23_1870460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_1870460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870460 prefixEnd_1870460 := by exact prefixLift 1870460
  have htrace : WordTrace (prefixWord ++ tailWord_1870460) baseStart_1870460 baseEnd_1870460 := by
    simpa [prefixWord, tailWord_1870460, baseEnd_1870460] using wordTrace_append hprefix tailTrace_1870460
  have hstable : (prefixWord ++ tailWord_1870460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870460).length < 2 ^ (prefixWord ++ tailWord_1870460).sum := by decide
  have hdescent : baseEnd_1870460 < baseStart_1870460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870577 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 3]
def baseStart_1870577 : Nat := 118140960795 + 1870577 * 2 ^ 59
def prefixEnd_1870577 : Nat := 4983230072969 + 3 ^ 40 * 1870577 * 2
def baseEnd_1870577 : Nat := 960505102245433092584879

theorem tailTrace_1870577 : CollatzResearch.WordTrace tailWord_1870577 prefixEnd_1870577 960505102245433092584879 := by
  unfold tailWord_1870577
  simp only [CollatzResearch.WordTrace]
  refine ⟨68225548144226472962473985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45483698762817648641649323 68225548144226472962473985)
  ·
    refine ⟨51169161108169854721855489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68225548144226472962473985 51169161108169854721855489)
    ·
      refine ⟨38376870831127391041391617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51169161108169854721855489 38376870831127391041391617)
      ·
        refine ⟨28782653123345543281043713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38376870831127391041391617 28782653123345543281043713)
        ·
          refine ⟨21586989842509157460782785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28782653123345543281043713 21586989842509157460782785)
          ·
            refine ⟨16190242381881868095587089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21586989842509157460782785 16190242381881868095587089)
            ·
              refine ⟨12142681786411401071690317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16190242381881868095587089 12142681786411401071690317)
              ·
                refine ⟨4553505669904275401883869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12142681786411401071690317 4553505669904275401883869)
                ·
                  refine ⟨1707564626214103275706451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4553505669904275401883869 1707564626214103275706451)
                  ·
                    refine ⟨2561346939321154913559677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1707564626214103275706451 2561346939321154913559677)
                    ·
                      refine ⟨960505102245433092584879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2561346939321154913559677 960505102245433092584879)
                      ·
                        rfl

theorem cell23_1870577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_1870577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870577 prefixEnd_1870577 := by exact prefixLift 1870577
  have htrace : WordTrace (prefixWord ++ tailWord_1870577) baseStart_1870577 baseEnd_1870577 := by
    simpa [prefixWord, tailWord_1870577, baseEnd_1870577] using wordTrace_append hprefix tailTrace_1870577
  have hstable : (prefixWord ++ tailWord_1870577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870577).length < 2 ^ (prefixWord ++ tailWord_1870577).sum := by decide
  have hdescent : baseEnd_1870577 < baseStart_1870577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870594 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_1870594 : Nat := 118140960795 + 1870594 * 2 ^ 59
def prefixEnd_1870594 : Nat := 4983230072969 + 3 ^ 40 * 1870594 * 2
def baseEnd_1870594 : Nat := 960513831416559526072301

theorem tailTrace_1870594 : CollatzResearch.WordTrace tailWord_1870594 prefixEnd_1870594 960513831416559526072301 := by
  unfold tailWord_1870594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17056542046291221216460709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45484112123443256577228557 17056542046291221216460709)
  ·
    refine ⟨3198101633679603978086383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17056542046291221216460709 3198101633679603978086383)
    ·
      refine ⟨4797152450519405967129575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3198101633679603978086383 4797152450519405967129575)
      ·
        refine ⟨7195728675779108950694363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4797152450519405967129575 7195728675779108950694363)
        ·
          refine ⟨10793593013668663426041545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7195728675779108950694363 10793593013668663426041545)
          ·
            refine ⟨8095194760251497569531159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10793593013668663426041545 8095194760251497569531159)
            ·
              refine ⟨12142792140377246354296739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8095194760251497569531159 12142792140377246354296739)
              ·
                refine ⟨18214188210565869531445109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12142792140377246354296739 18214188210565869531445109)
                ·
                  refine ⟨1707580144740550268572979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18214188210565869531445109 1707580144740550268572979)
                  ·
                    refine ⟨2561370217110825402859469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1707580144740550268572979 2561370217110825402859469)
                    ·
                      refine ⟨960513831416559526072301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2561370217110825402859469 960513831416559526072301)
                      ·
                        rfl

theorem cell23_1870594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_1870594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870594 prefixEnd_1870594 := by exact prefixLift 1870594
  have htrace : WordTrace (prefixWord ++ tailWord_1870594) baseStart_1870594 baseEnd_1870594 := by
    simpa [prefixWord, tailWord_1870594, baseEnd_1870594] using wordTrace_append hprefix tailTrace_1870594
  have hstable : (prefixWord ++ tailWord_1870594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870594).length < 2 ^ (prefixWord ++ tailWord_1870594).sum := by decide
  have hdescent : baseEnd_1870594 < baseStart_1870594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870662 : List Nat := [6, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1870662 : Nat := 118140960795 + 1870662 * 2 ^ 59
def prefixEnd_1870662 : Nat := 4983230072969 + 3 ^ 40 * 1870662 * 2
def baseEnd_1870662 : Nat := 960548748101065260021989

theorem tailTrace_1870662 : CollatzResearch.WordTrace tailWord_1870662 prefixEnd_1870662 960548748101065260021989 := by
  unfold tailWord_1870662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132145260903704139978695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45485765565945688319545493 2132145260903704139978695)
  ·
    refine ⟨3198217891355556209968043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2132145260903704139978695 3198217891355556209968043)
    ·
      refine ⟨4797326837033334314952065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3198217891355556209968043 4797326837033334314952065)
      ·
        refine ⟨3597995127775000736214049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4797326837033334314952065 3597995127775000736214049)
        ·
          refine ⟨2698496345831250552160537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3597995127775000736214049 2698496345831250552160537)
          ·
            refine ⟨2023872259373437914120403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2698496345831250552160537 2023872259373437914120403)
            ·
              refine ⟨3035808389060156871180605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023872259373437914120403 3035808389060156871180605)
              ·
                refine ⟨1138428145897558826692727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3035808389060156871180605 1138428145897558826692727)
                ·
                  refine ⟨1707642218846338240039091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138428145897558826692727 1707642218846338240039091)
                  ·
                    refine ⟨2561463328269507360058637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1707642218846338240039091 2561463328269507360058637)
                    ·
                      refine ⟨960548748101065260021989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2561463328269507360058637 960548748101065260021989)
                      ·
                        rfl

theorem cell23_1870662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1870662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870662 prefixEnd_1870662 := by exact prefixLift 1870662
  have htrace : WordTrace (prefixWord ++ tailWord_1870662) baseStart_1870662 baseEnd_1870662 := by
    simpa [prefixWord, tailWord_1870662, baseEnd_1870662] using wordTrace_append hprefix tailTrace_1870662
  have hstable : (prefixWord ++ tailWord_1870662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870662).length < 2 ^ (prefixWord ++ tailWord_1870662).sum := by decide
  have hdescent : baseEnd_1870662 < baseStart_1870662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870668 : List Nat := [2, 2, 1, 3, 3, 1, 3, 3, 1, 2, 2]
def baseStart_1870668 : Nat := 118140960795 + 1870668 * 2 ^ 59
def prefixEnd_1870668 : Nat := 4983230072969 + 3 ^ 40 * 1870668 * 2
def baseEnd_1870668 : Nat := 960551828984992236546961

theorem tailTrace_1870668 : CollatzResearch.WordTrace tailWord_1870668 prefixEnd_1870668 960551828984992236546961 := by
  unfold tailWord_1870668
  simp only [CollatzResearch.WordTrace]
  refine ⟨34114433593448397752018329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45485911457931197002691105 34114433593448397752018329)
  ·
    refine ⟨25585825195086298314013747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34114433593448397752018329 25585825195086298314013747)
    ·
      refine ⟨38378737792629447471020621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25585825195086298314013747 38378737792629447471020621)
      ·
        refine ⟨14392026672236042801632733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38378737792629447471020621 14392026672236042801632733)
        ·
          refine ⟨5397010002088516050612275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14392026672236042801632733 5397010002088516050612275)
          ·
            refine ⟨8095515003132774075918413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397010002088516050612275 8095515003132774075918413)
            ·
              refine ⟨3035818126174790278469405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8095515003132774075918413 3035818126174790278469405)
              ·
                refine ⟨1138431797315546354426027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3035818126174790278469405 1138431797315546354426027)
                ·
                  refine ⟨1707647695973319531639041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138431797315546354426027 1707647695973319531639041)
                  ·
                    refine ⟨1280735771979989648729281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1707647695973319531639041 1280735771979989648729281)
                    ·
                      refine ⟨960551828984992236546961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280735771979989648729281 960551828984992236546961)
                      ·
                        rfl

theorem cell23_1870668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_1870668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870668 prefixEnd_1870668 := by exact prefixLift 1870668
  have htrace : WordTrace (prefixWord ++ tailWord_1870668) baseStart_1870668 baseEnd_1870668 := by
    simpa [prefixWord, tailWord_1870668, baseEnd_1870668] using wordTrace_append hprefix tailTrace_1870668
  have hstable : (prefixWord ++ tailWord_1870668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870668).length < 2 ^ (prefixWord ++ tailWord_1870668).sum := by decide
  have hdescent : baseEnd_1870668 < baseStart_1870668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870700 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_1870700 : Nat := 118140960795 + 1870700 * 2 ^ 59
def prefixEnd_1870700 : Nat := 4983230072969 + 3 ^ 40 * 1870700 * 2
def baseEnd_1870700 : Nat := 320189420121978703782271

theorem tailTrace_1870700 : CollatzResearch.WordTrace tailWord_1870700 prefixEnd_1870700 320189420121978703782271 := by
  unfold tailWord_1870700
  simp only [CollatzResearch.WordTrace]
  refine ⟨34115017161390432484600777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45486689548520576646134369 34115017161390432484600777)
  ·
    refine ⟨25586262871042824363450583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34115017161390432484600777 25586262871042824363450583)
    ·
      refine ⟨38379394306564236545175875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25586262871042824363450583 38379394306564236545175875)
      ·
        refine ⟨57569091459846354817763813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38379394306564236545175875 57569091459846354817763813)
        ·
          refine ⟨10794204648721191528330715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57569091459846354817763813 10794204648721191528330715)
          ·
            refine ⟨16191306973081787292496073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10794204648721191528330715 16191306973081787292496073)
            ·
              refine ⟨12143480229811340469372055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16191306973081787292496073 12143480229811340469372055)
              ·
                refine ⟨18215220344717010704058083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12143480229811340469372055 18215220344717010704058083)
                ·
                  refine ⟨27322830517075516056087125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18215220344717010704058083 27322830517075516056087125)
                  ·
                    refine ⟨320189420121978703782271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27322830517075516056087125 320189420121978703782271)
                    ·
                      rfl

theorem cell23_1870700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_1870700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870700 prefixEnd_1870700 := by exact prefixLift 1870700
  have htrace : WordTrace (prefixWord ++ tailWord_1870700) baseStart_1870700 baseEnd_1870700 := by
    simpa [prefixWord, tailWord_1870700, baseEnd_1870700] using wordTrace_append hprefix tailTrace_1870700
  have hstable : (prefixWord ++ tailWord_1870700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870700).length < 2 ^ (prefixWord ++ tailWord_1870700).sum := by decide
  have hdescent : baseEnd_1870700 < baseStart_1870700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870720 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_1870720 : Nat := 118140960795 + 1870720 * 2 ^ 59
def prefixEnd_1870720 : Nat := 4983230072969 + 3 ^ 40 * 1870720 * 2
def baseEnd_1870720 : Nat := 960578529979026033096721

theorem tailTrace_1870720 : CollatzResearch.WordTrace tailWord_1870720 prefixEnd_1870720 960578529979026033096721 := by
  unfold tailWord_1870720
  simp only [CollatzResearch.WordTrace]
  refine ⟨34115381891354204192464807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45487175855138938923286409 34115381891354204192464807)
  ·
    refine ⟨51173072837031306288697211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34115381891354204192464807 51173072837031306288697211)
    ·
      refine ⟨76759609255546959433045817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51173072837031306288697211 76759609255546959433045817)
      ·
        refine ⟨57569706941660219574784363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76759609255546959433045817 57569706941660219574784363)
        ·
          refine ⟨86354560412490329362176545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57569706941660219574784363 86354560412490329362176545)
          ·
            refine ⟨64765920309367747021632409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86354560412490329362176545 64765920309367747021632409)
            ·
              refine ⟨48574440232025810266224307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64765920309367747021632409 48574440232025810266224307)
              ·
                refine ⟨72861660348038715399336461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48574440232025810266224307 72861660348038715399336461)
                ·
                  refine ⟨27323122630514518274751173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72861660348038715399336461 27323122630514518274751173)
                  ·
                    refine ⟨5123085493221472176515845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27323122630514518274751173 5123085493221472176515845)
                    ·
                      refine ⟨960578529979026033096721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5123085493221472176515845 960578529979026033096721)
                      ·
                        rfl

theorem cell23_1870720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_1870720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870720 prefixEnd_1870720 := by exact prefixLift 1870720
  have htrace : WordTrace (prefixWord ++ tailWord_1870720) baseStart_1870720 baseEnd_1870720 := by
    simpa [prefixWord, tailWord_1870720, baseEnd_1870720] using wordTrace_append hprefix tailTrace_1870720
  have hstable : (prefixWord ++ tailWord_1870720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870720).length < 2 ^ (prefixWord ++ tailWord_1870720).sum := by decide
  have hdescent : baseEnd_1870720 < baseStart_1870720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870727 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1870727 : Nat := 118140960795 + 1870727 * 2 ^ 59
def prefixEnd_1870727 : Nat := 4983230072969 + 3 ^ 40 * 1870727 * 2
def baseEnd_1870727 : Nat := 960582124343607505709189

theorem tailTrace_1870727 : CollatzResearch.WordTrace tailWord_1870727 prefixEnd_1870727 960582124343607505709189 := by
  unfold tailWord_1870727
  simp only [CollatzResearch.WordTrace]
  refine ⟨68231019093683048580434435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45487346062455365720289623 68231019093683048580434435)
  ·
    refine ⟨102346528640524572870651653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68231019093683048580434435 102346528640524572870651653)
    ·
      refine ⟨19189974120098357413247185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102346528640524572870651653 19189974120098357413247185)
      ·
        refine ⟨14392480590073768059935389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19189974120098357413247185 14392480590073768059935389)
        ·
          refine ⟨5397180221277663022475771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14392480590073768059935389 5397180221277663022475771)
          ·
            refine ⟨8095770331916494533713657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397180221277663022475771 8095770331916494533713657)
            ·
              refine ⟨6071827748937370900285243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8095770331916494533713657 6071827748937370900285243)
              ·
                refine ⟨9107741623406056350427865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071827748937370900285243 9107741623406056350427865)
                ·
                  refine ⟨6830806217554542262820899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9107741623406056350427865 6830806217554542262820899)
                  ·
                    refine ⟨10246209326331813394231349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6830806217554542262820899 10246209326331813394231349)
                    ·
                      refine ⟨960582124343607505709189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10246209326331813394231349 960582124343607505709189)
                      ·
                        rfl

theorem cell23_1870727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1870727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870727 prefixEnd_1870727 := by exact prefixLift 1870727
  have htrace : WordTrace (prefixWord ++ tailWord_1870727) baseStart_1870727 baseEnd_1870727 := by
    simpa [prefixWord, tailWord_1870727, baseEnd_1870727] using wordTrace_append hprefix tailTrace_1870727
  have hstable : (prefixWord ++ tailWord_1870727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870727).length < 2 ^ (prefixWord ++ tailWord_1870727).sum := by decide
  have hdescent : baseEnd_1870727 < baseStart_1870727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870728 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_1870728 : Nat := 118140960795 + 1870728 * 2 ^ 59
def prefixEnd_1870728 : Nat := 4983230072969 + 3 ^ 40 * 1870728 * 2
def baseEnd_1870728 : Nat := 960582637824262001796685

theorem tailTrace_1870728 : CollatzResearch.WordTrace tailWord_1870728 prefixEnd_1870728 960582637824262001796685 := by
  unfold tailWord_1870728
  simp only [CollatzResearch.WordTrace]
  refine ⟨34115527783339712875610419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45487370377786283834147225 34115527783339712875610419)
  ·
    refine ⟨51173291675009569313415629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34115527783339712875610419 51173291675009569313415629)
    ·
      refine ⟨19189984378128588492530861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51173291675009569313415629 19189984378128588492530861)
      ·
        refine ⟨7196244141798220684699073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19189984378128588492530861 7196244141798220684699073)
        ·
          refine ⟨5397183106348665513524305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7196244141798220684699073 5397183106348665513524305)
          ·
            refine ⟨4047887329761499135143229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397183106348665513524305 4047887329761499135143229)
            ·
              refine ⟨1517957748660562175678711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4047887329761499135143229 1517957748660562175678711)
              ·
                refine ⟨2276936622990843263518067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517957748660562175678711 2276936622990843263518067)
                ·
                  refine ⟨3415404934486264895277101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276936622990843263518067 3415404934486264895277101)
                  ·
                    refine ⟨1280776850432349335728913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415404934486264895277101 1280776850432349335728913)
                    ·
                      refine ⟨960582637824262001796685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280776850432349335728913 960582637824262001796685)
                      ·
                        rfl

theorem cell23_1870728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_1870728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870728 prefixEnd_1870728 := by exact prefixLift 1870728
  have htrace : WordTrace (prefixWord ++ tailWord_1870728) baseStart_1870728 baseEnd_1870728 := by
    simpa [prefixWord, tailWord_1870728, baseEnd_1870728] using wordTrace_append hprefix tailTrace_1870728
  have hstable : (prefixWord ++ tailWord_1870728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870728).length < 2 ^ (prefixWord ++ tailWord_1870728).sum := by decide
  have hdescent : baseEnd_1870728 < baseStart_1870728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870741 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_1870741 : Nat := 118140960795 + 1870741 * 2 ^ 59
def prefixEnd_1870741 : Nat := 4983230072969 + 3 ^ 40 * 1870741 * 2
def baseEnd_1870741 : Nat := 960589313072770450934125

theorem tailTrace_1870741 : CollatzResearch.WordTrace tailWord_1870741 prefixEnd_1870741 960589313072770450934125 := by
  unfold tailWord_1870741
  simp only [CollatzResearch.WordTrace]
  refine ⟨68231529715632328971444077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45487686477088219314296051 68231529715632328971444077)
  ·
    refine ⟨25586823643362123364291529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68231529715632328971444077 25586823643362123364291529)
    ·
      refine ⟨19190117732521592523218647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25586823643362123364291529 19190117732521592523218647)
      ·
        refine ⟨28785176598782388784827971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19190117732521592523218647 28785176598782388784827971)
        ·
          refine ⟨43177764898173583177241957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28785176598782388784827971 43177764898173583177241957)
          ·
            refine ⟨8095830918407546845732867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43177764898173583177241957 8095830918407546845732867)
            ·
              refine ⟨12143746377611320268599301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8095830918407546845732867 12143746377611320268599301)
              ·
                refine ⟨2276952445802122550362369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12143746377611320268599301 2276952445802122550362369)
                ·
                  refine ⟨1707714334351591912771777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2276952445802122550362369 1707714334351591912771777)
                  ·
                    refine ⟨1280785750763693934578833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1707714334351591912771777 1280785750763693934578833)
                    ·
                      refine ⟨960589313072770450934125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280785750763693934578833 960589313072770450934125)
                      ·
                        rfl

theorem cell23_1870741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_1870741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870741 prefixEnd_1870741 := by exact prefixLift 1870741
  have htrace : WordTrace (prefixWord ++ tailWord_1870741) baseStart_1870741 baseEnd_1870741 := by
    simpa [prefixWord, tailWord_1870741, baseEnd_1870741] using wordTrace_append hprefix tailTrace_1870741
  have hstable : (prefixWord ++ tailWord_1870741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870741).length < 2 ^ (prefixWord ++ tailWord_1870741).sum := by decide
  have hdescent : baseEnd_1870741 < baseStart_1870741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870754 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1870754 : Nat := 118140960795 + 1870754 * 2 ^ 59
def prefixEnd_1870754 : Nat := 4983230072969 + 3 ^ 40 * 1870754 * 2
def baseEnd_1870754 : Nat := 960595988321278900071565

theorem tailTrace_1870754 : CollatzResearch.WordTrace tailWord_1870754 prefixEnd_1870754 960595988321278900071565 := by
  unfold tailWord_1870754
  simp only [CollatzResearch.WordTrace]
  refine ⟨17058000966146308047916829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45488002576390154794444877 17058000966146308047916829)
  ·
    refine ⟨6396750362304865517968811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17058000966146308047916829 6396750362304865517968811)
    ·
      refine ⟨9595125543457298276953217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6396750362304865517968811 9595125543457298276953217)
      ·
        refine ⟨7196344157592973707714913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9595125543457298276953217 7196344157592973707714913)
        ·
          refine ⟨5397258118194730280786185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7196344157592973707714913 5397258118194730280786185)
          ·
            refine ⟨4047943588646047710589639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397258118194730280786185 4047943588646047710589639)
            ·
              refine ⟨6071915382969071565884459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047943588646047710589639 6071915382969071565884459)
              ·
                refine ⟨9107873074453607348826689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071915382969071565884459 9107873074453607348826689)
                ·
                  refine ⟨6830904805840205511620017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9107873074453607348826689 6830904805840205511620017)
                  ·
                    refine ⟨5123178604380154133715013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6830904805840205511620017 5123178604380154133715013)
                    ·
                      refine ⟨960595988321278900071565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5123178604380154133715013 960595988321278900071565)
                      ·
                        rfl

theorem cell23_1870754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1870754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870754 prefixEnd_1870754 := by exact prefixLift 1870754
  have htrace : WordTrace (prefixWord ++ tailWord_1870754) baseStart_1870754 baseEnd_1870754 := by
    simpa [prefixWord, tailWord_1870754, baseEnd_1870754] using wordTrace_append hprefix tailTrace_1870754
  have hstable : (prefixWord ++ tailWord_1870754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870754).length < 2 ^ (prefixWord ++ tailWord_1870754).sum := by decide
  have hdescent : baseEnd_1870754 < baseStart_1870754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870777 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 1, 7]
def baseStart_1870777 : Nat := 118140960795 + 1870777 * 2 ^ 59
def prefixEnd_1870777 : Nat := 4983230072969 + 3 ^ 40 * 1870777 * 2
def baseEnd_1870777 : Nat := 320202599458777436694653

theorem tailTrace_1870777 : CollatzResearch.WordTrace tailWord_1870777 prefixEnd_1870777 320202599458777436694653 := by
  unfold tailWord_1870777
  simp only [CollatzResearch.WordTrace]
  refine ⟨68232842743501907119754585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45488561829001271413169723 68232842743501907119754585)
  ·
    refine ⟨51174632057626430339815939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68232842743501907119754585 51174632057626430339815939)
    ·
      refine ⟨76761948086439645509723909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51174632057626430339815939 76761948086439645509723909)
      ·
        refine ⟨14392865266207433533073233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76761948086439645509723909 14392865266207433533073233)
        ·
          refine ⟨10794648949655575149804925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14392865266207433533073233 10794648949655575149804925)
          ·
            refine ⟨4047993356120840681176847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10794648949655575149804925 4047993356120840681176847)
            ·
              refine ⟨6071990034181261021765271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047993356120840681176847 6071990034181261021765271)
              ·
                refine ⟨9107985051271891532647907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071990034181261021765271 9107985051271891532647907)
                ·
                  refine ⟨13661977576907837298971861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9107985051271891532647907 13661977576907837298971861)
                  ·
                    refine ⟨320202599458777436694653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13661977576907837298971861 320202599458777436694653)
                    ·
                      rfl

theorem cell23_1870777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_1870777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870777 prefixEnd_1870777 := by exact prefixLift 1870777
  have htrace : WordTrace (prefixWord ++ tailWord_1870777) baseStart_1870777 baseEnd_1870777 := by
    simpa [prefixWord, tailWord_1870777, baseEnd_1870777] using wordTrace_append hprefix tailTrace_1870777
  have hstable : (prefixWord ++ tailWord_1870777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870777).length < 2 ^ (prefixWord ++ tailWord_1870777).sum := by decide
  have hdescent : baseEnd_1870777 < baseStart_1870777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870781 : List Nat := [1, 4, 1, 2, 4, 1, 2, 3, 5]
def baseStart_1870781 : Nat := 118140960795 + 1870781 * 2 ^ 59
def prefixEnd_1870781 : Nat := 4983230072969 + 3 ^ 40 * 1870781 * 2
def baseEnd_1870781 : Nat := 106734428033216699381549

theorem tailTrace_1870781 : CollatzResearch.WordTrace tailWord_1870781 prefixEnd_1870781 106734428033216699381549 := by
  unfold tailWord_1870781
  simp only [CollatzResearch.WordTrace]
  refine ⟨68232988635487415802900197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45488659090324943868600131 68232988635487415802900197)
  ·
    refine ⟨12793685369153890463043787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68232988635487415802900197 12793685369153890463043787)
    ·
      refine ⟨19190528053730835694565681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12793685369153890463043787 19190528053730835694565681)
      ·
        refine ⟨14392896040298126770924261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19190528053730835694565681 14392896040298126770924261)
        ·
          refine ⟨2698668007555898769548299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14392896040298126770924261 2698668007555898769548299)
          ·
            refine ⟨4048002011333848154322449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698668007555898769548299 4048002011333848154322449)
            ·
              refine ⟨3036001508500386115741837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048002011333848154322449 3036001508500386115741837)
              ·
                refine ⟨1138500565687644793403189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3036001508500386115741837 1138500565687644793403189)
                ·
                  refine ⟨106734428033216699381549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1138500565687644793403189 106734428033216699381549)
                  ·
                    rfl

theorem cell23_1870781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_1870781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870781 prefixEnd_1870781 := by exact prefixLift 1870781
  have htrace : WordTrace (prefixWord ++ tailWord_1870781) baseStart_1870781 baseEnd_1870781 := by
    simpa [prefixWord, tailWord_1870781, baseEnd_1870781] using wordTrace_append hprefix tailTrace_1870781
  have hstable : (prefixWord ++ tailWord_1870781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870781).length < 2 ^ (prefixWord ++ tailWord_1870781).sum := by decide
  have hdescent : baseEnd_1870781 < baseStart_1870781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870824 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1870824 : Nat := 118140960795 + 1870824 * 2 ^ 59
def prefixEnd_1870824 : Nat := 4983230072969 + 3 ^ 40 * 1870824 * 2
def baseEnd_1870824 : Nat := 320210643989031208732081

theorem tailTrace_1870824 : CollatzResearch.WordTrace tailWord_1870824 prefixEnd_1870824 320210643989031208732081 := by
  unfold tailWord_1870824
  simp only [CollatzResearch.WordTrace]
  refine ⟨34117278487165817073357763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45489704649554422764477017 34117278487165817073357763)
  ·
    refine ⟨51175917730748725610036645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34117278487165817073357763 51175917730748725610036645)
    ·
      refine ⟨9595484574515386051881871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51175917730748725610036645 9595484574515386051881871)
      ·
        refine ⟨14393226861773079077822807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9595484574515386051881871 14393226861773079077822807)
        ·
          refine ⟨21589840292659618616734211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14393226861773079077822807 21589840292659618616734211)
          ·
            refine ⟨32384760438989427925101317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21589840292659618616734211 32384760438989427925101317)
            ·
              refine ⟨6072142582310517735956497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32384760438989427925101317 6072142582310517735956497)
              ·
                refine ⟨4554106936732888301967373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6072142582310517735956497 4554106936732888301967373)
                ·
                  refine ⟨1707790101274833113237765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4554106936732888301967373 1707790101274833113237765)
                  ·
                    refine ⟨320210643989031208732081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1707790101274833113237765 320210643989031208732081)
                    ·
                      rfl

theorem cell23_1870824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1870824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870824 prefixEnd_1870824 := by exact prefixLift 1870824
  have htrace : WordTrace (prefixWord ++ tailWord_1870824) baseStart_1870824 baseEnd_1870824 := by
    simpa [prefixWord, tailWord_1870824, baseEnd_1870824] using wordTrace_append hprefix tailTrace_1870824
  have hstable : (prefixWord ++ tailWord_1870824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870824).length < 2 ^ (prefixWord ++ tailWord_1870824).sum := by decide
  have hdescent : baseEnd_1870824 < baseStart_1870824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870867 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 3, 5]
def baseStart_1870867 : Nat := 118140960795 + 1870867 * 2 ^ 59
def prefixEnd_1870867 : Nat := 4983230072969 + 3 ^ 40 * 1870867 * 2
def baseEnd_1870867 : Nat := 320218003878412319319515

theorem tailTrace_1870867 : CollatzResearch.WordTrace tailWord_1870867 prefixEnd_1870867 320218003878412319319515 := by
  unfold tailWord_1870867
  simp only [CollatzResearch.WordTrace]
  refine ⟨68236125313175852490530855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45490750208783901660353903 68236125313175852490530855)
  ·
    refine ⟨102354187969763778735796283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68236125313175852490530855 102354187969763778735796283)
    ·
      refine ⟨153531281954645668103694425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102354187969763778735796283 153531281954645668103694425)
      ·
        refine ⟨115148461465984251077770819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153531281954645668103694425 115148461465984251077770819)
        ·
          refine ⟨172722692198976376616656229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115148461465984251077770819 172722692198976376616656229)
          ·
            refine ⟨32385504787308070615623043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172722692198976376616656229 32385504787308070615623043)
            ·
              refine ⟨48578257180962105923434565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32385504787308070615623043 48578257180962105923434565)
              ·
                refine ⟨9108423221430394860643981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48578257180962105923434565 9108423221430394860643981)
                ·
                  refine ⟨3415658708036398072741493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9108423221430394860643981 3415658708036398072741493)
                  ·
                    refine ⟨320218003878412319319515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3415658708036398072741493 320218003878412319319515)
                    ·
                      rfl

theorem cell23_1870867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 5].length) (baseStart_1870867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870867 prefixEnd_1870867 := by exact prefixLift 1870867
  have htrace : WordTrace (prefixWord ++ tailWord_1870867) baseStart_1870867 baseEnd_1870867 := by
    simpa [prefixWord, tailWord_1870867, baseEnd_1870867] using wordTrace_append hprefix tailTrace_1870867
  have hstable : (prefixWord ++ tailWord_1870867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870867).length < 2 ^ (prefixWord ++ tailWord_1870867).sum := by decide
  have hdescent : baseEnd_1870867 < baseStart_1870867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870871 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 6]
def baseStart_1870871 : Nat := 118140960795 + 1870871 * 2 ^ 59
def prefixEnd_1870871 : Nat := 4983230072969 + 3 ^ 40 * 1870871 * 2
def baseEnd_1870871 : Nat := 106739562839761660256503

theorem tailTrace_1870871 : CollatzResearch.WordTrace tailWord_1870871 prefixEnd_1870871 106739562839761660256503 := by
  unfold tailWord_1870871
  simp only [CollatzResearch.WordTrace]
  refine ⟨68236271205161361173676467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45490847470107574115784311 68236271205161361173676467)
  ·
    refine ⟨102354406807742041760514701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68236271205161361173676467 102354406807742041760514701)
    ·
      refine ⟨38382902552903265660193013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102354406807742041760514701 38382902552903265660193013)
      ·
        refine ⟨3598397114334681155643095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38382902552903265660193013 3598397114334681155643095)
        ·
          refine ⟨5397595671502021733464643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598397114334681155643095 5397595671502021733464643)
          ·
            refine ⟨8096393507253032600196965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397595671502021733464643 8096393507253032600196965)
            ·
              refine ⟨1518073782609943612536931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8096393507253032600196965 1518073782609943612536931)
              ·
                refine ⟨2277110673914915418805397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518073782609943612536931 2277110673914915418805397)
                ·
                  refine ⟨106739562839761660256503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2277110673914915418805397 106739562839761660256503)
                  ·
                    rfl

theorem cell23_1870871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 6].length) (baseStart_1870871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870871 prefixEnd_1870871 := by exact prefixLift 1870871
  have htrace : WordTrace (prefixWord ++ tailWord_1870871) baseStart_1870871 baseEnd_1870871 := by
    simpa [prefixWord, tailWord_1870871, baseEnd_1870871] using wordTrace_append hprefix tailTrace_1870871
  have hstable : (prefixWord ++ tailWord_1870871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870871).length < 2 ^ (prefixWord ++ tailWord_1870871).sum := by decide
  have hdescent : baseEnd_1870871 < baseStart_1870871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870891 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 2, 3, 2]
def baseStart_1870891 : Nat := 118140960795 + 1870891 * 2 ^ 59
def prefixEnd_1870891 : Nat := 4983230072969 + 3 ^ 40 * 1870891 * 2
def baseEnd_1870891 : Nat := 960666335170944864058435

theorem tailTrace_1870891 : CollatzResearch.WordTrace tailWord_1870891 prefixEnd_1870891 960666335170944864058435 := by
  unfold tailWord_1870891
  simp only [CollatzResearch.WordTrace]
  refine ⟨68237000665088904589404527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45491333776725936392936351 68237000665088904589404527)
  ·
    refine ⟨102355500997633356884106791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68237000665088904589404527 102355500997633356884106791)
    ·
      refine ⟨153533251496450035326160187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102355500997633356884106791 153533251496450035326160187)
      ·
        refine ⟨230299877244675052989240281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153533251496450035326160187 230299877244675052989240281)
        ·
          refine ⟨172724907933506289741930211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230299877244675052989240281 172724907933506289741930211)
          ·
            refine ⟨259087361900259434612895317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172724907933506289741930211 259087361900259434612895317)
            ·
              refine ⟨3036180022268665249369867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 259087361900259434612895317 3036180022268665249369867)
              ·
                refine ⟨4554270033402997874054801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036180022268665249369867 4554270033402997874054801)
                ·
                  refine ⟨3415702525052248405541101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554270033402997874054801 3415702525052248405541101)
                  ·
                    refine ⟨1280888446894593152077913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415702525052248405541101 1280888446894593152077913)
                    ·
                      refine ⟨960666335170944864058435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280888446894593152077913 960666335170944864058435)
                      ·
                        rfl

theorem cell23_1870891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 3, 2].length) (baseStart_1870891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870891 prefixEnd_1870891 := by exact prefixLift 1870891
  have htrace : WordTrace (prefixWord ++ tailWord_1870891) baseStart_1870891 baseEnd_1870891 := by
    simpa [prefixWord, tailWord_1870891, baseEnd_1870891] using wordTrace_append hprefix tailTrace_1870891
  have hstable : (prefixWord ++ tailWord_1870891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870891).length < 2 ^ (prefixWord ++ tailWord_1870891).sum := by decide
  have hdescent : baseEnd_1870891 < baseStart_1870891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870898 : List Nat := [3, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3]
def baseStart_1870898 : Nat := 118140960795 + 1870898 * 2 ^ 59
def prefixEnd_1870898 : Nat := 4983230072969 + 3 ^ 40 * 1870898 * 2
def baseEnd_1870898 : Nat := 960669929535526336670903

theorem tailTrace_1870898 : CollatzResearch.WordTrace tailWord_1870898 prefixEnd_1870898 960669929535526336670903 := by
  unfold tailWord_1870898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059313994015886196227337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45491503984042363189939565 17059313994015886196227337)
  ·
    refine ⟨12794485495511914647170503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17059313994015886196227337 12794485495511914647170503)
    ·
      refine ⟨19191728243267871970755755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12794485495511914647170503 19191728243267871970755755)
      ·
        refine ⟨28787592364901807956133633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19191728243267871970755755 28787592364901807956133633)
        ·
          refine ⟨21590694273676355967100225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28787592364901807956133633 21590694273676355967100225)
          ·
            refine ⟨16193020705257266975325169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21590694273676355967100225 16193020705257266975325169)
            ·
              refine ⟨12144765528942950231493877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16193020705257266975325169 12144765528942950231493877)
              ·
                refine ⟨1138571768338401584202551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12144765528942950231493877 1138571768338401584202551)
                ·
                  refine ⟨1707857652507602376303827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138571768338401584202551 1707857652507602376303827)
                  ·
                    refine ⟨2561786478761403564455741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1707857652507602376303827 2561786478761403564455741)
                    ·
                      refine ⟨960669929535526336670903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2561786478761403564455741 960669929535526336670903)
                      ·
                        rfl

theorem cell23_1870898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_1870898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870898 prefixEnd_1870898 := by exact prefixLift 1870898
  have htrace : WordTrace (prefixWord ++ tailWord_1870898) baseStart_1870898 baseEnd_1870898 := by
    simpa [prefixWord, tailWord_1870898, baseEnd_1870898] using wordTrace_append hprefix tailTrace_1870898
  have hstable : (prefixWord ++ tailWord_1870898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870898).length < 2 ^ (prefixWord ++ tailWord_1870898).sum := by decide
  have hdescent : baseEnd_1870898 < baseStart_1870898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870917 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_1870917 : Nat := 118140960795 + 1870917 * 2 ^ 59
def prefixEnd_1870917 : Nat := 4983230072969 + 3 ^ 40 * 1870917 * 2
def baseEnd_1870917 : Nat := 960679685667961762333315

theorem tailTrace_1870917 : CollatzResearch.WordTrace tailWord_1870917 prefixEnd_1870917 960679685667961762333315 := by
  unfold tailWord_1870917
  simp only [CollatzResearch.WordTrace]
  refine ⟨68237948962994711029851005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45491965975329807353234003 68237948962994711029851005)
  ·
    refine ⟨25589230861123016636194127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68237948962994711029851005 25589230861123016636194127)
    ·
      refine ⟨38383846291684524954291191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25589230861123016636194127 38383846291684524954291191)
      ·
        refine ⟨57575769437526787431436787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38383846291684524954291191 57575769437526787431436787)
        ·
          refine ⟨86363654156290181147155181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57575769437526787431436787 86363654156290181147155181)
          ·
            refine ⟨32386370308608817930183193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86363654156290181147155181 32386370308608817930183193)
            ·
              refine ⟨24289777731456613447637395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32386370308608817930183193 24289777731456613447637395)
              ·
                refine ⟨36434666597184920171456093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24289777731456613447637395 36434666597184920171456093)
                ·
                  refine ⟨13662999973944345064296035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36434666597184920171456093 13662999973944345064296035)
                  ·
                    refine ⟨20494499960916517596444053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13662999973944345064296035 20494499960916517596444053)
                    ·
                      refine ⟨960679685667961762333315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20494499960916517596444053 960679685667961762333315)
                      ·
                        rfl

theorem cell23_1870917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_1870917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870917 prefixEnd_1870917 := by exact prefixLift 1870917
  have htrace : WordTrace (prefixWord ++ tailWord_1870917) baseStart_1870917 baseEnd_1870917 := by
    simpa [prefixWord, tailWord_1870917, baseEnd_1870917] using wordTrace_append hprefix tailTrace_1870917
  have hstable : (prefixWord ++ tailWord_1870917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870917).length < 2 ^ (prefixWord ++ tailWord_1870917).sum := by decide
  have hdescent : baseEnd_1870917 < baseStart_1870917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870942 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_1870942 : Nat := 118140960795 + 1870942 * 2 ^ 59
def prefixEnd_1870942 : Nat := 4983230072969 + 3 ^ 40 * 1870942 * 2
def baseEnd_1870942 : Nat := 960692522684324164520701

theorem tailTrace_1870942 : CollatzResearch.WordTrace tailWord_1870942 prefixEnd_1870942 960692522684324164520701 := by
  unfold tailWord_1870942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8529857598488017537438885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45492573858602760199674053 8529857598488017537438885)
  ·
    refine ⟨1599348299716503288269791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8529857598488017537438885 1599348299716503288269791)
    ·
      refine ⟨2399022449574754932404687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599348299716503288269791 2399022449574754932404687)
      ·
        refine ⟨3598533674362132398607031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399022449574754932404687 3598533674362132398607031)
        ·
          refine ⟨5397800511543198597910547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598533674362132398607031 5397800511543198597910547)
          ·
            refine ⟨8096700767314797896865821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397800511543198597910547 8096700767314797896865821)
            ·
              refine ⟨3036262787743049211324683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8096700767314797896865821 3036262787743049211324683)
              ·
                refine ⟨4554394181614573816987025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036262787743049211324683 4554394181614573816987025)
                ·
                  refine ⟨3415795636210930362740269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554394181614573816987025 3415795636210930362740269)
                  ·
                    refine ⟨1280923363579098886027601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415795636210930362740269 1280923363579098886027601)
                    ·
                      refine ⟨960692522684324164520701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280923363579098886027601 960692522684324164520701)
                      ·
                        rfl

theorem cell23_1870942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_1870942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870942 prefixEnd_1870942 := by exact prefixLift 1870942
  have htrace : WordTrace (prefixWord ++ tailWord_1870942) baseStart_1870942 baseEnd_1870942 := by
    simpa [prefixWord, tailWord_1870942, baseEnd_1870942] using wordTrace_append hprefix tailTrace_1870942
  have hstable : (prefixWord ++ tailWord_1870942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870942).length < 2 ^ (prefixWord ++ tailWord_1870942).sum := by decide
  have hdescent : baseEnd_1870942 < baseStart_1870942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870944 : List Nat := [2, 1, 1, 3, 2, 2, 5, 7]
def baseStart_1870944 : Nat := 118140960795 + 1870944 * 2 ^ 59
def prefixEnd_1870944 : Nat := 4983230072969 + 3 ^ 40 * 1870944 * 2
def baseEnd_1870944 : Nat := 35581242579467894692433

theorem tailTrace_1870944 : CollatzResearch.WordTrace tailWord_1870944 prefixEnd_1870944 35581242579467894692433 := by
  unfold tailWord_1870944
  simp only [CollatzResearch.WordTrace]
  refine ⟨34119466866948447320541943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45492622489264596427389257 34119466866948447320541943)
  ·
    refine ⟨51179200300422670980812915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34119466866948447320541943 51179200300422670980812915)
    ·
      refine ⟨76768800450634006471219373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51179200300422670980812915 76768800450634006471219373)
      ·
        refine ⟨28788300168987752426707265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76768800450634006471219373 28788300168987752426707265)
        ·
          refine ⟨21591225126740814320030449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28788300168987752426707265 21591225126740814320030449)
          ·
            refine ⟨16193418845055610740022837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21591225126740814320030449 16193418845055610740022837)
            ·
              refine ⟨1518133016723963506877141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16193418845055610740022837 1518133016723963506877141)
              ·
                refine ⟨35581242579467894692433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1518133016723963506877141 35581242579467894692433)
                ·
                  rfl

theorem cell23_1870944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 7].length) (baseStart_1870944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870944 prefixEnd_1870944 := by exact prefixLift 1870944
  have htrace : WordTrace (prefixWord ++ tailWord_1870944) baseStart_1870944 baseEnd_1870944 := by
    simpa [prefixWord, tailWord_1870944, baseEnd_1870944] using wordTrace_append hprefix tailTrace_1870944
  have hstable : (prefixWord ++ tailWord_1870944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870944).length < 2 ^ (prefixWord ++ tailWord_1870944).sum := by decide
  have hdescent : baseEnd_1870944 < baseStart_1870944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870952 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 1, 5]
def baseStart_1870952 : Nat := 118140960795 + 1870952 * 2 ^ 59
def prefixEnd_1870952 : Nat := 4983230072969 + 3 ^ 40 * 1870952 * 2
def baseEnd_1870952 : Nat := 320232552496956375131885

theorem tailTrace_1870952 : CollatzResearch.WordTrace tailWord_1870952 prefixEnd_1870952 320232552496956375131885 := by
  unfold tailWord_1870952
  simp only [CollatzResearch.WordTrace]
  refine ⟨34119612758933956003687555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45492817011911941338250073 34119612758933956003687555)
  ·
    refine ⟨51179419138400934005531333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34119612758933956003687555 51179419138400934005531333)
    ·
      refine ⟨9596141088450175126037125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51179419138400934005531333 9596141088450175126037125)
      ·
        refine ⟨1799276454084407836131961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9596141088450175126037125 1799276454084407836131961)
        ·
          refine ⟨1349457340563305877098971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1799276454084407836131961 1349457340563305877098971)
          ·
            refine ⟨2024186010844958815648457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349457340563305877098971 2024186010844958815648457)
            ·
              refine ⟨1518139508133719111736343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2024186010844958815648457 1518139508133719111736343)
              ·
                refine ⟨2277209262200578667604515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518139508133719111736343 2277209262200578667604515)
                ·
                  refine ⟨3415813893300868001406773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277209262200578667604515 3415813893300868001406773)
                  ·
                    refine ⟨320232552496956375131885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3415813893300868001406773 320232552496956375131885)
                    ·
                      rfl

theorem cell23_1870952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_1870952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870952 prefixEnd_1870952 := by exact prefixLift 1870952
  have htrace : WordTrace (prefixWord ++ tailWord_1870952) baseStart_1870952 baseEnd_1870952 := by
    simpa [prefixWord, tailWord_1870952, baseEnd_1870952] using wordTrace_append hprefix tailTrace_1870952
  have hstable : (prefixWord ++ tailWord_1870952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870952).length < 2 ^ (prefixWord ++ tailWord_1870952).sum := by decide
  have hdescent : baseEnd_1870952 < baseStart_1870952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870958 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1870958 : Nat := 118140960795 + 1870958 * 2 ^ 59
def prefixEnd_1870958 : Nat := 4983230072969 + 3 ^ 40 * 1870958 * 2
def baseEnd_1870958 : Nat := 960700738374796101920627

theorem tailTrace_1870958 : CollatzResearch.WordTrace tailWord_1870958 prefixEnd_1870958 960700738374796101920627 := by
  unfold tailWord_1870958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8529930544480771879011691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45492962903897450021395685 8529930544480771879011691)
  ·
    refine ⟨12794895816721157818517537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8529930544480771879011691 12794895816721157818517537)
    ·
      refine ⟨9596171862540868363888153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12794895816721157818517537 9596171862540868363888153)
      ·
        refine ⟨7197128896905651272916115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9596171862540868363888153 7197128896905651272916115)
        ·
          refine ⟨10795693345358476909374173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7197128896905651272916115 10795693345358476909374173)
          ·
            refine ⟨4048385004509428841015315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10795693345358476909374173 4048385004509428841015315)
            ·
              refine ⟨6072577506764143261522973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048385004509428841015315 6072577506764143261522973)
              ·
                refine ⟨2277216565036553723071115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6072577506764143261522973 2277216565036553723071115)
                ·
                  refine ⟨3415824847554830584606673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277216565036553723071115 3415824847554830584606673)
                  ·
                    refine ⟨2561868635666122938455005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3415824847554830584606673 2561868635666122938455005)
                    ·
                      refine ⟨960700738374796101920627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2561868635666122938455005 960700738374796101920627)
                      ·
                        rfl

theorem cell23_1870958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1870958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1870958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1870958 prefixEnd_1870958 := by exact prefixLift 1870958
  have htrace : WordTrace (prefixWord ++ tailWord_1870958) baseStart_1870958 baseEnd_1870958 := by
    simpa [prefixWord, tailWord_1870958, baseEnd_1870958] using wordTrace_append hprefix tailTrace_1870958
  have hstable : (prefixWord ++ tailWord_1870958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870958).length < 2 ^ (prefixWord ++ tailWord_1870958).sum := by decide
  have hdescent : baseEnd_1870958 < baseStart_1870958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871011 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 1, 4, 2]
def baseStart_1871011 : Nat := 118140960795 + 1871011 * 2 ^ 59
def prefixEnd_1871011 : Nat := 4983230072969 + 3 ^ 40 * 1871011 * 2
def baseEnd_1871011 : Nat := 960727952849484394557883

theorem tailTrace_1871011 : CollatzResearch.WordTrace tailWord_1871011 prefixEnd_1871011 960727952849484394557883 := by
  unfold tailWord_1871011
  simp only [CollatzResearch.WordTrace]
  refine ⟨68241377424654165083772887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45494251616436110055848591 68241377424654165083772887)
  ·
    refine ⟨102362066136981247625659331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68241377424654165083772887 102362066136981247625659331)
    ·
      refine ⟨153543099205471871438488997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102362066136981247625659331 153543099205471871438488997)
      ·
        refine ⟨28789331101025975894716687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153543099205471871438488997 28789331101025975894716687)
        ·
          refine ⟨43183996651538963842075031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28789331101025975894716687 43183996651538963842075031)
          ·
            refine ⟨64775994977308445763112547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43183996651538963842075031 64775994977308445763112547)
            ·
              refine ⟨97163992465962668644668821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64775994977308445763112547 97163992465962668644668821)
              ·
                refine ⟨4554562146842000092718851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97163992465962668644668821 4554562146842000092718851)
                ·
                  refine ⟨6831843220263000139078277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554562146842000092718851 6831843220263000139078277)
                  ·
                    refine ⟨1280970603799312526077177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6831843220263000139078277 1280970603799312526077177)
                    ·
                      refine ⟨960727952849484394557883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280970603799312526077177 960727952849484394557883)
                      ·
                        rfl

theorem cell23_1871011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_1871011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871011 prefixEnd_1871011 := by exact prefixLift 1871011
  have htrace : WordTrace (prefixWord ++ tailWord_1871011) baseStart_1871011 baseEnd_1871011 := by
    simpa [prefixWord, tailWord_1871011, baseEnd_1871011] using wordTrace_append hprefix tailTrace_1871011
  have hstable : (prefixWord ++ tailWord_1871011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871011).length < 2 ^ (prefixWord ++ tailWord_1871011).sum := by decide
  have hdescent : baseEnd_1871011 < baseStart_1871011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871015 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_1871015 : Nat := 118140960795 + 1871015 * 2 ^ 59
def prefixEnd_1871015 : Nat := 4983230072969 + 3 ^ 40 * 1871015 * 2
def baseEnd_1871015 : Nat := 960730006772102378907865

theorem tailTrace_1871015 : CollatzResearch.WordTrace tailWord_1871015 prefixEnd_1871015 960730006772102378907865 := by
  unfold tailWord_1871015
  simp only [CollatzResearch.WordTrace]
  refine ⟨68241523316639673766918499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45494348877759782511278999 68241523316639673766918499)
  ·
    refine ⟨102362284974959510650377749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68241523316639673766918499 102362284974959510650377749)
    ·
      refine ⟨4798232108201227061736457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102362284974959510650377749 4798232108201227061736457)
      ·
        refine ⟨3598674081150920296302343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4798232108201227061736457 3598674081150920296302343)
        ·
          refine ⟨5398011121726380444453515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598674081150920296302343 5398011121726380444453515)
          ·
            refine ⟨8097016682589570666680273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398011121726380444453515 8097016682589570666680273)
            ·
              refine ⟨6072762511942178000010205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8097016682589570666680273 6072762511942178000010205)
              ·
                refine ⟨2277285941978316750003827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6072762511942178000010205 2277285941978316750003827)
                ·
                  refine ⟨3415928912967475125005741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277285941978316750003827 3415928912967475125005741)
                  ·
                    refine ⟨1280973342362803171877153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415928912967475125005741 1280973342362803171877153)
                    ·
                      refine ⟨960730006772102378907865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1280973342362803171877153 960730006772102378907865)
                      ·
                        rfl

theorem cell23_1871015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_1871015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871015 prefixEnd_1871015 := by exact prefixLift 1871015
  have htrace : WordTrace (prefixWord ++ tailWord_1871015) baseStart_1871015 baseEnd_1871015 := by
    simpa [prefixWord, tailWord_1871015, baseEnd_1871015] using wordTrace_append hprefix tailTrace_1871015
  have hstable : (prefixWord ++ tailWord_1871015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871015).length < 2 ^ (prefixWord ++ tailWord_1871015).sum := by decide
  have hdescent : baseEnd_1871015 < baseStart_1871015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871062 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_1871062 : Nat := 118140960795 + 1871062 * 2 ^ 59
def prefixEnd_1871062 : Nat := 4983230072969 + 3 ^ 40 * 1871062 * 2
def baseEnd_1871062 : Nat := 960754140362863695020149

theorem tailTrace_1871062 : CollatzResearch.WordTrace tailWord_1871062 prefixEnd_1871062 960754140362863695020149 := by
  unfold tailWord_1871062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4265202346716837549617465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45495491698312933862586293 4265202346716837549617465)
  ·
    refine ⟨3198901760037628162213099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4265202346716837549617465 3198901760037628162213099)
    ·
      refine ⟨4798352640056442243319649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3198901760037628162213099 4798352640056442243319649)
      ·
        refine ⟨3598764480042331682489737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4798352640056442243319649 3598764480042331682489737)
        ·
          refine ⟨2699073360031748761867303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3598764480042331682489737 2699073360031748761867303)
          ·
            refine ⟨4048610040047623142800955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699073360031748761867303 4048610040047623142800955)
            ·
              refine ⟨6072915060071434714201433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048610040047623142800955 6072915060071434714201433)
              ·
                refine ⟨4554686295053576035651075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6072915060071434714201433 4554686295053576035651075)
                ·
                  refine ⟨6832029442580364053476613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554686295053576035651075 6832029442580364053476613)
                  ·
                    refine ⟨1281005520483818260026865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6832029442580364053476613 1281005520483818260026865)
                    ·
                      refine ⟨960754140362863695020149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281005520483818260026865 960754140362863695020149)
                      ·
                        rfl

theorem cell23_1871062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_1871062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871062 prefixEnd_1871062 := by exact prefixLift 1871062
  have htrace : WordTrace (prefixWord ++ tailWord_1871062) baseStart_1871062 baseEnd_1871062 := by
    simpa [prefixWord, tailWord_1871062, baseEnd_1871062] using wordTrace_append hprefix tailTrace_1871062
  have hstable : (prefixWord ++ tailWord_1871062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871062).length < 2 ^ (prefixWord ++ tailWord_1871062).sum := by decide
  have hdescent : baseEnd_1871062 < baseStart_1871062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871085 : List Nat := [1, 5, 1, 2, 2, 1, 4, 2, 5]
def baseStart_1871085 : Nat := 118140960795 + 1871085 * 2 ^ 59
def prefixEnd_1871085 : Nat := 4983230072969 + 3 ^ 40 * 1871085 * 2
def baseEnd_1871085 : Nat := 106751772268657456114727

theorem tailTrace_1871085 : CollatzResearch.WordTrace tailWord_1871085 prefixEnd_1871085 106751772268657456114727 := by
  unfold tailWord_1871085
  simp only [CollatzResearch.WordTrace]
  refine ⟨68244076426386075721966709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45496050950924050481311139 68244076426386075721966709)
  ·
    refine ⟨6397882164973694598934379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68244076426386075721966709 6397882164973694598934379)
    ·
      refine ⟨9596823247460541898401569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6397882164973694598934379 9596823247460541898401569)
      ·
        refine ⟨7197617435595406423801177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9596823247460541898401569 7197617435595406423801177)
        ·
          refine ⟨5398213076696554817850883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7197617435595406423801177 5398213076696554817850883)
          ·
            refine ⟨8097319615044832226776325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398213076696554817850883 8097319615044832226776325)
            ·
              refine ⟨1518247427820906042520561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8097319615044832226776325 1518247427820906042520561)
              ·
                refine ⟨1138685570865679531890421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1518247427820906042520561 1138685570865679531890421)
                ·
                  refine ⟨106751772268657456114727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1138685570865679531890421 106751772268657456114727)
                  ·
                    rfl

theorem cell23_1871085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_1871085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871085 prefixEnd_1871085 := by exact prefixLift 1871085
  have htrace : WordTrace (prefixWord ++ tailWord_1871085) baseStart_1871085 baseEnd_1871085 := by
    simpa [prefixWord, tailWord_1871085, baseEnd_1871085] using wordTrace_append hprefix tailTrace_1871085
  have hstable : (prefixWord ++ tailWord_1871085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871085).length < 2 ^ (prefixWord ++ tailWord_1871085).sum := by decide
  have hdescent : baseEnd_1871085 < baseStart_1871085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871092 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1871092 : Nat := 118140960795 + 1871092 * 2 ^ 59
def prefixEnd_1871092 : Nat := 4983230072969 + 3 ^ 40 * 1871092 * 2
def baseEnd_1871092 : Nat := 960769544782498577645011

theorem tailTrace_1871092 : CollatzResearch.WordTrace tailWord_1871092 prefixEnd_1871092 960769544782498577645011 := by
  unfold tailWord_1871092
  simp only [CollatzResearch.WordTrace]
  refine ⟨34122165868680357958735765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45496221158240477278314353 34122165868680357958735765)
  ·
    refine ⟨1599476525094391779315739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34122165868680357958735765 1599476525094391779315739)
    ·
      refine ⟨2399214787641587668973609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599476525094391779315739 2399214787641587668973609)
      ·
        refine ⟨1799411090731190751730207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2399214787641587668973609 1799411090731190751730207)
        ·
          refine ⟨2699116636096786127595311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1799411090731190751730207 2699116636096786127595311)
          ·
            refine ⟨4048674954145179191392967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699116636096786127595311 4048674954145179191392967)
            ·
              refine ⟨6073012431217768787089451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048674954145179191392967 6073012431217768787089451)
              ·
                refine ⟨9109518646826653180634177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073012431217768787089451 9109518646826653180634177)
                ·
                  refine ⟨6832138985119989885475633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9109518646826653180634177 6832138985119989885475633)
                  ·
                    refine ⟨5124104238839992414106725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6832138985119989885475633 5124104238839992414106725)
                    ·
                      refine ⟨960769544782498577645011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5124104238839992414106725 960769544782498577645011)
                      ·
                        rfl

theorem cell23_1871092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1871092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871092 prefixEnd_1871092 := by exact prefixLift 1871092
  have htrace : WordTrace (prefixWord ++ tailWord_1871092) baseStart_1871092 baseEnd_1871092 := by
    simpa [prefixWord, tailWord_1871092, baseEnd_1871092] using wordTrace_append hprefix tailTrace_1871092
  have hstable : (prefixWord ++ tailWord_1871092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871092).length < 2 ^ (prefixWord ++ tailWord_1871092).sum := by decide
  have hdescent : baseEnd_1871092 < baseStart_1871092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871118 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1871118 : Nat := 118140960795 + 1871118 * 2 ^ 59
def prefixEnd_1871118 : Nat := 4983230072969 + 3 ^ 40 * 1871118 * 2
def baseEnd_1871118 : Nat := 960782895279515475919891

theorem tailTrace_1871118 : CollatzResearch.WordTrace tailWord_1871118 prefixEnd_1871118 960782895279515475919891 := by
  unfold tailWord_1871118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8530660004408315294739751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45496853356844348238612005 8530660004408315294739751)
  ·
    refine ⟨12795990006612472942109627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8530660004408315294739751 12795990006612472942109627)
    ·
      refine ⟨19193985009918709413164441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12795990006612472942109627 19193985009918709413164441)
      ·
        refine ⟨14395488757439032059873331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19193985009918709413164441 14395488757439032059873331)
        ·
          refine ⟨21593233136158548089809997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14395488757439032059873331 21593233136158548089809997)
          ·
            refine ⟨8097462426059455533678749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21593233136158548089809997 8097462426059455533678749)
            ·
              refine ⟨3036548409772295825129531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8097462426059455533678749 3036548409772295825129531)
              ·
                refine ⟨4554822614658443737694297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036548409772295825129531 4554822614658443737694297)
                ·
                  refine ⟨3416116960993832803270723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554822614658443737694297 3416116960993832803270723)
                  ·
                    refine ⟨5124175441490749204906085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3416116960993832803270723 5124175441490749204906085)
                    ·
                      refine ⟨960782895279515475919891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5124175441490749204906085 960782895279515475919891)
                      ·
                        rfl

theorem cell23_1871118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1871118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871118 prefixEnd_1871118 := by exact prefixLift 1871118
  have htrace : WordTrace (prefixWord ++ tailWord_1871118) baseStart_1871118 baseEnd_1871118 := by
    simpa [prefixWord, tailWord_1871118, baseEnd_1871118] using wordTrace_append hprefix tailTrace_1871118
  have hstable : (prefixWord ++ tailWord_1871118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871118).length < 2 ^ (prefixWord ++ tailWord_1871118).sum := by decide
  have hdescent : baseEnd_1871118 < baseStart_1871118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871121 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_1871121 : Nat := 118140960795 + 1871121 * 2 ^ 59
def prefixEnd_1871121 : Nat := 4983230072969 + 3 ^ 40 * 1871121 * 2
def baseEnd_1871121 : Nat := 960784435721478964182377

theorem tailTrace_1871121 : CollatzResearch.WordTrace tailWord_1871121 prefixEnd_1871121 960784435721478964182377 := by
  unfold tailWord_1871121
  simp only [CollatzResearch.WordTrace]
  refine ⟨68245389454255653870277217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45496926302837102580184811 68245389454255653870277217)
  ·
    refine ⟨51184042090691740402707913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68245389454255653870277217 51184042090691740402707913)
    ·
      refine ⟨38388031568018805302030935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51184042090691740402707913 38388031568018805302030935)
      ·
        refine ⟨57582047352028207953046403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38388031568018805302030935 57582047352028207953046403)
        ·
          refine ⟨86373071028042311929569605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57582047352028207953046403 86373071028042311929569605)
          ·
            refine ⟨16194950817757933486794301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86373071028042311929569605 16194950817757933486794301)
            ·
              refine ⟨6073106556659225057547863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16194950817757933486794301 6073106556659225057547863)
              ·
                refine ⟨9109659834988837586321795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073106556659225057547863 9109659834988837586321795)
                ·
                  refine ⟨13664489752483256379482693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9109659834988837586321795 13664489752483256379482693)
                  ·
                    refine ⟨2562091828590610571153005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13664489752483256379482693 2562091828590610571153005)
                    ·
                      refine ⟨960784435721478964182377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2562091828590610571153005 960784435721478964182377)
                      ·
                        rfl

theorem cell23_1871121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_1871121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871121 prefixEnd_1871121 := by exact prefixLift 1871121
  have htrace : WordTrace (prefixWord ++ tailWord_1871121) baseStart_1871121 baseEnd_1871121 := by
    simpa [prefixWord, tailWord_1871121, baseEnd_1871121] using wordTrace_append hprefix tailTrace_1871121
  have hstable : (prefixWord ++ tailWord_1871121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871121).length < 2 ^ (prefixWord ++ tailWord_1871121).sum := by decide
  have hdescent : baseEnd_1871121 < baseStart_1871121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871141 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 8]
def baseStart_1871141 : Nat := 118140960795 + 1871141 * 2 ^ 59
def prefixEnd_1871141 : Nat := 4983230072969 + 3 ^ 40 * 1871141 * 2
def baseEnd_1871141 : Nat := 106754967259396542881365

theorem tailTrace_1871141 : CollatzResearch.WordTrace tailWord_1871141 prefixEnd_1871141 106754967259396542881365 := by
  unfold tailWord_1871141
  simp only [CollatzResearch.WordTrace]
  refine ⟨68246118914183197286005277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45497412609455464857336851 68246118914183197286005277)
  ·
    refine ⟨25592294592818698982251979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68246118914183197286005277 25592294592818698982251979)
    ·
      refine ⟨38388441889228048473377969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25592294592818698982251979 38388441889228048473377969)
      ·
        refine ⟨28791331416921036355033477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38388441889228048473377969 28791331416921036355033477)
        ·
          refine ⟨5398374640672694316568777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28791331416921036355033477 5398374640672694316568777)
          ·
            refine ⟨4048780980504520737426583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5398374640672694316568777 4048780980504520737426583)
            ·
              refine ⟨6073171470756781106139875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048780980504520737426583 6073171470756781106139875)
              ·
                refine ⟨9109757206135171659209813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073171470756781106139875 9109757206135171659209813)
                ·
                  refine ⟨106754967259396542881365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9109757206135171659209813 106754967259396542881365)
                  ·
                    rfl

theorem cell23_1871141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_1871141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871141 prefixEnd_1871141 := by exact prefixLift 1871141
  have htrace : WordTrace (prefixWord ++ tailWord_1871141) baseStart_1871141 baseEnd_1871141 := by
    simpa [prefixWord, tailWord_1871141, baseEnd_1871141] using wordTrace_append hprefix tailTrace_1871141
  have hstable : (prefixWord ++ tailWord_1871141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871141).length < 2 ^ (prefixWord ++ tailWord_1871141).sum := by decide
  have hdescent : baseEnd_1871141 < baseStart_1871141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871168 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 3, 1, 3]
def baseStart_1871168 : Nat := 118140960795 + 1871168 * 2 ^ 59
def prefixEnd_1871168 : Nat := 4983230072969 + 3 ^ 40 * 1871168 * 2
def baseEnd_1871168 : Nat := 960808569312240280294661

theorem tailTrace_1871168 : CollatzResearch.WordTrace tailWord_1871168 prefixEnd_1871168 960808569312240280294661 := by
  unfold tailWord_1871168
  simp only [CollatzResearch.WordTrace]
  refine ⟨34123551842542690448619079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45498069123390253931492105 34123551842542690448619079)
  ·
    refine ⟨51185327763814035672928619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34123551842542690448619079 51185327763814035672928619)
    ·
      refine ⟨76777991645721053509392929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51185327763814035672928619 76777991645721053509392929)
      ·
        refine ⟨57583493734290790132044697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76777991645721053509392929 57583493734290790132044697)
        ·
          refine ⟨43187620300718092599033523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57583493734290790132044697 43187620300718092599033523)
          ·
            refine ⟨64781430451077138898550285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43187620300718092599033523 64781430451077138898550285)
            ·
              refine ⟨24293036419153927086956357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64781430451077138898550285 24293036419153927086956357)
              ·
                refine ⟨4554944328591361328804317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24293036419153927086956357 4554944328591361328804317)
                ·
                  refine ⟨1708104123221760498301619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4554944328591361328804317 1708104123221760498301619)
                  ·
                    refine ⟨2562156184832640747452429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1708104123221760498301619 2562156184832640747452429)
                    ·
                      refine ⟨960808569312240280294661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2562156184832640747452429 960808569312240280294661)
                      ·
                        rfl

theorem cell23_1871168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_1871168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871168 prefixEnd_1871168 := by exact prefixLift 1871168
  have htrace : WordTrace (prefixWord ++ tailWord_1871168) baseStart_1871168 baseEnd_1871168 := by
    simpa [prefixWord, tailWord_1871168, baseEnd_1871168] using wordTrace_append hprefix tailTrace_1871168
  have hstable : (prefixWord ++ tailWord_1871168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871168).length < 2 ^ (prefixWord ++ tailWord_1871168).sum := by decide
  have hdescent : baseEnd_1871168 < baseStart_1871168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871178 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_1871178 : Nat := 118140960795 + 1871178 * 2 ^ 59
def prefixEnd_1871178 : Nat := 4983230072969 + 3 ^ 40 * 1871178 * 2
def baseEnd_1871178 : Nat := 960813704118785241169615

theorem tailTrace_1871178 : CollatzResearch.WordTrace tailWord_1871178 prefixEnd_1871178 960813704118785241169615 := by
  unfold tailWord_1871178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17061867103762288151275547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45498312276699435070068125 17061867103762288151275547)
  ·
    refine ⟨25592800655643432226913321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17061867103762288151275547 25592800655643432226913321)
    ·
      refine ⟨19194600491732574170184991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25592800655643432226913321 19194600491732574170184991)
      ·
        refine ⟨28791900737598861255277487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19194600491732574170184991 28791900737598861255277487)
        ·
          refine ⟨43187851106398291882916231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28791900737598861255277487 43187851106398291882916231)
          ·
            refine ⟨64781776659597437824374347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43187851106398291882916231 64781776659597437824374347)
            ·
              refine ⟨97172664989396156736561521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64781776659597437824374347 97172664989396156736561521)
              ·
                refine ⟨72879498742047117552421141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97172664989396156736561521 72879498742047117552421141)
                ·
                  refine ⟨3416226503533458635269741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72879498742047117552421141 3416226503533458635269741)
                  ·
                    refine ⟨1281084938825046988226153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3416226503533458635269741 1281084938825046988226153)
                    ·
                      refine ⟨960813704118785241169615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281084938825046988226153 960813704118785241169615)
                      ·
                        rfl

theorem cell23_1871178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_1871178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871178 prefixEnd_1871178 := by exact prefixLift 1871178
  have htrace : WordTrace (prefixWord ++ tailWord_1871178) baseStart_1871178 baseEnd_1871178 := by
    simpa [prefixWord, tailWord_1871178, baseEnd_1871178] using wordTrace_append hprefix tailTrace_1871178
  have hstable : (prefixWord ++ tailWord_1871178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871178).length < 2 ^ (prefixWord ++ tailWord_1871178).sum := by decide
  have hdescent : baseEnd_1871178 < baseStart_1871178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871188 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1871188 : Nat := 118140960795 + 1871188 * 2 ^ 59
def prefixEnd_1871188 : Nat := 4983230072969 + 3 ^ 40 * 1871188 * 2
def baseEnd_1871188 : Nat := 320272946308443400681523

theorem tailTrace_1871188 : CollatzResearch.WordTrace tailWord_1871188 prefixEnd_1871188 320272946308443400681523 := by
  unfold tailWord_1871188
  simp only [CollatzResearch.WordTrace]
  refine ⟨34123916572506462156483109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45498555430008616208644145 34123916572506462156483109)
  ·
    refine ⟨6398234357344961654340583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34123916572506462156483109 6398234357344961654340583)
    ·
      refine ⟨9597351536017442481510875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6398234357344961654340583 9597351536017442481510875)
      ·
        refine ⟨14396027304026163722266313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9597351536017442481510875 14396027304026163722266313)
        ·
          refine ⟨10797020478019622791699735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14396027304026163722266313 10797020478019622791699735)
          ·
            refine ⟨16195530717029434187549603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797020478019622791699735 16195530717029434187549603)
            ·
              refine ⟨24293296075544151281324405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16195530717029434187549603 24293296075544151281324405)
              ·
                refine ⟨2277496507082264182624163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24293296075544151281324405 2277496507082264182624163)
                ·
                  refine ⟨3416244760623396273936245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277496507082264182624163 3416244760623396273936245)
                  ·
                    refine ⟨320272946308443400681523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3416244760623396273936245 320272946308443400681523)
                    ·
                      rfl

theorem cell23_1871188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1871188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871188 prefixEnd_1871188 := by exact prefixLift 1871188
  have htrace : WordTrace (prefixWord ++ tailWord_1871188) baseStart_1871188 baseEnd_1871188 := by
    simpa [prefixWord, tailWord_1871188, baseEnd_1871188] using wordTrace_append hprefix tailTrace_1871188
  have hstable : (prefixWord ++ tailWord_1871188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871188).length < 2 ^ (prefixWord ++ tailWord_1871188).sum := by decide
  have hdescent : baseEnd_1871188 < baseStart_1871188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871225 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 3, 2, 2]
def baseStart_1871225 : Nat := 118140960795 + 1871225 * 2 ^ 59
def prefixEnd_1871225 : Nat := 4983230072969 + 3 ^ 40 * 1871225 * 2
def baseEnd_1871225 : Nat := 960837837709546557281899

theorem tailTrace_1871225 : CollatzResearch.WordTrace tailWord_1871225 prefixEnd_1871225 960837837709546557281899 := by
  unfold tailWord_1871225
  simp only [CollatzResearch.WordTrace]
  refine ⟨68249182645878879632063129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45499455097252586421375419 68249182645878879632063129)
  ·
    refine ⟨51186886984409159724047347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68249182645878879632063129 51186886984409159724047347)
    ·
      refine ⟨76780330476613739586071021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51186886984409159724047347 76780330476613739586071021)
      ·
        refine ⟨28792623928730152344776633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76780330476613739586071021 28792623928730152344776633)
        ·
          refine ⟨21594467946547614258582475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28792623928730152344776633 21594467946547614258582475)
          ·
            refine ⟨32391701919821421387873713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21594467946547614258582475 32391701919821421387873713)
            ·
              refine ⟨24293776439866066040905285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32391701919821421387873713 24293776439866066040905285)
              ·
                refine ⟨4555083082474887382669741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24293776439866066040905285 4555083082474887382669741)
                ·
                  refine ⟨1708156155928082768501153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4555083082474887382669741 1708156155928082768501153)
                  ·
                    refine ⟨1281117116946062076375865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1708156155928082768501153 1281117116946062076375865)
                    ·
                      refine ⟨960837837709546557281899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281117116946062076375865 960837837709546557281899)
                      ·
                        rfl

theorem cell23_1871225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_1871225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871225 prefixEnd_1871225 := by exact prefixLift 1871225
  have htrace : WordTrace (prefixWord ++ tailWord_1871225) baseStart_1871225 baseEnd_1871225 := by
    simpa [prefixWord, tailWord_1871225, baseEnd_1871225] using wordTrace_append hprefix tailTrace_1871225
  have hstable : (prefixWord ++ tailWord_1871225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871225).length < 2 ^ (prefixWord ++ tailWord_1871225).sum := by decide
  have hdescent : baseEnd_1871225 < baseStart_1871225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871228 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_1871228 : Nat := 118140960795 + 1871228 * 2 ^ 59
def prefixEnd_1871228 : Nat := 4983230072969 + 3 ^ 40 * 1871228 * 2
def baseEnd_1871228 : Nat := 960839378151510045544385

theorem tailTrace_1871228 : CollatzResearch.WordTrace tailWord_1871228 prefixEnd_1871228 960839378151510045544385 := by
  unfold tailWord_1871228
  simp only [CollatzResearch.WordTrace]
  refine ⟨34124646032434005572211169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45499528043245340762948225 34124646032434005572211169)
  ·
    refine ⟨25593484524325504179158377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34124646032434005572211169 25593484524325504179158377)
    ·
      refine ⟨19195113393244128134368783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25593484524325504179158377 19195113393244128134368783)
      ·
        refine ⟨28792670089866192201553175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19195113393244128134368783 28792670089866192201553175)
        ·
          refine ⟨43189005134799288302329763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28792670089866192201553175 43189005134799288302329763)
          ·
            refine ⟨64783507702198932453494645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43189005134799288302329763 64783507702198932453494645)
            ·
              refine ⟨6073453847081149917515123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64783507702198932453494645 6073453847081149917515123)
              ·
                refine ⟨9110180770621724876272685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073453847081149917515123 9110180770621724876272685)
                ·
                  refine ⟨3416317788983146828602257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9110180770621724876272685 3416317788983146828602257)
                  ·
                    refine ⟨2562238341737360121451693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3416317788983146828602257 2562238341737360121451693)
                    ·
                      refine ⟨960839378151510045544385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2562238341737360121451693 960839378151510045544385)
                      ·
                        rfl

theorem cell23_1871228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_1871228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871228 prefixEnd_1871228 := by exact prefixLift 1871228
  have htrace : WordTrace (prefixWord ++ tailWord_1871228) baseStart_1871228 baseEnd_1871228 := by
    simpa [prefixWord, tailWord_1871228, baseEnd_1871228] using wordTrace_append hprefix tailTrace_1871228
  have hstable : (prefixWord ++ tailWord_1871228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871228).length < 2 ^ (prefixWord ++ tailWord_1871228).sum := by decide
  have hdescent : baseEnd_1871228 < baseStart_1871228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871252 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1871252 : Nat := 118140960795 + 1871252 * 2 ^ 59
def prefixEnd_1871252 : Nat := 4983230072969 + 3 ^ 40 * 1871252 * 2
def baseEnd_1871252 : Nat := 320283900562405983881425

theorem tailTrace_1871252 : CollatzResearch.WordTrace tailWord_1871252 prefixEnd_1871252 320283900562405983881425 := by
  unfold tailWord_1871252
  simp only [CollatzResearch.WordTrace]
  refine ⟨34125083708390531621648005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45500111611187375495530673 34125083708390531621648005)
  ·
    refine ⟨6398453195323224679059001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34125083708390531621648005 6398453195323224679059001)
    ·
      refine ⟨4798839896492418509294251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6398453195323224679059001 4798839896492418509294251)
      ·
        refine ⟨7198259844738627763941377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798839896492418509294251 7198259844738627763941377)
        ·
          refine ⟨5398694883553970822956033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7198259844738627763941377 5398694883553970822956033)
          ·
            refine ⟨4049021162665478117217025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5398694883553970822956033 4049021162665478117217025)
            ·
              refine ⟨3036765871999108587912769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049021162665478117217025 3036765871999108587912769)
              ·
                refine ⟨2277574403999331440934577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3036765871999108587912769 2277574403999331440934577)
                ·
                  refine ⟨1708180802999498580700933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2277574403999331440934577 1708180802999498580700933)
                  ·
                    refine ⟨320283900562405983881425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1708180802999498580700933 320283900562405983881425)
                    ·
                      rfl

theorem cell23_1871252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1871252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871252 prefixEnd_1871252 := by exact prefixLift 1871252
  have htrace : WordTrace (prefixWord ++ tailWord_1871252) baseStart_1871252 baseEnd_1871252 := by
    simpa [prefixWord, tailWord_1871252, baseEnd_1871252] using wordTrace_append hprefix tailTrace_1871252
  have hstable : (prefixWord ++ tailWord_1871252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871252).length < 2 ^ (prefixWord ++ tailWord_1871252).sum := by decide
  have hdescent : baseEnd_1871252 < baseStart_1871252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871258 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1871258 : Nat := 118140960795 + 1871258 * 2 ^ 59
def prefixEnd_1871258 : Nat := 4983230072969 + 3 ^ 40 * 1871258 * 2
def baseEnd_1871258 : Nat := 960854782571144928169247

theorem tailTrace_1871258 : CollatzResearch.WordTrace tailWord_1871258 prefixEnd_1871258 960854782571144928169247 := by
  unfold tailWord_1871258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062596563689831567003607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45500257503172884178676285 17062596563689831567003607)
  ·
    refine ⟨25593894845534747350505411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17062596563689831567003607 25593894845534747350505411)
    ·
      refine ⟨38390842268302121025758117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25593894845534747350505411 38390842268302121025758117)
      ·
        refine ⟨7198282925306647692329647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38390842268302121025758117 7198282925306647692329647)
        ·
          refine ⟨10797424387959971538494471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7198282925306647692329647 10797424387959971538494471)
          ·
            refine ⟨16196136581939957307741707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797424387959971538494471 16196136581939957307741707)
            ·
              refine ⟨24294204872909935961612561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16196136581939957307741707 24294204872909935961612561)
              ·
                refine ⟨18220653654682451971209421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24294204872909935961612561 18220653654682451971209421)
                ·
                  refine ⟨6832745120505919489203533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18220653654682451971209421 6832745120505919489203533)
                  ·
                    refine ⟨2562279420189719808451325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6832745120505919489203533 2562279420189719808451325)
                    ·
                      refine ⟨960854782571144928169247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2562279420189719808451325 960854782571144928169247)
                      ·
                        rfl

theorem cell23_1871258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1871258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871258 prefixEnd_1871258 := by exact prefixLift 1871258
  have htrace : WordTrace (prefixWord ++ tailWord_1871258) baseStart_1871258 baseEnd_1871258 := by
    simpa [prefixWord, tailWord_1871258, baseEnd_1871258] using wordTrace_append hprefix tailTrace_1871258
  have hstable : (prefixWord ++ tailWord_1871258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871258).length < 2 ^ (prefixWord ++ tailWord_1871258).sum := by decide
  have hdescent : baseEnd_1871258 < baseStart_1871258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871272 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1871272 : Nat := 118140960795 + 1871272 * 2 ^ 59
def prefixEnd_1871272 : Nat := 4983230072969 + 3 ^ 40 * 1871272 * 2
def baseEnd_1871272 : Nat := 960861971300307873394183

theorem tailTrace_1871272 : CollatzResearch.WordTrace tailWord_1871272 prefixEnd_1871272 960861971300307873394183 := by
  unfold tailWord_1871272
  simp only [CollatzResearch.WordTrace]
  refine ⟨34125448438354303329512035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45500597917805737772682713 34125448438354303329512035)
  ·
    refine ⟨51188172657531454994268053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34125448438354303329512035 51188172657531454994268053)
    ·
      refine ⟨2399445593321786952856315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51188172657531454994268053 2399445593321786952856315)
      ·
        refine ⟨3599168389982680429284473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399445593321786952856315 3599168389982680429284473)
        ·
          refine ⟨2699376292487010321963355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3599168389982680429284473 2699376292487010321963355)
          ·
            refine ⟨4049064438730515482945033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699376292487010321963355 4049064438730515482945033)
            ·
              refine ⟨3036798329047886612208775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049064438730515482945033 3036798329047886612208775)
              ·
                refine ⟨4555197493571829918313163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036798329047886612208775 4555197493571829918313163)
                ·
                  refine ⟨6832796240357744877469745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555197493571829918313163 6832796240357744877469745)
                  ·
                    refine ⟨5124597180268308658102309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6832796240357744877469745 5124597180268308658102309)
                    ·
                      refine ⟨960861971300307873394183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5124597180268308658102309 960861971300307873394183)
                      ·
                        rfl

theorem cell23_1871272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1871272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871272 prefixEnd_1871272 := by exact prefixLift 1871272
  have htrace : WordTrace (prefixWord ++ tailWord_1871272) baseStart_1871272 baseEnd_1871272 := by
    simpa [prefixWord, tailWord_1871272, baseEnd_1871272] using wordTrace_append hprefix tailTrace_1871272
  have hstable : (prefixWord ++ tailWord_1871272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871272).length < 2 ^ (prefixWord ++ tailWord_1871272).sum := by decide
  have hdescent : baseEnd_1871272 < baseStart_1871272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871308 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_1871308 : Nat := 118140960795 + 1871308 * 2 ^ 59
def prefixEnd_1871308 : Nat := 4983230072969 + 3 ^ 40 * 1871308 * 2
def baseEnd_1871308 : Nat := 320293485534623244181339

theorem tailTrace_1871308 : CollatzResearch.WordTrace tailWord_1871308 prefixEnd_1871308 320293485534623244181339 := by
  unfold tailWord_1871308
  simp only [CollatzResearch.WordTrace]
  refine ⟨34126104952289092403667289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45501473269718789871556385 34126104952289092403667289)
  ·
    refine ⟨25594578714216819302750467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34126104952289092403667289 25594578714216819302750467)
    ·
      refine ⟨38391868071325228954125701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25594578714216819302750467 38391868071325228954125701)
      ·
        refine ⟨7198475263373480428898569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38391868071325228954125701 7198475263373480428898569)
        ·
          refine ⟨5398856447530110321673927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7198475263373480428898569 5398856447530110321673927)
          ·
            refine ⟨8098284671295165482510891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398856447530110321673927 8098284671295165482510891)
            ·
              refine ⟨12147427006942748223766337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8098284671295165482510891 12147427006942748223766337)
              ·
                refine ⟨9110570255207061167824753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12147427006942748223766337 9110570255207061167824753)
                ·
                  refine ⟨6832927691405295875868565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9110570255207061167824753 6832927691405295875868565)
                  ·
                    refine ⟨320293485534623244181339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6832927691405295875868565 320293485534623244181339)
                    ·
                      rfl

theorem cell23_1871308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_1871308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871308 prefixEnd_1871308 := by exact prefixLift 1871308
  have htrace : WordTrace (prefixWord ++ tailWord_1871308) baseStart_1871308 baseEnd_1871308 := by
    simpa [prefixWord, tailWord_1871308, baseEnd_1871308] using wordTrace_append hprefix tailTrace_1871308
  have hstable : (prefixWord ++ tailWord_1871308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871308).length < 2 ^ (prefixWord ++ tailWord_1871308).sum := by decide
  have hdescent : baseEnd_1871308 < baseStart_1871308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871332 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_1871332 : Nat := 118140960795 + 1871332 * 2 ^ 59
def prefixEnd_1871332 : Nat := 4983230072969 + 3 ^ 40 * 1871332 * 2
def baseEnd_1871332 : Nat := 960892780139577638643907

theorem tailTrace_1871332 : CollatzResearch.WordTrace tailWord_1871332 prefixEnd_1871332 960892780139577638643907 := by
  unfold tailWord_1871332
  simp only [CollatzResearch.WordTrace]
  refine ⟨34126542628245618453104125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45502056837660824604138833 34126542628245618453104125)
  ·
    refine ⟨12797453485592106919914047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34126542628245618453104125 12797453485592106919914047)
    ·
      refine ⟨19196180228388160379871071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12797453485592106919914047 19196180228388160379871071)
      ·
        refine ⟨28794270342582240569806607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19196180228388160379871071 28794270342582240569806607)
        ·
          refine ⟨43191405513873360854709911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28794270342582240569806607 43191405513873360854709911)
          ·
            refine ⟨64787108270810041282064867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43191405513873360854709911 64787108270810041282064867)
            ·
              refine ⟨97180662406215061923097301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64787108270810041282064867 97180662406215061923097301)
              ·
                refine ⟨2277671775145665513822593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97180662406215061923097301 2277671775145665513822593)
                ·
                  refine ⟨1708253831359249135366945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2277671775145665513822593 1708253831359249135366945)
                  ·
                    refine ⟨1281190373519436851525209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1708253831359249135366945 1281190373519436851525209)
                    ·
                      refine ⟨960892780139577638643907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281190373519436851525209 960892780139577638643907)
                      ·
                        rfl

theorem cell23_1871332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_1871332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871332 prefixEnd_1871332 := by exact prefixLift 1871332
  have htrace : WordTrace (prefixWord ++ tailWord_1871332) baseStart_1871332 baseEnd_1871332 := by
    simpa [prefixWord, tailWord_1871332, baseEnd_1871332] using wordTrace_append hprefix tailTrace_1871332
  have hstable : (prefixWord ++ tailWord_1871332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871332).length < 2 ^ (prefixWord ++ tailWord_1871332).sum := by decide
  have hdescent : baseEnd_1871332 < baseStart_1871332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871349 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1871349 : Nat := 118140960795 + 1871349 * 2 ^ 59
def prefixEnd_1871349 : Nat := 4983230072969 + 3 ^ 40 * 1871349 * 2
def baseEnd_1871349 : Nat := 960901509310704072131329

theorem tailTrace_1871349 : CollatzResearch.WordTrace tailWord_1871349 prefixEnd_1871349 960901509310704072131329 := by
  unfold tailWord_1871349
  simp only [CollatzResearch.WordTrace]
  refine ⟨68253705297429648809577101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45502470198286432539718067 68253705297429648809577101)
  ·
    refine ⟨25595139486536118303591413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68253705297429648809577101 25595139486536118303591413)
    ·
      refine ⟨2399544326862761090961695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25595139486536118303591413 2399544326862761090961695)
      ·
        refine ⟨3599316490294141636442543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399544326862761090961695 3599316490294141636442543)
        ·
          refine ⟨5398974735441212454663815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599316490294141636442543 5398974735441212454663815)
          ·
            refine ⟨8098462103161818681995723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398974735441212454663815 8098462103161818681995723)
            ·
              refine ⟨12147693154742728022993585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8098462103161818681995723 12147693154742728022993585)
              ·
                refine ⟨9110769866057046017245189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12147693154742728022993585 9110769866057046017245189)
                ·
                  refine ⟨1708269349885696128233473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9110769866057046017245189 1708269349885696128233473)
                  ·
                    refine ⟨1281202012414272096175105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1708269349885696128233473 1281202012414272096175105)
                    ·
                      refine ⟨960901509310704072131329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281202012414272096175105 960901509310704072131329)
                      ·
                        rfl

theorem cell23_1871349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1871349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871349 prefixEnd_1871349 := by exact prefixLift 1871349
  have htrace : WordTrace (prefixWord ++ tailWord_1871349) baseStart_1871349 baseEnd_1871349 := by
    simpa [prefixWord, tailWord_1871349, baseEnd_1871349] using wordTrace_append hprefix tailTrace_1871349
  have hstable : (prefixWord ++ tailWord_1871349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871349).length < 2 ^ (prefixWord ++ tailWord_1871349).sum := by decide
  have hdescent : baseEnd_1871349 < baseStart_1871349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871368 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1871368 : Nat := 118140960795 + 1871368 * 2 ^ 59
def prefixEnd_1871368 : Nat := 4983230072969 + 3 ^ 40 * 1871368 * 2
def baseEnd_1871368 : Nat := 320303755147713165931247

theorem tailTrace_1871368 : CollatzResearch.WordTrace tailWord_1871368 prefixEnd_1871368 320303755147713165931247 := by
  unfold tailWord_1871368
  simp only [CollatzResearch.WordTrace]
  refine ⟨34127199142180407527259379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45502932189573876703012505 34127199142180407527259379)
  ·
    refine ⟨51190798713270611290889069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34127199142180407527259379 51190798713270611290889069)
    ·
      refine ⟨19196549517476479234083401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51190798713270611290889069 19196549517476479234083401)
      ·
        refine ⟨14397412138107359425562551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19196549517476479234083401 14397412138107359425562551)
        ·
          refine ⟨21596118207161039138343827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14397412138107359425562551 21596118207161039138343827)
          ·
            refine ⟨32394177310741558707515741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21596118207161039138343827 32394177310741558707515741)
            ·
              refine ⟨12147816491528084515318403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32394177310741558707515741 12147816491528084515318403)
              ·
                refine ⟨18221724737292126772977605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12147816491528084515318403 18221724737292126772977605)
                ·
                  refine ⟨3416573388242273769933301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18221724737292126772977605 3416573388242273769933301)
                  ·
                    refine ⟨320303755147713165931247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3416573388242273769933301 320303755147713165931247)
                    ·
                      rfl

theorem cell23_1871368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1871368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871368 prefixEnd_1871368 := by exact prefixLift 1871368
  have htrace : WordTrace (prefixWord ++ tailWord_1871368) baseStart_1871368 baseEnd_1871368 := by
    simpa [prefixWord, tailWord_1871368, baseEnd_1871368] using wordTrace_append hprefix tailTrace_1871368
  have hstable : (prefixWord ++ tailWord_1871368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871368).length < 2 ^ (prefixWord ++ tailWord_1871368).sum := by decide
  have hdescent : baseEnd_1871368 < baseStart_1871368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871372 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 7]
def baseStart_1871372 : Nat := 118140960795 + 1871372 * 2 ^ 59
def prefixEnd_1871372 : Nat := 4983230072969 + 3 ^ 40 * 1871372 * 2
def baseEnd_1871372 : Nat := 106768146596195275793747

theorem tailTrace_1871372 : CollatzResearch.WordTrace tailWord_1871372 prefixEnd_1871372 106768146596195275793747 := by
  unfold tailWord_1871372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34127272088173161868832185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45503029450897549158442913 34127272088173161868832185)
  ·
    refine ⟨25595454066129871401624139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34127272088173161868832185 25595454066129871401624139)
    ·
      refine ⟨38393181099194807102436209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25595454066129871401624139 38393181099194807102436209)
      ·
        refine ⟨28794885824396105326827157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38393181099194807102436209 28794885824396105326827157)
        ·
          refine ⟨1349760273018567437195023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28794885824396105326827157 1349760273018567437195023)
          ·
            refine ⟨2024640409527851155792535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349760273018567437195023 2024640409527851155792535)
            ·
              refine ⟨3036960614291776733688803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024640409527851155792535 3036960614291776733688803)
              ·
                refine ⟨4555440921437665100533205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036960614291776733688803 4555440921437665100533205)
                ·
                  refine ⟨106768146596195275793747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4555440921437665100533205 106768146596195275793747)
                  ·
                    rfl

theorem cell23_1871372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_1871372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871372 prefixEnd_1871372 := by exact prefixLift 1871372
  have htrace : WordTrace (prefixWord ++ tailWord_1871372) baseStart_1871372 baseEnd_1871372 := by
    simpa [prefixWord, tailWord_1871372, baseEnd_1871372] using wordTrace_append hprefix tailTrace_1871372
  have hstable : (prefixWord ++ tailWord_1871372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871372).length < 2 ^ (prefixWord ++ tailWord_1871372).sum := by decide
  have hdescent : baseEnd_1871372 < baseStart_1871372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871418 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_1871418 : Nat := 118140960795 + 1871418 * 2 ^ 59
def prefixEnd_1871418 : Nat := 4983230072969 + 3 ^ 40 * 1871418 * 2
def baseEnd_1871418 : Nat := 960936939475864302168511

theorem tailTrace_1871418 : CollatzResearch.WordTrace tailWord_1871418 prefixEnd_1871418 960936939475864302168511 := by
  unfold tailWord_1871418
  simp only [CollatzResearch.WordTrace]
  refine ⟨17064055483544918398459727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45504147956119782395892605 17064055483544918398459727)
  ·
    refine ⟨25596083225317377597689591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17064055483544918398459727 25596083225317377597689591)
    ·
      refine ⟨38394124837976066396534387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25596083225317377597689591 38394124837976066396534387)
      ·
        refine ⟨57591187256964099594801581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38394124837976066396534387 57591187256964099594801581)
        ·
          refine ⟨21596695221361537348050593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57591187256964099594801581 21596695221361537348050593)
          ·
            refine ⟨16197521416021153011037945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21596695221361537348050593 16197521416021153011037945)
            ·
              refine ⟨12148141062015864758278459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16197521416021153011037945 12148141062015864758278459)
              ·
                refine ⟨18222211593023797137417689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12148141062015864758278459 18222211593023797137417689)
                ·
                  refine ⟨13666658694767847853063267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18222211593023797137417689 13666658694767847853063267)
                  ·
                    refine ⟨20499988042151771779594901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13666658694767847853063267 20499988042151771779594901)
                    ·
                      refine ⟨960936939475864302168511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20499988042151771779594901 960936939475864302168511)
                      ·
                        rfl

theorem cell23_1871418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_1871418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871418 prefixEnd_1871418 := by exact prefixLift 1871418
  have htrace : WordTrace (prefixWord ++ tailWord_1871418) baseStart_1871418 baseEnd_1871418 := by
    simpa [prefixWord, tailWord_1871418, baseEnd_1871418] using wordTrace_append hprefix tailTrace_1871418
  have hstable : (prefixWord ++ tailWord_1871418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871418).length < 2 ^ (prefixWord ++ tailWord_1871418).sum := by decide
  have hdescent : baseEnd_1871418 < baseStart_1871418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871468 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_1871468 : Nat := 118140960795 + 1871468 * 2 ^ 59
def prefixEnd_1871468 : Nat := 4983230072969 + 3 ^ 40 * 1871468 * 2
def baseEnd_1871468 : Nat := 960962613508589106543281

theorem tailTrace_1871468 : CollatzResearch.WordTrace tailWord_1871468 prefixEnd_1871468 960962613508589106543281 := by
  unfold tailWord_1871468
  simp only [CollatzResearch.WordTrace]
  refine ⟨34129022791999266066579529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45505363722665688088772705 34129022791999266066579529)
  ·
    refine ⟨25596767093999449549934647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34129022791999266066579529 25596767093999449549934647)
    ·
      refine ⟨38395150640999174324901971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25596767093999449549934647 38395150640999174324901971)
      ·
        refine ⟨57592725961498761487352957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38395150640999174324901971 57592725961498761487352957)
        ·
          refine ⟨21597272235562035557757359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57592725961498761487352957 21597272235562035557757359)
          ·
            refine ⟨32395908353343053336636039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21597272235562035557757359 32395908353343053336636039)
            ·
              refine ⟨48593862530014580004954059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32395908353343053336636039 48593862530014580004954059)
              ·
                refine ⟨72890793795021870007431089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48593862530014580004954059 72890793795021870007431089)
                ·
                  refine ⟨54668095346266402505573317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72890793795021870007431089 54668095346266402505573317)
                  ·
                    refine ⟨10250267877424950469794997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54668095346266402505573317 10250267877424950469794997)
                    ·
                      refine ⟨960962613508589106543281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10250267877424950469794997 960962613508589106543281)
                      ·
                        rfl

theorem cell23_1871468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_1871468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871468 prefixEnd_1871468 := by exact prefixLift 1871468
  have htrace : WordTrace (prefixWord ++ tailWord_1871468) baseStart_1871468 baseEnd_1871468 := by
    simpa [prefixWord, tailWord_1871468, baseEnd_1871468] using wordTrace_append hprefix tailTrace_1871468
  have hstable : (prefixWord ++ tailWord_1871468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871468).length < 2 ^ (prefixWord ++ tailWord_1871468).sum := by decide
  have hdescent : baseEnd_1871468 < baseStart_1871468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871489 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1871489 : Nat := 118140960795 + 1871489 * 2 ^ 59
def prefixEnd_1871489 : Nat := 4983230072969 + 3 ^ 40 * 1871489 * 2
def baseEnd_1871489 : Nat := 960973396602333524380685

theorem tailTrace_1871489 : CollatzResearch.WordTrace tailWord_1871489 prefixEnd_1871489 960973396602333524380685 := by
  unfold tailWord_1871489
  simp only [CollatzResearch.WordTrace]
  refine ⟨68258811516922452719673521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45505874344614968479782347 68258811516922452719673521)
  ·
    refine ⟨51194108637691839539755141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68258811516922452719673521 51194108637691839539755141)
    ·
      refine ⟨9598895369567219913704089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51194108637691839539755141 9598895369567219913704089)
      ·
        refine ⟨7199171527175414935278067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9598895369567219913704089 7199171527175414935278067)
        ·
          refine ⟨10798757290763122402917101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199171527175414935278067 10798757290763122402917101)
          ·
            refine ⟨4049533984036170901093913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10798757290763122402917101 4049533984036170901093913)
            ·
              refine ⟨3037150488027128175820435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049533984036170901093913 3037150488027128175820435)
              ·
                refine ⟨4555725732040692263730653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037150488027128175820435 4555725732040692263730653)
                ·
                  refine ⟨1708397149515259598898995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4555725732040692263730653 1708397149515259598898995)
                  ·
                    refine ⟨2562595724272889398348493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1708397149515259598898995 2562595724272889398348493)
                    ·
                      refine ⟨960973396602333524380685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2562595724272889398348493 960973396602333524380685)
                      ·
                        rfl

theorem cell23_1871489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1871489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871489 prefixEnd_1871489 := by exact prefixLift 1871489
  have htrace : WordTrace (prefixWord ++ tailWord_1871489) baseStart_1871489 baseEnd_1871489 := by
    simpa [prefixWord, tailWord_1871489, baseEnd_1871489] using wordTrace_append hprefix tailTrace_1871489
  have hstable : (prefixWord ++ tailWord_1871489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871489).length < 2 ^ (prefixWord ++ tailWord_1871489).sum := by decide
  have hdescent : baseEnd_1871489 < baseStart_1871489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871512 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1871512 : Nat := 118140960795 + 1871512 * 2 ^ 59
def prefixEnd_1871512 : Nat := 4983230072969 + 3 ^ 40 * 1871512 * 2
def baseEnd_1871512 : Nat := 960985206657386934393079

theorem tailTrace_1871512 : CollatzResearch.WordTrace tailWord_1871512 prefixEnd_1871512 960985206657386934393079 := by
  unfold tailWord_1871512
  simp only [CollatzResearch.WordTrace]
  refine ⟨34129825197919563823880395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45506433597226085098507193 34129825197919563823880395)
  ·
    refine ⟨51194737796879345735820593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34129825197919563823880395 51194737796879345735820593)
    ·
      refine ⟨38396053347659509301865445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51194737796879345735820593 38396053347659509301865445)
      ·
        refine ⟨7199260002686157994099771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38396053347659509301865445 7199260002686157994099771)
        ·
          refine ⟨10798890004029236991149657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199260002686157994099771 10798890004029236991149657)
          ·
            refine ⟨8099167503021927743362243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10798890004029236991149657 8099167503021927743362243)
            ·
              refine ⟨12148751254532891615043365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099167503021927743362243 12148751254532891615043365)
              ·
                refine ⟨2277890860224917177820631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12148751254532891615043365 2277890860224917177820631)
                ·
                  refine ⟨3416836290337375766730947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277890860224917177820631 3416836290337375766730947)
                  ·
                    refine ⟨5125254435506063650096421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3416836290337375766730947 5125254435506063650096421)
                    ·
                      refine ⟨960985206657386934393079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5125254435506063650096421 960985206657386934393079)
                      ·
                        rfl

theorem cell23_1871512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1871512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871512 prefixEnd_1871512 := by exact prefixLift 1871512
  have htrace : WordTrace (prefixWord ++ tailWord_1871512) baseStart_1871512 baseEnd_1871512 := by
    simpa [prefixWord, tailWord_1871512, baseEnd_1871512] using wordTrace_append hprefix tailTrace_1871512
  have hstable : (prefixWord ++ tailWord_1871512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871512).length < 2 ^ (prefixWord ++ tailWord_1871512).sum := by decide
  have hdescent : baseEnd_1871512 < baseStart_1871512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871525 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_1871525 : Nat := 118140960795 + 1871525 * 2 ^ 59
def prefixEnd_1871525 : Nat := 4983230072969 + 3 ^ 40 * 1871525 * 2
def baseEnd_1871525 : Nat := 960991881905895383530519

theorem tailTrace_1871525 : CollatzResearch.WordTrace tailWord_1871525 prefixEnd_1871525 960991881905895383530519 := by
  unfold tailWord_1871525
  simp only [CollatzResearch.WordTrace]
  refine ⟨68260124544792030867984029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45506749696528020578656019 68260124544792030867984029)
  ·
    refine ⟨25597546704297011575494011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68260124544792030867984029 25597546704297011575494011)
    ·
      refine ⟨38396320056445517363241017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25597546704297011575494011 38396320056445517363241017)
      ·
        refine ⟨28797240042334138022430763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38396320056445517363241017 28797240042334138022430763)
        ·
          refine ⟨43195860063501207033646145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28797240042334138022430763 43195860063501207033646145)
          ·
            refine ⟨32396895047625905275234609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43195860063501207033646145 32396895047625905275234609)
            ·
              refine ⟨24297671285719428956425957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32396895047625905275234609 24297671285719428956425957)
              ·
                refine ⟨4555813366072392929329867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24297671285719428956425957 4555813366072392929329867)
                ·
                  refine ⟨6833720049108589393994801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555813366072392929329867 6833720049108589393994801)
                  ·
                    refine ⟨5125290036831442045496101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6833720049108589393994801 5125290036831442045496101)
                    ·
                      refine ⟨960991881905895383530519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5125290036831442045496101 960991881905895383530519)
                      ·
                        rfl

theorem cell23_1871525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_1871525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871525 prefixEnd_1871525 := by exact prefixLift 1871525
  have htrace : WordTrace (prefixWord ++ tailWord_1871525) baseStart_1871525 baseEnd_1871525 := by
    simpa [prefixWord, tailWord_1871525, baseEnd_1871525] using wordTrace_append hprefix tailTrace_1871525
  have hstable : (prefixWord ++ tailWord_1871525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871525).length < 2 ^ (prefixWord ++ tailWord_1871525).sum := by decide
  have hdescent : baseEnd_1871525 < baseStart_1871525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871546 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2]
def baseStart_1871546 : Nat := 118140960795 + 1871546 * 2 ^ 59
def prefixEnd_1871546 : Nat := 4983230072969 + 3 ^ 40 * 1871546 * 2
def baseEnd_1871546 : Nat := 961002664999639801367923

theorem tailTrace_1871546 : CollatzResearch.WordTrace tailWord_1871546 prefixEnd_1871546 961002664999639801367923 := by
  unfold tailWord_1871546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17065222619428987863624623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45507260318477300969665661 17065222619428987863624623)
  ·
    refine ⟨25597833929143481795436935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17065222619428987863624623 25597833929143481795436935)
    ·
      refine ⟨38396750893715222693155403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25597833929143481795436935 38396750893715222693155403)
      ·
        refine ⟨57595126340572834039733105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38396750893715222693155403 57595126340572834039733105)
        ·
          refine ⟨43196344755429625529799829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57595126340572834039733105 43196344755429625529799829)
          ·
            refine ⟨2024828660410763696709367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43196344755429625529799829 2024828660410763696709367)
            ·
              refine ⟨3037242990616145545064051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024828660410763696709367 3037242990616145545064051)
              ·
                refine ⟨4555864485924218317596077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037242990616145545064051 4555864485924218317596077)
                ·
                  refine ⟨1708449182221581869098529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4555864485924218317596077 1708449182221581869098529)
                  ·
                    refine ⟨1281336886666186401823897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1708449182221581869098529 1281336886666186401823897)
                    ·
                      refine ⟨961002664999639801367923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281336886666186401823897 961002664999639801367923)
                      ·
                        rfl

theorem cell23_1871546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_1871546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871546 prefixEnd_1871546 := by exact prefixLift 1871546
  have htrace : WordTrace (prefixWord ++ tailWord_1871546) baseStart_1871546 baseEnd_1871546 := by
    simpa [prefixWord, tailWord_1871546, baseEnd_1871546] using wordTrace_append hprefix tailTrace_1871546
  have hstable : (prefixWord ++ tailWord_1871546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871546).length < 2 ^ (prefixWord ++ tailWord_1871546).sum := by decide
  have hdescent : baseEnd_1871546 < baseStart_1871546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871615 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_1871615 : Nat := 118140960795 + 1871615 * 2 ^ 59
def prefixEnd_1871615 : Nat := 4983230072969 + 3 ^ 40 * 1871615 * 2
def baseEnd_1871615 : Nat := 961038095164800031405105

theorem tailTrace_1871615 : CollatzResearch.WordTrace tailWord_1871615 prefixEnd_1871615 961038095164800031405105 := by
  unfold tailWord_1871615
  simp only [CollatzResearch.WordTrace]
  refine ⟨68263407114465976238760299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45508938076310650825840199 68263407114465976238760299)
  ·
    refine ⟨102395110671698964358140449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68263407114465976238760299 102395110671698964358140449)
    ·
      refine ⟨76796333003774223268605337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102395110671698964358140449 76796333003774223268605337)
      ·
        refine ⟨57597249752830667451454003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76796333003774223268605337 57597249752830667451454003)
        ·
          refine ⟨86395874629246001177181005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57597249752830667451454003 86395874629246001177181005)
          ·
            refine ⟨32398452985967250441442877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86395874629246001177181005 32398452985967250441442877)
            ·
              refine ⟨12149419869737718915541079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32398452985967250441442877 12149419869737718915541079)
              ·
                refine ⟨18224129804606578373311619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12149419869737718915541079 18224129804606578373311619)
                ·
                  refine ⟨27336194706909867559967429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18224129804606578373311619 27336194706909867559967429)
                  ·
                    refine ⟨5125536507545600167493893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27336194706909867559967429 5125536507545600167493893)
                    ·
                      refine ⟨961038095164800031405105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5125536507545600167493893 961038095164800031405105)
                      ·
                        rfl

theorem cell23_1871615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_1871615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871615 prefixEnd_1871615 := by exact prefixLift 1871615
  have htrace : WordTrace (prefixWord ++ tailWord_1871615) baseStart_1871615 baseEnd_1871615 := by
    simpa [prefixWord, tailWord_1871615, baseEnd_1871615] using wordTrace_append hprefix tailTrace_1871615
  have hstable : (prefixWord ++ tailWord_1871615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871615).length < 2 ^ (prefixWord ++ tailWord_1871615).sum := by decide
  have hdescent : baseEnd_1871615 < baseStart_1871615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871653 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 2, 2, 2]
def baseStart_1871653 : Nat := 118140960795 + 1871653 * 2 ^ 59
def prefixEnd_1871653 : Nat := 4983230072969 + 3 ^ 40 * 1871653 * 2
def baseEnd_1871653 : Nat := 961057607429670882729931

theorem tailTrace_1871653 : CollatzResearch.WordTrace tailWord_1871653 prefixEnd_1871653 961057607429670882729931 := by
  unfold tailWord_1871653
  simp only [CollatzResearch.WordTrace]
  refine ⟨68264793088328308728643613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45509862058885539152429075 68264793088328308728643613)
  ·
    refine ⟨25599297408123115773241355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68264793088328308728643613 25599297408123115773241355)
    ·
      refine ⟨38398946112184673659862033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25599297408123115773241355 38398946112184673659862033)
      ·
        refine ⟨28799209584138505244896525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38398946112184673659862033 28799209584138505244896525)
        ·
          refine ⟨10799703594051939466836197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28799209584138505244896525 10799703594051939466836197)
          ·
            refine ⟨2024944423884738650031787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10799703594051939466836197 2024944423884738650031787)
            ·
              refine ⟨3037416635827107975047681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024944423884738650031787 3037416635827107975047681)
              ·
                refine ⟨2278062476870330981285761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037416635827107975047681 2278062476870330981285761)
                ·
                  refine ⟨1708546857652748235964321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2278062476870330981285761 1708546857652748235964321)
                  ·
                    refine ⟨1281410143239561176973241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1708546857652748235964321 1281410143239561176973241)
                    ·
                      refine ⟨961057607429670882729931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281410143239561176973241 961057607429670882729931)
                      ·
                        rfl

theorem cell23_1871653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_1871653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871653 prefixEnd_1871653 := by exact prefixLift 1871653
  have htrace : WordTrace (prefixWord ++ tailWord_1871653) baseStart_1871653 baseEnd_1871653 := by
    simpa [prefixWord, tailWord_1871653, baseEnd_1871653] using wordTrace_append hprefix tailTrace_1871653
  have hstable : (prefixWord ++ tailWord_1871653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871653).length < 2 ^ (prefixWord ++ tailWord_1871653).sum := by decide
  have hdescent : baseEnd_1871653 < baseStart_1871653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871685 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_1871685 : Nat := 118140960795 + 1871685 * 2 ^ 59
def prefixEnd_1871685 : Nat := 4983230072969 + 3 ^ 40 * 1871685 * 2
def baseEnd_1871685 : Nat := 320358012936871585843261

theorem tailTrace_1871685 : CollatzResearch.WordTrace tailWord_1871685 prefixEnd_1871685 320358012936871585843261 := by
  unfold tailWord_1871685
  simp only [CollatzResearch.WordTrace]
  refine ⟨68265960224212378193808509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45510640149474918795872339 68265960224212378193808509)
  ·
    refine ⟨25599735084079641822678191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68265960224212378193808509 25599735084079641822678191)
    ·
      refine ⟨38399602626119462734017287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25599735084079641822678191 38399602626119462734017287)
      ·
        refine ⟨57599403939179194101025931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38399602626119462734017287 57599403939179194101025931)
        ·
          refine ⟨86399105908768791151538897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57599403939179194101025931 86399105908768791151538897)
          ·
            refine ⟨64799329431576593363654173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86399105908768791151538897 64799329431576593363654173)
            ·
              refine ⟨24299748536841222511370315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64799329431576593363654173 24299748536841222511370315)
              ·
                refine ⟨36449622805261833767055473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24299748536841222511370315 36449622805261833767055473)
                ·
                  refine ⟨27337217103946375325291605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36449622805261833767055473 27337217103946375325291605)
                  ·
                    refine ⟨320358012936871585843261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27337217103946375325291605 320358012936871585843261)
                    ·
                      rfl

theorem cell23_1871685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_1871685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871685 prefixEnd_1871685 := by exact prefixLift 1871685
  have htrace : WordTrace (prefixWord ++ tailWord_1871685) baseStart_1871685 baseEnd_1871685 := by
    simpa [prefixWord, tailWord_1871685, baseEnd_1871685] using wordTrace_append hprefix tailTrace_1871685
  have hstable : (prefixWord ++ tailWord_1871685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871685).length < 2 ^ (prefixWord ++ tailWord_1871685).sum := by decide
  have hdescent : baseEnd_1871685 < baseStart_1871685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871693 : List Nat := [1, 6, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1871693 : Nat := 118140960795 + 1871693 * 2 ^ 59
def prefixEnd_1871693 : Nat := 4983230072969 + 3 ^ 40 * 1871693 * 2
def baseEnd_1871693 : Nat := 106786460739538969581083

theorem tailTrace_1871693 : CollatzResearch.WordTrace tailWord_1871693 prefixEnd_1871693 106786460739538969581083 := by
  unfold tailWord_1871693
  simp only [CollatzResearch.WordTrace]
  refine ⟨68266252008183395560099733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45510834672122263706733155 68266252008183395560099733)
  ·
    refine ⟨3199980562883596666879675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68266252008183395560099733 3199980562883596666879675)
    ·
      refine ⟨4799970844325395000319513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3199980562883596666879675 4799970844325395000319513)
      ·
        refine ⟨3599978133244046250239635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4799970844325395000319513 3599978133244046250239635)
        ·
          refine ⟨5399967199866069375359453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599978133244046250239635 5399967199866069375359453)
          ·
            refine ⟨2024987699949776015759795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5399967199866069375359453 2024987699949776015759795)
            ·
              refine ⟨3037481549924664023639693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024987699949776015759795 3037481549924664023639693)
              ·
                refine ⟨1139055581221749008864885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3037481549924664023639693 1139055581221749008864885)
                ·
                  refine ⟨106786460739538969581083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1139055581221749008864885 106786460739538969581083)
                  ·
                    rfl

theorem cell23_1871693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1871693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871693 prefixEnd_1871693 := by exact prefixLift 1871693
  have htrace : WordTrace (prefixWord ++ tailWord_1871693) baseStart_1871693 baseEnd_1871693 := by
    simpa [prefixWord, tailWord_1871693, baseEnd_1871693] using wordTrace_append hprefix tailTrace_1871693
  have hstable : (prefixWord ++ tailWord_1871693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871693).length < 2 ^ (prefixWord ++ tailWord_1871693).sum := by decide
  have hdescent : baseEnd_1871693 < baseStart_1871693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871770 : List Nat := [3, 1, 1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_1871770 : Nat := 118140960795 + 1871770 * 2 ^ 59
def prefixEnd_1871770 : Nat := 4983230072969 + 3 ^ 40 * 1871770 * 2
def baseEnd_1871770 : Nat := 320372561555415641655631

theorem tailTrace_1871770 : CollatzResearch.WordTrace tailWord_1871770 prefixEnd_1871770 320372561555415641655631 := by
  unfold tailWord_1871770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17067265107226109427663191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45512706952602958473768509 17067265107226109427663191)
  ·
    refine ⟨25600897660839164141494787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17067265107226109427663191 25600897660839164141494787)
    ·
      refine ⟨38401346491258746212242181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25600897660839164141494787 38401346491258746212242181)
      ·
        refine ⟨7200252467111014914795409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38401346491258746212242181 7200252467111014914795409)
        ·
          refine ⟨5400189350333261186096557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7200252467111014914795409 5400189350333261186096557)
          ·
            refine ⟨2025071006374972944786209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5400189350333261186096557 2025071006374972944786209)
            ·
              refine ⟨1518803254781229708589657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025071006374972944786209 1518803254781229708589657)
              ·
                refine ⟨1139102441085922281442243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1518803254781229708589657 1139102441085922281442243)
                ·
                  refine ⟨1708653661628883422163365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139102441085922281442243 1708653661628883422163365)
                  ·
                    refine ⟨320372561555415641655631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1708653661628883422163365 320372561555415641655631)
                    ·
                      rfl

theorem cell23_1871770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_1871770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871770 prefixEnd_1871770 := by exact prefixLift 1871770
  have htrace : WordTrace (prefixWord ++ tailWord_1871770) baseStart_1871770 baseEnd_1871770 := by
    simpa [prefixWord, tailWord_1871770, baseEnd_1871770] using wordTrace_append hprefix tailTrace_1871770
  have hstable : (prefixWord ++ tailWord_1871770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871770).length < 2 ^ (prefixWord ++ tailWord_1871770).sum := by decide
  have hdescent : baseEnd_1871770 < baseStart_1871770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871799 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 4]
def baseStart_1871799 : Nat := 118140960795 + 1871799 * 2 ^ 59
def prefixEnd_1871799 : Nat := 4983230072969 + 3 ^ 40 * 1871799 * 2
def baseEnd_1871799 : Nat := 961132575605227311504259

theorem tailTrace_1871799 : CollatzResearch.WordTrace tailWord_1871799 prefixEnd_1871799 961132575605227311504259 := by
  unfold tailWord_1871799
  simp only [CollatzResearch.WordTrace]
  refine ⟨68270118145799375663458451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45513412097199583775638967 68270118145799375663458451)
  ·
    refine ⟨102405177218699063495187677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68270118145799375663458451 102405177218699063495187677)
    ·
      refine ⟨38401941457012148810695379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102405177218699063495187677 38401941457012148810695379)
      ·
        refine ⟨57602912185518223216043069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38401941457012148810695379 57602912185518223216043069)
        ·
          refine ⟨21601092069569333706016151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57602912185518223216043069 21601092069569333706016151)
          ·
            refine ⟨32401638104354000559024227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21601092069569333706016151 32401638104354000559024227)
            ·
              refine ⟨48602457156531000838536341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32401638104354000559024227 48602457156531000838536341)
              ·
                refine ⟨2278240179212390664306391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48602457156531000838536341 2278240179212390664306391)
                ·
                  refine ⟨3417360268818585996459587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278240179212390664306391 3417360268818585996459587)
                  ·
                    refine ⟨5126040403227878994689381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3417360268818585996459587 5126040403227878994689381)
                    ·
                      refine ⟨961132575605227311504259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5126040403227878994689381 961132575605227311504259)
                      ·
                        rfl

theorem cell23_1871799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_1871799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871799 prefixEnd_1871799 := by exact prefixLift 1871799
  have htrace : WordTrace (prefixWord ++ tailWord_1871799) baseStart_1871799 baseEnd_1871799 := by
    simpa [prefixWord, tailWord_1871799, baseEnd_1871799] using wordTrace_append hprefix tailTrace_1871799
  have hstable : (prefixWord ++ tailWord_1871799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871799).length < 2 ^ (prefixWord ++ tailWord_1871799).sum := by decide
  have hdescent : baseEnd_1871799 < baseStart_1871799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871802 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_1871802 : Nat := 118140960795 + 1871802 * 2 ^ 59
def prefixEnd_1871802 : Nat := 4983230072969 + 3 ^ 40 * 1871802 * 2
def baseEnd_1871802 : Nat := 961134116047190799766745

theorem tailTrace_1871802 : CollatzResearch.WordTrace tailWord_1871802 prefixEnd_1871802 961134116047190799766745 := by
  unfold tailWord_1871802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17067556891197126793954415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45513485043192338117211773 17067556891197126793954415)
  ·
    refine ⟨25601335336795690190931623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17067556891197126793954415 25601335336795690190931623)
    ·
      refine ⟨38402003005193535286397435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25601335336795690190931623 38402003005193535286397435)
      ·
        refine ⟨57603004507790302929596153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38402003005193535286397435 57603004507790302929596153)
        ·
          refine ⟨43202253380842727197197115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57603004507790302929596153 43202253380842727197197115)
          ·
            refine ⟨64803380071264090795795673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43202253380842727197197115 64803380071264090795795673)
            ·
              refine ⟨48602535053448068096846755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64803380071264090795795673 48602535053448068096846755)
              ·
                refine ⟨72903802580172102145270133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48602535053448068096846755 72903802580172102145270133)
                ·
                  refine ⟨6834731491891134576119075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72903802580172102145270133 6834731491891134576119075)
                  ·
                    refine ⟨10252097237836701864178613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6834731491891134576119075 10252097237836701864178613)
                    ·
                      refine ⟨961134116047190799766745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10252097237836701864178613 961134116047190799766745)
                      ·
                        rfl

theorem cell23_1871802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_1871802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871802 prefixEnd_1871802 := by exact prefixLift 1871802
  have htrace : WordTrace (prefixWord ++ tailWord_1871802) baseStart_1871802 baseEnd_1871802 := by
    simpa [prefixWord, tailWord_1871802, baseEnd_1871802] using wordTrace_append hprefix tailTrace_1871802
  have hstable : (prefixWord ++ tailWord_1871802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871802).length < 2 ^ (prefixWord ++ tailWord_1871802).sum := by decide
  have hdescent : baseEnd_1871802 < baseStart_1871802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871816 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_1871816 : Nat := 118140960795 + 1871816 * 2 ^ 59
def prefixEnd_1871816 : Nat := 4983230072969 + 3 ^ 40 * 1871816 * 2
def baseEnd_1871816 : Nat := 961141304776353744991681

theorem tailTrace_1871816 : CollatzResearch.WordTrace tailWord_1871816 prefixEnd_1871816 961141304776353744991681 := by
  unfold tailWord_1871816
  simp only [CollatzResearch.WordTrace]
  refine ⟨34135369093368893783413651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45513825457825191711218201 34135369093368893783413651)
  ·
    refine ⟨51203053640053340675120477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34135369093368893783413651 51203053640053340675120477)
    ·
      refine ⟨19201145115020002753170179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51203053640053340675120477 19201145115020002753170179)
      ·
        refine ⟨28801717672530004129755269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19201145115020002753170179 28801717672530004129755269)
        ·
          refine ⟨5400322063599375774329113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28801717672530004129755269 5400322063599375774329113)
          ·
            refine ⟨4050241547699531830746835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5400322063599375774329113 4050241547699531830746835)
            ·
              refine ⟨6075362321549297746120253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050241547699531830746835 6075362321549297746120253)
              ·
                refine ⟨2278260870580986654795095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6075362321549297746120253 2278260870580986654795095)
                ·
                  refine ⟨3417391305871479982192643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278260870580986654795095 3417391305871479982192643)
                  ·
                    refine ⟨5126086958807219973288965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3417391305871479982192643 5126086958807219973288965)
                    ·
                      refine ⟨961141304776353744991681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5126086958807219973288965 961141304776353744991681)
                      ·
                        rfl

theorem cell23_1871816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_1871816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871816 prefixEnd_1871816 := by exact prefixLift 1871816
  have htrace : WordTrace (prefixWord ++ tailWord_1871816) baseStart_1871816 baseEnd_1871816 := by
    simpa [prefixWord, tailWord_1871816, baseEnd_1871816] using wordTrace_append hprefix tailTrace_1871816
  have hstable : (prefixWord ++ tailWord_1871816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871816).length < 2 ^ (prefixWord ++ tailWord_1871816).sum := by decide
  have hdescent : baseEnd_1871816 < baseStart_1871816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871822 : List Nat := [4, 1, 1, 1, 2, 2, 12]
def baseStart_1871822 : Nat := 118140960795 + 1871822 * 2 ^ 59
def prefixEnd_1871822 : Nat := 4983230072969 + 3 ^ 40 * 1871822 * 2
def baseEnd_1871822 : Nat := 11865980069880008907613

theorem tailTrace_1871822 : CollatzResearch.WordTrace tailWord_1871822 prefixEnd_1871822 11865980069880008907613 := by
  unfold tailWord_1871822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8533869628089506323943215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45513971349810700394363813 8533869628089506323943215)
  ·
    refine ⟨12800804442134259485914823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8533869628089506323943215 12800804442134259485914823)
    ·
      refine ⟨19201206663201389228872235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12800804442134259485914823 19201206663201389228872235)
      ·
        refine ⟨28801809994802083843308353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19201206663201389228872235 28801809994802083843308353)
        ·
          refine ⟨21601357496101562882481265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28801809994802083843308353 21601357496101562882481265)
          ·
            refine ⟨16201018122076172161860949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21601357496101562882481265 16201018122076172161860949)
            ·
              refine ⟨11865980069880008907613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 16201018122076172161860949 11865980069880008907613)
              ·
                rfl

theorem cell23_1871822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 12].length) (baseStart_1871822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871822 prefixEnd_1871822 := by exact prefixLift 1871822
  have htrace : WordTrace (prefixWord ++ tailWord_1871822) baseStart_1871822 baseEnd_1871822 := by
    simpa [prefixWord, tailWord_1871822, baseEnd_1871822] using wordTrace_append hprefix tailTrace_1871822
  have hstable : (prefixWord ++ tailWord_1871822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871822).length < 2 ^ (prefixWord ++ tailWord_1871822).sum := by decide
  have hdescent : baseEnd_1871822 < baseStart_1871822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871843 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 2, 4]
def baseStart_1871843 : Nat := 118140960795 + 1871843 * 2 ^ 59
def prefixEnd_1871843 : Nat := 4983230072969 + 3 ^ 40 * 1871843 * 2
def baseEnd_1871843 : Nat := 320385056251341713118019

theorem tailTrace_1871843 : CollatzResearch.WordTrace tailWord_1871843 prefixEnd_1871843 320385056251341713118019 := by
  unfold tailWord_1871843
  simp only [CollatzResearch.WordTrace]
  refine ⟨68271722957639971178060183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45514481971759980785373455 68271722957639971178060183)
  ·
    refine ⟨102407584436459956767090275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68271722957639971178060183 102407584436459956767090275)
    ·
      refine ⟨153611376654689935150635413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102407584436459956767090275 153611376654689935150635413)
      ·
        refine ⟨7200533280688590710186035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153611376654689935150635413 7200533280688590710186035)
        ·
          refine ⟨10800799921032886065279053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7200533280688590710186035 10800799921032886065279053)
          ·
            refine ⟨4050299970387332274479645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10800799921032886065279053 4050299970387332274479645)
            ·
              refine ⟨1518862488895249602929867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4050299970387332274479645 1518862488895249602929867)
              ·
                refine ⟨2278293733342874404394801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518862488895249602929867 2278293733342874404394801)
                ·
                  refine ⟨1708720300007155803296101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2278293733342874404394801 1708720300007155803296101)
                  ·
                    refine ⟨320385056251341713118019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1708720300007155803296101 320385056251341713118019)
                    ·
                      rfl

theorem cell23_1871843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 4].length) (baseStart_1871843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871843 prefixEnd_1871843 := by exact prefixLift 1871843
  have htrace : WordTrace (prefixWord ++ tailWord_1871843) baseStart_1871843 baseEnd_1871843 := by
    simpa [prefixWord, tailWord_1871843, baseEnd_1871843] using wordTrace_append hprefix tailTrace_1871843
  have hstable : (prefixWord ++ tailWord_1871843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871843).length < 2 ^ (prefixWord ++ tailWord_1871843).sum := by decide
  have hdescent : baseEnd_1871843 < baseStart_1871843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871852 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_1871852 : Nat := 118140960795 + 1871852 * 2 ^ 59
def prefixEnd_1871852 : Nat := 4983230072969 + 3 ^ 40 * 1871852 * 2
def baseEnd_1871852 : Nat := 320386596693305201380505

theorem tailTrace_1871852 : CollatzResearch.WordTrace tailWord_1871852 prefixEnd_1871852 320386596693305201380505 := by
  unfold tailWord_1871852
  simp only [CollatzResearch.WordTrace]
  refine ⟨34136025607303682857568905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45514700809738243810091873 34136025607303682857568905)
  ·
    refine ⟨25602019205477762143176679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34136025607303682857568905 25602019205477762143176679)
    ·
      refine ⟨38403028808216643214765019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25602019205477762143176679 38403028808216643214765019)
      ·
        refine ⟨57604543212324964822147529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38403028808216643214765019 57604543212324964822147529)
        ·
          refine ⟨43203407409243723616610647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57604543212324964822147529 43203407409243723616610647)
          ·
            refine ⟨64805111113865585424915971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43203407409243723616610647 64805111113865585424915971)
            ·
              refine ⟨97207666670798378137373957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64805111113865585424915971 97207666670798378137373957)
              ·
                refine ⟨18226437500774695900757617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97207666670798378137373957 18226437500774695900757617)
                ·
                  refine ⟨13669828125581021925568213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18226437500774695900757617 13669828125581021925568213)
                  ·
                    refine ⟨320386596693305201380505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13669828125581021925568213 320386596693305201380505)
                    ·
                      rfl

theorem cell23_1871852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_1871852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871852 prefixEnd_1871852 := by exact prefixLift 1871852
  have htrace : WordTrace (prefixWord ++ tailWord_1871852) baseStart_1871852 baseEnd_1871852 := by
    simpa [prefixWord, tailWord_1871852, baseEnd_1871852] using wordTrace_append hprefix tailTrace_1871852
  have hstable : (prefixWord ++ tailWord_1871852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871852).length < 2 ^ (prefixWord ++ tailWord_1871852).sum := by decide
  have hdescent : baseEnd_1871852 < baseStart_1871852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871859 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 2, 7, 2]
def baseStart_1871859 : Nat := 118140960795 + 1871859 * 2 ^ 59
def prefixEnd_1871859 : Nat := 4983230072969 + 3 ^ 40 * 1871859 * 2
def baseEnd_1871859 : Nat := 961163384444497076753983

theorem tailTrace_1871859 : CollatzResearch.WordTrace tailWord_1871859 prefixEnd_1871859 961163384444497076753983 := by
  unfold tailWord_1871859
  simp only [CollatzResearch.WordTrace]
  refine ⟨68272306525582005910642631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45514871017054670607095087 68272306525582005910642631)
  ·
    refine ⟨102408459788373008865963947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68272306525582005910642631 102408459788373008865963947)
    ·
      refine ⟨153612689682559513298945921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102408459788373008865963947 153612689682559513298945921)
      ·
        refine ⟨115209517261919634974209441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153612689682559513298945921 115209517261919634974209441)
        ·
          refine ⟨86407137946439726230657081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115209517261919634974209441 86407137946439726230657081)
          ·
            refine ⟨64805353459829794672992811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86407137946439726230657081 64805353459829794672992811)
            ·
              refine ⟨97208030189744692009489217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64805353459829794672992811 97208030189744692009489217)
              ·
                refine ⟨72906022642308519007116913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97208030189744692009489217 72906022642308519007116913)
                ·
                  refine ⟨54679516981731389255337685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72906022642308519007116913 54679516981731389255337685)
                  ·
                    refine ⟨1281551179259329435671977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54679516981731389255337685 1281551179259329435671977)
                    ·
                      refine ⟨961163384444497076753983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281551179259329435671977 961163384444497076753983)
                      ·
                        rfl

theorem cell23_1871859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 7, 2].length) (baseStart_1871859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871859 prefixEnd_1871859 := by exact prefixLift 1871859
  have htrace : WordTrace (prefixWord ++ tailWord_1871859) baseStart_1871859 baseEnd_1871859 := by
    simpa [prefixWord, tailWord_1871859, baseEnd_1871859] using wordTrace_append hprefix tailTrace_1871859
  have hstable : (prefixWord ++ tailWord_1871859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871859).length < 2 ^ (prefixWord ++ tailWord_1871859).sum := by decide
  have hdescent : baseEnd_1871859 < baseStart_1871859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871878 : List Nat := [6, 2, 1, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1871878 : Nat := 118140960795 + 1871878 * 2 ^ 59
def prefixEnd_1871878 : Nat := 4983230072969 + 3 ^ 40 * 1871878 * 2
def baseEnd_1871878 : Nat := 961173140576932502416397

theorem tailTrace_1871878 : CollatzResearch.WordTrace tailWord_1871878 prefixEnd_1871878 961173140576932502416397 := by
  unfold tailWord_1871878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133531234766036629862009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45515333008342114770389525 2133531234766036629862009)
  ·
    refine ⟨1600148426074527472396507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2133531234766036629862009 1600148426074527472396507)
    ·
      refine ⟨2400222639111791208594761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600148426074527472396507 2400222639111791208594761)
      ·
        refine ⟨1800166979333843406446071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2400222639111791208594761 1800166979333843406446071)
        ·
          refine ⟨2700250469000765109669107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800166979333843406446071 2700250469000765109669107)
          ·
            refine ⟨4050375703501147664503661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700250469000765109669107 4050375703501147664503661)
            ·
              refine ⟨1518890888812930374188873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4050375703501147664503661 1518890888812930374188873)
              ·
                refine ⟨1139168166609697780641655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1518890888812930374188873 1139168166609697780641655)
                ·
                  refine ⟨1708752249914546670962483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139168166609697780641655 1708752249914546670962483)
                  ·
                    refine ⟨2563128374871820006443725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1708752249914546670962483 2563128374871820006443725)
                    ·
                      refine ⟨961173140576932502416397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2563128374871820006443725 961173140576932502416397)
                      ·
                        rfl

theorem cell23_1871878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1871878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871878 prefixEnd_1871878 := by exact prefixLift 1871878
  have htrace : WordTrace (prefixWord ++ tailWord_1871878) baseStart_1871878 baseEnd_1871878 := by
    simpa [prefixWord, tailWord_1871878, baseEnd_1871878] using wordTrace_append hprefix tailTrace_1871878
  have hstable : (prefixWord ++ tailWord_1871878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871878).length < 2 ^ (prefixWord ++ tailWord_1871878).sum := by decide
  have hdescent : baseEnd_1871878 < baseStart_1871878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871900 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_1871900 : Nat := 118140960795 + 1871900 * 2 ^ 59
def prefixEnd_1871900 : Nat := 4983230072969 + 3 ^ 40 * 1871900 * 2
def baseEnd_1871900 : Nat := 961184437151331416341295

theorem tailTrace_1871900 : CollatzResearch.WordTrace tailWord_1871900 prefixEnd_1871900 961184437151331416341295 := by
  unfold tailWord_1871900
  simp only [CollatzResearch.WordTrace]
  refine ⟨34136900959216734956442577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45515867945622313275256769 34136900959216734956442577)
  ·
    refine ⟨25602675719412551217331933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34136900959216734956442577 25602675719412551217331933)
    ·
      refine ⟨9601003394779706706499475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25602675719412551217331933 9601003394779706706499475)
      ·
        refine ⟨14401505092169560059749213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9601003394779706706499475 14401505092169560059749213)
        ·
          refine ⟨5400564409563585022405955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14401505092169560059749213 5400564409563585022405955)
          ·
            refine ⟨8100846614345377533608933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400564409563585022405955 8100846614345377533608933)
            ·
              refine ⟨1518908740189758287551675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8100846614345377533608933 1518908740189758287551675)
              ·
                refine ⟨2278363110284637431327513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518908740189758287551675 2278363110284637431327513)
                ·
                  refine ⟨1708772332713478073495635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2278363110284637431327513 1708772332713478073495635)
                  ·
                    refine ⟨2563158499070217110243453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1708772332713478073495635 2563158499070217110243453)
                    ·
                      refine ⟨961184437151331416341295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2563158499070217110243453 961184437151331416341295)
                      ·
                        rfl

theorem cell23_1871900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_1871900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871900 prefixEnd_1871900 := by exact prefixLift 1871900
  have htrace : WordTrace (prefixWord ++ tailWord_1871900) baseStart_1871900 baseEnd_1871900 := by
    simpa [prefixWord, tailWord_1871900, baseEnd_1871900] using wordTrace_append hprefix tailTrace_1871900
  have hstable : (prefixWord ++ tailWord_1871900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871900).length < 2 ^ (prefixWord ++ tailWord_1871900).sum := by decide
  have hdescent : baseEnd_1871900 < baseStart_1871900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871909 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_1871909 : Nat := 118140960795 + 1871909 * 2 ^ 59
def prefixEnd_1871909 : Nat := 4983230072969 + 3 ^ 40 * 1871909 * 2
def baseEnd_1871909 : Nat := 961189058477221881128753

theorem tailTrace_1871909 : CollatzResearch.WordTrace tailWord_1871909 prefixEnd_1871909 961189058477221881128753 := by
  unfold tailWord_1871909
  simp only [CollatzResearch.WordTrace]
  refine ⟨68274130175400864449962781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45516086783600576299975187 68274130175400864449962781)
  ·
    refine ⟨25602798815775324168736043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68274130175400864449962781 25602798815775324168736043)
    ·
      refine ⟨38404198223662986253104065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25602798815775324168736043 38404198223662986253104065)
      ·
        refine ⟨28803148667747239689828049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38404198223662986253104065 28803148667747239689828049)
        ·
          refine ⟨21602361500810429767371037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28803148667747239689828049 21602361500810429767371037)
          ·
            refine ⟨8100885562803911162764139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21602361500810429767371037 8100885562803911162764139)
            ·
              refine ⟨12151328344205866744146209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100885562803911162764139 12151328344205866744146209)
              ·
                refine ⟨9113496258154400058109657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12151328344205866744146209 9113496258154400058109657)
                ·
                  refine ⟨6835122193615800043582243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9113496258154400058109657 6835122193615800043582243)
                  ·
                    refine ⟨10252683290423700065373365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6835122193615800043582243 10252683290423700065373365)
                    ·
                      refine ⟨961189058477221881128753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10252683290423700065373365 961189058477221881128753)
                      ·
                        rfl

theorem cell23_1871909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_1871909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871909 prefixEnd_1871909 := by exact prefixLift 1871909
  have htrace : WordTrace (prefixWord ++ tailWord_1871909) baseStart_1871909 baseEnd_1871909 := by
    simpa [prefixWord, tailWord_1871909, baseEnd_1871909] using wordTrace_append hprefix tailTrace_1871909
  have hstable : (prefixWord ++ tailWord_1871909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871909).length < 2 ^ (prefixWord ++ tailWord_1871909).sum := by decide
  have hdescent : baseEnd_1871909 < baseStart_1871909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871926 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1871926 : Nat := 118140960795 + 1871926 * 2 ^ 59
def prefixEnd_1871926 : Nat := 4983230072969 + 3 ^ 40 * 1871926 * 2
def baseEnd_1871926 : Nat := 961197787648348314616175

theorem tailTrace_1871926 : CollatzResearch.WordTrace tailWord_1871926 prefixEnd_1871926 961197787648348314616175 := by
  unfold tailWord_1871926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267171888521204772083227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45516500144226184235554421 4267171888521204772083227)
  ·
    refine ⟨6400757832781807158124841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4267171888521204772083227 6400757832781807158124841)
    ·
      refine ⟨4800568374586355368593631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6400757832781807158124841 4800568374586355368593631)
      ·
        refine ⟨7200852561879533052890447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800568374586355368593631 7200852561879533052890447)
        ·
          refine ⟨10801278842819299579335671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7200852561879533052890447 10801278842819299579335671)
          ·
            refine ⟨16201918264228949369003507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10801278842819299579335671 16201918264228949369003507)
            ·
              refine ⟨24302877396343424053505261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16201918264228949369003507 24302877396343424053505261)
              ·
                refine ⟨9113579023628784020064473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24302877396343424053505261 9113579023628784020064473)
                ·
                  refine ⟨6835184267721588015048355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9113579023628784020064473 6835184267721588015048355)
                  ·
                    refine ⟨10252776401582382022572533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6835184267721588015048355 10252776401582382022572533)
                    ·
                      refine ⟨961197787648348314616175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10252776401582382022572533 961197787648348314616175)
                      ·
                        rfl

theorem cell23_1871926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1871926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871926 prefixEnd_1871926 := by exact prefixLift 1871926
  have htrace : WordTrace (prefixWord ++ tailWord_1871926) baseStart_1871926 baseEnd_1871926 := by
    simpa [prefixWord, tailWord_1871926, baseEnd_1871926] using wordTrace_append hprefix tailTrace_1871926
  have hstable : (prefixWord ++ tailWord_1871926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871926).length < 2 ^ (prefixWord ++ tailWord_1871926).sum := by decide
  have hdescent : baseEnd_1871926 < baseStart_1871926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871959 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 4, 5]
def baseStart_1871959 : Nat := 118140960795 + 1871959 * 2 ^ 59
def prefixEnd_1871959 : Nat := 4983230072969 + 3 ^ 40 * 1871959 * 2
def baseEnd_1871959 : Nat := 320404910836648895167841

theorem tailTrace_1871959 : CollatzResearch.WordTrace tailWord_1871959 prefixEnd_1871959 320404910836648895167841 := by
  unfold tailWord_1871959
  simp only [CollatzResearch.WordTrace]
  refine ⟨68275953825219722989282931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45517302550146481992855287 68275953825219722989282931)
  ·
    refine ⟨102413930737829584483924397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68275953825219722989282931 102413930737829584483924397)
    ·
      refine ⟨38405224026686094181471649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102413930737829584483924397 38405224026686094181471649)
      ·
        refine ⟨28803918020014570636103737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38405224026686094181471649 28803918020014570636103737)
        ·
          refine ⟨21602938515010927977077803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28803918020014570636103737 21602938515010927977077803)
          ·
            refine ⟨32404407772516391965616705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21602938515010927977077803 32404407772516391965616705)
            ·
              refine ⟨24303305829387293974212529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32404407772516391965616705 24303305829387293974212529)
              ·
                refine ⟨18227479372040470480659397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24303305829387293974212529 18227479372040470480659397)
                ·
                  refine ⟨3417652382257588215123637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18227479372040470480659397 3417652382257588215123637)
                  ·
                    refine ⟨320404910836648895167841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3417652382257588215123637 320404910836648895167841)
                    ·
                      rfl

theorem cell23_1871959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_1871959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1871959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1871959 prefixEnd_1871959 := by exact prefixLift 1871959
  have htrace : WordTrace (prefixWord ++ tailWord_1871959) baseStart_1871959 baseEnd_1871959 := by
    simpa [prefixWord, tailWord_1871959, baseEnd_1871959] using wordTrace_append hprefix tailTrace_1871959
  have hstable : (prefixWord ++ tailWord_1871959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871959).length < 2 ^ (prefixWord ++ tailWord_1871959).sum := by decide
  have hdescent : baseEnd_1871959 < baseStart_1871959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872009 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_1872009 : Nat := 118140960795 + 1872009 * 2 ^ 59
def prefixEnd_1872009 : Nat := 4983230072969 + 3 ^ 40 * 1872009 * 2
def baseEnd_1872009 : Nat := 961240406542671489878293

theorem tailTrace_1872009 : CollatzResearch.WordTrace tailWord_1872009 prefixEnd_1872009 961240406542671489878293 := by
  unfold tailWord_1872009
  simp only [CollatzResearch.WordTrace]
  refine ⟨68277777475038581528603081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45518518316692387685735387 68277777475038581528603081)
  ·
    refine ⟨51208333106278936146452311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68277777475038581528603081 51208333106278936146452311)
    ·
      refine ⟨76812499659418404219678467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51208333106278936146452311 76812499659418404219678467)
      ·
        refine ⟨115218749489127606329517701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76812499659418404219678467 115218749489127606329517701)
        ·
          refine ⟨21603515529211426186784569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115218749489127606329517701 21603515529211426186784569)
          ·
            refine ⟨16202636646908569640088427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21603515529211426186784569 16202636646908569640088427)
            ·
              refine ⟨24303954970362854460132641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16202636646908569640088427 24303954970362854460132641)
              ·
                refine ⟨18227966227772140845099481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24303954970362854460132641 18227966227772140845099481)
                ·
                  refine ⟨13670974670829105633824611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18227966227772140845099481 13670974670829105633824611)
                  ·
                    refine ⟨20506462006243658450736917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13670974670829105633824611 20506462006243658450736917)
                    ·
                      refine ⟨961240406542671489878293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20506462006243658450736917 961240406542671489878293)
                      ·
                        rfl

theorem cell23_1872009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_1872009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872009 prefixEnd_1872009 := by exact prefixLift 1872009
  have htrace : WordTrace (prefixWord ++ tailWord_1872009) baseStart_1872009 baseEnd_1872009 := by
    simpa [prefixWord, tailWord_1872009, baseEnd_1872009] using wordTrace_append hprefix tailTrace_1872009
  have hstable : (prefixWord ++ tailWord_1872009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872009).length < 2 ^ (prefixWord ++ tailWord_1872009).sum := by decide
  have hdescent : baseEnd_1872009 < baseStart_1872009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872096 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 1, 6]
def baseStart_1872096 : Nat := 118140960795 + 1872096 * 2 ^ 59
def prefixEnd_1872096 : Nat := 4983230072969 + 3 ^ 40 * 1872096 * 2
def baseEnd_1872096 : Nat := 320428359786537549830131

theorem tailTrace_1872096 : CollatzResearch.WordTrace tailWord_1872096 prefixEnd_1872096 320428359786537549830131 := by
  unfold tailWord_1872096
  simp only [CollatzResearch.WordTrace]
  refine ⟨34140475312861697693510071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45520633750482263591346761 34140475312861697693510071)
  ·
    refine ⟨51210712969292546540265107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34140475312861697693510071 51210712969292546540265107)
    ·
      refine ⟨76816069453938819810397661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51210712969292546540265107 76816069453938819810397661)
      ·
        refine ⟨28806026045227057428899123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76816069453938819810397661 28806026045227057428899123)
        ·
          refine ⟨43209039067840586143348685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28806026045227057428899123 43209039067840586143348685)
          ·
            refine ⟨16203389650440219803755757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43209039067840586143348685 16203389650440219803755757)
            ·
              refine ⟨6076271118915082426408409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16203389650440219803755757 6076271118915082426408409)
              ·
                refine ⟨4557203339186311819806307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6076271118915082426408409 4557203339186311819806307)
                ·
                  refine ⟨6835805008779467729709461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557203339186311819806307 6835805008779467729709461)
                  ·
                    refine ⟨320428359786537549830131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6835805008779467729709461 320428359786537549830131)
                    ·
                      rfl

theorem cell23_1872096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_1872096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872096 prefixEnd_1872096 := by exact prefixLift 1872096
  have htrace : WordTrace (prefixWord ++ tailWord_1872096) baseStart_1872096 baseEnd_1872096 := by
    simpa [prefixWord, tailWord_1872096, baseEnd_1872096] using wordTrace_append hprefix tailTrace_1872096
  have hstable : (prefixWord ++ tailWord_1872096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872096).length < 2 ^ (prefixWord ++ tailWord_1872096).sum := by decide
  have hdescent : baseEnd_1872096 < baseStart_1872096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872113 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 2, 4]
def baseStart_1872113 : Nat := 118140960795 + 1872113 * 2 ^ 59
def prefixEnd_1872113 : Nat := 4983230072969 + 3 ^ 40 * 1872113 * 2
def baseEnd_1872113 : Nat := 320431269510246360992605

theorem tailTrace_1872113 : CollatzResearch.WordTrace tailWord_1872113 prefixEnd_1872113 320431269510246360992605 := by
  unfold tailWord_1872113
  simp only [CollatzResearch.WordTrace]
  refine ⟨68281570666661807290388993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45521047111107871526925995 68281570666661807290388993)
  ·
    refine ⟨51211177999996355467791745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68281570666661807290388993 51211177999996355467791745)
    ·
      refine ⟨38408383499997266600843809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51211177999996355467791745 38408383499997266600843809)
      ·
        refine ⟨28806287624997949950632857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38408383499997266600843809 28806287624997949950632857)
        ·
          refine ⟨21604715718748462462974643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28806287624997949950632857 21604715718748462462974643)
          ·
            refine ⟨32407073578122693694461965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21604715718748462462974643 32407073578122693694461965)
            ·
              refine ⟨12152652591796010135423237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32407073578122693694461965 12152652591796010135423237)
              ·
                refine ⟨2278622360961751900391857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12152652591796010135423237 2278622360961751900391857)
                ·
                  refine ⟨1708966770721313925293893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2278622360961751900391857 1708966770721313925293893)
                  ·
                    refine ⟨320431269510246360992605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1708966770721313925293893 320431269510246360992605)
                    ·
                      rfl

theorem cell23_1872113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_1872113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872113 prefixEnd_1872113 := by exact prefixLift 1872113
  have htrace : WordTrace (prefixWord ++ tailWord_1872113) baseStart_1872113 baseEnd_1872113 := by
    simpa [prefixWord, tailWord_1872113, baseEnd_1872113] using wordTrace_append hprefix tailTrace_1872113
  have hstable : (prefixWord ++ tailWord_1872113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872113).length < 2 ^ (prefixWord ++ tailWord_1872113).sum := by decide
  have hdescent : baseEnd_1872113 < baseStart_1872113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872114 : List Nat := [3, 2, 1, 3, 2, 1, 4, 2, 1, 1, 3]
def baseStart_1872114 : Nat := 118140960795 + 1872114 * 2 ^ 59
def prefixEnd_1872114 : Nat := 4983230072969 + 3 ^ 40 * 1872114 * 2
def baseEnd_1872114 : Nat := 961294322011393579065311

theorem tailTrace_1872114 : CollatzResearch.WordTrace tailWord_1872114 prefixEnd_1872114 961294322011393579065311 := by
  unfold tailWord_1872114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17070401784914546115293849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45521071426438789640783597 17070401784914546115293849)
  ·
    refine ⟨12802801338685909586470387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17070401784914546115293849 12802801338685909586470387)
    ·
      refine ⟨19204202008028864379705581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12802801338685909586470387 19204202008028864379705581)
      ·
        refine ⟨7201575753010824142389593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19204202008028864379705581 7201575753010824142389593)
        ·
          refine ⟨5401181814758118106792195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7201575753010824142389593 5401181814758118106792195)
          ·
            refine ⟨8101772722137177160188293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401181814758118106792195 8101772722137177160188293)
            ·
              refine ⟨1519082385400720717535305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8101772722137177160188293 1519082385400720717535305)
              ·
                refine ⟨1139311789050540538151479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519082385400720717535305 1139311789050540538151479)
                ·
                  refine ⟨1708967683575810807227219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139311789050540538151479 1708967683575810807227219)
                  ·
                    refine ⟨2563451525363716210840829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1708967683575810807227219 2563451525363716210840829)
                    ·
                      refine ⟨961294322011393579065311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2563451525363716210840829 961294322011393579065311)
                      ·
                        rfl

theorem cell23_1872114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_1872114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872114 prefixEnd_1872114 := by exact prefixLift 1872114
  have htrace : WordTrace (prefixWord ++ tailWord_1872114) baseStart_1872114 baseEnd_1872114 := by
    simpa [prefixWord, tailWord_1872114, baseEnd_1872114] using wordTrace_append hprefix tailTrace_1872114
  have hstable : (prefixWord ++ tailWord_1872114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872114).length < 2 ^ (prefixWord ++ tailWord_1872114).sum := by decide
  have hdescent : baseEnd_1872114 < baseStart_1872114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872130 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1872130 : Nat := 118140960795 + 1872130 * 2 ^ 59
def prefixEnd_1872130 : Nat := 4983230072969 + 3 ^ 40 * 1872130 * 2
def baseEnd_1872130 : Nat := 320434179233955172155079

theorem tailTrace_1872130 : CollatzResearch.WordTrace tailWord_1872130 prefixEnd_1872130 320434179233955172155079 := by
  unfold tailWord_1872130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17070547676900054798439461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45521460471733479462505229 17070547676900054798439461)
  ·
    refine ⟨3200727689418760274707399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17070547676900054798439461 3200727689418760274707399)
    ·
      refine ⟨4801091534128140412061099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200727689418760274707399 4801091534128140412061099)
      ·
        refine ⟨7201637301192210618091649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4801091534128140412061099 7201637301192210618091649)
        ·
          refine ⟨5401227975894157963568737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7201637301192210618091649 5401227975894157963568737)
          ·
            refine ⟨4050920981920618472676553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5401227975894157963568737 4050920981920618472676553)
            ·
              refine ⟨3038190736440463854507415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4050920981920618472676553 3038190736440463854507415)
              ·
                refine ⟨4557286104660695781761123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038190736440463854507415 4557286104660695781761123)
                ·
                  refine ⟨6835929156991043672641685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557286104660695781761123 6835929156991043672641685)
                  ·
                    refine ⟨320434179233955172155079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6835929156991043672641685 320434179233955172155079)
                    ·
                      rfl

theorem cell23_1872130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1872130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872130 prefixEnd_1872130 := by exact prefixLift 1872130
  have htrace : WordTrace (prefixWord ++ tailWord_1872130) baseStart_1872130 baseEnd_1872130 := by
    simpa [prefixWord, tailWord_1872130, baseEnd_1872130] using wordTrace_append hprefix tailTrace_1872130
  have hstable : (prefixWord ++ tailWord_1872130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872130).length < 2 ^ (prefixWord ++ tailWord_1872130).sum := by decide
  have hdescent : baseEnd_1872130 < baseStart_1872130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872154 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4]
def baseStart_1872154 : Nat := 118140960795 + 1872154 * 2 ^ 59
def prefixEnd_1872154 : Nat := 4983230072969 + 3 ^ 40 * 1872154 * 2
def baseEnd_1872154 : Nat := 961314861237573422565127

theorem tailTrace_1872154 : CollatzResearch.WordTrace tailWord_1872154 prefixEnd_1872154 961314861237573422565127 := by
  unfold tailWord_1872154
  simp only [CollatzResearch.WordTrace]
  refine ⟨17070766514878317823157879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45522044039675514195087677 17070766514878317823157879)
  ·
    refine ⟨25606149772317476734736819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17070766514878317823157879 25606149772317476734736819)
    ·
      refine ⟨38409224658476215102105229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25606149772317476734736819 38409224658476215102105229)
      ·
        refine ⟨14403459246928580663289461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38409224658476215102105229 14403459246928580663289461)
        ·
          refine ⟨1350324304399554437183387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14403459246928580663289461 1350324304399554437183387)
          ·
            refine ⟨2025486456599331655775081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350324304399554437183387 2025486456599331655775081)
            ·
              refine ⟨1519114842449498741831311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025486456599331655775081 1519114842449498741831311)
              ·
                refine ⟨2278672263674248112746967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519114842449498741831311 2278672263674248112746967)
                ·
                  refine ⟨3418008395511372169120451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278672263674248112746967 3418008395511372169120451)
                  ·
                    refine ⟨5127012593267058253680677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3418008395511372169120451 5127012593267058253680677)
                    ·
                      refine ⟨961314861237573422565127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5127012593267058253680677 961314861237573422565127)
                      ·
                        rfl

theorem cell23_1872154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_1872154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872154 prefixEnd_1872154 := by exact prefixLift 1872154
  have htrace : WordTrace (prefixWord ++ tailWord_1872154) baseStart_1872154 baseEnd_1872154 := by
    simpa [prefixWord, tailWord_1872154, baseEnd_1872154] using wordTrace_append hprefix tailTrace_1872154
  have hstable : (prefixWord ++ tailWord_1872154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872154).length < 2 ^ (prefixWord ++ tailWord_1872154).sum := by decide
  have hdescent : baseEnd_1872154 < baseStart_1872154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872157 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1872157 : Nat := 118140960795 + 1872157 * 2 ^ 59
def prefixEnd_1872157 : Nat := 4983230072969 + 3 ^ 40 * 1872157 * 2
def baseEnd_1872157 : Nat := 961316401679536910827613

theorem tailTrace_1872157 : CollatzResearch.WordTrace tailWord_1872157 prefixEnd_1872157 961316401679536910827613 := by
  unfold tailWord_1872157
  simp only [CollatzResearch.WordTrace]
  refine ⟨68283175478502402804990725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45522116985668268536660483 68283175478502402804990725)
  ·
    refine ⟨12803095402219200525935761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68283175478502402804990725 12803095402219200525935761)
    ·
      refine ⟨9602321551664400394451821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12803095402219200525935761 9602321551664400394451821)
      ·
        refine ⟨3600870581874150147919433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9602321551664400394451821 3600870581874150147919433)
        ·
          refine ⟨2700652936405612610939575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3600870581874150147919433 2700652936405612610939575)
          ·
            refine ⟨4050979404608418916409363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700652936405612610939575 4050979404608418916409363)
            ·
              refine ⟨6076469106912628374614045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050979404608418916409363 6076469106912628374614045)
              ·
                refine ⟨2278675915092235640480267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6076469106912628374614045 2278675915092235640480267)
                ·
                  refine ⟨3418013872638353460720401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278675915092235640480267 3418013872638353460720401)
                  ·
                    refine ⟨2563510404478765095540301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3418013872638353460720401 2563510404478765095540301)
                    ·
                      refine ⟨961316401679536910827613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2563510404478765095540301 961316401679536910827613)
                      ·
                        rfl

theorem cell23_1872157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1872157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872157 prefixEnd_1872157 := by exact prefixLift 1872157
  have htrace : WordTrace (prefixWord ++ tailWord_1872157) baseStart_1872157 baseEnd_1872157 := by
    simpa [prefixWord, tailWord_1872157, baseEnd_1872157] using wordTrace_append hprefix tailTrace_1872157
  have hstable : (prefixWord ++ tailWord_1872157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872157).length < 2 ^ (prefixWord ++ tailWord_1872157).sum := by decide
  have hdescent : baseEnd_1872157 < baseStart_1872157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872176 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_1872176 : Nat := 118140960795 + 1872176 * 2 ^ 59
def prefixEnd_1872176 : Nat := 4983230072969 + 3 ^ 40 * 1872176 * 2
def baseEnd_1872176 : Nat := 961326157811972336490025

theorem tailTrace_1872176 : CollatzResearch.WordTrace tailWord_1872176 prefixEnd_1872176 961326157811972336490025 := by
  unfold tailWord_1872176
  simp only [CollatzResearch.WordTrace]
  refine ⟨34141934232716784524966191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45522578976955712699954921 34141934232716784524966191)
  ·
    refine ⟨51212901349075176787449287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34141934232716784524966191 51212901349075176787449287)
    ·
      refine ⟨76819352023612765181173931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51212901349075176787449287 76819352023612765181173931)
      ·
        refine ⟨115229028035419147771760897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76819352023612765181173931 115229028035419147771760897)
        ·
          refine ⟨86421771026564360828820673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115229028035419147771760897 86421771026564360828820673)
          ·
            refine ⟨64816328269923270621615505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86421771026564360828820673 64816328269923270621615505)
            ·
              refine ⟨48612246202442452966211629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64816328269923270621615505 48612246202442452966211629)
              ·
                refine ⟨18229592325915919862329361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48612246202442452966211629 18229592325915919862329361)
                ·
                  refine ⟨13672194244436939896747021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18229592325915919862329361 13672194244436939896747021)
                  ·
                    refine ⟨5127072841663852461280133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13672194244436939896747021 5127072841663852461280133)
                    ·
                      refine ⟨961326157811972336490025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5127072841663852461280133 961326157811972336490025)
                      ·
                        rfl

theorem cell23_1872176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_1872176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872176 prefixEnd_1872176 := by exact prefixLift 1872176
  have htrace : WordTrace (prefixWord ++ tailWord_1872176) baseStart_1872176 baseEnd_1872176 := by
    simpa [prefixWord, tailWord_1872176, baseEnd_1872176] using wordTrace_append hprefix tailTrace_1872176
  have hstable : (prefixWord ++ tailWord_1872176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872176).length < 2 ^ (prefixWord ++ tailWord_1872176).sum := by decide
  have hdescent : baseEnd_1872176 < baseStart_1872176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872210 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_1872210 : Nat := 118140960795 + 1872210 * 2 ^ 59
def prefixEnd_1872210 : Nat := 4983230072969 + 3 ^ 40 * 1872210 * 2
def baseEnd_1872210 : Nat := 961343616154225203464869

theorem tailTrace_1872210 : CollatzResearch.WordTrace tailWord_1872210 prefixEnd_1872210 961343616154225203464869 := by
  unfold tailWord_1872210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17071277136827598214167521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45523405698206928571113389 17071277136827598214167521)
  ·
    refine ⟨12803457852620698660625641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17071277136827598214167521 12803457852620698660625641)
    ·
      refine ⟨9602593389465523995469231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12803457852620698660625641 9602593389465523995469231)
      ·
        refine ⟨14403890084198285993203847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9602593389465523995469231 14403890084198285993203847)
        ·
          refine ⟨21605835126297428989805771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14403890084198285993203847 21605835126297428989805771)
          ·
            refine ⟨32408752689446143484708657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21605835126297428989805771 32408752689446143484708657)
            ·
              refine ⟨24306564517084607613531493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32408752689446143484708657 24306564517084607613531493)
              ·
                refine ⟨4557480846953363927537155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24306564517084607613531493 4557480846953363927537155)
                ·
                  refine ⟨6836221270430045891305733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557480846953363927537155 6836221270430045891305733)
                  ·
                    refine ⟨1281791488205633604619825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6836221270430045891305733 1281791488205633604619825)
                    ·
                      refine ⟨961343616154225203464869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281791488205633604619825 961343616154225203464869)
                      ·
                        rfl

theorem cell23_1872210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_1872210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872210 prefixEnd_1872210 := by exact prefixLift 1872210
  have htrace : WordTrace (prefixWord ++ tailWord_1872210) baseStart_1872210 baseEnd_1872210 := by
    simpa [prefixWord, tailWord_1872210, baseEnd_1872210] using wordTrace_append hprefix tailTrace_1872210
  have hstable : (prefixWord ++ tailWord_1872210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872210).length < 2 ^ (prefixWord ++ tailWord_1872210).sum := by decide
  have hdescent : baseEnd_1872210 < baseStart_1872210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872222 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1872222 : Nat := 118140960795 + 1872222 * 2 ^ 59
def prefixEnd_1872222 : Nat := 4983230072969 + 3 ^ 40 * 1872222 * 2
def baseEnd_1872222 : Nat := 961349777922079156514815

theorem tailTrace_1872222 : CollatzResearch.WordTrace tailWord_1872222 prefixEnd_1872222 961349777922079156514815 := by
  unfold tailWord_1872222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535693277908364863263365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45523697482177945937404613 8535693277908364863263365)
  ·
    refine ⟨1600442489607818411861881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8535693277908364863263365 1600442489607818411861881)
    ·
      refine ⟨1200331867205863808896411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1600442489607818411861881 1200331867205863808896411)
      ·
        refine ⟨1800497800808795713344617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200331867205863808896411 1800497800808795713344617)
        ·
          refine ⟨1350373350606596785008463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800497800808795713344617 1350373350606596785008463)
          ·
            refine ⟨2025560025909895177512695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350373350606596785008463 2025560025909895177512695)
            ·
              refine ⟨3038340038864842766269043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025560025909895177512695 3038340038864842766269043)
              ·
                refine ⟨4557510058297264149403565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038340038864842766269043 4557510058297264149403565)
                ·
                  refine ⟨1709066271861474056026337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4557510058297264149403565 1709066271861474056026337)
                  ·
                    refine ⟨1281799703896105542019753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1709066271861474056026337 1281799703896105542019753)
                    ·
                      refine ⟨961349777922079156514815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281799703896105542019753 961349777922079156514815)
                      ·
                        rfl

theorem cell23_1872222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1872222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872222 prefixEnd_1872222 := by exact prefixLift 1872222
  have htrace : WordTrace (prefixWord ++ tailWord_1872222) baseStart_1872222 baseEnd_1872222 := by
    simpa [prefixWord, tailWord_1872222, baseEnd_1872222] using wordTrace_append hprefix tailTrace_1872222
  have hstable : (prefixWord ++ tailWord_1872222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872222).length < 2 ^ (prefixWord ++ tailWord_1872222).sum := by decide
  have hdescent : baseEnd_1872222 < baseStart_1872222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872227 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 2, 2, 2]
def baseStart_1872227 : Nat := 118140960795 + 1872227 * 2 ^ 59
def prefixEnd_1872227 : Nat := 4983230072969 + 3 ^ 40 * 1872227 * 2
def baseEnd_1872227 : Nat := 961352345325351636952291

theorem tailTrace_1872227 : CollatzResearch.WordTrace tailWord_1872227 prefixEnd_1872227 961352345325351636952291 := by
  unfold tailWord_1872227
  simp only [CollatzResearch.WordTrace]
  refine ⟨68285728588248804760038935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45523819058832536506692623 68285728588248804760038935)
  ·
    refine ⟨102428592882373207140058403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68285728588248804760038935 102428592882373207140058403)
    ·
      refine ⟨153642889323559810710087605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102428592882373207140058403 153642889323559810710087605)
      ·
        refine ⟨14404020874083732254070713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153642889323559810710087605 14404020874083732254070713)
        ·
          refine ⟨10803015655562799190553035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14404020874083732254070713 10803015655562799190553035)
          ·
            refine ⟨16204523483344198785829553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10803015655562799190553035 16204523483344198785829553)
            ·
              refine ⟨12153392612508149089372165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16204523483344198785829553 12153392612508149089372165)
              ·
                refine ⟨2278761114845277954257281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12153392612508149089372165 2278761114845277954257281)
                ·
                  refine ⟨1709070836133958465692961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2278761114845277954257281 1709070836133958465692961)
                  ·
                    refine ⟨1281803127100468849269721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1709070836133958465692961 1281803127100468849269721)
                    ·
                      refine ⟨961352345325351636952291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281803127100468849269721 961352345325351636952291)
                      ·
                        rfl

theorem cell23_1872227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_1872227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872227 prefixEnd_1872227 := by exact prefixLift 1872227
  have htrace : WordTrace (prefixWord ++ tailWord_1872227) baseStart_1872227 baseEnd_1872227 := by
    simpa [prefixWord, tailWord_1872227, baseEnd_1872227] using wordTrace_append hprefix tailTrace_1872227
  have hstable : (prefixWord ++ tailWord_1872227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872227).length < 2 ^ (prefixWord ++ tailWord_1872227).sum := by decide
  have hdescent : baseEnd_1872227 < baseStart_1872227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872280 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 2, 5]
def baseStart_1872280 : Nat := 118140960795 + 1872280 * 2 ^ 59
def prefixEnd_1872280 : Nat := 4983230072969 + 3 ^ 40 * 1872280 * 2
def baseEnd_1872280 : Nat := 320459853266679976529849

theorem tailTrace_1872280 : CollatzResearch.WordTrace tailWord_1872280 prefixEnd_1872280 320459853266679976529849 := by
  unfold tailWord_1872280
  simp only [CollatzResearch.WordTrace]
  refine ⟨34143830828528397405859147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45525107771371196541145529 34143830828528397405859147)
  ·
    refine ⟨51215746242792596108788721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34143830828528397405859147 51215746242792596108788721)
    ·
      refine ⟨38411809682094447081591541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51215746242792596108788721 38411809682094447081591541)
      ·
        refine ⟨3601107157696354413899207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38411809682094447081591541 3601107157696354413899207)
        ·
          refine ⟨5401660736544531620848811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3601107157696354413899207 5401660736544531620848811)
          ·
            refine ⟨8102491104816797431273217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401660736544531620848811 8102491104816797431273217)
            ·
              refine ⟨6076868328612598073454913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8102491104816797431273217 6076868328612598073454913)
              ·
                refine ⟨4557651246459448555091185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6076868328612598073454913 4557651246459448555091185)
                ·
                  refine ⟨3418238434844586416318389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4557651246459448555091185 3418238434844586416318389)
                  ·
                    refine ⟨320459853266679976529849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3418238434844586416318389 320459853266679976529849)
                    ·
                      rfl

theorem cell23_1872280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_1872280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872280 prefixEnd_1872280 := by exact prefixLift 1872280
  have htrace : WordTrace (prefixWord ++ tailWord_1872280) baseStart_1872280 baseEnd_1872280 := by
    simpa [prefixWord, tailWord_1872280, baseEnd_1872280] using wordTrace_append hprefix tailTrace_1872280
  have hstable : (prefixWord ++ tailWord_1872280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872280).length < 2 ^ (prefixWord ++ tailWord_1872280).sum := by decide
  have hdescent : baseEnd_1872280 < baseStart_1872280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872317 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_1872317 : Nat := 118140960795 + 1872317 * 2 ^ 59
def prefixEnd_1872317 : Nat := 4983230072969 + 3 ^ 40 * 1872317 * 2
def baseEnd_1872317 : Nat := 961398558584256284826877

theorem tailTrace_1872317 : CollatzResearch.WordTrace tailWord_1872317 prefixEnd_1872317 961398558584256284826877 := by
  unfold tailWord_1872317
  simp only [CollatzResearch.WordTrace]
  refine ⟨68289011157922750130815205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45526007438615166753876803 68289011157922750130815205)
  ·
    refine ⟨12804189592110515649527851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68289011157922750130815205 12804189592110515649527851)
    ·
      refine ⟨19206284388165773474291777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12804189592110515649527851 19206284388165773474291777)
      ·
        refine ⟨14404713291124330105718833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19206284388165773474291777 14404713291124330105718833)
        ·
          refine ⟨10803534968343247579289125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14404713291124330105718833 10803534968343247579289125)
          ·
            refine ⟨2025662806564358921116711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10803534968343247579289125 2025662806564358921116711)
            ·
              refine ⟨3038494209846538381675067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025662806564358921116711 3038494209846538381675067)
              ·
                refine ⟨4557741314769807572512601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038494209846538381675067 4557741314769807572512601)
                ·
                  refine ⟨3418305986077355679384451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4557741314769807572512601 3418305986077355679384451)
                  ·
                    refine ⟨5127458979116033519076677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3418305986077355679384451 5127458979116033519076677)
                    ·
                      refine ⟨961398558584256284826877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5127458979116033519076677 961398558584256284826877)
                      ·
                        rfl

theorem cell23_1872317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_1872317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872317 prefixEnd_1872317 := by exact prefixLift 1872317
  have htrace : WordTrace (prefixWord ++ tailWord_1872317) baseStart_1872317 baseEnd_1872317 := by
    simpa [prefixWord, tailWord_1872317, baseEnd_1872317] using wordTrace_append hprefix tailTrace_1872317
  have hstable : (prefixWord ++ tailWord_1872317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872317).length < 2 ^ (prefixWord ++ tailWord_1872317).sum := by decide
  have hdescent : baseEnd_1872317 < baseStart_1872317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872327 : List Nat := [1, 1, 4, 1, 1, 4, 1, 5, 1, 4]
def baseStart_1872327 : Nat := 118140960795 + 1872327 * 2 ^ 59
def prefixEnd_1872327 : Nat := 4983230072969 + 3 ^ 40 * 1872327 * 2
def baseEnd_1872327 : Nat := 320467897796933748567277

theorem tailTrace_1872327 : CollatzResearch.WordTrace tailWord_1872327 prefixEnd_1872327 320467897796933748567277 := by
  unfold tailWord_1872327
  simp only [CollatzResearch.WordTrace]
  refine ⟨68289375887886521838679235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45526250591924347892452823 68289375887886521838679235)
  ·
    refine ⟨102434063831829782758018853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68289375887886521838679235 102434063831829782758018853)
    ·
      refine ⟨19206386968468084267128535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102434063831829782758018853 19206386968468084267128535)
      ·
        refine ⟨28809580452702126400692803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19206386968468084267128535 28809580452702126400692803)
        ·
          refine ⟨43214370679053189601039205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28809580452702126400692803 43214370679053189601039205)
          ·
            refine ⟨8102694502322473050194851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43214370679053189601039205 8102694502322473050194851)
            ·
              refine ⟨12154041753483709575292277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102694502322473050194851 12154041753483709575292277)
              ·
                refine ⟨1139441414389097772683651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12154041753483709575292277 1139441414389097772683651)
                ·
                  refine ⟨1709162121583646659025477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139441414389097772683651 1709162121583646659025477)
                  ·
                    refine ⟨320467897796933748567277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1709162121583646659025477 320467897796933748567277)
                    ·
                      rfl

theorem cell23_1872327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_1872327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872327 prefixEnd_1872327 := by exact prefixLift 1872327
  have htrace : WordTrace (prefixWord ++ tailWord_1872327) baseStart_1872327 baseEnd_1872327 := by
    simpa [prefixWord, tailWord_1872327, baseEnd_1872327] using wordTrace_append hprefix tailTrace_1872327
  have hstable : (prefixWord ++ tailWord_1872327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872327).length < 2 ^ (prefixWord ++ tailWord_1872327).sum := by decide
  have hdescent : baseEnd_1872327 < baseStart_1872327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872340 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 8]
def baseStart_1872340 : Nat := 118140960795 + 1872340 * 2 ^ 59
def prefixEnd_1872340 : Nat := 4983230072969 + 3 ^ 40 * 1872340 * 2
def baseEnd_1872340 : Nat := 106823374293256632759919

theorem tailTrace_1872340 : CollatzResearch.WordTrace tailWord_1872340 prefixEnd_1872340 106823374293256632759919 := by
  unfold tailWord_1872340
  simp only [CollatzResearch.WordTrace]
  refine ⟨34144925018419712529451237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45526566691226283372601649 34144925018419712529451237)
  ·
    refine ⟨6402173440953696099272107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34144925018419712529451237 6402173440953696099272107)
    ·
      refine ⟨9603260161430544148908161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402173440953696099272107 9603260161430544148908161)
      ·
        refine ⟨7202445121072908111681121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9603260161430544148908161 7202445121072908111681121)
        ·
          refine ⟨5401833840804681083760841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7202445121072908111681121 5401833840804681083760841)
          ·
            refine ⟨4051375380603510812820631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5401833840804681083760841 4051375380603510812820631)
            ·
              refine ⟨6077063070905266219230947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051375380603510812820631 6077063070905266219230947)
              ·
                refine ⟨9115594606357899328846421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6077063070905266219230947 9115594606357899328846421)
                ·
                  refine ⟨106823374293256632759919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9115594606357899328846421 106823374293256632759919)
                  ·
                    rfl

theorem cell23_1872340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_1872340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872340 prefixEnd_1872340 := by exact prefixLift 1872340
  have htrace : WordTrace (prefixWord ++ tailWord_1872340) baseStart_1872340 baseEnd_1872340 := by
    simpa [prefixWord, tailWord_1872340, baseEnd_1872340] using wordTrace_append hprefix tailTrace_1872340
  have hstable : (prefixWord ++ tailWord_1872340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872340).length < 2 ^ (prefixWord ++ tailWord_1872340).sum := by decide
  have hdescent : baseEnd_1872340 < baseStart_1872340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872383 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 3, 6]
def baseStart_1872383 : Nat := 118140960795 + 1872383 * 2 ^ 59
def prefixEnd_1872383 : Nat := 4983230072969 + 3 ^ 40 * 1872383 * 2
def baseEnd_1872383 : Nat := 320477482769151008867191

theorem tailTrace_1872383 : CollatzResearch.WordTrace tailWord_1872383 prefixEnd_1872383 320477482769151008867191 := by
  unfold tailWord_1872383
  simp only [CollatzResearch.WordTrace]
  refine ⟨68291418375683643402717803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45527612250455762268478535 68291418375683643402717803)
  ·
    refine ⟨102437127563525465104076705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68291418375683643402717803 102437127563525465104076705)
    ·
      refine ⟨76827845672644098828057529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102437127563525465104076705 76827845672644098828057529)
      ·
        refine ⟨57620884254483074121043147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76827845672644098828057529 57620884254483074121043147)
        ·
          refine ⟨86431326381724611181564721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57620884254483074121043147 86431326381724611181564721)
          ·
            refine ⟨64823494786293458386173541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86431326381724611181564721 64823494786293458386173541)
            ·
              refine ⟨12154405272430023447407539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64823494786293458386173541 12154405272430023447407539)
              ·
                refine ⟨18231607908645035171111309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12154405272430023447407539 18231607908645035171111309)
                ·
                  refine ⟨6836852965741888189166741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18231607908645035171111309 6836852965741888189166741)
                  ·
                    refine ⟨320477482769151008867191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6836852965741888189166741 320477482769151008867191)
                    ·
                      rfl

theorem cell23_1872383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_1872383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872383 prefixEnd_1872383 := by exact prefixLift 1872383
  have htrace : WordTrace (prefixWord ++ tailWord_1872383) baseStart_1872383 baseEnd_1872383 := by
    simpa [prefixWord, tailWord_1872383, baseEnd_1872383] using wordTrace_append hprefix tailTrace_1872383
  have hstable : (prefixWord ++ tailWord_1872383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872383).length < 2 ^ (prefixWord ++ tailWord_1872383).sum := by decide
  have hdescent : baseEnd_1872383 < baseStart_1872383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872403 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 6]
def baseStart_1872403 : Nat := 118140960795 + 1872403 * 2 ^ 59
def prefixEnd_1872403 : Nat := 4983230072969 + 3 ^ 40 * 1872403 * 2
def baseEnd_1872403 : Nat := 961442717920542948351481

theorem tailTrace_1872403 : CollatzResearch.WordTrace tailWord_1872403 prefixEnd_1872403 961442717920542948351481 := by
  unfold tailWord_1872403
  simp only [CollatzResearch.WordTrace]
  refine ⟨68292147835611186818445863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45528098557074124545630575 68292147835611186818445863)
  ·
    refine ⟨102438221753416780227668795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68292147835611186818445863 102438221753416780227668795)
    ·
      refine ⟨153657332630125170341503193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102438221753416780227668795 153657332630125170341503193)
      ·
        refine ⟨115242999472593877756127395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153657332630125170341503193 115242999472593877756127395)
        ·
          refine ⟨172864499208890816634191093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115242999472593877756127395 172864499208890816634191093)
          ·
            refine ⟨16206046800833514059455415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172864499208890816634191093 16206046800833514059455415)
            ·
              refine ⟨24309070201250271089183123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16206046800833514059455415 24309070201250271089183123)
              ·
                refine ⟨36463605301875406633774685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24309070201250271089183123 36463605301875406633774685)
                ·
                  refine ⟨13673851988203277487665507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36463605301875406633774685 13673851988203277487665507)
                  ·
                    refine ⟨20510777982304916231498261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13673851988203277487665507 20510777982304916231498261)
                    ·
                      refine ⟨961442717920542948351481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20510777982304916231498261 961442717920542948351481)
                      ·
                        rfl

theorem cell23_1872403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_1872403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872403 prefixEnd_1872403 := by exact prefixLift 1872403
  have htrace : WordTrace (prefixWord ++ tailWord_1872403) baseStart_1872403 baseEnd_1872403 := by
    simpa [prefixWord, tailWord_1872403, baseEnd_1872403] using wordTrace_append hprefix tailTrace_1872403
  have hstable : (prefixWord ++ tailWord_1872403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872403).length < 2 ^ (prefixWord ++ tailWord_1872403).sum := by decide
  have hdescent : baseEnd_1872403 < baseStart_1872403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872410 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1872410 : Nat := 118140960795 + 1872410 * 2 ^ 59
def prefixEnd_1872410 : Nat := 4983230072969 + 3 ^ 40 * 1872410 * 2
def baseEnd_1872410 : Nat := 961446312285124420963949

theorem tailTrace_1872410 : CollatzResearch.WordTrace tailWord_1872410 prefixEnd_1872410 961446312285124420963949 := by
  unfold tailWord_1872410
  simp only [CollatzResearch.WordTrace]
  refine ⟨17073100786646456753487671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45528268764390551342633789 17073100786646456753487671)
  ·
    refine ⟨25609651179969685130231507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17073100786646456753487671 25609651179969685130231507)
    ·
      refine ⟨38414476769954527695347261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25609651179969685130231507 38414476769954527695347261)
      ·
        refine ⟨14405428788732947885755223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38414476769954527695347261 14405428788732947885755223)
        ·
          refine ⟨21608143183099421828632835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14405428788732947885755223 21608143183099421828632835)
          ·
            refine ⟨32412214774649132742949253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21608143183099421828632835 32412214774649132742949253)
            ·
              refine ⟨6077290270246712389302985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32412214774649132742949253 6077290270246712389302985)
              ·
                refine ⟨4557967702685034291977239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6077290270246712389302985 4557967702685034291977239)
                ·
                  refine ⟨6836951554027551437965859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557967702685034291977239 6836951554027551437965859)
                  ·
                    refine ⟨10255427331041327156948789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6836951554027551437965859 10255427331041327156948789)
                    ·
                      refine ⟨961446312285124420963949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10255427331041327156948789 961446312285124420963949)
                      ·
                        rfl

theorem cell23_1872410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1872410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872410 prefixEnd_1872410 := by exact prefixLift 1872410
  have htrace : WordTrace (prefixWord ++ tailWord_1872410) baseStart_1872410 baseEnd_1872410 := by
    simpa [prefixWord, tailWord_1872410, baseEnd_1872410] using wordTrace_append hprefix tailTrace_1872410
  have hstable : (prefixWord ++ tailWord_1872410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872410).length < 2 ^ (prefixWord ++ tailWord_1872410).sum := by decide
  have hdescent : baseEnd_1872410 < baseStart_1872410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872417 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 2, 4]
def baseStart_1872417 : Nat := 118140960795 + 1872417 * 2 ^ 59
def prefixEnd_1872417 : Nat := 4983230072969 + 3 ^ 40 * 1872417 * 2
def baseEnd_1872417 : Nat := 320483302216568631192139

theorem tailTrace_1872417 : CollatzResearch.WordTrace tailWord_1872417 prefixEnd_1872417 320483302216568631192139 := by
  unfold tailWord_1872417
  simp only [CollatzResearch.WordTrace]
  refine ⟨68292658457560467209455505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45528438971706978139637003 68292658457560467209455505)
  ·
    refine ⟨51219493843170350407091629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68292658457560467209455505 51219493843170350407091629)
    ·
      refine ⟨19207310191188881402659361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51219493843170350407091629 19207310191188881402659361)
      ·
        refine ⟨14405482643391661051994521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19207310191188881402659361 14405482643391661051994521)
        ·
          refine ⟨10804111982543745788995891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14405482643391661051994521 10804111982543745788995891)
          ·
            refine ⟨16206167973815618683493837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10804111982543745788995891 16206167973815618683493837)
            ·
              refine ⟨6077312990180857006310189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16206167973815618683493837 6077312990180857006310189)
              ·
                refine ⟨2278992371317821377366321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6077312990180857006310189 2278992371317821377366321)
                ·
                  refine ⟨1709244278488366033024741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2278992371317821377366321 1709244278488366033024741)
                  ·
                    refine ⟨320483302216568631192139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1709244278488366033024741 320483302216568631192139)
                    ·
                      rfl

theorem cell23_1872417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_1872417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872417 prefixEnd_1872417 := by exact prefixLift 1872417
  have htrace : WordTrace (prefixWord ++ tailWord_1872417) baseStart_1872417 baseEnd_1872417 := by
    simpa [prefixWord, tailWord_1872417, baseEnd_1872417] using wordTrace_append hprefix tailTrace_1872417
  have hstable : (prefixWord ++ tailWord_1872417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872417).length < 2 ^ (prefixWord ++ tailWord_1872417).sum := by decide
  have hdescent : baseEnd_1872417 < baseStart_1872417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872424 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1872424 : Nat := 118140960795 + 1872424 * 2 ^ 59
def prefixEnd_1872424 : Nat := 4983230072969 + 3 ^ 40 * 1872424 * 2
def baseEnd_1872424 : Nat := 961453501014287366188885

theorem tailTrace_1872424 : CollatzResearch.WordTrace tailWord_1872424 prefixEnd_1872424 961453501014287366188885 := by
  unfold tailWord_1872424
  simp only [CollatzResearch.WordTrace]
  refine ⟨34146456884267553702480163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45528609179023404936640217 34146456884267553702480163)
  ·
    refine ⟨51219685326401330553720245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34146456884267553702480163 51219685326401330553720245)
    ·
      refine ⟨4801845499350124739411273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51219685326401330553720245 4801845499350124739411273)
      ·
        refine ⟨3601384124512593554558455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4801845499350124739411273 3601384124512593554558455)
        ·
          refine ⟨5402076186768890331837683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3601384124512593554558455 5402076186768890331837683)
          ·
            refine ⟨8103114280153335497756525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402076186768890331837683 8103114280153335497756525)
            ·
              refine ⟨3038667855057500811658697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8103114280153335497756525 3038667855057500811658697)
              ·
                refine ⟨2279000891293125608744023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3038667855057500811658697 2279000891293125608744023)
                ·
                  refine ⟨3418501336939688413116035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279000891293125608744023 3418501336939688413116035)
                  ·
                    refine ⟨5127752005409532619674053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3418501336939688413116035 5127752005409532619674053)
                    ·
                      refine ⟨961453501014287366188885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5127752005409532619674053 961453501014287366188885)
                      ·
                        rfl

theorem cell23_1872424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1872424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872424 prefixEnd_1872424 := by exact prefixLift 1872424
  have htrace : WordTrace (prefixWord ++ tailWord_1872424) baseStart_1872424 baseEnd_1872424 := by
    simpa [prefixWord, tailWord_1872424, baseEnd_1872424] using wordTrace_append hprefix tailTrace_1872424
  have hstable : (prefixWord ++ tailWord_1872424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872424).length < 2 ^ (prefixWord ++ tailWord_1872424).sum := by decide
  have hdescent : baseEnd_1872424 < baseStart_1872424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872441 : List Nat := [1, 2, 1, 5, 1, 1, 2, 5, 1, 2, 2]
def baseStart_1872441 : Nat := 118140960795 + 1872441 * 2 ^ 59
def prefixEnd_1872441 : Nat := 4983230072969 + 3 ^ 40 * 1872441 * 2
def baseEnd_1872441 : Nat := 961462230185413799676307

theorem tailTrace_1872441 : CollatzResearch.WordTrace tailWord_1872441 prefixEnd_1872441 961462230185413799676307 := by
  unfold tailWord_1872441
  simp only [CollatzResearch.WordTrace]
  refine ⟨68293533809473519308329177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45529022539649012872219451 68293533809473519308329177)
  ·
    refine ⟨51220150357105139481246883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68293533809473519308329177 51220150357105139481246883)
    ·
      refine ⟨76830225535657709221870325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51220150357105139481246883 76830225535657709221870325)
      ·
        refine ⟨7202833643967910239550343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76830225535657709221870325 7202833643967910239550343)
        ·
          refine ⟨10804250465951865359325515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7202833643967910239550343 10804250465951865359325515)
          ·
            refine ⟨16206375698927798038988273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10804250465951865359325515 16206375698927798038988273)
            ·
              refine ⟨12154781774195848529241205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16206375698927798038988273 12154781774195848529241205)
              ·
                refine ⟨1139510791330860799616363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12154781774195848529241205 1139510791330860799616363)
                ·
                  refine ⟨1709266186996291199424545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139510791330860799616363 1709266186996291199424545)
                  ·
                    refine ⟨1281949640247218399568409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1709266186996291199424545 1281949640247218399568409)
                    ·
                      refine ⟨961462230185413799676307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281949640247218399568409 961462230185413799676307)
                      ·
                        rfl

theorem cell23_1872441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_1872441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872441 prefixEnd_1872441 := by exact prefixLift 1872441
  have htrace : WordTrace (prefixWord ++ tailWord_1872441) baseStart_1872441 baseEnd_1872441 := by
    simpa [prefixWord, tailWord_1872441, baseEnd_1872441] using wordTrace_append hprefix tailTrace_1872441
  have hstable : (prefixWord ++ tailWord_1872441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872441).length < 2 ^ (prefixWord ++ tailWord_1872441).sum := by decide
  have hdescent : baseEnd_1872441 < baseStart_1872441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872458 : List Nat := [3, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2]
def baseStart_1872458 : Nat := 118140960795 + 1872458 * 2 ^ 59
def prefixEnd_1872458 : Nat := 4983230072969 + 3 ^ 40 * 1872458 * 2
def baseEnd_1872458 : Nat := 961470959356540233163729

theorem tailTrace_1872458 : CollatzResearch.WordTrace tailWord_1872458 prefixEnd_1872458 961470959356540233163729 := by
  unfold tailWord_1872458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17073538462602982802924507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45529435900274620807798685 17073538462602982802924507)
  ·
    refine ⟨25610307693904474204386761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17073538462602982802924507 25610307693904474204386761)
    ·
      refine ⟨19207730770428355653290071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25610307693904474204386761 19207730770428355653290071)
      ·
        refine ⟨28811596155642533479935107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19207730770428355653290071 28811596155642533479935107)
        ·
          refine ⟨43217394233463800219902661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28811596155642533479935107 43217394233463800219902661)
          ·
            refine ⟨8103261418774462541231749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43217394233463800219902661 8103261418774462541231749)
            ·
              refine ⟨1519361516020211726480953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8103261418774462541231749 1519361516020211726480953)
              ·
                refine ⟨1139521137015158794860715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519361516020211726480953 1139521137015158794860715)
                ·
                  refine ⟨1709281705522738192291073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139521137015158794860715 1709281705522738192291073)
                  ·
                    refine ⟨1281961279142053644218305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1709281705522738192291073 1281961279142053644218305)
                    ·
                      refine ⟨961470959356540233163729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281961279142053644218305 961470959356540233163729)
                      ·
                        rfl

theorem cell23_1872458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_1872458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872458 prefixEnd_1872458 := by exact prefixLift 1872458
  have htrace : WordTrace (prefixWord ++ tailWord_1872458) baseStart_1872458 baseEnd_1872458 := by
    simpa [prefixWord, tailWord_1872458, baseEnd_1872458] using wordTrace_append hprefix tailTrace_1872458
  have hstable : (prefixWord ++ tailWord_1872458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872458).length < 2 ^ (prefixWord ++ tailWord_1872458).sum := by decide
  have hdescent : baseEnd_1872458 < baseStart_1872458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872484 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_1872484 : Nat := 118140960795 + 1872484 * 2 ^ 59
def prefixEnd_1872484 : Nat := 4983230072969 + 3 ^ 40 * 1872484 * 2
def baseEnd_1872484 : Nat := 961484309853557131438609

theorem tailTrace_1872484 : CollatzResearch.WordTrace tailWord_1872484 prefixEnd_1872484 961484309853557131438609 := by
  unfold tailWord_1872484
  simp only [CollatzResearch.WordTrace]
  refine ⟨34147551074158868826072253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45530068098878491768096337 34147551074158868826072253)
  ·
    refine ⟨12805331652809575809777095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34147551074158868826072253 12805331652809575809777095)
    ·
      refine ⟨19207997479214363714665643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12805331652809575809777095 19207997479214363714665643)
      ·
        refine ⟨28811996218821545571998465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19207997479214363714665643 28811996218821545571998465)
        ·
          refine ⟨21608997164116159178998849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28811996218821545571998465 21608997164116159178998849)
          ·
            refine ⟨16206747873087119384249137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21608997164116159178998849 16206747873087119384249137)
            ·
              refine ⟨12155060904815339538186853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16206747873087119384249137 12155060904815339538186853)
              ·
                refine ⟨2279073919652876163410035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12155060904815339538186853 2279073919652876163410035)
                ·
                  refine ⟨3418610879479314245115053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279073919652876163410035 3418610879479314245115053)
                  ·
                    refine ⟨1281979079804742841918145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418610879479314245115053 1281979079804742841918145)
                    ·
                      refine ⟨961484309853557131438609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1281979079804742841918145 961484309853557131438609)
                      ·
                        rfl

theorem cell23_1872484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_1872484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872484 prefixEnd_1872484 := by exact prefixLift 1872484
  have htrace : WordTrace (prefixWord ++ tailWord_1872484) baseStart_1872484 baseEnd_1872484 := by
    simpa [prefixWord, tailWord_1872484, baseEnd_1872484] using wordTrace_append hprefix tailTrace_1872484
  have hstable : (prefixWord ++ tailWord_1872484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872484).length < 2 ^ (prefixWord ++ tailWord_1872484).sum := by decide
  have hdescent : baseEnd_1872484 < baseStart_1872484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872490 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1872490 : Nat := 118140960795 + 1872490 * 2 ^ 59
def prefixEnd_1872490 : Nat := 4983230072969 + 3 ^ 40 * 1872490 * 2
def baseEnd_1872490 : Nat := 320495796912494702654527

theorem tailTrace_1872490 : CollatzResearch.WordTrace tailWord_1872490 prefixEnd_1872490 320495796912494702654527 := by
  unfold tailWord_1872490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17073830246574000169215731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45530213990864000451241949 17073830246574000169215731)
  ·
    refine ⟨25610745369861000253823597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17073830246574000169215731 25610745369861000253823597)
    ·
      refine ⟨9604029513697875095183849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25610745369861000253823597 9604029513697875095183849)
      ·
        refine ⟨7203022135273406321387887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9604029513697875095183849 7203022135273406321387887)
        ·
          refine ⟨10804533202910109482081831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203022135273406321387887 10804533202910109482081831)
          ·
            refine ⟨16206799804365164223122747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10804533202910109482081831 16206799804365164223122747)
            ·
              refine ⟨24310199706547746334684121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16206799804365164223122747 24310199706547746334684121)
              ·
                refine ⟨18232649779910809751013091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24310199706547746334684121 18232649779910809751013091)
                ·
                  refine ⟨27348974669866214626519637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18232649779910809751013091 27348974669866214626519637)
                  ·
                    refine ⟨320495796912494702654527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27348974669866214626519637 320495796912494702654527)
                    ·
                      rfl

theorem cell23_1872490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1872490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872490 prefixEnd_1872490 := by exact prefixLift 1872490
  have htrace : WordTrace (prefixWord ++ tailWord_1872490) baseStart_1872490 baseEnd_1872490 := by
    simpa [prefixWord, tailWord_1872490, baseEnd_1872490] using wordTrace_append hprefix tailTrace_1872490
  have hstable : (prefixWord ++ tailWord_1872490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872490).length < 2 ^ (prefixWord ++ tailWord_1872490).sum := by decide
  have hdescent : baseEnd_1872490 < baseStart_1872490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872560 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_1872560 : Nat := 118140960795 + 1872560 * 2 ^ 59
def prefixEnd_1872560 : Nat := 4983230072969 + 3 ^ 40 * 1872560 * 2
def baseEnd_1872560 : Nat := 961523334383298834088259

theorem tailTrace_1872560 : CollatzResearch.WordTrace tailWord_1872560 prefixEnd_1872560 961523334383298834088259 := by
  unfold tailWord_1872560
  simp only [CollatzResearch.WordTrace]
  refine ⟨34148937048021201315955567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45531916064028268421274089 34148937048021201315955567)
  ·
    refine ⟨51223405572031801973933351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34148937048021201315955567 51223405572031801973933351)
    ·
      refine ⟨76835108358047702960900027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51223405572031801973933351 76835108358047702960900027)
      ·
        refine ⟨115252662537071554441350041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76835108358047702960900027 115252662537071554441350041)
        ·
          refine ⟨86439496902803665831012531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115252662537071554441350041 86439496902803665831012531)
          ·
            refine ⟨129659245354205498746518797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86439496902803665831012531 129659245354205498746518797)
            ·
              refine ⟨48622217007827062029944549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129659245354205498746518797 48622217007827062029944549)
              ·
                refine ⟨9116665688967574130614603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48622217007827062029944549 9116665688967574130614603)
                ·
                  refine ⟨13674998533451361195921905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9116665688967574130614603 13674998533451361195921905)
                  ·
                    refine ⟨10256248900088520896941429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13674998533451361195921905 10256248900088520896941429)
                    ·
                      refine ⟨961523334383298834088259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10256248900088520896941429 961523334383298834088259)
                      ·
                        rfl

theorem cell23_1872560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_1872560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872560 prefixEnd_1872560 := by exact prefixLift 1872560
  have htrace : WordTrace (prefixWord ++ tailWord_1872560) baseStart_1872560 baseEnd_1872560 := by
    simpa [prefixWord, tailWord_1872560, baseEnd_1872560] using wordTrace_append hprefix tailTrace_1872560
  have hstable : (prefixWord ++ tailWord_1872560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872560).length < 2 ^ (prefixWord ++ tailWord_1872560).sum := by decide
  have hdescent : baseEnd_1872560 < baseStart_1872560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872574 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_1872574 : Nat := 118140960795 + 1872574 * 2 ^ 59
def prefixEnd_1872574 : Nat := 4983230072969 + 3 ^ 40 * 1872574 * 2
def baseEnd_1872574 : Nat := 961530523112461779313195

theorem tailTrace_1872574 : CollatzResearch.WordTrace tailWord_1872574 prefixEnd_1872574 961530523112461779313195 := by
  unfold tailWord_1872574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8537298089748960377865097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45532256478661122015280517 8537298089748960377865097)
  ·
    refine ⟨6402973567311720283398823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8537298089748960377865097 6402973567311720283398823)
    ·
      refine ⟨9604460350967580425098235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402973567311720283398823 9604460350967580425098235)
      ·
        refine ⟨14406690526451370637647353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9604460350967580425098235 14406690526451370637647353)
        ·
          refine ⟨10805017894838527978235515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14406690526451370637647353 10805017894838527978235515)
          ·
            refine ⟨16207526842257791967353273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10805017894838527978235515 16207526842257791967353273)
            ·
              refine ⟨12155645131693343975514955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16207526842257791967353273 12155645131693343975514955)
              ·
                refine ⟨18233467697540015963272433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12155645131693343975514955 18233467697540015963272433)
                ·
                  refine ⟨13675100773155011972454325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18233467697540015963272433 13675100773155011972454325)
                  ·
                    refine ⟨1282040697483282372417593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13675100773155011972454325 1282040697483282372417593)
                    ·
                      refine ⟨961530523112461779313195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282040697483282372417593 961530523112461779313195)
                      ·
                        rfl

theorem cell23_1872574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_1872574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872574 prefixEnd_1872574 := by exact prefixLift 1872574
  have htrace : WordTrace (prefixWord ++ tailWord_1872574) baseStart_1872574 baseEnd_1872574 := by
    simpa [prefixWord, tailWord_1872574, baseEnd_1872574] using wordTrace_append hprefix tailTrace_1872574
  have hstable : (prefixWord ++ tailWord_1872574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872574).length < 2 ^ (prefixWord ++ tailWord_1872574).sum := by decide
  have hdescent : baseEnd_1872574 < baseStart_1872574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872582 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_1872582 : Nat := 118140960795 + 1872582 * 2 ^ 59
def prefixEnd_1872582 : Nat := 4983230072969 + 3 ^ 40 * 1872582 * 2
def baseEnd_1872582 : Nat := 961534630957697748013159

theorem tailTrace_1872582 : CollatzResearch.WordTrace tailWord_1872582 prefixEnd_1872582 961534630957697748013159 := by
  unfold tailWord_1872582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134333640686334387162875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45532451001308466926141333 2134333640686334387162875)
  ·
    refine ⟨3201500461029501580744313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2134333640686334387162875 3201500461029501580744313)
    ·
      refine ⟨2401125345772126185558235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3201500461029501580744313 2401125345772126185558235)
      ·
        refine ⟨3601688018658189278337353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401125345772126185558235 3601688018658189278337353)
        ·
          refine ⟨2701266013993641958753015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3601688018658189278337353 2701266013993641958753015)
          ·
            refine ⟨4051899020990462938129523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701266013993641958753015 4051899020990462938129523)
            ·
              refine ⟨6077848531485694407194285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051899020990462938129523 6077848531485694407194285)
              ·
                refine ⟨2279193199307135402697857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6077848531485694407194285 2279193199307135402697857)
                ·
                  refine ⟨1709394899480351552023393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2279193199307135402697857 1709394899480351552023393)
                  ·
                    refine ⟨1282046174610263664017545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1709394899480351552023393 1282046174610263664017545)
                    ·
                      refine ⟨961534630957697748013159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282046174610263664017545 961534630957697748013159)
                      ·
                        rfl

theorem cell23_1872582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_1872582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872582 prefixEnd_1872582 := by exact prefixLift 1872582
  have htrace : WordTrace (prefixWord ++ tailWord_1872582) baseStart_1872582 baseEnd_1872582 := by
    simpa [prefixWord, tailWord_1872582, baseEnd_1872582] using wordTrace_append hprefix tailTrace_1872582
  have hstable : (prefixWord ++ tailWord_1872582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872582).length < 2 ^ (prefixWord ++ tailWord_1872582).sum := by decide
  have hdescent : baseEnd_1872582 < baseStart_1872582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872640 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 11]
def baseStart_1872640 : Nat := 118140960795 + 1872640 * 2 ^ 59
def prefixEnd_1872640 : Nat := 4983230072969 + 3 ^ 40 * 1872640 * 2
def baseEnd_1872640 : Nat := 320521470945219507029297

theorem tailTrace_1872640 : CollatzResearch.WordTrace tailWord_1872640 prefixEnd_1872640 320521470945219507029297 := by
  unfold tailWord_1872640
  simp only [CollatzResearch.WordTrace]
  refine ⟨34150395967876288147411687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45533861290501717529882249 34150395967876288147411687)
  ·
    refine ⟨51225593951814432221117531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34150395967876288147411687 51225593951814432221117531)
    ·
      refine ⟨76838390927721648331676297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51225593951814432221117531 76838390927721648331676297)
      ·
        refine ⟨57628793195791236248757223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76838390927721648331676297 57628793195791236248757223)
        ·
          refine ⟨86443189793686854373135835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57628793195791236248757223 86443189793686854373135835)
          ·
            refine ⟨129664784690530281559703753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86443189793686854373135835 129664784690530281559703753)
            ·
              refine ⟨97248588517897711169777815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129664784690530281559703753 97248588517897711169777815)
              ·
                refine ⟨145872882776846566754666723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97248588517897711169777815 145872882776846566754666723)
                ·
                  refine ⟨218809324165269850132000085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145872882776846566754666723 218809324165269850132000085)
                  ·
                    refine ⟨320521470945219507029297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 218809324165269850132000085 320521470945219507029297)
                    ·
                      rfl

theorem cell23_1872640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_1872640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872640 prefixEnd_1872640 := by exact prefixLift 1872640
  have htrace : WordTrace (prefixWord ++ tailWord_1872640) baseStart_1872640 baseEnd_1872640 := by
    simpa [prefixWord, tailWord_1872640, baseEnd_1872640] using wordTrace_append hprefix tailTrace_1872640
  have hstable : (prefixWord ++ tailWord_1872640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872640).length < 2 ^ (prefixWord ++ tailWord_1872640).sum := by decide
  have hdescent : baseEnd_1872640 < baseStart_1872640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872657 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 3, 5]
def baseStart_1872657 : Nat := 118140960795 + 1872657 * 2 ^ 59
def prefixEnd_1872657 : Nat := 4983230072969 + 3 ^ 40 * 1872657 * 2
def baseEnd_1872657 : Nat := 320524380668928318191771

theorem tailTrace_1872657 : CollatzResearch.WordTrace tailWord_1872657 prefixEnd_1872657 320524380668928318191771 := by
  unfold tailWord_1872657
  simp only [CollatzResearch.WordTrace]
  refine ⟨68301411976690988198192225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45534274651127325465461483 68301411976690988198192225)
  ·
    refine ⟨51226058982518241148644169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68301411976690988198192225 51226058982518241148644169)
    ·
      refine ⟨38419544236888680861483127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51226058982518241148644169 38419544236888680861483127)
      ·
        refine ⟨57629316355333021292224691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38419544236888680861483127 57629316355333021292224691)
        ·
          refine ⟨86443974532999531938337037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57629316355333021292224691 86443974532999531938337037)
          ·
            refine ⟨32416490449874824476876389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86443974532999531938337037 32416490449874824476876389)
            ·
              refine ⟨6078091959351529589414323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32416490449874824476876389 6078091959351529589414323)
              ·
                refine ⟨9117137939027294384121485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6078091959351529589414323 9117137939027294384121485)
                ·
                  refine ⟨3418926727135235394045557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9117137939027294384121485 3418926727135235394045557)
                  ·
                    refine ⟨320524380668928318191771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3418926727135235394045557 320524380668928318191771)
                    ·
                      rfl

theorem cell23_1872657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_1872657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872657 prefixEnd_1872657 := by exact prefixLift 1872657
  have htrace : WordTrace (prefixWord ++ tailWord_1872657) baseStart_1872657 baseEnd_1872657 := by
    simpa [prefixWord, tailWord_1872657, baseEnd_1872657] using wordTrace_append hprefix tailTrace_1872657
  have hstable : (prefixWord ++ tailWord_1872657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872657).length < 2 ^ (prefixWord ++ tailWord_1872657).sum := by decide
  have hdescent : baseEnd_1872657 < baseStart_1872657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872704 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 2, 4]
def baseStart_1872704 : Nat := 118140960795 + 1872704 * 2 ^ 59
def prefixEnd_1872704 : Nat := 4983230072969 + 3 ^ 40 * 1872704 * 2
def baseEnd_1872704 : Nat := 320532425199182090229199

theorem tailTrace_1872704 : CollatzResearch.WordTrace tailWord_1872704 prefixEnd_1872704 320532425199182090229199 := by
  unfold tailWord_1872704
  simp only [CollatzResearch.WordTrace]
  refine ⟨34151563103760357612576583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45535417471680476816768777 34151563103760357612576583)
  ·
    refine ⟨51227344655640536418864875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34151563103760357612576583 51227344655640536418864875)
    ·
      refine ⟨76841016983460804628297313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51227344655640536418864875 76841016983460804628297313)
      ·
        refine ⟨57630762737595603471222985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76841016983460804628297313 57630762737595603471222985)
        ·
          refine ⟨43223072053196702603417239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57630762737595603471222985 43223072053196702603417239)
          ·
            refine ⟨64834608079795053905125859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43223072053196702603417239 64834608079795053905125859)
            ·
              refine ⟨97251912119692580857688789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64834608079795053905125859 97251912119692580857688789)
              ·
                refine ⟨2279341690305294863852081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97251912119692580857688789 2279341690305294863852081)
                ·
                  refine ⟨1709506267728971147889061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2279341690305294863852081 1709506267728971147889061)
                  ·
                    refine ⟨320532425199182090229199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1709506267728971147889061 320532425199182090229199)
                    ·
                      rfl

theorem cell23_1872704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 4].length) (baseStart_1872704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872704 prefixEnd_1872704 := by exact prefixLift 1872704
  have htrace : WordTrace (prefixWord ++ tailWord_1872704) baseStart_1872704 baseEnd_1872704 := by
    simpa [prefixWord, tailWord_1872704, baseEnd_1872704] using wordTrace_append hprefix tailTrace_1872704
  have hstable : (prefixWord ++ tailWord_1872704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872704).length < 2 ^ (prefixWord ++ tailWord_1872704).sum := by decide
  have hdescent : baseEnd_1872704 < baseStart_1872704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872707 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 6]
def baseStart_1872707 : Nat := 118140960795 + 1872707 * 2 ^ 59
def prefixEnd_1872707 : Nat := 4983230072969 + 3 ^ 40 * 1872707 * 2
def baseEnd_1872707 : Nat := 961598816039509758950083

theorem tailTrace_1872707 : CollatzResearch.WordTrace tailWord_1872707 prefixEnd_1872707 961598816039509758950083 := by
  unfold tailWord_1872707
  simp only [CollatzResearch.WordTrace]
  refine ⟨68303235626509846737512375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45535490417673231158341583 68303235626509846737512375)
  ·
    refine ⟨102454853439764770106268563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68303235626509846737512375 102454853439764770106268563)
    ·
      refine ⟨153682280159647155159402845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102454853439764770106268563 153682280159647155159402845)
      ·
        refine ⟨57630855059867683184776067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153682280159647155159402845 57630855059867683184776067)
        ·
          refine ⟨86446282589801524777164101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57630855059867683184776067 86446282589801524777164101)
          ·
            refine ⟨16208677985587785895718269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86446282589801524777164101 16208677985587785895718269)
            ·
              refine ⟨6078254244595419710894351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16208677985587785895718269 6078254244595419710894351)
              ·
                refine ⟨9117381366893129566341527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6078254244595419710894351 9117381366893129566341527)
                ·
                  refine ⟨13676072050339694349512291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9117381366893129566341527 13676072050339694349512291)
                  ·
                    refine ⟨20514108075509541524268437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13676072050339694349512291 20514108075509541524268437)
                    ·
                      refine ⟨961598816039509758950083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20514108075509541524268437 961598816039509758950083)
                      ·
                        rfl

theorem cell23_1872707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_1872707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872707 prefixEnd_1872707 := by exact prefixLift 1872707
  have htrace : WordTrace (prefixWord ++ tailWord_1872707) baseStart_1872707 baseEnd_1872707 := by
    simpa [prefixWord, tailWord_1872707, baseEnd_1872707] using wordTrace_append hprefix tailTrace_1872707
  have hstable : (prefixWord ++ tailWord_1872707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872707).length < 2 ^ (prefixWord ++ tailWord_1872707).sum := by decide
  have hdescent : baseEnd_1872707 < baseStart_1872707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872771 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 3, 3, 2]
def baseStart_1872771 : Nat := 118140960795 + 1872771 * 2 ^ 59
def prefixEnd_1872771 : Nat := 4983230072969 + 3 ^ 40 * 1872771 * 2
def baseEnd_1872771 : Nat := 961631678801397508549789

theorem tailTrace_1872771 : CollatzResearch.WordTrace tailWord_1872771 prefixEnd_1872771 961631678801397508549789 := by
  unfold tailWord_1872771
  simp only [CollatzResearch.WordTrace]
  refine ⟨68305569898277985667842167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45537046598851990445228111 68305569898277985667842167)
  ·
    refine ⟨102458354847416978501763251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68305569898277985667842167 102458354847416978501763251)
    ·
      refine ⟨153687532271125467752644877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102458354847416978501763251 153687532271125467752644877)
      ·
        refine ⟨57632824601672050407241829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153687532271125467752644877 57632824601672050407241829)
        ·
          refine ⟨10806154612813509451357843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57632824601672050407241829 10806154612813509451357843)
          ·
            refine ⟨16209231919220264177036765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10806154612813509451357843 16209231919220264177036765)
            ·
              refine ⟨6078461969707599066388787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16209231919220264177036765 6078461969707599066388787)
              ·
                refine ⟨9117692954561398599583181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6078461969707599066388787 9117692954561398599583181)
                ·
                  refine ⟨3419134857960524474843693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9117692954561398599583181 3419134857960524474843693)
                  ·
                    refine ⟨1282175571735196678066385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419134857960524474843693 1282175571735196678066385)
                    ·
                      refine ⟨961631678801397508549789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282175571735196678066385 961631678801397508549789)
                      ·
                        rfl

theorem cell23_1872771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_1872771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872771 prefixEnd_1872771 := by exact prefixLift 1872771
  have htrace : WordTrace (prefixWord ++ tailWord_1872771) baseStart_1872771 baseEnd_1872771 := by
    simpa [prefixWord, tailWord_1872771, baseEnd_1872771] using wordTrace_append hprefix tailTrace_1872771
  have hstable : (prefixWord ++ tailWord_1872771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872771).length < 2 ^ (prefixWord ++ tailWord_1872771).sum := by decide
  have hdescent : baseEnd_1872771 < baseStart_1872771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872784 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 2, 8, 2]
def baseStart_1872784 : Nat := 118140960795 + 1872784 * 2 ^ 59
def prefixEnd_1872784 : Nat := 4983230072969 + 3 ^ 40 * 1872784 * 2
def baseEnd_1872784 : Nat := 961638354049905957687229

theorem tailTrace_1872784 : CollatzResearch.WordTrace tailWord_1872784 prefixEnd_1872784 961638354049905957687229 := by
  unfold tailWord_1872784
  simp only [CollatzResearch.WordTrace]
  refine ⟨34153022023615444444032703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45537362698153925925376937 34153022023615444444032703)
  ·
    refine ⟨51229533035423166666049055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34153022023615444444032703 51229533035423166666049055)
    ·
      refine ⟨76844299553134749999073583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51229533035423166666049055 76844299553134749999073583)
      ·
        refine ⟨115266449329702124998610375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76844299553134749999073583 115266449329702124998610375)
        ·
          refine ⟨172899673994553187497915563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115266449329702124998610375 172899673994553187497915563)
          ·
            refine ⟨259349510991829781246873345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172899673994553187497915563 259349510991829781246873345)
            ·
              refine ⟨194512133243872335935155009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259349510991829781246873345 194512133243872335935155009)
              ·
                refine ⟨145884099932904251951366257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194512133243872335935155009 145884099932904251951366257)
                ·
                  refine ⟨109413074949678188963524693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145884099932904251951366257 109413074949678188963524693)
                  ·
                    refine ⟨1282184472066541276916305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109413074949678188963524693 1282184472066541276916305)
                    ·
                      refine ⟨961638354049905957687229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282184472066541276916305 961638354049905957687229)
                      ·
                        rfl

theorem cell23_1872784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 8, 2].length) (baseStart_1872784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872784 prefixEnd_1872784 := by exact prefixLift 1872784
  have htrace : WordTrace (prefixWord ++ tailWord_1872784) baseStart_1872784 baseEnd_1872784 := by
    simpa [prefixWord, tailWord_1872784, baseEnd_1872784] using wordTrace_append hprefix tailTrace_1872784
  have hstable : (prefixWord ++ tailWord_1872784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872784).length < 2 ^ (prefixWord ++ tailWord_1872784).sum := by decide
  have hdescent : baseEnd_1872784 < baseStart_1872784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872787 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 5]
def baseStart_1872787 : Nat := 118140960795 + 1872787 * 2 ^ 59
def prefixEnd_1872787 : Nat := 4983230072969 + 3 ^ 40 * 1872787 * 2
def baseEnd_1872787 : Nat := 961639894491869445949715

theorem tailTrace_1872787 : CollatzResearch.WordTrace tailWord_1872787 prefixEnd_1872787 961639894491869445949715 := by
  unfold tailWord_1872787
  simp only [CollatzResearch.WordTrace]
  refine ⟨68306153466220020400424615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45537435644146680266949743 68306153466220020400424615)
  ·
    refine ⟨102459230199330030600636923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68306153466220020400424615 102459230199330030600636923)
    ·
      refine ⟨153688845298995045900955385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102459230199330030600636923 153688845298995045900955385)
      ·
        refine ⟨115266633974246284425716539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153688845298995045900955385 115266633974246284425716539)
        ·
          refine ⟨172899950961369426638574809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115266633974246284425716539 172899950961369426638574809)
          ·
            refine ⟨129674963221027069978931107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172899950961369426638574809 129674963221027069978931107)
            ·
              refine ⟨194512444831540604968396661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129674963221027069978931107 194512444831540604968396661)
              ·
                refine ⟨18235541702956931715787187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194512444831540604968396661 18235541702956931715787187)
                ·
                  refine ⟨27353312554435397573680781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18235541702956931715787187 27353312554435397573680781)
                  ·
                    refine ⟨10257492207913274090130293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27353312554435397573680781 10257492207913274090130293)
                    ·
                      refine ⟨961639894491869445949715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10257492207913274090130293 961639894491869445949715)
                      ·
                        rfl

theorem cell23_1872787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_1872787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872787 prefixEnd_1872787 := by exact prefixLift 1872787
  have htrace : WordTrace (prefixWord ++ tailWord_1872787) baseStart_1872787 baseEnd_1872787 := by
    simpa [prefixWord, tailWord_1872787, baseEnd_1872787] using wordTrace_append hprefix tailTrace_1872787
  have hstable : (prefixWord ++ tailWord_1872787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872787).length < 2 ^ (prefixWord ++ tailWord_1872787).sum := by decide
  have hdescent : baseEnd_1872787 < baseStart_1872787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872796 : List Nat := [2, 2, 3, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1872796 : Nat := 118140960795 + 1872796 * 2 ^ 59
def prefixEnd_1872796 : Nat := 4983230072969 + 3 ^ 40 * 1872796 * 2
def baseEnd_1872796 : Nat := 961644515817759910737175

theorem tailTrace_1872796 : CollatzResearch.WordTrace tailWord_1872796 prefixEnd_1872796 961644515817759910737175 := by
  unfold tailWord_1872796
  simp only [CollatzResearch.WordTrace]
  refine ⟨34153240861593707468751121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45537654482124943291668161 34153240861593707468751121)
  ·
    refine ⟨25614930646195280601563341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34153240861593707468751121 25614930646195280601563341)
    ·
      refine ⟨9605598992323230225586253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25614930646195280601563341 9605598992323230225586253)
      ·
        refine ⟨3602099622121211334594845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9605598992323230225586253 3602099622121211334594845)
        ·
          refine ⟨1350787358295454250473067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3602099622121211334594845 1350787358295454250473067)
          ·
            refine ⟨2026181037443181375709601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350787358295454250473067 2026181037443181375709601)
            ·
              refine ⟨1519635778082386031782201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026181037443181375709601 1519635778082386031782201)
              ·
                refine ⟨1139726833561789523836651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519635778082386031782201 1139726833561789523836651)
                ·
                  refine ⟨1709590250342684285754977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139726833561789523836651 1709590250342684285754977)
                  ·
                    refine ⟨1282192687757013214316233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1709590250342684285754977 1282192687757013214316233)
                    ·
                      refine ⟨961644515817759910737175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282192687757013214316233 961644515817759910737175)
                      ·
                        rfl

theorem cell23_1872796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1872796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872796 prefixEnd_1872796 := by exact prefixLift 1872796
  have htrace : WordTrace (prefixWord ++ tailWord_1872796) baseStart_1872796 baseEnd_1872796 := by
    simpa [prefixWord, tailWord_1872796, baseEnd_1872796] using wordTrace_append hprefix tailTrace_1872796
  have hstable : (prefixWord ++ tailWord_1872796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872796).length < 2 ^ (prefixWord ++ tailWord_1872796).sum := by decide
  have hdescent : baseEnd_1872796 < baseStart_1872796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872804 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_1872804 : Nat := 118140960795 + 1872804 * 2 ^ 59
def prefixEnd_1872804 : Nat := 4983230072969 + 3 ^ 40 * 1872804 * 2
def baseEnd_1872804 : Nat := 961648623662995879437137

theorem tailTrace_1872804 : CollatzResearch.WordTrace tailWord_1872804 prefixEnd_1872804 961648623662995879437137 := by
  unfold tailWord_1872804
  simp only [CollatzResearch.WordTrace]
  refine ⟨34153386753579216151896733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45537849004772288202528977 34153386753579216151896733)
  ·
    refine ⟨12807520032592206056961275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34153386753579216151896733 12807520032592206056961275)
    ·
      refine ⟨19211280048888309085441913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12807520032592206056961275 19211280048888309085441913)
      ·
        refine ⟨14408460036666231814081435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19211280048888309085441913 14408460036666231814081435)
        ·
          refine ⟨21612690054999347721122153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14408460036666231814081435 21612690054999347721122153)
          ·
            refine ⟨16209517541249510790841615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21612690054999347721122153 16209517541249510790841615)
            ·
              refine ⟨24314276311874266186262423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16209517541249510790841615 24314276311874266186262423)
              ·
                refine ⟨36471414467811399279393635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24314276311874266186262423 36471414467811399279393635)
                ·
                  refine ⟨54707121701717098919090453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36471414467811399279393635 54707121701717098919090453)
                  ·
                    refine ⟨2564396329767989011832365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54707121701717098919090453 2564396329767989011832365)
                    ·
                      refine ⟨961648623662995879437137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2564396329767989011832365 961648623662995879437137)
                      ·
                        rfl

theorem cell23_1872804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_1872804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872804 prefixEnd_1872804 := by exact prefixLift 1872804
  have htrace : WordTrace (prefixWord ++ tailWord_1872804) baseStart_1872804 baseEnd_1872804 := by
    simpa [prefixWord, tailWord_1872804, baseEnd_1872804] using wordTrace_append hprefix tailTrace_1872804
  have hstable : (prefixWord ++ tailWord_1872804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872804).length < 2 ^ (prefixWord ++ tailWord_1872804).sum := by decide
  have hdescent : baseEnd_1872804 < baseStart_1872804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872824 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 7]
def baseStart_1872824 : Nat := 118140960795 + 1872824 * 2 ^ 59
def prefixEnd_1872824 : Nat := 4983230072969 + 3 ^ 40 * 1872824 * 2
def baseEnd_1872824 : Nat := 106850988141787311243005

theorem tailTrace_1872824 : CollatzResearch.WordTrace tailWord_1872824 prefixEnd_1872824 106850988141787311243005 := by
  unfold tailWord_1872824
  simp only [CollatzResearch.WordTrace]
  refine ⟨34153751483542987859760763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45538335311390650479681017 34153751483542987859760763)
  ·
    refine ⟨51230627225314481789641145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34153751483542987859760763 51230627225314481789641145)
    ·
      refine ⟨38422970418985861342230859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51230627225314481789641145 38422970418985861342230859)
      ·
        refine ⟨57634455628478792013346289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38422970418985861342230859 57634455628478792013346289)
        ·
          refine ⟨43225841721359094010009717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57634455628478792013346289 43225841721359094010009717)
          ·
            refine ⟨4052422661377415063438411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43225841721359094010009717 4052422661377415063438411)
            ·
              refine ⟨6078633992066122595157617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4052422661377415063438411 6078633992066122595157617)
              ·
                refine ⟨4558975494049591946368213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6078633992066122595157617 4558975494049591946368213)
                ·
                  refine ⟨106850988141787311243005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4558975494049591946368213 106850988141787311243005)
                  ·
                    rfl

theorem cell23_1872824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 7].length) (baseStart_1872824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872824 prefixEnd_1872824 := by exact prefixLift 1872824
  have htrace : WordTrace (prefixWord ++ tailWord_1872824) baseStart_1872824 baseEnd_1872824 := by
    simpa [prefixWord, tailWord_1872824, baseEnd_1872824] using wordTrace_append hprefix tailTrace_1872824
  have hstable : (prefixWord ++ tailWord_1872824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872824).length < 2 ^ (prefixWord ++ tailWord_1872824).sum := by decide
  have hdescent : baseEnd_1872824 < baseStart_1872824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872827 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 6]
def baseStart_1872827 : Nat := 118140960795 + 1872827 * 2 ^ 59
def prefixEnd_1872827 : Nat := 4983230072969 + 3 ^ 40 * 1872827 * 2
def baseEnd_1872827 : Nat := 961660433718049289449531

theorem tailTrace_1872827 : CollatzResearch.WordTrace tailWord_1872827 prefixEnd_1872827 961660433718049289449531 := by
  unfold tailWord_1872827
  simp only [CollatzResearch.WordTrace]
  refine ⟨68307612386075107231880735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45538408257383404821253823 68307612386075107231880735)
  ·
    refine ⟨102461418579112660847821103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68307612386075107231880735 102461418579112660847821103)
    ·
      refine ⟨153692127868668991271731655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102461418579112660847821103 153692127868668991271731655)
      ·
        refine ⟨230538191803003486907597483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153692127868668991271731655 230538191803003486907597483)
        ·
          refine ⟨345807287704505230361396225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230538191803003486907597483 345807287704505230361396225)
          ·
            refine ⟨259355465778378922771047169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345807287704505230361396225 259355465778378922771047169)
            ·
              refine ⟨194516599333784192078285377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259355465778378922771047169 194516599333784192078285377)
              ·
                refine ⟨145887449500338144058714033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194516599333784192078285377 145887449500338144058714033)
                ·
                  refine ⟨109415587125253608044035525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145887449500338144058714033 109415587125253608044035525)
                  ·
                    refine ⟨20515422585985051508256661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109415587125253608044035525 20515422585985051508256661)
                    ·
                      refine ⟨961660433718049289449531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20515422585985051508256661 961660433718049289449531)
                      ·
                        rfl

theorem cell23_1872827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_1872827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872827 prefixEnd_1872827 := by exact prefixLift 1872827
  have htrace : WordTrace (prefixWord ++ tailWord_1872827) baseStart_1872827 baseEnd_1872827 := by
    simpa [prefixWord, tailWord_1872827, baseEnd_1872827] using wordTrace_append hprefix tailTrace_1872827
  have hstable : (prefixWord ++ tailWord_1872827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872827).length < 2 ^ (prefixWord ++ tailWord_1872827).sum := by decide
  have hdescent : baseEnd_1872827 < baseStart_1872827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872852 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_1872852 : Nat := 118140960795 + 1872852 * 2 ^ 59
def prefixEnd_1872852 : Nat := 4983230072969 + 3 ^ 40 * 1872852 * 2
def baseEnd_1872852 : Nat := 961673270734411691636917

theorem tailTrace_1872852 : CollatzResearch.WordTrace tailWord_1872852 prefixEnd_1872852 961673270734411691636917 := by
  unfold tailWord_1872852
  simp only [CollatzResearch.WordTrace]
  refine ⟨34154262105492268250770405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45539016140656357667693873 34154262105492268250770405)
  ·
    refine ⟨6403924144779800297019451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34154262105492268250770405 6403924144779800297019451)
    ·
      refine ⟨9605886217169700445529177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6403924144779800297019451 9605886217169700445529177)
      ·
        refine ⟨7204414662877275334146883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9605886217169700445529177 7204414662877275334146883)
        ·
          refine ⟨10806621994315913001220325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7204414662877275334146883 10806621994315913001220325)
          ·
            refine ⟨2026241623934233687728811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10806621994315913001220325 2026241623934233687728811)
            ·
              refine ⟨3039362435901350531593217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026241623934233687728811 3039362435901350531593217)
              ·
                refine ⟨2279521826926012898694913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3039362435901350531593217 2279521826926012898694913)
                ·
                  refine ⟨1709641370194509674021185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2279521826926012898694913 1709641370194509674021185)
                  ·
                    refine ⟨1282231027645882255515889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1709641370194509674021185 1282231027645882255515889)
                    ·
                      refine ⟨961673270734411691636917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282231027645882255515889 961673270734411691636917)
                      ·
                        rfl

theorem cell23_1872852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_1872852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872852 prefixEnd_1872852 := by exact prefixLift 1872852
  have htrace : WordTrace (prefixWord ++ tailWord_1872852) baseStart_1872852 baseEnd_1872852 := by
    simpa [prefixWord, tailWord_1872852, baseEnd_1872852] using wordTrace_append hprefix tailTrace_1872852
  have hstable : (prefixWord ++ tailWord_1872852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872852).length < 2 ^ (prefixWord ++ tailWord_1872852).sum := by decide
  have hdescent : baseEnd_1872852 < baseStart_1872852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872869 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1872869 : Nat := 118140960795 + 1872869 * 2 ^ 59
def prefixEnd_1872869 : Nat := 4983230072969 + 3 ^ 40 * 1872869 * 2
def baseEnd_1872869 : Nat := 961681999905538125124339

theorem tailTrace_1872869 : CollatzResearch.WordTrace tailWord_1872869 prefixEnd_1872869 961681999905538125124339 := by
  unfold tailWord_1872869
  simp only [CollatzResearch.WordTrace]
  refine ⟨68309144251922948404909661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45539429501281965603273107 68309144251922948404909661)
  ·
    refine ⟨25615929094471105651841123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68309144251922948404909661 25615929094471105651841123)
    ·
      refine ⟨38423893641706658477761685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25615929094471105651841123 38423893641706658477761685)
      ·
        refine ⟨1801120014454999616145079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38423893641706658477761685 1801120014454999616145079)
        ·
          refine ⟨2701680021682499424217619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801120014454999616145079 2701680021682499424217619)
          ·
            refine ⟨4052520032523749136326429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701680021682499424217619 4052520032523749136326429)
            ·
              refine ⟨1519695012196405926122411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4052520032523749136326429 1519695012196405926122411)
              ·
                refine ⟨2279542518294608889183617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519695012196405926122411 2279542518294608889183617)
                ·
                  refine ⟨1709656888720956666887713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2279542518294608889183617 1709656888720956666887713)
                  ·
                    refine ⟨1282242666540717500165785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1709656888720956666887713 1282242666540717500165785)
                    ·
                      refine ⟨961681999905538125124339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282242666540717500165785 961681999905538125124339)
                      ·
                        rfl

theorem cell23_1872869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1872869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872869 prefixEnd_1872869 := by exact prefixLift 1872869
  have htrace : WordTrace (prefixWord ++ tailWord_1872869) baseStart_1872869 baseEnd_1872869 := by
    simpa [prefixWord, tailWord_1872869, baseEnd_1872869] using wordTrace_append hprefix tailTrace_1872869
  have hstable : (prefixWord ++ tailWord_1872869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872869).length < 2 ^ (prefixWord ++ tailWord_1872869).sum := by decide
  have hdescent : baseEnd_1872869 < baseStart_1872869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872931 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 6]
def baseStart_1872931 : Nat := 118140960795 + 1872931 * 2 ^ 59
def prefixEnd_1872931 : Nat := 4983230072969 + 3 ^ 40 * 1872931 * 2
def baseEnd_1872931 : Nat := 106857092856235209172117

theorem tailTrace_1872931 : CollatzResearch.WordTrace tailWord_1872931 prefixEnd_1872931 106857092856235209172117 := by
  unfold tailWord_1872931
  simp only [CollatzResearch.WordTrace]
  refine ⟨68311405577698332993666647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45540937051798888662444431 68311405577698332993666647)
  ·
    refine ⟨102467108366547499490499971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68311405577698332993666647 102467108366547499490499971)
    ·
      refine ⟨153700662549821249235749957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102467108366547499490499971 153700662549821249235749957)
      ·
        refine ⟨28818874228091484231703117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153700662549821249235749957 28818874228091484231703117)
        ·
          refine ⟨10807077835534306586888669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28818874228091484231703117 10807077835534306586888669)
          ·
            refine ⟨4052654188325364970083251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10807077835534306586888669 4052654188325364970083251)
            ·
              refine ⟨6078981282488047455124877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4052654188325364970083251 6078981282488047455124877)
              ·
                refine ⟨2279617980933017795671829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6078981282488047455124877 2279617980933017795671829)
                ·
                  refine ⟨106857092856235209172117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2279617980933017795671829 106857092856235209172117)
                  ·
                    rfl

theorem cell23_1872931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 6].length) (baseStart_1872931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872931 prefixEnd_1872931 := by exact prefixLift 1872931
  have htrace : WordTrace (prefixWord ++ tailWord_1872931) baseStart_1872931 baseEnd_1872931 := by
    simpa [prefixWord, tailWord_1872931, baseEnd_1872931] using wordTrace_append hprefix tailTrace_1872931
  have hstable : (prefixWord ++ tailWord_1872931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872931).length < 2 ^ (prefixWord ++ tailWord_1872931).sum := by decide
  have hdescent : baseEnd_1872931 < baseStart_1872931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872968 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_1872968 : Nat := 118140960795 + 1872968 * 2 ^ 59
def prefixEnd_1872968 : Nat := 4983230072969 + 3 ^ 40 * 1872968 * 2
def baseEnd_1872968 : Nat := 961732834490333237786383

theorem tailTrace_1872968 : CollatzResearch.WordTrace tailWord_1872968 prefixEnd_1872968 961732834490333237786383 := by
  unfold tailWord_1872968
  simp only [CollatzResearch.WordTrace]
  refine ⟨34156377539282144156381779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45541836719042858875175705 34156377539282144156381779)
  ·
    refine ⟨51234566308923216234572669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34156377539282144156381779 51234566308923216234572669)
    ·
      refine ⟨19212962365846206087964751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51234566308923216234572669 19212962365846206087964751)
      ·
        refine ⟨28819443548769309131947127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19212962365846206087964751 28819443548769309131947127)
        ·
          refine ⟨43229165323153963697920691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28819443548769309131947127 43229165323153963697920691)
          ·
            refine ⟨64843747984730945546881037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43229165323153963697920691 64843747984730945546881037)
            ·
              refine ⟨24316405494274104580080389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64843747984730945546881037 24316405494274104580080389)
              ·
                refine ⟨4559326030176394608765073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24316405494274104580080389 4559326030176394608765073)
                ·
                  refine ⟨3419494522632295956573805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4559326030176394608765073 3419494522632295956573805)
                  ·
                    refine ⟨1282310445987110983715177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419494522632295956573805 1282310445987110983715177)
                    ·
                      refine ⟨961732834490333237786383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282310445987110983715177 961732834490333237786383)
                      ·
                        rfl

theorem cell23_1872968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_1872968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872968 prefixEnd_1872968 := by exact prefixLift 1872968
  have htrace : WordTrace (prefixWord ++ tailWord_1872968) baseStart_1872968 baseEnd_1872968 := by
    simpa [prefixWord, tailWord_1872968, baseEnd_1872968] using wordTrace_append hprefix tailTrace_1872968
  have hstable : (prefixWord ++ tailWord_1872968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872968).length < 2 ^ (prefixWord ++ tailWord_1872968).sum := by decide
  have hdescent : baseEnd_1872968 < baseStart_1872968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872981 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1872981 : Nat := 118140960795 + 1872981 * 2 ^ 59
def prefixEnd_1872981 : Nat := 4983230072969 + 3 ^ 40 * 1872981 * 2
def baseEnd_1872981 : Nat := 961739509738841686923823

theorem tailTrace_1872981 : CollatzResearch.WordTrace tailWord_1872981 prefixEnd_1872981 961739509738841686923823 := by
  unfold tailWord_1872981
  simp only [CollatzResearch.WordTrace]
  refine ⟨68313229227517191532986797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45542152818344794355324531 68313229227517191532986797)
  ·
    refine ⟨25617460960318946824870049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68313229227517191532986797 25617460960318946824870049)
    ·
      refine ⟨19213095720239210118652537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25617460960318946824870049 19213095720239210118652537)
      ·
        refine ⟨14409821790179407588989403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19213095720239210118652537 14409821790179407588989403)
        ·
          refine ⟨21614732685269111383484105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14409821790179407588989403 21614732685269111383484105)
          ·
            refine ⟨16211049513951833537613079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21614732685269111383484105 16211049513951833537613079)
            ·
              refine ⟨24316574270927750306419619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16211049513951833537613079 24316574270927750306419619)
              ·
                refine ⟨36474861406391625459629429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24316574270927750306419619 36474861406391625459629429)
                ·
                  refine ⟨3419518256849214886840259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36474861406391625459629429 3419518256849214886840259)
                  ·
                    refine ⟨5129277385273822330260389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3419518256849214886840259 5129277385273822330260389)
                    ·
                      refine ⟨961739509738841686923823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5129277385273822330260389 961739509738841686923823)
                      ·
                        rfl

theorem cell23_1872981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1872981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872981 prefixEnd_1872981 := by exact prefixLift 1872981
  have htrace : WordTrace (prefixWord ++ tailWord_1872981) baseStart_1872981 baseEnd_1872981 := by
    simpa [prefixWord, tailWord_1872981, baseEnd_1872981] using wordTrace_append hprefix tailTrace_1872981
  have hstable : (prefixWord ++ tailWord_1872981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872981).length < 2 ^ (prefixWord ++ tailWord_1872981).sum := by decide
  have hdescent : baseEnd_1872981 < baseStart_1872981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872991 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 1, 6]
def baseStart_1872991 : Nat := 118140960795 + 1872991 * 2 ^ 59
def prefixEnd_1872991 : Nat := 4983230072969 + 3 ^ 40 * 1872991 * 2
def baseEnd_1872991 : Nat := 320581548181795549266259

theorem tailTrace_1872991 : CollatzResearch.WordTrace tailWord_1872991 prefixEnd_1872991 320581548181795549266259 := by
  unfold tailWord_1872991
  simp only [CollatzResearch.WordTrace]
  refine ⟨68313593957480963240850827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45542395971653975493900551 68313593957480963240850827)
  ·
    refine ⟨102470390936221444861276241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68313593957480963240850827 102470390936221444861276241)
    ·
      refine ⟨76852793202166083645957181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102470390936221444861276241 76852793202166083645957181)
      ·
        refine ⟨28819797450812281367233943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76852793202166083645957181 28819797450812281367233943)
        ·
          refine ⟨43229696176218422050850915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28819797450812281367233943 43229696176218422050850915)
          ·
            refine ⟨64844544264327633076276373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43229696176218422050850915 64844544264327633076276373)
            ·
              refine ⟨3039588012390357800450455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64844544264327633076276373 3039588012390357800450455)
              ·
                refine ⟨4559382018585536700675683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039588012390357800450455 4559382018585536700675683)
                ·
                  refine ⟨6839073027878305051013525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559382018585536700675683 6839073027878305051013525)
                  ·
                    refine ⟨320581548181795549266259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6839073027878305051013525 320581548181795549266259)
                    ·
                      rfl

theorem cell23_1872991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_1872991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1872991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1872991 prefixEnd_1872991 := by exact prefixLift 1872991
  have htrace : WordTrace (prefixWord ++ tailWord_1872991) baseStart_1872991 baseEnd_1872991 := by
    simpa [prefixWord, tailWord_1872991, baseEnd_1872991] using wordTrace_append hprefix tailTrace_1872991
  have hstable : (prefixWord ++ tailWord_1872991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872991).length < 2 ^ (prefixWord ++ tailWord_1872991).sum := by decide
  have hdescent : baseEnd_1872991 < baseStart_1872991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873002 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_1873002 : Nat := 118140960795 + 1873002 * 2 ^ 59
def prefixEnd_1873002 : Nat := 4983230072969 + 3 ^ 40 * 1873002 * 2
def baseEnd_1873002 : Nat := 961750292832586104761227

theorem tailTrace_1873002 : CollatzResearch.WordTrace tailWord_1873002 prefixEnd_1873002 961750292832586104761227 := by
  unfold tailWord_1873002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17078498790110278029875315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45542663440294074746334173 17078498790110278029875315)
  ·
    refine ⟨25617748185165417044812973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17078498790110278029875315 25617748185165417044812973)
    ·
      refine ⟨9606655569437031391804865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25617748185165417044812973 9606655569437031391804865)
      ·
        refine ⟨7204991677077773543853649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9606655569437031391804865 7204991677077773543853649)
        ·
          refine ⟨5403743757808330157890237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7204991677077773543853649 5403743757808330157890237)
          ·
            refine ⟨2026403909178123809208839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5403743757808330157890237 2026403909178123809208839)
            ·
              refine ⟨3039605863767185713813259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026403909178123809208839 3039605863767185713813259)
              ·
                refine ⟨4559408795650778570719889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039605863767185713813259 4559408795650778570719889)
                ·
                  refine ⟨3419556596738083928039917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4559408795650778570719889 3419556596738083928039917)
                  ·
                    refine ⟨1282333723776781473014969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419556596738083928039917 1282333723776781473014969)
                    ·
                      refine ⟨961750292832586104761227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282333723776781473014969 961750292832586104761227)
                      ·
                        rfl

theorem cell23_1873002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_1873002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873002 prefixEnd_1873002 := by exact prefixLift 1873002
  have htrace : WordTrace (prefixWord ++ tailWord_1873002) baseStart_1873002 baseEnd_1873002 := by
    simpa [prefixWord, tailWord_1873002, baseEnd_1873002] using wordTrace_append hprefix tailTrace_1873002
  have hstable : (prefixWord ++ tailWord_1873002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873002).length < 2 ^ (prefixWord ++ tailWord_1873002).sum := by decide
  have hdescent : baseEnd_1873002 < baseStart_1873002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873025 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 2, 4]
def baseStart_1873025 : Nat := 118140960795 + 1873025 * 2 ^ 59
def prefixEnd_1873025 : Nat := 4983230072969 + 3 ^ 40 * 1873025 * 2
def baseEnd_1873025 : Nat := 320587367629213171591207

theorem tailTrace_1873025 : CollatzResearch.WordTrace tailWord_1873025 prefixEnd_1873025 320587367629213171591207 := by
  unfold tailWord_1873025
  simp only [CollatzResearch.WordTrace]
  refine ⟨68314834039357787047588529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45543222692905191365059019 68314834039357787047588529)
  ·
    refine ⟨51236125529518340285691397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68314834039357787047588529 51236125529518340285691397)
    ·
      refine ⟨9606773536784688803567137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51236125529518340285691397 9606773536784688803567137)
      ·
        refine ⟨7205080152588516602675353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9606773536784688803567137 7205080152588516602675353)
        ·
          refine ⟨5403810114441387452006515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7205080152588516602675353 5403810114441387452006515)
          ·
            refine ⟨8105715171662081178009773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403810114441387452006515 8105715171662081178009773)
            ·
              refine ⟨3039643189373280441753665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8105715171662081178009773 3039643189373280441753665)
              ·
                refine ⟨2279732392029960331315249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3039643189373280441753665 2279732392029960331315249)
                ·
                  refine ⟨1709799294022470248486437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2279732392029960331315249 1709799294022470248486437)
                  ·
                    refine ⟨320587367629213171591207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1709799294022470248486437 320587367629213171591207)
                    ·
                      rfl

theorem cell23_1873025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_1873025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873025 prefixEnd_1873025 := by exact prefixLift 1873025
  have htrace : WordTrace (prefixWord ++ tailWord_1873025) baseStart_1873025 baseEnd_1873025 := by
    simpa [prefixWord, tailWord_1873025, baseEnd_1873025] using wordTrace_append hprefix tailTrace_1873025
  have hstable : (prefixWord ++ tailWord_1873025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873025).length < 2 ^ (prefixWord ++ tailWord_1873025).sum := by decide
  have hdescent : baseEnd_1873025 < baseStart_1873025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873042 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1873042 : Nat := 118140960795 + 1873042 * 2 ^ 59
def prefixEnd_1873042 : Nat := 4983230072969 + 3 ^ 40 * 1873042 * 2
def baseEnd_1873042 : Nat := 320590277352921982753681

theorem tailTrace_1873042 : CollatzResearch.WordTrace tailWord_1873042 prefixEnd_1873042 320590277352921982753681 := by
  unfold tailWord_1873042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17078863520074049737739345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45543636053530799300638253 17078863520074049737739345)
  ·
    refine ⟨12809147640055537303304509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17078863520074049737739345 12809147640055537303304509)
    ·
      refine ⟨4803430365020826488739191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12809147640055537303304509 4803430365020826488739191)
      ·
        refine ⟨7205145547531239733108787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803430365020826488739191 7205145547531239733108787)
        ·
          refine ⟨10807718321296859599663181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205145547531239733108787 10807718321296859599663181)
          ·
            refine ⟨4052894370486322349873693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10807718321296859599663181 4052894370486322349873693)
            ·
              refine ⟨1519835388932370881202635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4052894370486322349873693 1519835388932370881202635)
              ·
                refine ⟨2279753083398556321803953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519835388932370881202635 2279753083398556321803953)
                ·
                  refine ⟨1709814812548917241352965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2279753083398556321803953 1709814812548917241352965)
                  ·
                    refine ⟨320590277352921982753681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1709814812548917241352965 320590277352921982753681)
                    ·
                      rfl

theorem cell23_1873042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1873042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873042 prefixEnd_1873042 := by exact prefixLift 1873042
  have htrace : WordTrace (prefixWord ++ tailWord_1873042) baseStart_1873042 baseEnd_1873042 := by
    simpa [prefixWord, tailWord_1873042, baseEnd_1873042] using wordTrace_append hprefix tailTrace_1873042
  have hstable : (prefixWord ++ tailWord_1873042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873042).length < 2 ^ (prefixWord ++ tailWord_1873042).sum := by decide
  have hdescent : baseEnd_1873042 < baseStart_1873042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873055 : List Nat := [1, 1, 2, 6, 2, 2, 2, 7]
def baseStart_1873055 : Nat := 118140960795 + 1873055 * 2 ^ 59
def prefixEnd_1873055 : Nat := 4983230072969 + 3 ^ 40 * 1873055 * 2
def baseEnd_1873055 : Nat := 35621389159528681385129

theorem tailTrace_1873055 : CollatzResearch.WordTrace tailWord_1873055 prefixEnd_1873055 35621389159528681385129 := by
  unfold tailWord_1873055
  simp only [CollatzResearch.WordTrace]
  refine ⟨68315928229249102171180619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45543952152832734780787079 68315928229249102171180619)
  ·
    refine ⟨102473892343873653256770929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68315928229249102171180619 102473892343873653256770929)
    ·
      refine ⟨76855419257905239942578197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102473892343873653256770929 76855419257905239942578197)
      ·
        refine ⟨3602597777714308122308353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76855419257905239942578197 3602597777714308122308353)
        ·
          refine ⟨2701948333285731091731265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3602597777714308122308353 2701948333285731091731265)
          ·
            refine ⟨2026461249964298318798449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701948333285731091731265 2026461249964298318798449)
            ·
              refine ⟨1519845937473223739098837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026461249964298318798449 1519845937473223739098837)
              ·
                refine ⟨35621389159528681385129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1519845937473223739098837 35621389159528681385129)
                ·
                  rfl

theorem cell23_1873055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 7].length) (baseStart_1873055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873055 prefixEnd_1873055 := by exact prefixLift 1873055
  have htrace : WordTrace (prefixWord ++ tailWord_1873055) baseStart_1873055 baseEnd_1873055 := by
    simpa [prefixWord, tailWord_1873055, baseEnd_1873055] using wordTrace_append hprefix tailTrace_1873055
  have hstable : (prefixWord ++ tailWord_1873055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873055).length < 2 ^ (prefixWord ++ tailWord_1873055).sum := by decide
  have hdescent : baseEnd_1873055 < baseStart_1873055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873061 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_1873061 : Nat := 118140960795 + 1873061 * 2 ^ 59
def prefixEnd_1873061 : Nat := 4983230072969 + 3 ^ 40 * 1873061 * 2
def baseEnd_1873061 : Nat := 961780588191201373923455

theorem tailTrace_1873061 : CollatzResearch.WordTrace tailWord_1873061 prefixEnd_1873061 961780588191201373923455 := by
  unfold tailWord_1873061
  simp only [CollatzResearch.WordTrace]
  refine ⟨68316147067227365195899037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45544098044818243463932691 68316147067227365195899037)
  ·
    refine ⟨25618555150210261948462139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68316147067227365195899037 25618555150210261948462139)
    ·
      refine ⟨38427832725315392922693209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25618555150210261948462139 38427832725315392922693209)
      ·
        refine ⟨28820874543986544692019907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38427832725315392922693209 28820874543986544692019907)
        ·
          refine ⟨43231311815979817038029861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28820874543986544692019907 43231311815979817038029861)
          ·
            refine ⟨8105870965496215694630599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43231311815979817038029861 8105870965496215694630599)
            ·
              refine ⟨12158806448244323541945899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105870965496215694630599 12158806448244323541945899)
              ·
                refine ⟨18238209672366485312918849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158806448244323541945899 18238209672366485312918849)
                ·
                  refine ⟨13678657254274863984689137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18238209672366485312918849 13678657254274863984689137)
                  ·
                    refine ⟨10258992940706147988516853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13678657254274863984689137 10258992940706147988516853)
                    ·
                      refine ⟨961780588191201373923455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10258992940706147988516853 961780588191201373923455)
                      ·
                        rfl

theorem cell23_1873061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_1873061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873061 prefixEnd_1873061 := by exact prefixLift 1873061
  have htrace : WordTrace (prefixWord ++ tailWord_1873061) baseStart_1873061 baseEnd_1873061 := by
    simpa [prefixWord, tailWord_1873061, baseEnd_1873061] using wordTrace_append hprefix tailTrace_1873061
  have hstable : (prefixWord ++ tailWord_1873061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873061).length < 2 ^ (prefixWord ++ tailWord_1873061).sum := by decide
  have hdescent : baseEnd_1873061 < baseStart_1873061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873066 : List Nat := [3, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1873066 : Nat := 118140960795 + 1873066 * 2 ^ 59
def prefixEnd_1873066 : Nat := 4983230072969 + 3 ^ 40 * 1873066 * 2
def baseEnd_1873066 : Nat := 961783155594473854360933

theorem tailTrace_1873066 : CollatzResearch.WordTrace tailWord_1873066 prefixEnd_1873066 961783155594473854360933 := by
  unfold tailWord_1873066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17079082358052312762457763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45544219621472834033220701 17079082358052312762457763)
  ·
    refine ⟨25618623537078469143686645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17079082358052312762457763 25618623537078469143686645)
    ·
      refine ⟨2401745956601106482220623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25618623537078469143686645 2401745956601106482220623)
      ·
        refine ⟨3602618934901659723330935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401745956601106482220623 3602618934901659723330935)
        ·
          refine ⟨5403928402352489584996403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3602618934901659723330935 5403928402352489584996403)
          ·
            refine ⟨8105892603528734377494605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403928402352489584996403 8105892603528734377494605)
            ·
              refine ⟨3039709726323275391560477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8105892603528734377494605 3039709726323275391560477)
              ·
                refine ⟨1139891147371228271835179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3039709726323275391560477 1139891147371228271835179)
                ·
                  refine ⟨1709836721056842407752769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139891147371228271835179 1709836721056842407752769)
                  ·
                    refine ⟨1282377540792631805814577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1709836721056842407752769 1282377540792631805814577)
                    ·
                      refine ⟨961783155594473854360933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282377540792631805814577 961783155594473854360933)
                      ·
                        rfl

theorem cell23_1873066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1873066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873066 prefixEnd_1873066 := by exact prefixLift 1873066
  have htrace : WordTrace (prefixWord ++ tailWord_1873066) baseStart_1873066 baseEnd_1873066 := by
    simpa [prefixWord, tailWord_1873066, baseEnd_1873066] using wordTrace_append hprefix tailTrace_1873066
  have hstable : (prefixWord ++ tailWord_1873066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873066).length < 2 ^ (prefixWord ++ tailWord_1873066).sum := by decide
  have hdescent : baseEnd_1873066 < baseStart_1873066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873075 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 1, 3, 2]
def baseStart_1873075 : Nat := 118140960795 + 1873075 * 2 ^ 59
def prefixEnd_1873075 : Nat := 4983230072969 + 3 ^ 40 * 1873075 * 2
def baseEnd_1873075 : Nat := 961787776920364319148391

theorem tailTrace_1873075 : CollatzResearch.WordTrace tailWord_1873075 prefixEnd_1873075 961787776920364319148391 := by
  unfold tailWord_1873075
  simp only [CollatzResearch.WordTrace]
  refine ⟨68316657689176645586908679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45544438459451097057939119 68316657689176645586908679)
  ·
    refine ⟨102474986533764968380363019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68316657689176645586908679 102474986533764968380363019)
    ·
      refine ⟨153712479800647452570544529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102474986533764968380363019 153712479800647452570544529)
      ·
        refine ⟨115284359850485589427908397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153712479800647452570544529 115284359850485589427908397)
        ·
          refine ⟨43231634943932096035465649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115284359850485589427908397 43231634943932096035465649)
          ·
            refine ⟨32423726207949072026599237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43231634943932096035465649 32423726207949072026599237)
            ·
              refine ⟨6079448663990451004987357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32423726207949072026599237 6079448663990451004987357)
              ·
                refine ⟨2279793248996419126870259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6079448663990451004987357 2279793248996419126870259)
                ·
                  refine ⟨3419689873494628690305389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279793248996419126870259 3419689873494628690305389)
                  ·
                    refine ⟨1282383702560485758864521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419689873494628690305389 1282383702560485758864521)
                    ·
                      refine ⟨961787776920364319148391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282383702560485758864521 961787776920364319148391)
                      ·
                        rfl

theorem cell23_1873075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 3, 2].length) (baseStart_1873075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873075 prefixEnd_1873075 := by exact prefixLift 1873075
  have htrace : WordTrace (prefixWord ++ tailWord_1873075) baseStart_1873075 baseEnd_1873075 := by
    simpa [prefixWord, tailWord_1873075, baseEnd_1873075] using wordTrace_append hprefix tailTrace_1873075
  have hstable : (prefixWord ++ tailWord_1873075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873075).length < 2 ^ (prefixWord ++ tailWord_1873075).sum := by decide
  have hdescent : baseEnd_1873075 < baseStart_1873075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873109 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1873109 : Nat := 118140960795 + 1873109 * 2 ^ 59
def prefixEnd_1873109 : Nat := 4983230072969 + 3 ^ 40 * 1873109 * 2
def baseEnd_1873109 : Nat := 961805235262617186123235

theorem tailTrace_1873109 : CollatzResearch.WordTrace tailWord_1873109 prefixEnd_1873109 961805235262617186123235 := by
  unfold tailWord_1873109
  simp only [CollatzResearch.WordTrace]
  refine ⟨68317897771053469393646381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45545265180702312929097587 68317897771053469393646381)
  ·
    refine ⟨25619211664145051022617393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68317897771053469393646381 25619211664145051022617393)
    ·
      refine ⟨19214408748108788266963045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25619211664145051022617393 19214408748108788266963045)
      ·
        refine ⟨3602701640270397800055571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19214408748108788266963045 3602701640270397800055571)
        ·
          refine ⟨5404052460405596700083357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3602701640270397800055571 5404052460405596700083357)
          ·
            refine ⟨2026519672652098762531259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5404052460405596700083357 2026519672652098762531259)
            ·
              refine ⟨3039779508978148143796889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026519672652098762531259 3039779508978148143796889)
              ·
                refine ⟨2279834631733611107847667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3039779508978148143796889 2279834631733611107847667)
                ·
                  refine ⟨3419751947600416661771501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279834631733611107847667 3419751947600416661771501)
                  ·
                    refine ⟨1282406980350156248164313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3419751947600416661771501 1282406980350156248164313)
                    ·
                      refine ⟨961805235262617186123235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282406980350156248164313 961805235262617186123235)
                      ·
                        rfl

theorem cell23_1873109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1873109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873109 prefixEnd_1873109 := by exact prefixLift 1873109
  have htrace : WordTrace (prefixWord ++ tailWord_1873109) baseStart_1873109 baseEnd_1873109 := by
    simpa [prefixWord, tailWord_1873109, baseEnd_1873109] using wordTrace_append hprefix tailTrace_1873109
  have hstable : (prefixWord ++ tailWord_1873109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873109).length < 2 ^ (prefixWord ++ tailWord_1873109).sum := by decide
  have hdescent : baseEnd_1873109 < baseStart_1873109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873111 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 7]
def baseStart_1873111 : Nat := 118140960795 + 1873111 * 2 ^ 59
def prefixEnd_1873111 : Nat := 4983230072969 + 3 ^ 40 * 1873111 * 2
def baseEnd_1873111 : Nat := 106867362469325130922025

theorem tailTrace_1873111 : CollatzResearch.WordTrace tailWord_1873111 prefixEnd_1873111 106867362469325130922025 := by
  unfold tailWord_1873111
  simp only [CollatzResearch.WordTrace]
  refine ⟨68317970717046223735219187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45545313811364149156812791 68317970717046223735219187)
  ·
    refine ⟨102476956075569335602828781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68317970717046223735219187 102476956075569335602828781)
    ·
      refine ⟨38428858528338500851060793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102476956075569335602828781 38428858528338500851060793)
      ·
        refine ⟨28821643896253875638295595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38428858528338500851060793 28821643896253875638295595)
        ·
          refine ⟨43232465844380813457443393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28821643896253875638295595 43232465844380813457443393)
          ·
            refine ⟨32424349383285610093082545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43232465844380813457443393 32424349383285610093082545)
            ·
              refine ⟨24318262037464207569811909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32424349383285610093082545 24318262037464207569811909)
              ·
                refine ⟨4559674132024538919339733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24318262037464207569811909 4559674132024538919339733)
                ·
                  refine ⟨106867362469325130922025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4559674132024538919339733 106867362469325130922025)
                  ·
                    rfl

theorem cell23_1873111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 7].length) (baseStart_1873111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873111 prefixEnd_1873111 := by exact prefixLift 1873111
  have htrace : WordTrace (prefixWord ++ tailWord_1873111) baseStart_1873111 baseEnd_1873111 := by
    simpa [prefixWord, tailWord_1873111, baseEnd_1873111] using wordTrace_append hprefix tailTrace_1873111
  have hstable : (prefixWord ++ tailWord_1873111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873111).length < 2 ^ (prefixWord ++ tailWord_1873111).sum := by decide
  have hdescent : baseEnd_1873111 < baseStart_1873111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873205 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1873205 : Nat := 118140960795 + 1873205 * 2 ^ 59
def prefixEnd_1873205 : Nat := 4983230072969 + 3 ^ 40 * 1873205 * 2
def baseEnd_1873205 : Nat := 320618176468482936840931

theorem tailTrace_1873205 : CollatzResearch.WordTrace tailWord_1873205 prefixEnd_1873205 320618176468482936840931 := by
  unfold tailWord_1873205
  simp only [CollatzResearch.WordTrace]
  refine ⟨68321399178705677789141069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45547599452470451859427379 68321399178705677789141069)
  ·
    refine ⟨25620524692014629170927901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68321399178705677789141069 25620524692014629170927901)
    ·
      refine ⟨9607696759505485939097963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25620524692014629170927901 9607696759505485939097963)
      ·
        refine ⟨14411545139258228908646945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9607696759505485939097963 14411545139258228908646945)
        ·
          refine ⟨10808658854443671681485209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14411545139258228908646945 10808658854443671681485209)
          ·
            refine ⟨8106494140832753761113907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10808658854443671681485209 8106494140832753761113907)
            ·
              refine ⟨12159741211249130641670861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8106494140832753761113907 12159741211249130641670861)
              ·
                refine ⟨4559902954218423990626573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12159741211249130641670861 4559902954218423990626573)
                ·
                  refine ⟨1709963607831908996484965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4559902954218423990626573 1709963607831908996484965)
                  ·
                    refine ⟨320618176468482936840931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1709963607831908996484965 320618176468482936840931)
                    ·
                      rfl

theorem cell23_1873205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1873205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873205 prefixEnd_1873205 := by exact prefixLift 1873205
  have htrace : WordTrace (prefixWord ++ tailWord_1873205) baseStart_1873205 baseEnd_1873205 := by
    simpa [prefixWord, tailWord_1873205, baseEnd_1873205] using wordTrace_append hprefix tailTrace_1873205
  have hstable : (prefixWord ++ tailWord_1873205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873205).length < 2 ^ (prefixWord ++ tailWord_1873205).sum := by decide
  have hdescent : baseEnd_1873205 < baseStart_1873205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873211 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 9]
def baseStart_1873211 : Nat := 118140960795 + 1873211 * 2 ^ 59
def prefixEnd_1873211 : Nat := 4983230072969 + 3 ^ 40 * 1873211 * 2
def baseEnd_1873211 : Nat := 961857610289375787047765

theorem tailTrace_1873211 : CollatzResearch.WordTrace tailWord_1873211 prefixEnd_1873211 961857610289375787047765 := by
  unfold tailWord_1873211
  simp only [CollatzResearch.WordTrace]
  refine ⟨68321618016683940813859487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45547745344455960542572991 68321618016683940813859487)
  ·
    refine ⟨102482427025025911220789231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68321618016683940813859487 102482427025025911220789231)
    ·
      refine ⟨153723640537538866831183847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102482427025025911220789231 153723640537538866831183847)
      ·
        refine ⟨230585460806308300246775771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153723640537538866831183847 230585460806308300246775771)
        ·
          refine ⟨345878191209462450370163657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230585460806308300246775771 345878191209462450370163657)
          ·
            refine ⟨259408643407096837777622743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345878191209462450370163657 259408643407096837777622743)
            ·
              refine ⟨389112965110645256666434115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259408643407096837777622743 389112965110645256666434115)
              ·
                refine ⟨583669447665967884999651173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389112965110645256666434115 583669447665967884999651173)
                ·
                  refine ⟨109438021437368978437434595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583669447665967884999651173 109438021437368978437434595)
                  ·
                    refine ⟨164157032156053467656151893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109438021437368978437434595 164157032156053467656151893)
                    ·
                      refine ⟨961857610289375787047765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 164157032156053467656151893 961857610289375787047765)
                      ·
                        rfl

theorem cell23_1873211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_1873211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873211 prefixEnd_1873211 := by exact prefixLift 1873211
  have htrace : WordTrace (prefixWord ++ tailWord_1873211) baseStart_1873211 baseEnd_1873211 := by
    simpa [prefixWord, tailWord_1873211, baseEnd_1873211] using wordTrace_append hprefix tailTrace_1873211
  have hstable : (prefixWord ++ tailWord_1873211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873211).length < 2 ^ (prefixWord ++ tailWord_1873211).sum := by decide
  have hdescent : baseEnd_1873211 < baseStart_1873211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873239 : List Nat := [1, 1, 3, 2, 3, 4, 1, 3, 1, 4]
def baseStart_1873239 : Nat := 118140960795 + 1873239 * 2 ^ 59
def prefixEnd_1873239 : Nat := 4983230072969 + 3 ^ 40 * 1873239 * 2
def baseEnd_1873239 : Nat := 320623995915900559165879

theorem tailTrace_1873239 : CollatzResearch.WordTrace tailWord_1873239 prefixEnd_1873239 320623995915900559165879 := by
  unfold tailWord_1873239
  simp only [CollatzResearch.WordTrace]
  refine ⟨68322639260582501595878771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45548426173721667730585847 68322639260582501595878771)
  ·
    refine ⟨102483958890873752393818157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68322639260582501595878771 102483958890873752393818157)
    ·
      refine ⟨38431484584077657147681809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102483958890873752393818157 38431484584077657147681809)
      ·
        refine ⟨28823613438058242860761357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38431484584077657147681809 28823613438058242860761357)
        ·
          refine ⟨10808855039271841072785509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28823613438058242860761357 10808855039271841072785509)
          ·
            refine ⟨2026660319863470201147283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10808855039271841072785509 2026660319863470201147283)
            ·
              refine ⟨3039990479795205301720925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026660319863470201147283 3039990479795205301720925)
              ·
                refine ⟨1139996429923201988145347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3039990479795205301720925 1139996429923201988145347)
                ·
                  refine ⟨1709994644884802982218021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139996429923201988145347 1709994644884802982218021)
                  ·
                    refine ⟨320623995915900559165879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1709994644884802982218021 320623995915900559165879)
                    ·
                      rfl

theorem cell23_1873239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_1873239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873239 prefixEnd_1873239 := by exact prefixLift 1873239
  have htrace : WordTrace (prefixWord ++ tailWord_1873239) baseStart_1873239 baseEnd_1873239 := by
    simpa [prefixWord, tailWord_1873239, baseEnd_1873239] using wordTrace_append hprefix tailTrace_1873239
  have hstable : (prefixWord ++ tailWord_1873239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873239).length < 2 ^ (prefixWord ++ tailWord_1873239).sum := by decide
  have hdescent : baseEnd_1873239 < baseStart_1873239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873256 : List Nat := [2, 1, 4, 2, 3, 1, 3, 2, 1, 4]
def baseStart_1873256 : Nat := 118140960795 + 1873256 * 2 ^ 59
def prefixEnd_1873256 : Nat := 4983230072969 + 3 ^ 40 * 1873256 * 2
def baseEnd_1873256 : Nat := 320626905639609370328353

theorem tailTrace_1873256 : CollatzResearch.WordTrace tailWord_1873256 prefixEnd_1873256 320626905639609370328353 := by
  unfold tailWord_1873256
  simp only [CollatzResearch.WordTrace]
  refine ⟨34161629650760456749623811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45548839534347275666165081 34161629650760456749623811)
  ·
    refine ⟨51242444476140685124435717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34161629650760456749623811 51242444476140685124435717)
    ·
      refine ⟨9607958339276378460831697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51242444476140685124435717 9607958339276378460831697)
      ·
        refine ⟨7205968754457283845623773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9607958339276378460831697 7205968754457283845623773)
        ·
          refine ⟨2702238282921481442108915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7205968754457283845623773 2702238282921481442108915)
          ·
            refine ⟨4053357424382222163163373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702238282921481442108915 4053357424382222163163373)
            ·
              refine ⟨1520009034143333311186265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4053357424382222163163373 1520009034143333311186265)
              ·
                refine ⟨1140006775607499983389699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520009034143333311186265 1140006775607499983389699)
                ·
                  refine ⟨1710010163411249975084549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140006775607499983389699 1710010163411249975084549)
                  ·
                    refine ⟨320626905639609370328353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1710010163411249975084549 320626905639609370328353)
                    ·
                      rfl

theorem cell23_1873256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_1873256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873256 prefixEnd_1873256 := by exact prefixLift 1873256
  have htrace : WordTrace (prefixWord ++ tailWord_1873256) baseStart_1873256 baseEnd_1873256 := by
    simpa [prefixWord, tailWord_1873256, baseEnd_1873256] using wordTrace_append hprefix tailTrace_1873256
  have hstable : (prefixWord ++ tailWord_1873256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873256).length < 2 ^ (prefixWord ++ tailWord_1873256).sum := by decide
  have hdescent : baseEnd_1873256 < baseStart_1873256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873269 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 6]
def baseStart_1873269 : Nat := 118140960795 + 1873269 * 2 ^ 59
def prefixEnd_1873269 : Nat := 4983230072969 + 3 ^ 40 * 1873269 * 2
def baseEnd_1873269 : Nat := 106876376907481840013611

theorem tailTrace_1873269 : CollatzResearch.WordTrace tailWord_1873269 prefixEnd_1873269 106876376907481840013611 := by
  unfold tailWord_1873269
  simp only [CollatzResearch.WordTrace]
  refine ⟨68323733450473816719470861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45549155633649211146313907 68323733450473816719470861)
  ·
    refine ⟨25621400043927681269801573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68323733450473816719470861 25621400043927681269801573)
    ·
      refine ⟨4804012508236440238087795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25621400043927681269801573 4804012508236440238087795)
      ·
        refine ⟨7206018762354660357131693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804012508236440238087795 7206018762354660357131693)
        ·
          refine ⟨2702257035882997633924385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7206018762354660357131693 2702257035882997633924385)
          ·
            refine ⟨2026692776912248225443289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2702257035882997633924385 2026692776912248225443289)
            ·
              refine ⟨1520019582684186169082467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026692776912248225443289 1520019582684186169082467)
              ·
                refine ⟨2280029374026279253623701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520019582684186169082467 2280029374026279253623701)
                ·
                  refine ⟨106876376907481840013611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2280029374026279253623701 106876376907481840013611)
                  ·
                    rfl

theorem cell23_1873269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_1873269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873269 prefixEnd_1873269 := by exact prefixLift 1873269
  have htrace : WordTrace (prefixWord ++ tailWord_1873269) baseStart_1873269 baseEnd_1873269 := by
    simpa [prefixWord, tailWord_1873269, baseEnd_1873269] using wordTrace_append hprefix tailTrace_1873269
  have hstable : (prefixWord ++ tailWord_1873269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873269).length < 2 ^ (prefixWord ++ tailWord_1873269).sum := by decide
  have hdescent : baseEnd_1873269 < baseStart_1873269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873285 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 2, 6, 2]
def baseStart_1873285 : Nat := 118140960795 + 1873285 * 2 ^ 59
def prefixEnd_1873285 : Nat := 4983230072969 + 3 ^ 40 * 1873285 * 2
def baseEnd_1873285 : Nat := 961895607857808497522425

theorem tailTrace_1873285 : CollatzResearch.WordTrace tailWord_1873285 prefixEnd_1873285 961895607857808497522425 := by
  unfold tailWord_1873285
  simp only [CollatzResearch.WordTrace]
  refine ⟨68324317018415851452053309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45549544678943900968035539 68324317018415851452053309)
  ·
    refine ⟨25621618881905944294519991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68324317018415851452053309 25621618881905944294519991)
    ·
      refine ⟨38432428322858916441779987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25621618881905944294519991 38432428322858916441779987)
      ·
        refine ⟨57648642484288374662669981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38432428322858916441779987 57648642484288374662669981)
        ·
          refine ⟨21618240931608140498501243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57648642484288374662669981 21618240931608140498501243)
          ·
            refine ⟨32427361397412210747751865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21618240931608140498501243 32427361397412210747751865)
            ·
              refine ⟨24320521048059158060813899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32427361397412210747751865 24320521048059158060813899)
              ·
                refine ⟨36480781572088737091220849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24320521048059158060813899 36480781572088737091220849)
                ·
                  refine ⟨27360586179066552818415637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36480781572088737091220849 27360586179066552818415637)
                  ·
                    refine ⟨1282527477143744663363233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27360586179066552818415637 1282527477143744663363233)
                    ·
                      refine ⟨961895607857808497522425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282527477143744663363233 961895607857808497522425)
                      ·
                        rfl

theorem cell23_1873285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_1873285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873285 prefixEnd_1873285 := by exact prefixLift 1873285
  have htrace : WordTrace (prefixWord ++ tailWord_1873285) baseStart_1873285 baseEnd_1873285 := by
    simpa [prefixWord, tailWord_1873285, baseEnd_1873285] using wordTrace_append hprefix tailTrace_1873285
  have hstable : (prefixWord ++ tailWord_1873285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873285).length < 2 ^ (prefixWord ++ tailWord_1873285).sum := by decide
  have hdescent : baseEnd_1873285 < baseStart_1873285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873289 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 2, 3, 2]
def baseStart_1873289 : Nat := 118140960795 + 1873289 * 2 ^ 59
def prefixEnd_1873289 : Nat := 4983230072969 + 3 ^ 40 * 1873289 * 2
def baseEnd_1873289 : Nat := 961897661780426481872407

theorem tailTrace_1873289 : CollatzResearch.WordTrace tailWord_1873289 prefixEnd_1873289 961897661780426481872407 := by
  unfold tailWord_1873289
  simp only [CollatzResearch.WordTrace]
  refine ⟨68324462910401360135198921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45549641940267573423465947 68324462910401360135198921)
  ·
    refine ⟨51243347182801020101399191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68324462910401360135198921 51243347182801020101399191)
    ·
      refine ⟨76865020774201530152098787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51243347182801020101399191 76865020774201530152098787)
      ·
        refine ⟨115297531161302295228148181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76865020774201530152098787 115297531161302295228148181)
        ·
          refine ⟨2702285886593022544409723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 115297531161302295228148181 2702285886593022544409723)
          ·
            refine ⟨4053428829889533816614585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702285886593022544409723 4053428829889533816614585)
            ·
              refine ⟨3040071622417150362460939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053428829889533816614585 3040071622417150362460939)
              ·
                refine ⟨4560107433625725543691409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040071622417150362460939 4560107433625725543691409)
                ·
                  refine ⟨3420080575219294157768557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4560107433625725543691409 3420080575219294157768557)
                  ·
                    refine ⟨1282530215707235309163209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3420080575219294157768557 1282530215707235309163209)
                    ·
                      refine ⟨961897661780426481872407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282530215707235309163209 961897661780426481872407)
                      ·
                        rfl

theorem cell23_1873289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 3, 2].length) (baseStart_1873289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873289 prefixEnd_1873289 := by exact prefixLift 1873289
  have htrace : WordTrace (prefixWord ++ tailWord_1873289) baseStart_1873289 baseEnd_1873289 := by
    simpa [prefixWord, tailWord_1873289, baseEnd_1873289] using wordTrace_append hprefix tailTrace_1873289
  have hstable : (prefixWord ++ tailWord_1873289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873289).length < 2 ^ (prefixWord ++ tailWord_1873289).sum := by decide
  have hdescent : baseEnd_1873289 < baseStart_1873289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873305 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 5]
def baseStart_1873305 : Nat := 118140960795 + 1873305 * 2 ^ 59
def prefixEnd_1873305 : Nat := 4983230072969 + 3 ^ 40 * 1873305 * 2
def baseEnd_1873305 : Nat := 961905877470898419272333

theorem tailTrace_1873305 : CollatzResearch.WordTrace tailWord_1873305 prefixEnd_1873305 961905877470898419272333 := by
  unfold tailWord_1873305
  simp only [CollatzResearch.WordTrace]
  refine ⟨68325046478343394867781369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45550030985562263245187579 68325046478343394867781369)
  ·
    refine ⟨51243784858757546150836027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68325046478343394867781369 51243784858757546150836027)
    ·
      refine ⟨76865677288136319226254041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51243784858757546150836027 76865677288136319226254041)
      ·
        refine ⟨57649257966102239419690531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76865677288136319226254041 57649257966102239419690531)
        ·
          refine ⟨86473886949153359129535797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57649257966102239419690531 86473886949153359129535797)
          ·
            refine ⟨8106926901483127418393981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86473886949153359129535797 8106926901483127418393981)
            ·
              refine ⟨3040097588056172781897743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8106926901483127418393981 3040097588056172781897743)
              ·
                refine ⟨4560146382084259172846615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040097588056172781897743 4560146382084259172846615)
                ·
                  refine ⟨6840219573126388759269923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560146382084259172846615 6840219573126388759269923)
                  ·
                    refine ⟨10260329359689583138904885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6840219573126388759269923 10260329359689583138904885)
                    ·
                      refine ⟨961905877470898419272333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10260329359689583138904885 961905877470898419272333)
                      ·
                        rfl

theorem cell23_1873305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_1873305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873305 prefixEnd_1873305 := by exact prefixLift 1873305
  have htrace : WordTrace (prefixWord ++ tailWord_1873305) baseStart_1873305 baseEnd_1873305 := by
    simpa [prefixWord, tailWord_1873305, baseEnd_1873305] using wordTrace_append hprefix tailTrace_1873305
  have hstable : (prefixWord ++ tailWord_1873305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873305).length < 2 ^ (prefixWord ++ tailWord_1873305).sum := by decide
  have hdescent : baseEnd_1873305 < baseStart_1873305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873312 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 2, 4]
def baseStart_1873312 : Nat := 118140960795 + 1873312 * 2 ^ 59
def prefixEnd_1873312 : Nat := 4983230072969 + 3 ^ 40 * 1873312 * 2
def baseEnd_1873312 : Nat := 320636490611826630628267

theorem tailTrace_1873312 : CollatzResearch.WordTrace tailWord_1873312 prefixEnd_1873312 320636490611826630628267 := by
  unfold tailWord_1873312
  simp only [CollatzResearch.WordTrace]
  refine ⟨34162650894659017531643095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45550201192878690042190793 34162650894659017531643095)
  ·
    refine ⟨51243976341988526297464643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34162650894659017531643095 51243976341988526297464643)
    ·
      refine ⟨76865964512982789446196965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51243976341988526297464643 76865964512982789446196965)
      ·
        refine ⟨14412368346184273021161931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76865964512982789446196965 14412368346184273021161931)
        ·
          refine ⟨21618552519276409531742897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14412368346184273021161931 21618552519276409531742897)
          ·
            refine ⟨16213914389457307148807173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21618552519276409531742897 16213914389457307148807173)
            ·
              refine ⟨3040108948023245090401345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16213914389457307148807173 3040108948023245090401345)
              ·
                refine ⟨2280081711017433817801009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3040108948023245090401345 2280081711017433817801009)
                ·
                  refine ⟨1710061283263075363350757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2280081711017433817801009 1710061283263075363350757)
                  ·
                    refine ⟨320636490611826630628267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1710061283263075363350757 320636490611826630628267)
                    ·
                      rfl

theorem cell23_1873312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 4].length) (baseStart_1873312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873312 prefixEnd_1873312 := by exact prefixLift 1873312
  have htrace : WordTrace (prefixWord ++ tailWord_1873312) baseStart_1873312 baseEnd_1873312 := by
    simpa [prefixWord, tailWord_1873312, baseEnd_1873312] using wordTrace_append hprefix tailTrace_1873312
  have hstable : (prefixWord ++ tailWord_1873312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873312).length < 2 ^ (prefixWord ++ tailWord_1873312).sum := by decide
  have hdescent : baseEnd_1873312 < baseStart_1873312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873319 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_1873319 : Nat := 118140960795 + 1873319 * 2 ^ 59
def prefixEnd_1873319 : Nat := 4983230072969 + 3 ^ 40 * 1873319 * 2
def baseEnd_1873319 : Nat := 961913066200061364497269

theorem tailTrace_1873319 : CollatzResearch.WordTrace tailWord_1873319 prefixEnd_1873319 961913066200061364497269 := by
  unfold tailWord_1873319
  simp only [CollatzResearch.WordTrace]
  refine ⟨68325557100292675258791011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45550371400195116839194007 68325557100292675258791011)
  ·
    refine ⟨102488335650439012888186517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68325557100292675258791011 102488335650439012888186517)
    ·
      refine ⟨4804140733614328729133743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102488335650439012888186517 4804140733614328729133743)
      ·
        refine ⟨7206211100421493093700615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804140733614328729133743 7206211100421493093700615)
        ·
          refine ⟨10809316650632239640550923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7206211100421493093700615 10809316650632239640550923)
          ·
            refine ⟨16213974975948359460826385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10809316650632239640550923 16213974975948359460826385)
            ·
              refine ⟨12160481231961269595619789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16213974975948359460826385 12160481231961269595619789)
              ·
                refine ⟨4560180461985476098357421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12160481231961269595619789 4560180461985476098357421)
                ·
                  refine ⟨1710067673244553536884033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4560180461985476098357421 1710067673244553536884033)
                  ·
                    refine ⟨1282550754933415152663025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1710067673244553536884033 1282550754933415152663025)
                    ·
                      refine ⟨961913066200061364497269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282550754933415152663025 961913066200061364497269)
                      ·
                        rfl

theorem cell23_1873319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_1873319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873319 prefixEnd_1873319 := by exact prefixLift 1873319
  have htrace : WordTrace (prefixWord ++ tailWord_1873319) baseStart_1873319 baseEnd_1873319 := by
    simpa [prefixWord, tailWord_1873319, baseEnd_1873319] using wordTrace_append hprefix tailTrace_1873319
  have hstable : (prefixWord ++ tailWord_1873319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873319).length < 2 ^ (prefixWord ++ tailWord_1873319).sum := by decide
  have hdescent : baseEnd_1873319 < baseStart_1873319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873352 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_1873352 : Nat := 118140960795 + 1873352 * 2 ^ 59
def prefixEnd_1873352 : Nat := 4983230072969 + 3 ^ 40 * 1873352 * 2
def baseEnd_1873352 : Nat := 961930011061659735384617

theorem tailTrace_1873352 : CollatzResearch.WordTrace tailWord_1873352 prefixEnd_1873352 961930011061659735384617 := by
  unfold tailWord_1873352
  simp only [CollatzResearch.WordTrace]
  refine ⟨34163380354586560947371155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45551173806115414596494873 34163380354586560947371155)
  ·
    refine ⟨51245070531879841421056733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34163380354586560947371155 51245070531879841421056733)
    ·
      refine ⟨19216901449454940532896275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51245070531879841421056733 19216901449454940532896275)
      ·
        refine ⟨28825352174182410799344413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19216901449454940532896275 28825352174182410799344413)
        ·
          refine ⟨10809507065318404049754155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28825352174182410799344413 10809507065318404049754155)
          ·
            refine ⟨16214260597977606074631233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10809507065318404049754155 16214260597977606074631233)
            ·
              refine ⟨12160695448483204555973425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16214260597977606074631233 12160695448483204555973425)
              ·
                refine ⟨9120521586362403416980069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12160695448483204555973425 9120521586362403416980069)
                ·
                  refine ⟨1710097797442950640683763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9120521586362403416980069 1710097797442950640683763)
                  ·
                    refine ⟨2565146696164425961025645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1710097797442950640683763 2565146696164425961025645)
                    ·
                      refine ⟨961930011061659735384617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2565146696164425961025645 961930011061659735384617)
                      ·
                        rfl

theorem cell23_1873352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_1873352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873352 prefixEnd_1873352 := by exact prefixLift 1873352
  have htrace : WordTrace (prefixWord ++ tailWord_1873352) baseStart_1873352 baseEnd_1873352 := by
    simpa [prefixWord, tailWord_1873352, baseEnd_1873352] using wordTrace_append hprefix tailTrace_1873352
  have hstable : (prefixWord ++ tailWord_1873352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873352).length < 2 ^ (prefixWord ++ tailWord_1873352).sum := by decide
  have hdescent : baseEnd_1873352 < baseStart_1873352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873356 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 1, 2, 3]
def baseStart_1873356 : Nat := 118140960795 + 1873356 * 2 ^ 59
def prefixEnd_1873356 : Nat := 4983230072969 + 3 ^ 40 * 1873356 * 2
def baseEnd_1873356 : Nat := 961932064984277719734599

theorem tailTrace_1873356 : CollatzResearch.WordTrace tailWord_1873356 prefixEnd_1873356 961932064984277719734599 := by
  unfold tailWord_1873356
  simp only [CollatzResearch.WordTrace]
  refine ⟨34163453300579315288943961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45551271067439087051925281 34163453300579315288943961)
  ·
    refine ⟨25622589975434486466707971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34163453300579315288943961 25622589975434486466707971)
    ·
      refine ⟨38433884963151729700061957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25622589975434486466707971 38433884963151729700061957)
      ·
        refine ⟨7206353430590949318761617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38433884963151729700061957 7206353430590949318761617)
        ·
          refine ⟨5404765072943211989071213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7206353430590949318761617 5404765072943211989071213)
          ·
            refine ⟨2026786902353704495901705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5404765072943211989071213 2026786902353704495901705)
            ·
              refine ⟨1520090176765278371926279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026786902353704495901705 1520090176765278371926279)
              ·
                refine ⟨2280135265147917557889419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520090176765278371926279 2280135265147917557889419)
                ·
                  refine ⟨3420202897721876336834129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280135265147917557889419 3420202897721876336834129)
                  ·
                    refine ⟨2565152173291407252625597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3420202897721876336834129 2565152173291407252625597)
                    ·
                      refine ⟨961932064984277719734599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2565152173291407252625597 961932064984277719734599)
                      ·
                        rfl

theorem cell23_1873356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_1873356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873356 prefixEnd_1873356 := by exact prefixLift 1873356
  have htrace : WordTrace (prefixWord ++ tailWord_1873356) baseStart_1873356 baseEnd_1873356 := by
    simpa [prefixWord, tailWord_1873356, baseEnd_1873356] using wordTrace_append hprefix tailTrace_1873356
  have hstable : (prefixWord ++ tailWord_1873356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873356).length < 2 ^ (prefixWord ++ tailWord_1873356).sum := by decide
  have hdescent : baseEnd_1873356 < baseStart_1873356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873369 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 3]
def baseStart_1873369 : Nat := 118140960795 + 1873369 * 2 ^ 59
def prefixEnd_1873369 : Nat := 4983230072969 + 3 ^ 40 * 1873369 * 2
def baseEnd_1873369 : Nat := 961938740232786168872039

theorem tailTrace_1873369 : CollatzResearch.WordTrace tailWord_1873369 prefixEnd_1873369 961938740232786168872039 := by
  unfold tailWord_1873369
  simp only [CollatzResearch.WordTrace]
  refine ⟨68327380750111533798111161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45551587166741022532074107 68327380750111533798111161)
  ·
    refine ⟨51245535562583650348583371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68327380750111533798111161 51245535562583650348583371)
    ·
      refine ⟨76868303343875475522875057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51245535562583650348583371 76868303343875475522875057)
      ·
        refine ⟨57651227507906606642156293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76868303343875475522875057 57651227507906606642156293)
        ·
          refine ⟨10809605157732488745404305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57651227507906606642156293 10809605157732488745404305)
          ·
            refine ⟨8107203868299366559053229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10809605157732488745404305 8107203868299366559053229)
            ·
              refine ⟨3040201450612262459644961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8107203868299366559053229 3040201450612262459644961)
              ·
                refine ⟨2280151087959196844733721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3040201450612262459644961 2280151087959196844733721)
                ·
                  refine ⟨1710113315969397633550291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2280151087959196844733721 1710113315969397633550291)
                  ·
                    refine ⟨2565169973954096450325437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1710113315969397633550291 2565169973954096450325437)
                    ·
                      refine ⟨961938740232786168872039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2565169973954096450325437 961938740232786168872039)
                      ·
                        rfl

theorem cell23_1873369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_1873369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873369 prefixEnd_1873369 := by exact prefixLift 1873369
  have htrace : WordTrace (prefixWord ++ tailWord_1873369) baseStart_1873369 baseEnd_1873369 := by
    simpa [prefixWord, tailWord_1873369, baseEnd_1873369] using wordTrace_append hprefix tailTrace_1873369
  have hstable : (prefixWord ++ tailWord_1873369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873369).length < 2 ^ (prefixWord ++ tailWord_1873369).sum := by decide
  have hdescent : baseEnd_1873369 < baseStart_1873369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873386 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_1873386 : Nat := 118140960795 + 1873386 * 2 ^ 59
def prefixEnd_1873386 : Nat := 4983230072969 + 3 ^ 40 * 1873386 * 2
def baseEnd_1873386 : Nat := 961947469403912602359461

theorem tailTrace_1873386 : CollatzResearch.WordTrace tailWord_1873386 prefixEnd_1873386 961947469403912602359461 := by
  unfold tailWord_1873386
  simp only [CollatzResearch.WordTrace]
  refine ⟨17082000197762486425370003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45552000527366630467653341 17082000197762486425370003)
  ·
    refine ⟨25623000296643729638055005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17082000197762486425370003 25623000296643729638055005)
    ·
      refine ⟨9608625111241398614270627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25623000296643729638055005 9608625111241398614270627)
      ·
        refine ⟨14412937666862097921405941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9608625111241398614270627 14412937666862097921405941)
        ·
          refine ⟨1351212906268321680131807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14412937666862097921405941 1351212906268321680131807)
          ·
            refine ⟨2026819359402482520197711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351212906268321680131807 2026819359402482520197711)
            ·
              refine ⟨3040229039103723780296567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026819359402482520197711 3040229039103723780296567)
              ·
                refine ⟨4560343558655585670444851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040229039103723780296567 4560343558655585670444851)
                ·
                  refine ⟨6840515337983378505667277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560343558655585670444851 6840515337983378505667277)
                  ·
                    refine ⟨2565193251743766939625229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6840515337983378505667277 2565193251743766939625229)
                    ·
                      refine ⟨961947469403912602359461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2565193251743766939625229 961947469403912602359461)
                      ·
                        rfl

theorem cell23_1873386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_1873386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873386 prefixEnd_1873386 := by exact prefixLift 1873386
  have htrace : WordTrace (prefixWord ++ tailWord_1873386) baseStart_1873386 baseEnd_1873386 := by
    simpa [prefixWord, tailWord_1873386, baseEnd_1873386] using wordTrace_append hprefix tailTrace_1873386
  have hstable : (prefixWord ++ tailWord_1873386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873386).length < 2 ^ (prefixWord ++ tailWord_1873386).sum := by decide
  have hdescent : baseEnd_1873386 < baseStart_1873386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873442 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_1873442 : Nat := 118140960795 + 1873442 * 2 ^ 59
def prefixEnd_1873442 : Nat := 4983230072969 + 3 ^ 40 * 1873442 * 2
def baseEnd_1873442 : Nat := 961976224320564383259203

theorem tailTrace_1873442 : CollatzResearch.WordTrace tailWord_1873442 prefixEnd_1873442 961976224320564383259203 := by
  unfold tailWord_1873442
  simp only [CollatzResearch.WordTrace]
  refine ⟨17082510819711766816379645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45553362185898044843679053 17082510819711766816379645)
  ·
    refine ⟨6405941557391912556142367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17082510819711766816379645 6405941557391912556142367)
    ·
      refine ⟨9608912336087868834213551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6405941557391912556142367 9608912336087868834213551)
      ·
        refine ⟨14413368504131803251320327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9608912336087868834213551 14413368504131803251320327)
        ·
          refine ⟨21620052756197704876980491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14413368504131803251320327 21620052756197704876980491)
          ·
            refine ⟨32430079134296557315470737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21620052756197704876980491 32430079134296557315470737)
            ·
              refine ⟨24322559350722417986603053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32430079134296557315470737 24322559350722417986603053)
              ·
                refine ⟨9120959756520906744976145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24322559350722417986603053 9120959756520906744976145)
                ·
                  refine ⟨6840719817390680058732109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9120959756520906744976145 6840719817390680058732109)
                  ·
                    refine ⟨2565269931521505022024541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6840719817390680058732109 2565269931521505022024541)
                    ·
                      refine ⟨961976224320564383259203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2565269931521505022024541 961976224320564383259203)
                      ·
                        rfl

theorem cell23_1873442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_1873442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873442 prefixEnd_1873442 := by exact prefixLift 1873442
  have htrace : WordTrace (prefixWord ++ tailWord_1873442) baseStart_1873442 baseEnd_1873442 := by
    simpa [prefixWord, tailWord_1873442, baseEnd_1873442] using wordTrace_append hprefix tailTrace_1873442
  have hstable : (prefixWord ++ tailWord_1873442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873442).length < 2 ^ (prefixWord ++ tailWord_1873442).sum := by decide
  have hdescent : baseEnd_1873442 < baseStart_1873442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873445 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_1873445 : Nat := 118140960795 + 1873445 * 2 ^ 59
def prefixEnd_1873445 : Nat := 4983230072969 + 3 ^ 40 * 1873445 * 2
def baseEnd_1873445 : Nat := 320659254920842623840563

theorem tailTrace_1873445 : CollatzResearch.WordTrace tailWord_1873445 prefixEnd_1873445 320659254920842623840563 := by
  unfold tailWord_1873445
  simp only [CollatzResearch.WordTrace]
  refine ⟨68330152697836198777877789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45553435131890799185251859 68330152697836198777877789)
  ·
    refine ⟨25623807261688574541704171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68330152697836198777877789 25623807261688574541704171)
    ·
      refine ⟨38435710892532861812556257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25623807261688574541704171 38435710892532861812556257)
      ·
        refine ⟨28826783169399646359417193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38435710892532861812556257 28826783169399646359417193)
        ·
          refine ⟨21620087377049734769562895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28826783169399646359417193 21620087377049734769562895)
          ·
            refine ⟨32430131065574602154344343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21620087377049734769562895 32430131065574602154344343)
            ·
              refine ⟨48645196598361903231516515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32430131065574602154344343 48645196598361903231516515)
              ·
                refine ⟨72967794897542854847274773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48645196598361903231516515 72967794897542854847274773)
                ·
                  refine ⟨3420365385822321320966005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72967794897542854847274773 3420365385822321320966005)
                  ·
                    refine ⟨320659254920842623840563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3420365385822321320966005 320659254920842623840563)
                    ·
                      rfl

theorem cell23_1873445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_1873445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873445 prefixEnd_1873445 := by exact prefixLift 1873445
  have htrace : WordTrace (prefixWord ++ tailWord_1873445) baseStart_1873445 baseEnd_1873445 := by
    simpa [prefixWord, tailWord_1873445, baseEnd_1873445] using wordTrace_append hprefix tailTrace_1873445
  have hstable : (prefixWord ++ tailWord_1873445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873445).length < 2 ^ (prefixWord ++ tailWord_1873445).sum := by decide
  have hdescent : baseEnd_1873445 < baseStart_1873445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873482 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_1873482 : Nat := 118140960795 + 1873482 * 2 ^ 59
def prefixEnd_1873482 : Nat := 4983230072969 + 3 ^ 40 * 1873482 * 2
def baseEnd_1873482 : Nat := 961996763546744226759019

theorem tailTrace_1873482 : CollatzResearch.WordTrace tailWord_1873482 prefixEnd_1873482 961996763546744226759019 := by
  unfold tailWord_1873482
  simp only [CollatzResearch.WordTrace]
  refine ⟨17082875549675538524243675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45554334799134769397983133 17082875549675538524243675)
  ·
    refine ⟨25624313324513307786365513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17082875549675538524243675 25624313324513307786365513)
    ·
      refine ⟨19218234993384980839774135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25624313324513307786365513 19218234993384980839774135)
      ·
        refine ⟨28827352490077471259661203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19218234993384980839774135 28827352490077471259661203)
        ·
          refine ⟨43241028735116206889491805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28827352490077471259661203 43241028735116206889491805)
          ·
            refine ⟨16215385775668577583559427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43241028735116206889491805 16215385775668577583559427)
            ·
              refine ⟨24323078663502866375339141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16215385775668577583559427 24323078663502866375339141)
              ·
                refine ⟨4560577249406787445376089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24323078663502866375339141 4560577249406787445376089)
                ·
                  refine ⟨3420432937055090584032067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4560577249406787445376089 3420432937055090584032067)
                  ·
                    refine ⟨5130649405582635876048101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3420432937055090584032067 5130649405582635876048101)
                    ·
                      refine ⟨961996763546744226759019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5130649405582635876048101 961996763546744226759019)
                      ·
                        rfl

theorem cell23_1873482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_1873482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873482 prefixEnd_1873482 := by exact prefixLift 1873482
  have htrace : WordTrace (prefixWord ++ tailWord_1873482) baseStart_1873482 baseEnd_1873482 := by
    simpa [prefixWord, tailWord_1873482, baseEnd_1873482] using wordTrace_append hprefix tailTrace_1873482
  have hstable : (prefixWord ++ tailWord_1873482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873482).length < 2 ^ (prefixWord ++ tailWord_1873482).sum := by decide
  have hdescent : baseEnd_1873482 < baseStart_1873482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873509 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_1873509 : Nat := 118140960795 + 1873509 * 2 ^ 59
def prefixEnd_1873509 : Nat := 4983230072969 + 3 ^ 40 * 1873509 * 2
def baseEnd_1873509 : Nat := 320670209174805207040465

theorem tailTrace_1873509 : CollatzResearch.WordTrace tailWord_1873509 prefixEnd_1873509 320670209174805207040465 := by
  unfold tailWord_1873509
  simp only [CollatzResearch.WordTrace]
  refine ⟨68332486969604337708207581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45554991313069558472138387 68332486969604337708207581)
  ·
    refine ⟨25624682613601626640577843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68332486969604337708207581 25624682613601626640577843)
    ·
      refine ⟨38437023920402439960866765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25624682613601626640577843 38437023920402439960866765)
      ·
        refine ⟨14413883970150914985325037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38437023920402439960866765 14413883970150914985325037)
        ·
          refine ⟨5405206488806593119496889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14413883970150914985325037 5405206488806593119496889)
          ·
            refine ⟨4053904866604944839622667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5405206488806593119496889 4053904866604944839622667)
            ·
              refine ⟨6080857299907417259434001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4053904866604944839622667 6080857299907417259434001)
              ·
                refine ⟨4560642974930562944575501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6080857299907417259434001 4560642974930562944575501)
                ·
                  refine ⟨1710241115598961104215813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4560642974930562944575501 1710241115598961104215813)
                  ·
                    refine ⟨320670209174805207040465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1710241115598961104215813 320670209174805207040465)
                    ·
                      rfl

theorem cell23_1873509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_1873509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873509 prefixEnd_1873509 := by exact prefixLift 1873509
  have htrace : WordTrace (prefixWord ++ tailWord_1873509) baseStart_1873509 baseEnd_1873509 := by
    simpa [prefixWord, tailWord_1873509, baseEnd_1873509] using wordTrace_append hprefix tailTrace_1873509
  have hstable : (prefixWord ++ tailWord_1873509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873509).length < 2 ^ (prefixWord ++ tailWord_1873509).sum := by decide
  have hdescent : baseEnd_1873509 < baseStart_1873509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873559 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 1, 5, 2]
def baseStart_1873559 : Nat := 118140960795 + 1873559 * 2 ^ 59
def prefixEnd_1873559 : Nat := 4983230072969 + 3 ^ 40 * 1873559 * 2
def baseEnd_1873559 : Nat := 962036301557140425496165

theorem tailTrace_1873559 : CollatzResearch.WordTrace tailWord_1873559 prefixEnd_1873559 962036301557140425496165 := by
  unfold tailWord_1873559
  simp only [CollatzResearch.WordTrace]
  refine ⟨68334310619423196247527731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45556207079615464165018487 68334310619423196247527731)
  ·
    refine ⟨102501465929134794371291597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68334310619423196247527731 102501465929134794371291597)
    ·
      refine ⟨38438049723425547889234349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102501465929134794371291597 38438049723425547889234349)
      ·
        refine ⟨14414268646284580458462881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38438049723425547889234349 14414268646284580458462881)
        ·
          refine ⟨10810701484713435343847161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14414268646284580458462881 10810701484713435343847161)
          ·
            refine ⟨8108026113535076507885371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10810701484713435343847161 8108026113535076507885371)
            ·
              refine ⟨12162039170302614761828057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108026113535076507885371 12162039170302614761828057)
              ·
                refine ⟨9121529377726961071371043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12162039170302614761828057 9121529377726961071371043)
                ·
                  refine ⟨13682294066590441607056565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9121529377726961071371043 13682294066590441607056565)
                  ·
                    refine ⟨1282715068742853900661553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13682294066590441607056565 1282715068742853900661553)
                    ·
                      refine ⟨962036301557140425496165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282715068742853900661553 962036301557140425496165)
                      ·
                        rfl

theorem cell23_1873559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_1873559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873559 prefixEnd_1873559 := by exact prefixLift 1873559
  have htrace : WordTrace (prefixWord ++ tailWord_1873559) baseStart_1873559 baseEnd_1873559 := by
    simpa [prefixWord, tailWord_1873559, baseEnd_1873559] using wordTrace_append hprefix tailTrace_1873559
  have hstable : (prefixWord ++ tailWord_1873559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873559).length < 2 ^ (prefixWord ++ tailWord_1873559).sum := by decide
  have hdescent : baseEnd_1873559 < baseStart_1873559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873569 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 1, 5]
def baseStart_1873569 : Nat := 118140960795 + 1873569 * 2 ^ 59
def prefixEnd_1873569 : Nat := 4983230072969 + 3 ^ 40 * 1873569 * 2
def baseEnd_1873569 : Nat := 320680478787895128790373

theorem tailTrace_1873569 : CollatzResearch.WordTrace tailWord_1873569 prefixEnd_1873569 320680478787895128790373 := by
  unfold tailWord_1873569
  simp only [CollatzResearch.WordTrace]
  refine ⟨68334675349386967955391761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45556450232924645303594507 68334675349386967955391761)
  ·
    refine ⟨51251006512040225966543821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68334675349386967955391761 51251006512040225966543821)
    ·
      refine ⟨19219127442015084737453933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51251006512040225966543821 19219127442015084737453933)
      ·
        refine ⟨7207172790755656776545225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19219127442015084737453933 7207172790755656776545225)
        ·
          refine ⟨5405379593066742582408919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7207172790755656776545225 5405379593066742582408919)
          ·
            refine ⟨8108069389600113873613379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405379593066742582408919 8108069389600113873613379)
            ·
              refine ⟨12162104084400170810420069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108069389600113873613379 12162104084400170810420069)
              ·
                refine ⟨2280394515825032026953763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12162104084400170810420069 2280394515825032026953763)
                ·
                  refine ⟨3420591773737548040430645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280394515825032026953763 3420591773737548040430645)
                  ·
                    refine ⟨320680478787895128790373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3420591773737548040430645 320680478787895128790373)
                    ·
                      rfl

theorem cell23_1873569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_1873569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873569 prefixEnd_1873569 := by exact prefixLift 1873569
  have htrace : WordTrace (prefixWord ++ tailWord_1873569) baseStart_1873569 baseEnd_1873569 := by
    simpa [prefixWord, tailWord_1873569, baseEnd_1873569] using wordTrace_append hprefix tailTrace_1873569
  have hstable : (prefixWord ++ tailWord_1873569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873569).length < 2 ^ (prefixWord ++ tailWord_1873569).sum := by decide
  have hdescent : baseEnd_1873569 < baseStart_1873569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873599 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 2, 4]
def baseStart_1873599 : Nat := 118140960795 + 1873599 * 2 ^ 59
def prefixEnd_1873599 : Nat := 4983230072969 + 3 ^ 40 * 1873599 * 2
def baseEnd_1873599 : Nat := 320685613594440089665327

theorem tailTrace_1873599 : CollatzResearch.WordTrace tailWord_1873599 prefixEnd_1873599 320685613594440089665327 := by
  unfold tailWord_1873599
  simp only [CollatzResearch.WordTrace]
  refine ⟨68335769539278283078983851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45557179692852188719322567 68335769539278283078983851)
  ·
    refine ⟨102503654308917424618475777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68335769539278283078983851 102503654308917424618475777)
    ·
      refine ⟨76877740731688068463856833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102503654308917424618475777 76877740731688068463856833)
      ·
        refine ⟨57658305548766051347892625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76877740731688068463856833 57658305548766051347892625)
        ·
          refine ⟨43243729161574538510919469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57658305548766051347892625 43243729161574538510919469)
          ·
            refine ⟨16216398435590451941594801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43243729161574538510919469 16216398435590451941594801)
            ·
              refine ⟨12162298826692838956196101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16216398435590451941594801 12162298826692838956196101)
              ·
                refine ⟨2280431030004907304286769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12162298826692838956196101 2280431030004907304286769)
                ·
                  refine ⟨1710323272503680478215077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2280431030004907304286769 1710323272503680478215077)
                  ·
                    refine ⟨320685613594440089665327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1710323272503680478215077 320685613594440089665327)
                    ·
                      rfl

theorem cell23_1873599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 4].length) (baseStart_1873599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873599 prefixEnd_1873599 := by exact prefixLift 1873599
  have htrace : WordTrace (prefixWord ++ tailWord_1873599) baseStart_1873599 baseEnd_1873599 := by
    simpa [prefixWord, tailWord_1873599, baseEnd_1873599] using wordTrace_append hprefix tailTrace_1873599
  have hstable : (prefixWord ++ tailWord_1873599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873599).length < 2 ^ (prefixWord ++ tailWord_1873599).sum := by decide
  have hdescent : baseEnd_1873599 < baseStart_1873599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873626 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3]
def baseStart_1873626 : Nat := 118140960795 + 1873626 * 2 ^ 59
def prefixEnd_1873626 : Nat := 4983230072969 + 3 ^ 40 * 1873626 * 2
def baseEnd_1873626 : Nat := 962070704760991663358357

theorem tailTrace_1873626 : CollatzResearch.WordTrace tailWord_1873626 prefixEnd_1873626 962070704760991663358357 := by
  unfold tailWord_1873626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17084188577545116672554183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45557836206786977793477821 17084188577545116672554183)
  ·
    refine ⟨25626282866317675008831275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17084188577545116672554183 25626282866317675008831275)
    ·
      refine ⟨38439424299476512513246913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25626282866317675008831275 38439424299476512513246913)
      ·
        refine ⟨28829568224607384384935185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38439424299476512513246913 28829568224607384384935185)
        ·
          refine ⟨21622176168455538288701389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28829568224607384384935185 21622176168455538288701389)
          ·
            refine ⟨8108316063170826858263021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21622176168455538288701389 8108316063170826858263021)
            ·
              refine ⟨3040618523689060071848633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8108316063170826858263021 3040618523689060071848633)
              ·
                refine ⟨2280463892766795053886475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3040618523689060071848633 2280463892766795053886475)
                ·
                  refine ⟨3420695839150192580829713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280463892766795053886475 3420695839150192580829713)
                  ·
                    refine ⟨2565521879362644435622285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3420695839150192580829713 2565521879362644435622285)
                    ·
                      refine ⟨962070704760991663358357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2565521879362644435622285 962070704760991663358357)
                      ·
                        rfl

theorem cell23_1873626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_1873626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873626 prefixEnd_1873626 := by exact prefixLift 1873626
  have htrace : WordTrace (prefixWord ++ tailWord_1873626) baseStart_1873626 baseEnd_1873626 := by
    simpa [prefixWord, tailWord_1873626, baseEnd_1873626] using wordTrace_append hprefix tailTrace_1873626
  have hstable : (prefixWord ++ tailWord_1873626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873626).length < 2 ^ (prefixWord ++ tailWord_1873626).sum := by decide
  have hdescent : baseEnd_1873626 < baseStart_1873626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873694 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1873694 : Nat := 118140960795 + 1873694 * 2 ^ 59
def prefixEnd_1873694 : Nat := 4983230072969 + 3 ^ 40 * 1873694 * 2
def baseEnd_1873694 : Nat := 962105621445497397308045

theorem tailTrace_1873694 : CollatzResearch.WordTrace tailWord_1873694 prefixEnd_1873694 962105621445497397308045 := by
  unfold tailWord_1873694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542404309241764287961517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45559489649289409535794757 8542404309241764287961517)
  ·
    refine ⟨3203401615965661607985569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8542404309241764287961517 3203401615965661607985569)
    ·
      refine ⟨2402551211974246205989177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3203401615965661607985569 2402551211974246205989177)
      ·
        refine ⟨1801913408980684654491883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2402551211974246205989177 1801913408980684654491883)
        ·
          refine ⟨2702870113471026981737825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801913408980684654491883 2702870113471026981737825)
          ·
            refine ⟨2027152585103270236303369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2702870113471026981737825 2027152585103270236303369)
            ·
              refine ⟨1520364438827452677227527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027152585103270236303369 1520364438827452677227527)
              ·
                refine ⟨2280546658241179015841291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520364438827452677227527 2280546658241179015841291)
                ·
                  refine ⟨3420819987361768523761937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280546658241179015841291 3420819987361768523761937)
                  ·
                    refine ⟨2565614990521326392821453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3420819987361768523761937 2565614990521326392821453)
                    ·
                      refine ⟨962105621445497397308045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2565614990521326392821453 962105621445497397308045)
                      ·
                        rfl

theorem cell23_1873694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1873694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873694 prefixEnd_1873694 := by exact prefixLift 1873694
  have htrace : WordTrace (prefixWord ++ tailWord_1873694) baseStart_1873694 baseEnd_1873694 := by
    simpa [prefixWord, tailWord_1873694, baseEnd_1873694] using wordTrace_append hprefix tailTrace_1873694
  have hstable : (prefixWord ++ tailWord_1873694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873694).length < 2 ^ (prefixWord ++ tailWord_1873694).sum := by decide
  have hdescent : baseEnd_1873694 < baseStart_1873694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873696 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 1, 4, 2]
def baseStart_1873696 : Nat := 118140960795 + 1873696 * 2 ^ 59
def prefixEnd_1873696 : Nat := 4983230072969 + 3 ^ 40 * 1873696 * 2
def baseEnd_1873696 : Nat := 962106648406806389483035

theorem tailTrace_1873696 : CollatzResearch.WordTrace tailWord_1873696 prefixEnd_1873696 962106648406806389483035 := by
  unfold tailWord_1873696
  simp only [CollatzResearch.WordTrace]
  refine ⟨34169653709963434322632471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45559538279951245763509961 34169653709963434322632471)
  ·
    refine ⟨51254480564945151483948707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34169653709963434322632471 51254480564945151483948707)
    ·
      refine ⟨76881720847417727225923061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51254480564945151483948707 76881720847417727225923061)
      ·
        refine ⟨7207661329445411927430287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76881720847417727225923061 7207661329445411927430287)
        ·
          refine ⟨10811491994168117891145431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7207661329445411927430287 10811491994168117891145431)
          ·
            refine ⟨16217237991252176836718147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10811491994168117891145431 16217237991252176836718147)
            ·
              refine ⟨24325856986878265255077221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16217237991252176836718147 24325856986878265255077221)
              ·
                refine ⟨4561098185039674735326979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24325856986878265255077221 4561098185039674735326979)
                ·
                  refine ⟨6841647277559512102990469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561098185039674735326979 6841647277559512102990469)
                  ·
                    refine ⟨1282808864542408519310713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6841647277559512102990469 1282808864542408519310713)
                    ·
                      refine ⟨962106648406806389483035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282808864542408519310713 962106648406806389483035)
                      ·
                        rfl

theorem cell23_1873696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_1873696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873696 prefixEnd_1873696 := by exact prefixLift 1873696
  have htrace : WordTrace (prefixWord ++ tailWord_1873696) baseStart_1873696 baseEnd_1873696 := by
    simpa [prefixWord, tailWord_1873696, baseEnd_1873696] using wordTrace_append hprefix tailTrace_1873696
  have hstable : (prefixWord ++ tailWord_1873696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873696).length < 2 ^ (prefixWord ++ tailWord_1873696).sum := by decide
  have hdescent : baseEnd_1873696 < baseStart_1873696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873700 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_1873700 : Nat := 118140960795 + 1873700 * 2 ^ 59
def prefixEnd_1873700 : Nat := 4983230072969 + 3 ^ 40 * 1873700 * 2
def baseEnd_1873700 : Nat := 962108702329424373833017

theorem tailTrace_1873700 : CollatzResearch.WordTrace tailWord_1873700 prefixEnd_1873700 962108702329424373833017 := by
  unfold tailWord_1873700
  simp only [CollatzResearch.WordTrace]
  refine ⟨34169726655956188664205277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45559635541274918218940369 34169726655956188664205277)
  ·
    refine ⟨12813647495983570749076979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34169726655956188664205277 12813647495983570749076979)
    ·
      refine ⟨19220471243975356123615469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12813647495983570749076979 19220471243975356123615469)
      ·
        refine ⟨7207676716490758546355801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19220471243975356123615469 7207676716490758546355801)
        ·
          refine ⟨5405757537368068909766851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7207676716490758546355801 5405757537368068909766851)
          ·
            refine ⟨8108636306052103364650277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405757537368068909766851 8108636306052103364650277)
            ·
              refine ⟨1520369307384769380871927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8108636306052103364650277 1520369307384769380871927)
              ·
                refine ⟨2280553961077154071307891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520369307384769380871927 2280553961077154071307891)
                ·
                  refine ⟨3420830941615731106961837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280553961077154071307891 3420830941615731106961837)
                  ·
                    refine ⟨1282811603105899165110689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3420830941615731106961837 1282811603105899165110689)
                    ·
                      refine ⟨962108702329424373833017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282811603105899165110689 962108702329424373833017)
                      ·
                        rfl

theorem cell23_1873700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_1873700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873700 prefixEnd_1873700 := by exact prefixLift 1873700
  have htrace : WordTrace (prefixWord ++ tailWord_1873700) baseStart_1873700 baseEnd_1873700 := by
    simpa [prefixWord, tailWord_1873700, baseEnd_1873700] using wordTrace_append hprefix tailTrace_1873700
  have hstable : (prefixWord ++ tailWord_1873700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873700).length < 2 ^ (prefixWord ++ tailWord_1873700).sum := by decide
  have hdescent : baseEnd_1873700 < baseStart_1873700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873713 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 4, 2, 2]
def baseStart_1873713 : Nat := 118140960795 + 1873713 * 2 ^ 59
def prefixEnd_1873713 : Nat := 4983230072969 + 3 ^ 40 * 1873713 * 2
def baseEnd_1873713 : Nat := 962115377577932822970457

theorem tailTrace_1873713 : CollatzResearch.WordTrace tailWord_1873713 prefixEnd_1873713 962115377577932822970457 := by
  unfold tailWord_1873713
  simp only [CollatzResearch.WordTrace]
  refine ⟨68339927460865280548633793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45559951640576853699089195 68339927460865280548633793)
  ·
    refine ⟨51254945595648960411475345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68339927460865280548633793 51254945595648960411475345)
    ·
      refine ⟨38441209196736720308606509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51254945595648960411475345 38441209196736720308606509)
      ·
        refine ⟨14415453448776270115727441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38441209196736720308606509 14415453448776270115727441)
        ·
          refine ⟨10811590086582202586795581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14415453448776270115727441 10811590086582202586795581)
          ·
            refine ⟨4054346282468325970048343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10811590086582202586795581 4054346282468325970048343)
            ·
              refine ⟨6081519423702488955072515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054346282468325970048343 6081519423702488955072515)
              ·
                refine ⟨9122279135553733432608773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081519423702488955072515 9122279135553733432608773)
                ·
                  refine ⟨1710427337916325018614145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9122279135553733432608773 1710427337916325018614145)
                  ·
                    refine ⟨1282820503437243763960609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1710427337916325018614145 1282820503437243763960609)
                    ·
                      refine ⟨962115377577932822970457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282820503437243763960609 962115377577932822970457)
                      ·
                        rfl

theorem cell23_1873713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_1873713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873713 prefixEnd_1873713 := by exact prefixLift 1873713
  have htrace : WordTrace (prefixWord ++ tailWord_1873713) baseStart_1873713 baseEnd_1873713 := by
    simpa [prefixWord, tailWord_1873713, baseEnd_1873713] using wordTrace_append hprefix tailTrace_1873713
  have hstable : (prefixWord ++ tailWord_1873713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873713).length < 2 ^ (prefixWord ++ tailWord_1873713).sum := by decide
  have hdescent : baseEnd_1873713 < baseStart_1873713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873726 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1873726 : Nat := 118140960795 + 1873726 * 2 ^ 59
def prefixEnd_1873726 : Nat := 4983230072969 + 3 ^ 40 * 1873726 * 2
def baseEnd_1873726 : Nat := 962122052826441272107897

theorem tailTrace_1873726 : CollatzResearch.WordTrace tailWord_1873726 prefixEnd_1873726 962122052826441272107897 := by
  unfold tailWord_1873726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542550201227272971107129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45560267739878789179238021 8542550201227272971107129)
  ·
    refine ⟨6406912650920454728330347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8542550201227272971107129 6406912650920454728330347)
    ·
      refine ⟨9610368976380682092495521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6406912650920454728330347 9610368976380682092495521)
      ·
        refine ⟨7207776732285511569371641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9610368976380682092495521 7207776732285511569371641)
        ·
          refine ⟨5405832549214133677028731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7207776732285511569371641 5405832549214133677028731)
          ·
            refine ⟨8108748823821200515543097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405832549214133677028731 8108748823821200515543097)
            ·
              refine ⟨6081561617865900386657323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8108748823821200515543097 6081561617865900386657323)
              ·
                refine ⟨9122342426798850579985985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081561617865900386657323 9122342426798850579985985)
                ·
                  refine ⟨6841756820099137934989489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9122342426798850579985985 6841756820099137934989489)
                  ·
                    refine ⟨5131317615074353451242117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6841756820099137934989489 5131317615074353451242117)
                    ·
                      refine ⟨962122052826441272107897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5131317615074353451242117 962122052826441272107897)
                      ·
                        rfl

theorem cell23_1873726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1873726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873726 prefixEnd_1873726 := by exact prefixLift 1873726
  have htrace : WordTrace (prefixWord ++ tailWord_1873726) baseStart_1873726 baseEnd_1873726 := by
    simpa [prefixWord, tailWord_1873726, baseEnd_1873726] using wordTrace_append hprefix tailTrace_1873726
  have hstable : (prefixWord ++ tailWord_1873726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873726).length < 2 ^ (prefixWord ++ tailWord_1873726).sum := by decide
  have hdescent : baseEnd_1873726 < baseStart_1873726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873749 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_1873749 : Nat := 118140960795 + 1873749 * 2 ^ 59
def prefixEnd_1873749 : Nat := 4983230072969 + 3 ^ 40 * 1873749 * 2
def baseEnd_1873749 : Nat := 320711287627164894040097

theorem tailTrace_1873749 : CollatzResearch.WordTrace tailWord_1873749 prefixEnd_1873749 320711287627164894040097 := by
  unfold tailWord_1873749
  simp only [CollatzResearch.WordTrace]
  refine ⟨68341240488734858696944301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45560826992489905797962867 68341240488734858696944301)
  ·
    refine ⟨25627965183275572011354113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68341240488734858696944301 25627965183275572011354113)
    ·
      refine ⟨19220973887456679008515585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25627965183275572011354113 19220973887456679008515585)
      ·
        refine ⟨14415730415592509256386689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19220973887456679008515585 14415730415592509256386689)
        ·
          refine ⟨10811797811694381942290017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14415730415592509256386689 10811797811694381942290017)
          ·
            refine ⟨8108848358770786456717513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10811797811694381942290017 8108848358770786456717513)
            ·
              refine ⟨6081636269078089842538135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8108848358770786456717513 6081636269078089842538135)
              ·
                refine ⟨9122454403617134763807203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081636269078089842538135 9122454403617134763807203)
                ·
                  refine ⟨13683681605425702145710805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9122454403617134763807203 13683681605425702145710805)
                  ·
                    refine ⟨320711287627164894040097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13683681605425702145710805 320711287627164894040097)
                    ·
                      rfl

theorem cell23_1873749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_1873749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873749 prefixEnd_1873749 := by exact prefixLift 1873749
  have htrace : WordTrace (prefixWord ++ tailWord_1873749) baseStart_1873749 baseEnd_1873749 := by
    simpa [prefixWord, tailWord_1873749, baseEnd_1873749] using wordTrace_append hprefix tailTrace_1873749
  have hstable : (prefixWord ++ tailWord_1873749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873749).length < 2 ^ (prefixWord ++ tailWord_1873749).sum := by decide
  have hdescent : baseEnd_1873749 < baseStart_1873749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873770 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 7]
def baseStart_1873770 : Nat := 118140960795 + 1873770 * 2 ^ 59
def prefixEnd_1873770 : Nat := 4983230072969 + 3 ^ 40 * 1873770 * 2
def baseEnd_1873770 : Nat := 106904960663915455550855

theorem tailTrace_1873770 : CollatzResearch.WordTrace tailWord_1873770 prefixEnd_1873770 106904960663915455550855 := by
  unfold tailWord_1873770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17085501605414694820864691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45561337614439186188972509 17085501605414694820864691)
  ·
    refine ⟨25628252408122042231297037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17085501605414694820864691 25628252408122042231297037)
    ·
      refine ⟨9610594653045765836736389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25628252408122042231297037 9610594653045765836736389)
      ·
        refine ⟨1801986497446081094388073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9610594653045765836736389 1801986497446081094388073)
        ·
          refine ⟨1351489873084560820791055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1801986497446081094388073 1351489873084560820791055)
          ·
            refine ⟨2027234809626841231186583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351489873084560820791055 2027234809626841231186583)
            ·
              refine ⟨3040852214440261846779875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027234809626841231186583 3040852214440261846779875)
              ·
                refine ⟨4561278321660392770169813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040852214440261846779875 4561278321660392770169813)
                ·
                  refine ⟨106904960663915455550855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4561278321660392770169813 106904960663915455550855)
                  ·
                    rfl

theorem cell23_1873770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_1873770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873770 prefixEnd_1873770 := by exact prefixLift 1873770
  have htrace : WordTrace (prefixWord ++ tailWord_1873770) baseStart_1873770 baseEnd_1873770 := by
    simpa [prefixWord, tailWord_1873770, baseEnd_1873770] using wordTrace_append hprefix tailTrace_1873770
  have hstable : (prefixWord ++ tailWord_1873770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873770).length < 2 ^ (prefixWord ++ tailWord_1873770).sum := by decide
  have hdescent : baseEnd_1873770 < baseStart_1873770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873786 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2]
def baseStart_1873786 : Nat := 118140960795 + 1873786 * 2 ^ 59
def prefixEnd_1873786 : Nat := 4983230072969 + 3 ^ 40 * 1873786 * 2
def baseEnd_1873786 : Nat := 962152861665711037357621

theorem tailTrace_1873786 : CollatzResearch.WordTrace tailWord_1873786 prefixEnd_1873786 962152861665711037357621 := by
  unfold tailWord_1873786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17085647497400203504010303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45561726659733876010694141 17085647497400203504010303)
  ·
    refine ⟨25628471246100305256015455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17085647497400203504010303 25628471246100305256015455)
    ·
      refine ⟨38442706869150457884023183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25628471246100305256015455 38442706869150457884023183)
      ·
        refine ⟨57664060303725686826034775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38442706869150457884023183 57664060303725686826034775)
        ·
          refine ⟨86496090455588530239052163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57664060303725686826034775 86496090455588530239052163)
          ·
            refine ⟨129744135683382795358578245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86496090455588530239052163 129744135683382795358578245)
            ·
              refine ⟨24327025440634274129733421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129744135683382795358578245 24327025440634274129733421)
              ·
                refine ⟨9122634540237852798650033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24327025440634274129733421 9122634540237852798650033)
                ·
                  refine ⟨6841975905178389598987525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9122634540237852798650033 6841975905178389598987525)
                  ·
                    refine ⟨1282870482220948049810161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6841975905178389598987525 1282870482220948049810161)
                    ·
                      refine ⟨962152861665711037357621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282870482220948049810161 962152861665711037357621)
                      ·
                        rfl

theorem cell23_1873786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_1873786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873786 prefixEnd_1873786 := by exact prefixLift 1873786
  have htrace : WordTrace (prefixWord ++ tailWord_1873786) baseStart_1873786 baseEnd_1873786 := by
    simpa [prefixWord, tailWord_1873786, baseEnd_1873786] using wordTrace_append hprefix tailTrace_1873786
  have hstable : (prefixWord ++ tailWord_1873786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873786).length < 2 ^ (prefixWord ++ tailWord_1873786).sum := by decide
  have hdescent : baseEnd_1873786 < baseStart_1873786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873796 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_1873796 : Nat := 118140960795 + 1873796 * 2 ^ 59
def prefixEnd_1873796 : Nat := 4983230072969 + 3 ^ 40 * 1873796 * 2
def baseEnd_1873796 : Nat := 320719332157418666077525

theorem tailTrace_1873796 : CollatzResearch.WordTrace tailWord_1873796 prefixEnd_1873796 320719332157418666077525 := by
  unfold tailWord_1873796
  simp only [CollatzResearch.WordTrace]
  refine ⟨34171477359782292861952621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45561969813043057149270161 34171477359782292861952621)
  ·
    refine ⟨12814304009918359823232233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34171477359782292861952621 12814304009918359823232233)
    ·
      refine ⟨9610728007438769867424175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12814304009918359823232233 9610728007438769867424175)
      ·
        refine ⟨14416092011158154801136263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9610728007438769867424175 14416092011158154801136263)
        ·
          refine ⟨21624138016737232201704395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14416092011158154801136263 21624138016737232201704395)
          ·
            refine ⟨32436207025105848302556593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21624138016737232201704395 32436207025105848302556593)
            ·
              refine ⟨24327155268829386226917445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32436207025105848302556593 24327155268829386226917445)
              ·
                refine ⟨4561341612905509917547021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24327155268829386226917445 4561341612905509917547021)
                ·
                  refine ⟨1710503104839566219080133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4561341612905509917547021 1710503104839566219080133)
                  ·
                    refine ⟨320719332157418666077525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1710503104839566219080133 320719332157418666077525)
                    ·
                      rfl

theorem cell23_1873796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_1873796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873796 prefixEnd_1873796 := by exact prefixLift 1873796
  have htrace : WordTrace (prefixWord ++ tailWord_1873796) baseStart_1873796 baseEnd_1873796 := by
    simpa [prefixWord, tailWord_1873796, baseEnd_1873796] using wordTrace_append hprefix tailTrace_1873796
  have hstable : (prefixWord ++ tailWord_1873796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873796).length < 2 ^ (prefixWord ++ tailWord_1873796).sum := by decide
  have hdescent : baseEnd_1873796 < baseStart_1873796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873813 : List Nat := [1, 3, 2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_1873813 : Nat := 118140960795 + 1873813 * 2 ^ 59
def prefixEnd_1873813 : Nat := 4983230072969 + 3 ^ 40 * 1873813 * 2
def baseEnd_1873813 : Nat := 320722241881127477239999

theorem tailTrace_1873813 : CollatzResearch.WordTrace tailWord_1873813 prefixEnd_1873813 320722241881127477239999 := by
  unfold tailWord_1873813
  simp only [CollatzResearch.WordTrace]
  refine ⟨68343574760502997627274093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45562383173668665084849395 68343574760502997627274093)
  ·
    refine ⟨25628840535188624110227785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68343574760502997627274093 25628840535188624110227785)
    ·
      refine ⟨19221630401391468082670839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25628840535188624110227785 19221630401391468082670839)
      ·
        refine ⟨28832445602087202124006259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19221630401391468082670839 28832445602087202124006259)
        ·
          refine ⟨43248668403130803186009389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28832445602087202124006259 43248668403130803186009389)
          ·
            refine ⟨16218250651174051194753521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43248668403130803186009389 16218250651174051194753521)
            ·
              refine ⟨12163687988380538396065141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16218250651174051194753521 12163687988380538396065141)
              ·
                refine ⟨1140345748910675474631107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12163687988380538396065141 1140345748910675474631107)
                ·
                  refine ⟨1710518623366013211946661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140345748910675474631107 1710518623366013211946661)
                  ·
                    refine ⟨320722241881127477239999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1710518623366013211946661 320722241881127477239999)
                    ·
                      rfl

theorem cell23_1873813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_1873813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873813 prefixEnd_1873813 := by exact prefixLift 1873813
  have htrace : WordTrace (prefixWord ++ tailWord_1873813) baseStart_1873813 baseEnd_1873813 := by
    simpa [prefixWord, tailWord_1873813, baseEnd_1873813] using wordTrace_append hprefix tailTrace_1873813
  have hstable : (prefixWord ++ tailWord_1873813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873813).length < 2 ^ (prefixWord ++ tailWord_1873813).sum := by decide
  have hdescent : baseEnd_1873813 < baseStart_1873813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873839 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 5, 5]
def baseStart_1873839 : Nat := 118140960795 + 1873839 * 2 ^ 59
def prefixEnd_1873839 : Nat := 4983230072969 + 3 ^ 40 * 1873839 * 2
def baseEnd_1873839 : Nat := 320726692046799776664959

theorem tailTrace_1873839 : CollatzResearch.WordTrace tailWord_1873839 prefixEnd_1873839 320726692046799776664959 := by
  unfold tailWord_1873839
  simp only [CollatzResearch.WordTrace]
  refine ⟨68344523058408804067720571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45563015372272536045147047 68344523058408804067720571)
  ·
    refine ⟨102516784587613206101580857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68344523058408804067720571 102516784587613206101580857)
    ·
      refine ⟨76887588440709904576185643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102516784587613206101580857 76887588440709904576185643)
      ·
        refine ⟨115331382661064856864278465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76887588440709904576185643 115331382661064856864278465)
        ·
          refine ⟨86498536995798642648208849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115331382661064856864278465 86498536995798642648208849)
          ·
            refine ⟨64873902746848981986156637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86498536995798642648208849 64873902746848981986156637)
            ·
              refine ⟨24327713530068368244808739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64873902746848981986156637 24327713530068368244808739)
              ·
                refine ⟨36491570295102552367213109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24327713530068368244808739 36491570295102552367213109)
                ·
                  refine ⟨3421084715165864284426229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36491570295102552367213109 3421084715165864284426229)
                  ·
                    refine ⟨320726692046799776664959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3421084715165864284426229 320726692046799776664959)
                    ·
                      rfl

theorem cell23_1873839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_1873839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873839 prefixEnd_1873839 := by exact prefixLift 1873839
  have htrace : WordTrace (prefixWord ++ tailWord_1873839) baseStart_1873839 baseEnd_1873839 := by
    simpa [prefixWord, tailWord_1873839, baseEnd_1873839] using wordTrace_append hprefix tailTrace_1873839
  have hstable : (prefixWord ++ tailWord_1873839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873839).length < 2 ^ (prefixWord ++ tailWord_1873839).sum := by decide
  have hdescent : baseEnd_1873839 < baseStart_1873839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873849 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1873849 : Nat := 118140960795 + 1873849 * 2 ^ 59
def prefixEnd_1873849 : Nat := 4983230072969 + 3 ^ 40 * 1873849 * 2
def baseEnd_1873849 : Nat := 962185210946944290869831

theorem tailTrace_1873849 : CollatzResearch.WordTrace tailWord_1873849 prefixEnd_1873849 962185210946944290869831 := by
  unfold tailWord_1873849
  simp only [CollatzResearch.WordTrace]
  refine ⟨68344887788372575775584601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45563258525581717183723067 68344887788372575775584601)
  ·
    refine ⟨51258665841279431831688451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68344887788372575775584601 51258665841279431831688451)
    ·
      refine ⟨76887998761919147747532677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51258665841279431831688451 76887998761919147747532677)
      ·
        refine ⟨14416499767859840202662377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76887998761919147747532677 14416499767859840202662377)
        ·
          refine ⟨10812374825894880151996783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14416499767859840202662377 10812374825894880151996783)
          ·
            refine ⟨16218562238842320227995175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10812374825894880151996783 16218562238842320227995175)
            ·
              refine ⟨24327843358263480341992763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16218562238842320227995175 24327843358263480341992763)
              ·
                refine ⟨36491765037395220512989145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24327843358263480341992763 36491765037395220512989145)
                ·
                  refine ⟨27368823778046415384741859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36491765037395220512989145 27368823778046415384741859)
                  ·
                    refine ⟨41053235667069623077112789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27368823778046415384741859 41053235667069623077112789)
                    ·
                      refine ⟨962185210946944290869831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41053235667069623077112789 962185210946944290869831)
                      ·
                        rfl

theorem cell23_1873849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1873849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873849 prefixEnd_1873849 := by exact prefixLift 1873849
  have htrace : WordTrace (prefixWord ++ tailWord_1873849) baseStart_1873849 baseEnd_1873849 := by
    simpa [prefixWord, tailWord_1873849, baseEnd_1873849] using wordTrace_append hprefix tailTrace_1873849
  have hstable : (prefixWord ++ tailWord_1873849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873849).length < 2 ^ (prefixWord ++ tailWord_1873849).sum := by decide
  have hdescent : baseEnd_1873849 < baseStart_1873849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873853 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_1873853 : Nat := 118140960795 + 1873853 * 2 ^ 59
def prefixEnd_1873853 : Nat := 4983230072969 + 3 ^ 40 * 1873853 * 2
def baseEnd_1873853 : Nat := 962187264869562275219813

theorem tailTrace_1873853 : CollatzResearch.WordTrace tailWord_1873853 prefixEnd_1873853 962187264869562275219813 := by
  unfold tailWord_1873853
  simp only [CollatzResearch.WordTrace]
  refine ⟨68345033680358084458730213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45563355786905389639153475 68345033680358084458730213)
  ·
    refine ⟨12814693815067140836011915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68345033680358084458730213 12814693815067140836011915)
    ·
      refine ⟨19222040722600711254017873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12814693815067140836011915 19222040722600711254017873)
      ·
        refine ⟨14416530541950533440513405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19222040722600711254017873 14416530541950533440513405)
        ·
          refine ⟨5406198953231450040192527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14416530541950533440513405 5406198953231450040192527)
          ·
            refine ⟨8109298429847175060288791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406198953231450040192527 8109298429847175060288791)
            ·
              refine ⟨12163947644770762590433187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8109298429847175060288791 12163947644770762590433187)
              ·
                refine ⟨18245921467156143885649781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12163947644770762590433187 18245921467156143885649781)
                ·
                  refine ⟨1710555137545888489279667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18245921467156143885649781 1710555137545888489279667)
                  ·
                    refine ⟨2565832706318832733919501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1710555137545888489279667 2565832706318832733919501)
                    ·
                      refine ⟨962187264869562275219813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2565832706318832733919501 962187264869562275219813)
                      ·
                        rfl

theorem cell23_1873853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_1873853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873853 prefixEnd_1873853 := by exact prefixLift 1873853
  have htrace : WordTrace (prefixWord ++ tailWord_1873853) baseStart_1873853 baseEnd_1873853 := by
    simpa [prefixWord, tailWord_1873853, baseEnd_1873853] using wordTrace_append hprefix tailTrace_1873853
  have hstable : (prefixWord ++ tailWord_1873853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873853).length < 2 ^ (prefixWord ++ tailWord_1873853).sum := by decide
  have hdescent : baseEnd_1873853 < baseStart_1873853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873856 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 1, 5]
def baseStart_1873856 : Nat := 118140960795 + 1873856 * 2 ^ 59
def prefixEnd_1873856 : Nat := 4983230072969 + 3 ^ 40 * 1873856 * 2
def baseEnd_1873856 : Nat := 320729601770508587827433

theorem tailTrace_1873856 : CollatzResearch.WordTrace tailWord_1873856 prefixEnd_1873856 320729601770508587827433 := by
  unfold tailWord_1873856
  simp only [CollatzResearch.WordTrace]
  refine ⟨34172571549673607985544711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45563428732898143980726281 34172571549673607985544711)
  ·
    refine ⟨51258857324510411978317067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34172571549673607985544711 51258857324510411978317067)
    ·
      refine ⟨76888285986765617967475601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51258857324510411978317067 76888285986765617967475601)
      ·
        refine ⟨57666214490074213475606701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76888285986765617967475601 57666214490074213475606701)
        ·
          refine ⟨21624830433777830053352513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57666214490074213475606701 21624830433777830053352513)
          ·
            refine ⟨16218622825333372540014385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21624830433777830053352513 16218622825333372540014385)
            ·
              refine ⟨12163967119000029405010789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16218622825333372540014385 12163967119000029405010789)
              ·
                refine ⟨2280743834812505513439523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12163967119000029405010789 2280743834812505513439523)
                ·
                  refine ⟨3421115752218758270159285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280743834812505513439523 3421115752218758270159285)
                  ·
                    refine ⟨320729601770508587827433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3421115752218758270159285 320729601770508587827433)
                    ·
                      rfl

theorem cell23_1873856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 5].length) (baseStart_1873856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873856 prefixEnd_1873856 := by exact prefixLift 1873856
  have htrace : WordTrace (prefixWord ++ tailWord_1873856) baseStart_1873856 baseEnd_1873856 := by
    simpa [prefixWord, tailWord_1873856, baseEnd_1873856] using wordTrace_append hprefix tailTrace_1873856
  have hstable : (prefixWord ++ tailWord_1873856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873856).length < 2 ^ (prefixWord ++ tailWord_1873856).sum := by decide
  have hdescent : baseEnd_1873856 < baseStart_1873856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873913 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 3]
def baseStart_1873913 : Nat := 118140960795 + 1873913 * 2 ^ 59
def prefixEnd_1873913 : Nat := 4983230072969 + 3 ^ 40 * 1873913 * 2
def baseEnd_1873913 : Nat := 962218073708832040469537

theorem tailTrace_1873913 : CollatzResearch.WordTrace tailWord_1873913 prefixEnd_1873913 962218073708832040469537 := by
  unfold tailWord_1873913
  simp only [CollatzResearch.WordTrace]
  refine ⟨68347222060140714705914393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45564814706760476470609595 68347222060140714705914393)
  ·
    refine ⟨51260416545105536029435795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68347222060140714705914393 51260416545105536029435795)
    ·
      refine ⟨76890624817658304044153693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51260416545105536029435795 76890624817658304044153693)
      ·
        refine ⟨28833984306621864016557635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76890624817658304044153693 28833984306621864016557635)
        ·
          refine ⟨43250976459932796024836453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28833984306621864016557635 43250976459932796024836453)
          ·
            refine ⟨8109558086237399254656835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43250976459932796024836453 8109558086237399254656835)
            ·
              refine ⟨12164337129356098881985253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8109558086237399254656835 12164337129356098881985253)
              ·
                refine ⟨2280813211754268540372235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12164337129356098881985253 2280813211754268540372235)
                ·
                  refine ⟨3421219817631402810558353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280813211754268540372235 3421219817631402810558353)
                  ·
                    refine ⟨2565914863223552107918765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3421219817631402810558353 2565914863223552107918765)
                    ·
                      refine ⟨962218073708832040469537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2565914863223552107918765 962218073708832040469537)
                      ·
                        rfl

theorem cell23_1873913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_1873913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873913 prefixEnd_1873913 := by exact prefixLift 1873913
  have htrace : WordTrace (prefixWord ++ tailWord_1873913) baseStart_1873913 baseEnd_1873913 := by
    simpa [prefixWord, tailWord_1873913, baseEnd_1873913] using wordTrace_append hprefix tailTrace_1873913
  have hstable : (prefixWord ++ tailWord_1873913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873913).length < 2 ^ (prefixWord ++ tailWord_1873913).sum := by decide
  have hdescent : baseEnd_1873913 < baseStart_1873913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873919 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_1873919 : Nat := 118140960795 + 1873919 * 2 ^ 59
def prefixEnd_1873919 : Nat := 4983230072969 + 3 ^ 40 * 1873919 * 2
def baseEnd_1873919 : Nat := 962221154592759016994509

theorem tailTrace_1873919 : CollatzResearch.WordTrace tailWord_1873919 prefixEnd_1873919 962221154592759016994509 := by
  unfold tailWord_1873919
  simp only [CollatzResearch.WordTrace]
  refine ⟨68347440898118977730632811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45564960598745985153755207 68347440898118977730632811)
  ·
    refine ⟨102521161347178466595949217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68347440898118977730632811 102521161347178466595949217)
    ·
      refine ⟨76890871010383849946961913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102521161347178466595949217 76890871010383849946961913)
      ·
        refine ⟨57668153257787887460221435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76890871010383849946961913 57668153257787887460221435)
        ·
          refine ⟨86502229886681831190332153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57668153257787887460221435 86502229886681831190332153)
          ·
            refine ⟨64876672415011373392749115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86502229886681831190332153 64876672415011373392749115)
            ·
              refine ⟨97315008622517060089123673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64876672415011373392749115 97315008622517060089123673)
              ·
                refine ⟨72986256466887795066842755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97315008622517060089123673 72986256466887795066842755)
                ·
                  refine ⟨109479384700331692600264133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72986256466887795066842755 109479384700331692600264133)
                  ·
                    refine ⟨20527384631312192362549525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109479384700331692600264133 20527384631312192362549525)
                    ·
                      refine ⟨962221154592759016994509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20527384631312192362549525 962221154592759016994509)
                      ·
                        rfl

theorem cell23_1873919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_1873919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873919 prefixEnd_1873919 := by exact prefixLift 1873919
  have htrace : WordTrace (prefixWord ++ tailWord_1873919) baseStart_1873919 baseEnd_1873919 := by
    simpa [prefixWord, tailWord_1873919, baseEnd_1873919] using wordTrace_append hprefix tailTrace_1873919
  have hstable : (prefixWord ++ tailWord_1873919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873919).length < 2 ^ (prefixWord ++ tailWord_1873919).sum := by decide
  have hdescent : baseEnd_1873919 < baseStart_1873919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873929 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 3, 9]
def baseStart_1873929 : Nat := 118140960795 + 1873929 * 2 ^ 59
def prefixEnd_1873929 : Nat := 4983230072969 + 3 ^ 40 * 1873929 * 2
def baseEnd_1873929 : Nat := 320742096466434659289821

theorem tailTrace_1873929 : CollatzResearch.WordTrace tailWord_1873929 prefixEnd_1873929 320742096466434659289821 := by
  unfold tailWord_1873929
  simp only [CollatzResearch.WordTrace]
  refine ⟨68347805628082749438496841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45565203752055166292331227 68347805628082749438496841)
  ·
    refine ⟨51260854221062062078872631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68347805628082749438496841 51260854221062062078872631)
    ·
      refine ⟨76891281331593093118308947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51260854221062062078872631 76891281331593093118308947)
      ·
        refine ⟨115336921997389639677463421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76891281331593093118308947 115336921997389639677463421)
        ·
          refine ⟨43251345749021114879048783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115336921997389639677463421 43251345749021114879048783)
          ·
            refine ⟨64877018623531672318573175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43251345749021114879048783 64877018623531672318573175)
            ·
              refine ⟨97315527935297508477859763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64877018623531672318573175 97315527935297508477859763)
              ·
                refine ⟨145973291902946262716789645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97315527935297508477859763 145973291902946262716789645)
                ·
                  refine ⟨54739984463604848518796117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145973291902946262716789645 54739984463604848518796117)
                  ·
                    refine ⟨320742096466434659289821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 54739984463604848518796117 320742096466434659289821)
                    ·
                      rfl

theorem cell23_1873929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_1873929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873929 prefixEnd_1873929 := by exact prefixLift 1873929
  have htrace : WordTrace (prefixWord ++ tailWord_1873929) baseStart_1873929 baseEnd_1873929 := by
    simpa [prefixWord, tailWord_1873929, baseEnd_1873929] using wordTrace_append hprefix tailTrace_1873929
  have hstable : (prefixWord ++ tailWord_1873929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873929).length < 2 ^ (prefixWord ++ tailWord_1873929).sum := by decide
  have hdescent : baseEnd_1873929 < baseStart_1873929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873944 : List Nat := [2, 1, 2, 3, 2, 1, 5, 2, 1, 2, 2]
def baseStart_1873944 : Nat := 118140960795 + 1873944 * 2 ^ 59
def prefixEnd_1873944 : Nat := 4983230072969 + 3 ^ 40 * 1873944 * 2
def baseEnd_1873944 : Nat := 962233991609121419181895

theorem tailTrace_1873944 : CollatzResearch.WordTrace tailWord_1873944 prefixEnd_1873944 962233991609121419181895 := by
  unfold tailWord_1873944
  simp only [CollatzResearch.WordTrace]
  refine ⟨34174176361514203500146443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45565568482018938000195257 34174176361514203500146443)
  ·
    refine ⟨51261264542271305250219665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34174176361514203500146443 51261264542271305250219665)
    ·
      refine ⟨38445948406703478937664749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51261264542271305250219665 38445948406703478937664749)
      ·
        refine ⟨14417230652513804601624281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38445948406703478937664749 14417230652513804601624281)
        ·
          refine ⟨10812922989385353451218211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14417230652513804601624281 10812922989385353451218211)
          ·
            refine ⟨16219384484078030176827317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10812922989385353451218211 16219384484078030176827317)
            ·
              refine ⟨1520567295382315329077561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16219384484078030176827317 1520567295382315329077561)
              ·
                refine ⟨1140425471536736496808171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520567295382315329077561 1140425471536736496808171)
                ·
                  refine ⟨1710638207305104745212257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140425471536736496808171 1710638207305104745212257)
                  ·
                    refine ⟨1282978655478828558909193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1710638207305104745212257 1282978655478828558909193)
                    ·
                      refine ⟨962233991609121419181895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282978655478828558909193 962233991609121419181895)
                      ·
                        rfl

theorem cell23_1873944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_1873944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873944 prefixEnd_1873944 := by exact prefixLift 1873944
  have htrace : WordTrace (prefixWord ++ tailWord_1873944) baseStart_1873944 baseEnd_1873944 := by
    simpa [prefixWord, tailWord_1873944, baseEnd_1873944] using wordTrace_append hprefix tailTrace_1873944
  have hstable : (prefixWord ++ tailWord_1873944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873944).length < 2 ^ (prefixWord ++ tailWord_1873944).sum := by decide
  have hdescent : baseEnd_1873944 < baseStart_1873944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873970 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_1873970 : Nat := 118140960795 + 1873970 * 2 ^ 59
def prefixEnd_1873970 : Nat := 4983230072969 + 3 ^ 40 * 1873970 * 2
def baseEnd_1873970 : Nat := 962247342106138317456775

theorem tailTrace_1873970 : CollatzResearch.WordTrace tailWord_1873970 prefixEnd_1873970 962247342106138317456775 := by
  unfold tailWord_1873970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17087325255233553360184841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45566200680622808960492909 17087325255233553360184841)
  ·
    refine ⟨12815493941425165020138631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17087325255233553360184841 12815493941425165020138631)
    ·
      refine ⟨19223240912137747530207947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12815493941425165020138631 19223240912137747530207947)
      ·
        refine ⟨28834861368206621295311921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19223240912137747530207947 28834861368206621295311921)
        ·
          refine ⟨21626146026154965971483941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28834861368206621295311921 21626146026154965971483941)
          ·
            refine ⟨4054902379904056119653239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21626146026154965971483941 4054902379904056119653239)
            ·
              refine ⟨6082353569856084179479859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054902379904056119653239 6082353569856084179479859)
              ·
                refine ⟨9123530354784126269219789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6082353569856084179479859 9123530354784126269219789)
                ·
                  refine ⟨3421323883044047350957421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9123530354784126269219789 3421323883044047350957421)
                  ·
                    refine ⟨1282996456141517756609033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3421323883044047350957421 1282996456141517756609033)
                    ·
                      refine ⟨962247342106138317456775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1282996456141517756609033 962247342106138317456775)
                      ·
                        rfl

theorem cell23_1873970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_1873970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873970 prefixEnd_1873970 := by exact prefixLift 1873970
  have htrace : WordTrace (prefixWord ++ tailWord_1873970) baseStart_1873970 baseEnd_1873970 := by
    simpa [prefixWord, tailWord_1873970, baseEnd_1873970] using wordTrace_append hprefix tailTrace_1873970
  have hstable : (prefixWord ++ tailWord_1873970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873970).length < 2 ^ (prefixWord ++ tailWord_1873970).sum := by decide
  have hdescent : baseEnd_1873970 < baseStart_1873970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873983 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 3, 4, 2]
def baseStart_1873983 : Nat := 118140960795 + 1873983 * 2 ^ 59
def prefixEnd_1873983 : Nat := 4983230072969 + 3 ^ 40 * 1873983 * 2
def baseEnd_1873983 : Nat := 962254017354646766594215

theorem tailTrace_1873983 : CollatzResearch.WordTrace tailWord_1873983 prefixEnd_1873983 962254017354646766594215 := by
  unfold tailWord_1873983
  simp only [CollatzResearch.WordTrace]
  refine ⟨68349775169887116660962603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45566516779924744440641735 68349775169887116660962603)
  ·
    refine ⟨102524662754830674991443905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68349775169887116660962603 102524662754830674991443905)
    ·
      refine ⟨76893497066123006243582929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102524662754830674991443905 76893497066123006243582929)
      ·
        refine ⟨57670122799592254682687197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76893497066123006243582929 57670122799592254682687197)
        ·
          refine ⟨21626296049847095506007699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57670122799592254682687197 21626296049847095506007699)
          ·
            refine ⟨32439444074770643259011549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21626296049847095506007699 32439444074770643259011549)
            ·
              refine ⟨12164791528038991222129331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32439444074770643259011549 12164791528038991222129331)
              ·
                refine ⟨18247187292058486833193997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12164791528038991222129331 18247187292058486833193997)
                ·
                  refine ⟨6842695234521932562447749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18247187292058486833193997 6842695234521932562447749)
                  ·
                    refine ⟨1283005356472862355458953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6842695234521932562447749 1283005356472862355458953)
                    ·
                      refine ⟨962254017354646766594215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283005356472862355458953 962254017354646766594215)
                      ·
                        rfl

theorem cell23_1873983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_1873983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1873983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1873983 prefixEnd_1873983 := by exact prefixLift 1873983
  have htrace : WordTrace (prefixWord ++ tailWord_1873983) baseStart_1873983 baseEnd_1873983 := by
    simpa [prefixWord, tailWord_1873983, baseEnd_1873983] using wordTrace_append hprefix tailTrace_1873983
  have hstable : (prefixWord ++ tailWord_1873983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873983).length < 2 ^ (prefixWord ++ tailWord_1873983).sum := by decide
  have hdescent : baseEnd_1873983 < baseStart_1873983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874068 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1874068 : Nat := 118140960795 + 1874068 * 2 ^ 59
def prefixEnd_1874068 : Nat := 4983230072969 + 3 ^ 40 * 1874068 * 2
def baseEnd_1874068 : Nat := 962297663210278934031325

theorem tailTrace_1874068 : CollatzResearch.WordTrace tailWord_1874068 prefixEnd_1874068 962297663210278934031325 := by
  unfold tailWord_1874068
  simp only [CollatzResearch.WordTrace]
  refine ⟨34176437687289588088903429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45568583583052784118537905 34176437687289588088903429)
  ·
    refine ⟨6408082066366797766669393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34176437687289588088903429 6408082066366797766669393)
    ·
      refine ⟨4806061549775098325002045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6408082066366797766669393 4806061549775098325002045)
      ·
        refine ⟨1802273081165661871875767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4806061549775098325002045 1802273081165661871875767)
        ·
          refine ⟨2703409621748492807813651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802273081165661871875767 2703409621748492807813651)
          ·
            refine ⟨4055114432622739211720477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703409621748492807813651 4055114432622739211720477)
            ·
              refine ⟨1520667912233527204395179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4055114432622739211720477 1520667912233527204395179)
              ·
                refine ⟨2281001868350290806592769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520667912233527204395179 2281001868350290806592769)
                ·
                  refine ⟨1710751401262718104944577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2281001868350290806592769 1710751401262718104944577)
                  ·
                    refine ⟨1283063550947038578708433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1710751401262718104944577 1283063550947038578708433)
                    ·
                      refine ⟨962297663210278934031325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283063550947038578708433 962297663210278934031325)
                      ·
                        rfl

theorem cell23_1874068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1874068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874068 prefixEnd_1874068 := by exact prefixLift 1874068
  have htrace : WordTrace (prefixWord ++ tailWord_1874068) baseStart_1874068 baseEnd_1874068 := by
    simpa [prefixWord, tailWord_1874068, baseEnd_1874068] using wordTrace_append hprefix tailTrace_1874068
  have hstable : (prefixWord ++ tailWord_1874068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874068).length < 2 ^ (prefixWord ++ tailWord_1874068).sum := by decide
  have hdescent : baseEnd_1874068 < baseStart_1874068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874130 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 6]
def baseStart_1874130 : Nat := 118140960795 + 1874130 * 2 ^ 59
def prefixEnd_1874130 : Nat := 4983230072969 + 3 ^ 40 * 1874130 * 2
def baseEnd_1874130 : Nat := 106925499890095299050671

theorem tailTrace_1874130 : CollatzResearch.WordTrace tailWord_1874130 prefixEnd_1874130 106925499890095299050671 := by
  unfold tailWord_1874130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17088784175088640191640961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45570091133569707177709229 17088784175088640191640961)
  ·
    refine ⟨12816588131316480143730721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17088784175088640191640961 12816588131316480143730721)
    ·
      refine ⟨9612441098487360107798041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12816588131316480143730721 9612441098487360107798041)
      ·
        refine ⟨7209330823865520080848531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9612441098487360107798041 7209330823865520080848531)
        ·
          refine ⟨10813996235798280121272797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7209330823865520080848531 10813996235798280121272797)
          ·
            refine ⟨4055248588424355045477299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10813996235798280121272797 4055248588424355045477299)
            ·
              refine ⟨6082872882636532568215949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055248588424355045477299 6082872882636532568215949)
              ·
                refine ⟨2281077330988699713080981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6082872882636532568215949 2281077330988699713080981)
                ·
                  refine ⟨106925499890095299050671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2281077330988699713080981 106925499890095299050671)
                  ·
                    rfl

theorem cell23_1874130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_1874130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874130 prefixEnd_1874130 := by exact prefixLift 1874130
  have htrace : WordTrace (prefixWord ++ tailWord_1874130) baseStart_1874130 baseEnd_1874130 := by
    simpa [prefixWord, tailWord_1874130, baseEnd_1874130] using wordTrace_append hprefix tailTrace_1874130
  have hstable : (prefixWord ++ tailWord_1874130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874130).length < 2 ^ (prefixWord ++ tailWord_1874130).sum := by decide
  have hdescent : baseEnd_1874130 < baseStart_1874130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874190 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_1874190 : Nat := 118140960795 + 1874190 * 2 ^ 59
def prefixEnd_1874190 : Nat := 4983230072969 + 3 ^ 40 * 1874190 * 2
def baseEnd_1874190 : Nat := 320786769283375818901921

theorem tailTrace_1874190 : CollatzResearch.WordTrace tailWord_1874190 prefixEnd_1874190 320786769283375818901921 := by
  unfold tailWord_1874190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544665635017148876718503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45571550053424794009165349 8544665635017148876718503)
  ·
    refine ⟨12816998452525723315077755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8544665635017148876718503 12816998452525723315077755)
    ·
      refine ⟨19225497678788584972616633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12816998452525723315077755 19225497678788584972616633)
      ·
        refine ⟨14419123259091438729462475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19225497678788584972616633 14419123259091438729462475)
        ·
          refine ⟨21628684888637158094193713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14419123259091438729462475 21628684888637158094193713)
          ·
            refine ⟨16221513666477868570645285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21628684888637158094193713 16221513666477868570645285)
            ·
              refine ⟨3041533812464600356995991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16221513666477868570645285 3041533812464600356995991)
              ·
                refine ⟨4562300718696900535493987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041533812464600356995991 4562300718696900535493987)
                ·
                  refine ⟨6843451078045350803240981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4562300718696900535493987 6843451078045350803240981)
                  ·
                    refine ⟨320786769283375818901921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6843451078045350803240981 320786769283375818901921)
                    ·
                      rfl

theorem cell23_1874190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_1874190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874190 prefixEnd_1874190 := by exact prefixLift 1874190
  have htrace : WordTrace (prefixWord ++ tailWord_1874190) baseStart_1874190 baseEnd_1874190 := by
    simpa [prefixWord, tailWord_1874190, baseEnd_1874190] using wordTrace_append hprefix tailTrace_1874190
  have hstable : (prefixWord ++ tailWord_1874190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874190).length < 2 ^ (prefixWord ++ tailWord_1874190).sum := by decide
  have hdescent : baseEnd_1874190 < baseStart_1874190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874197 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_1874197 : Nat := 118140960795 + 1874197 * 2 ^ 59
def prefixEnd_1874197 : Nat := 4983230072969 + 3 ^ 40 * 1874197 * 2
def baseEnd_1874197 : Nat := 962363902214708929318231

theorem tailTrace_1874197 : CollatzResearch.WordTrace tailWord_1874197 prefixEnd_1874197 962363902214708929318231 := by
  unfold tailWord_1874197
  simp only [CollatzResearch.WordTrace]
  refine ⟨68357580391111831209252845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45571720260741220806168563 68357580391111831209252845)
  ·
    refine ⟨25634092646666936703469817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68357580391111831209252845 25634092646666936703469817)
    ·
      refine ⟨19225569485000202527602363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25634092646666936703469817 19225569485000202527602363)
      ·
        refine ⟨28838354227500303791403545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19225569485000202527602363 28838354227500303791403545)
        ·
          refine ⟨21628765670625227843552659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28838354227500303791403545 21628765670625227843552659)
          ·
            refine ⟨32443148505937841765328989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21628765670625227843552659 32443148505937841765328989)
            ·
              refine ⟨12166180689726690661998371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32443148505937841765328989 12166180689726690661998371)
              ·
                refine ⟨18249271034590035992997557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12166180689726690661998371 18249271034590035992997557)
                ·
                  refine ⟨1710869159492815874343521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18249271034590035992997557 1710869159492815874343521)
                  ·
                    refine ⟨1283151869619611905757641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1710869159492815874343521 1283151869619611905757641)
                    ·
                      refine ⟨962363902214708929318231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283151869619611905757641 962363902214708929318231)
                      ·
                        rfl

theorem cell23_1874197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_1874197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874197 prefixEnd_1874197 := by exact prefixLift 1874197
  have htrace : WordTrace (prefixWord ++ tailWord_1874197) baseStart_1874197 baseEnd_1874197 := by
    simpa [prefixWord, tailWord_1874197, baseEnd_1874197] using wordTrace_append hprefix tailTrace_1874197
  have hstable : (prefixWord ++ tailWord_1874197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874197).length < 2 ^ (prefixWord ++ tailWord_1874197).sum := by decide
  have hdescent : baseEnd_1874197 < baseStart_1874197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874200 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1874200 : Nat := 118140960795 + 1874200 * 2 ^ 59
def prefixEnd_1874200 : Nat := 4983230072969 + 3 ^ 40 * 1874200 * 2
def baseEnd_1874200 : Nat := 962365442656672417580717

theorem tailTrace_1874200 : CollatzResearch.WordTrace tailWord_1874200 prefixEnd_1874200 962365442656672417580717 := by
  unfold tailWord_1874200
  simp only [CollatzResearch.WordTrace]
  refine ⟨34178844905050481360806027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45571793206733975147741369 34178844905050481360806027)
  ·
    refine ⟨51268267357575722041209041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34178844905050481360806027 51268267357575722041209041)
    ·
      refine ⟨38451200518181791530906781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51268267357575722041209041 38451200518181791530906781)
      ·
        refine ⟨14419200194318171824090043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38451200518181791530906781 14419200194318171824090043)
        ·
          refine ⟨21628800291477257736135065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14419200194318171824090043 21628800291477257736135065)
          ·
            refine ⟨16221600218607943302101299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21628800291477257736135065 16221600218607943302101299)
            ·
              refine ⟨24332400327911914953151949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16221600218607943302101299 24332400327911914953151949)
              ·
                refine ⟨9124650122966968107431981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24332400327911914953151949 9124650122966968107431981)
                ·
                  refine ⟨3421743796112613040286993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9124650122966968107431981 3421743796112613040286993)
                  ·
                    refine ⟨2566307847084459780215245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3421743796112613040286993 2566307847084459780215245)
                    ·
                      refine ⟨962365442656672417580717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2566307847084459780215245 962365442656672417580717)
                      ·
                        rfl

theorem cell23_1874200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1874200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874200 prefixEnd_1874200 := by exact prefixLift 1874200
  have htrace : WordTrace (prefixWord ++ tailWord_1874200) baseStart_1874200 baseEnd_1874200 := by
    simpa [prefixWord, tailWord_1874200, baseEnd_1874200] using wordTrace_append hprefix tailTrace_1874200
  have hstable : (prefixWord ++ tailWord_1874200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874200).length < 2 ^ (prefixWord ++ tailWord_1874200).sum := by decide
  have hdescent : baseEnd_1874200 < baseStart_1874200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874240 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 2, 7, 2]
def baseStart_1874240 : Nat := 118140960795 + 1874240 * 2 ^ 59
def prefixEnd_1874240 : Nat := 4983230072969 + 3 ^ 40 * 1874240 * 2
def baseEnd_1874240 : Nat := 962385981882852261080533

theorem tailTrace_1874240 : CollatzResearch.WordTrace tailWord_1874240 prefixEnd_1874240 962385981882852261080533 := by
  unfold tailWord_1874240
  simp only [CollatzResearch.WordTrace]
  refine ⟨34179574364978024776534087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45572765819970699702045449 34179574364978024776534087)
  ·
    refine ⟨51269361547467037164801131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34179574364978024776534087 51269361547467037164801131)
    ·
      refine ⟨76904042321200555747201697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51269361547467037164801131 76904042321200555747201697)
      ·
        refine ⟨57678031740900416810401273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76904042321200555747201697 57678031740900416810401273)
        ·
          refine ⟨43258523805675312607800955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57678031740900416810401273 43258523805675312607800955)
          ·
            refine ⟨64887785708512968911701433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43258523805675312607800955 64887785708512968911701433)
            ·
              refine ⟨48665839281384726683776075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64887785708512968911701433 48665839281384726683776075)
              ·
                refine ⟨72998758922077090025664113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48665839281384726683776075 72998758922077090025664113)
                ·
                  refine ⟨54749069191557817519248085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72998758922077090025664113 54749069191557817519248085)
                  ·
                    refine ⟨1283181309177136348107377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54749069191557817519248085 1283181309177136348107377)
                    ·
                      refine ⟨962385981882852261080533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283181309177136348107377 962385981882852261080533)
                      ·
                        rfl

theorem cell23_1874240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_1874240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874240 prefixEnd_1874240 := by exact prefixLift 1874240
  have htrace : WordTrace (prefixWord ++ tailWord_1874240) baseStart_1874240 baseEnd_1874240 := by
    simpa [prefixWord, tailWord_1874240, baseEnd_1874240] using wordTrace_append hprefix tailTrace_1874240
  have hstable : (prefixWord ++ tailWord_1874240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874240).length < 2 ^ (prefixWord ++ tailWord_1874240).sum := by decide
  have hdescent : baseEnd_1874240 < baseStart_1874240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874241 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 2, 4]
def baseStart_1874241 : Nat := 118140960795 + 1874241 * 2 ^ 59
def prefixEnd_1874241 : Nat := 4983230072969 + 3 ^ 40 * 1874241 * 2
def baseEnd_1874241 : Nat := 320795498454502252389343

theorem tailTrace_1874241 : CollatzResearch.WordTrace tailWord_1874241 prefixEnd_1874241 320795498454502252389343 := by
  unfold tailWord_1874241
  simp only [CollatzResearch.WordTrace]
  refine ⟨68359185202952426723854577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45572790135301617815903051 68359185202952426723854577)
  ·
    refine ⟨51269388902214320042890933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68359185202952426723854577 51269388902214320042890933)
    ·
      refine ⟨4806505209582592504021025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51269388902214320042890933 4806505209582592504021025)
      ·
        refine ⟨3604878907186944378015769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4806505209582592504021025 3604878907186944378015769)
        ·
          refine ⟨2703659180390208283511827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3604878907186944378015769 2703659180390208283511827)
          ·
            refine ⟨4055488770585312425267741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703659180390208283511827 4055488770585312425267741)
            ·
              refine ⟨1520808288969492159475403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4055488770585312425267741 1520808288969492159475403)
              ·
                refine ⟨2281212433454238239213105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520808288969492159475403 2281212433454238239213105)
                ·
                  refine ⟨1710909325090678679409829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2281212433454238239213105 1710909325090678679409829)
                  ·
                    refine ⟨320795498454502252389343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1710909325090678679409829 320795498454502252389343)
                    ·
                      rfl

theorem cell23_1874241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_1874241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874241 prefixEnd_1874241 := by exact prefixLift 1874241
  have htrace : WordTrace (prefixWord ++ tailWord_1874241) baseStart_1874241 baseEnd_1874241 := by
    simpa [prefixWord, tailWord_1874241, baseEnd_1874241] using wordTrace_append hprefix tailTrace_1874241
  have hstable : (prefixWord ++ tailWord_1874241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874241).length < 2 ^ (prefixWord ++ tailWord_1874241).sum := by decide
  have hdescent : baseEnd_1874241 < baseStart_1874241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874260 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1874260 : Nat := 118140960795 + 1874260 * 2 ^ 59
def prefixEnd_1874260 : Nat := 4983230072969 + 3 ^ 40 * 1874260 * 2
def baseEnd_1874260 : Nat := 962396251495942182830441

theorem tailTrace_1874260 : CollatzResearch.WordTrace tailWord_1874260 prefixEnd_1874260 962396251495942182830441 := by
  unfold tailWord_1874260
  simp only [CollatzResearch.WordTrace]
  refine ⟨34179939094941796484398117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45573252126589061979197489 34179939094941796484398117)
  ·
    refine ⟨6408738580301586840824647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34179939094941796484398117 6408738580301586840824647)
    ·
      refine ⟨9613107870452380261236971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6408738580301586840824647 9613107870452380261236971)
      ·
        refine ⟨14419661805678570391855457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9613107870452380261236971 14419661805678570391855457)
        ·
          refine ⟨10814746354258927793891593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14419661805678570391855457 10814746354258927793891593)
          ·
            refine ⟨8111059765694195845418695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10814746354258927793891593 8111059765694195845418695)
            ·
              refine ⟨12166589648541293768128043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8111059765694195845418695 12166589648541293768128043)
              ·
                refine ⟨18249884472811940652192065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12166589648541293768128043 18249884472811940652192065)
                ·
                  refine ⟨13687413354608955489144049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18249884472811940652192065 13687413354608955489144049)
                  ·
                    refine ⟨10265560015956716616858037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13687413354608955489144049 10265560015956716616858037)
                    ·
                      refine ⟨962396251495942182830441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10265560015956716616858037 962396251495942182830441)
                      ·
                        rfl

theorem cell23_1874260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1874260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874260 prefixEnd_1874260 := by exact prefixLift 1874260
  have htrace : WordTrace (prefixWord ++ tailWord_1874260) baseStart_1874260 baseEnd_1874260 := by
    simpa [prefixWord, tailWord_1874260, baseEnd_1874260] using wordTrace_append hprefix tailTrace_1874260
  have hstable : (prefixWord ++ tailWord_1874260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874260).length < 2 ^ (prefixWord ++ tailWord_1874260).sum := by decide
  have hdescent : baseEnd_1874260 < baseStart_1874260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874303 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_1874303 : Nat := 118140960795 + 1874303 * 2 ^ 59
def prefixEnd_1874303 : Nat := 4983230072969 + 3 ^ 40 * 1874303 * 2
def baseEnd_1874303 : Nat := 962418331164085514592743

theorem tailTrace_1874303 : CollatzResearch.WordTrace tailWord_1874303 prefixEnd_1874303 962418331164085514592743 := by
  unfold tailWord_1874303
  simp only [CollatzResearch.WordTrace]
  refine ⟨68361446528727811312611563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45574297685818540875074375 68361446528727811312611563)
  ·
    refine ⟨102542169793091716968917345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68361446528727811312611563 102542169793091716968917345)
    ·
      refine ⟨76906627344818787726688009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102542169793091716968917345 76906627344818787726688009)
      ·
        refine ⟨57679970508614090795016007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76906627344818787726688009 57679970508614090795016007)
        ·
          refine ⟨86519955762921136192524011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57679970508614090795016007 86519955762921136192524011)
          ·
            refine ⟨129779933644381704288786017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86519955762921136192524011 129779933644381704288786017)
            ·
              refine ⟨97334950233286278216589513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129779933644381704288786017 97334950233286278216589513)
              ·
                refine ⟨73001212674964708662442135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97334950233286278216589513 73001212674964708662442135)
                ·
                  refine ⟨109501819012447062993663203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73001212674964708662442135 109501819012447062993663203)
                  ·
                    refine ⟨164252728518670594490494805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109501819012447062993663203 164252728518670594490494805)
                    ·
                      refine ⟨962418331164085514592743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 164252728518670594490494805 962418331164085514592743)
                      ·
                        rfl

theorem cell23_1874303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_1874303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874303 prefixEnd_1874303 := by exact prefixLift 1874303
  have htrace : WordTrace (prefixWord ++ tailWord_1874303) baseStart_1874303 baseEnd_1874303 := by
    simpa [prefixWord, tailWord_1874303, baseEnd_1874303] using wordTrace_append hprefix tailTrace_1874303
  have hstable : (prefixWord ++ tailWord_1874303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874303).length < 2 ^ (prefixWord ++ tailWord_1874303).sum := by decide
  have hdescent : baseEnd_1874303 < baseStart_1874303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874360 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_1874360 : Nat := 118140960795 + 1874360 * 2 ^ 59
def prefixEnd_1874360 : Nat := 4983230072969 + 3 ^ 40 * 1874360 * 2
def baseEnd_1874360 : Nat := 962447599561391791579981

theorem tailTrace_1874360 : CollatzResearch.WordTrace tailWord_1874360 prefixEnd_1874360 962447599561391791579981 := by
  unfold tailWord_1874360
  simp only [CollatzResearch.WordTrace]
  refine ⟨34181762744760655023718267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45575683659680873364957689 34181762744760655023718267)
  ·
    refine ⟨51272644117140982535577401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34181762744760655023718267 51272644117140982535577401)
    ·
      refine ⟨38454483087855736901683051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51272644117140982535577401 38454483087855736901683051)
      ·
        refine ⟨57681724631783605352524577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38454483087855736901683051 57681724631783605352524577)
        ·
          refine ⟨43261293473837704014393433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57681724631783605352524577 43261293473837704014393433)
          ·
            refine ⟨32445970105378278010795075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43261293473837704014393433 32445970105378278010795075)
            ·
              refine ⟨48668955158067417016192613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32445970105378278010795075 48668955158067417016192613)
              ·
                refine ⟨9125429092137640690536115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48668955158067417016192613 9125429092137640690536115)
                ·
                  refine ⟨13688143638206461035804173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9125429092137640690536115 13688143638206461035804173)
                  ·
                    refine ⟨5133053864327422888426565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13688143638206461035804173 5133053864327422888426565)
                    ·
                      refine ⟨962447599561391791579981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5133053864327422888426565 962447599561391791579981)
                      ·
                        rfl

theorem cell23_1874360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_1874360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874360 prefixEnd_1874360 := by exact prefixLift 1874360
  have htrace : WordTrace (prefixWord ++ tailWord_1874360) baseStart_1874360 baseEnd_1874360 := by
    simpa [prefixWord, tailWord_1874360, baseEnd_1874360] using wordTrace_append hprefix tailTrace_1874360
  have hstable : (prefixWord ++ tailWord_1874360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874360).length < 2 ^ (prefixWord ++ tailWord_1874360).sum := by decide
  have hdescent : baseEnd_1874360 < baseStart_1874360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874377 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 4]
def baseStart_1874377 : Nat := 118140960795 + 1874377 * 2 ^ 59
def prefixEnd_1874377 : Nat := 4983230072969 + 3 ^ 40 * 1874377 * 2
def baseEnd_1874377 : Nat := 962456328732518225067403

theorem tailTrace_1874377 : CollatzResearch.WordTrace tailWord_1874377 prefixEnd_1874377 962456328732518225067403 := by
  unfold tailWord_1874377
  simp only [CollatzResearch.WordTrace]
  refine ⟨68364145530459721950805385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45576097020306481300536923 68364145530459721950805385)
  ·
    refine ⟨51273109147844791463104039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68364145530459721950805385 51273109147844791463104039)
    ·
      refine ⟨76909663721767187194656059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51273109147844791463104039 76909663721767187194656059)
      ·
        refine ⟨115364495582650780791984089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76909663721767187194656059 115364495582650780791984089)
        ·
          refine ⟨86523371686988085593988067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115364495582650780791984089 86523371686988085593988067)
          ·
            refine ⟨129785057530482128390982101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86523371686988085593988067 129785057530482128390982101)
            ·
              refine ⟨3041837285870674884163643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 129785057530482128390982101 3041837285870674884163643)
              ·
                refine ⟨4562755928806012326245465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041837285870674884163643 4562755928806012326245465)
                ·
                  refine ⟨3422066946604509244684099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4562755928806012326245465 3422066946604509244684099)
                  ·
                    refine ⟨5133100419906763867026149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3422066946604509244684099 5133100419906763867026149)
                    ·
                      refine ⟨962456328732518225067403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5133100419906763867026149 962456328732518225067403)
                      ·
                        rfl

theorem cell23_1874377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_1874377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874377 prefixEnd_1874377 := by exact prefixLift 1874377
  have htrace : WordTrace (prefixWord ++ tailWord_1874377) baseStart_1874377 baseEnd_1874377 := by
    simpa [prefixWord, tailWord_1874377, baseEnd_1874377] using wordTrace_append hprefix tailTrace_1874377
  have hstable : (prefixWord ++ tailWord_1874377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874377).length < 2 ^ (prefixWord ++ tailWord_1874377).sum := by decide
  have hdescent : baseEnd_1874377 < baseStart_1874377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874400 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 8]
def baseStart_1874400 : Nat := 118140960795 + 1874400 * 2 ^ 59
def prefixEnd_1874400 : Nat := 4983230072969 + 3 ^ 40 * 1874400 * 2
def baseEnd_1874400 : Nat := 106940904309730181675533

theorem tailTrace_1874400 : CollatzResearch.WordTrace tailWord_1874400 prefixEnd_1874400 106940904309730181675533 := by
  unfold tailWord_1874400
  simp only [CollatzResearch.WordTrace]
  refine ⟨34182492204688198439446327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45576656272917597919261769 34182492204688198439446327)
  ·
    refine ⟨51273738307032297659169491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34182492204688198439446327 51273738307032297659169491)
    ·
      refine ⟨76910607460548446488754237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51273738307032297659169491 76910607460548446488754237)
      ·
        refine ⟨28841477797705667433282839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76910607460548446488754237 28841477797705667433282839)
        ·
          refine ⟨43262216696558501149924259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28841477797705667433282839 43262216696558501149924259)
          ·
            refine ⟨64893325044837751724886389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43262216696558501149924259 64893325044837751724886389)
            ·
              refine ⟨6083749222953539224208099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64893325044837751724886389 6083749222953539224208099)
              ·
                refine ⟨9125623834430308836312149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083749222953539224208099 9125623834430308836312149)
                ·
                  refine ⟨106940904309730181675533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9125623834430308836312149 106940904309730181675533)
                  ·
                    rfl

theorem cell23_1874400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 8].length) (baseStart_1874400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874400 prefixEnd_1874400 := by exact prefixLift 1874400
  have htrace : WordTrace (prefixWord ++ tailWord_1874400) baseStart_1874400 baseEnd_1874400 := by
    simpa [prefixWord, tailWord_1874400, baseEnd_1874400] using wordTrace_append hprefix tailTrace_1874400
  have hstable : (prefixWord ++ tailWord_1874400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874400).length < 2 ^ (prefixWord ++ tailWord_1874400).sum := by decide
  have hdescent : baseEnd_1874400 < baseStart_1874400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874455 : List Nat := [1, 1, 3, 6, 1, 1, 3, 2, 1, 4]
def baseStart_1874455 : Nat := 118140960795 + 1874455 * 2 ^ 59
def prefixEnd_1874455 : Nat := 4983230072969 + 3 ^ 40 * 1874455 * 2
def baseEnd_1874455 : Nat := 320832126741189639964015

theorem tailTrace_1874455 : CollatzResearch.WordTrace tailWord_1874455 prefixEnd_1874455 320832126741189639964015 := by
  unfold tailWord_1874455
  simp only [CollatzResearch.WordTrace]
  refine ⟨68366990424177141272144819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45577993616118094181429879 68366990424177141272144819)
  ·
    refine ⟨102550485636265711908217229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68366990424177141272144819 102550485636265711908217229)
    ·
      refine ⟨38456432113599641965581461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102550485636265711908217229 38456432113599641965581461)
      ·
        refine ⟨1802645255324983217136631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38456432113599641965581461 1802645255324983217136631)
        ·
          refine ⟨2703967882987474825704947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802645255324983217136631 2703967882987474825704947)
          ·
            refine ⟨4055951824481212238557421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703967882987474825704947 4055951824481212238557421)
            ·
              refine ⟨1520981934180454589459033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4055951824481212238557421 1520981934180454589459033)
              ·
                refine ⟨1140736450635340942094275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520981934180454589459033 1140736450635340942094275)
                ·
                  refine ⟨1711104675953011413141413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140736450635340942094275 1711104675953011413141413)
                  ·
                    refine ⟨320832126741189639964015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1711104675953011413141413 320832126741189639964015)
                    ·
                      rfl

theorem cell23_1874455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_1874455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874455 prefixEnd_1874455 := by exact prefixLift 1874455
  have htrace : WordTrace (prefixWord ++ tailWord_1874455) baseStart_1874455 baseEnd_1874455 := by
    simpa [prefixWord, tailWord_1874455, baseEnd_1874455] using wordTrace_append hprefix tailTrace_1874455
  have hstable : (prefixWord ++ tailWord_1874455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874455).length < 2 ^ (prefixWord ++ tailWord_1874455).sum := by decide
  have hdescent : baseEnd_1874455 < baseStart_1874455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874461 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1874461 : Nat := 118140960795 + 1874461 * 2 ^ 59
def prefixEnd_1874461 : Nat := 4983230072969 + 3 ^ 40 * 1874461 * 2
def baseEnd_1874461 : Nat := 962499461107495896417017

theorem tailTrace_1874461 : CollatzResearch.WordTrace tailWord_1874461 prefixEnd_1874461 962499461107495896417017 := by
  unfold tailWord_1874461
  simp only [CollatzResearch.WordTrace]
  refine ⟨68367209262155404296863237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45578139508103602864575491 68367209262155404296863237)
  ·
    refine ⟨12818851736654138305661857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68367209262155404296863237 12818851736654138305661857)
    ·
      refine ⟨9614138802490603729246393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12818851736654138305661857 9614138802490603729246393)
      ·
        refine ⟨7210604101867952796934795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9614138802490603729246393 7210604101867952796934795)
        ·
          refine ⟨10815906152801929195402193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7210604101867952796934795 10815906152801929195402193)
          ·
            refine ⟨8111929614601446896551645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10815906152801929195402193 8111929614601446896551645)
            ·
              refine ⟨3041973605475542586206867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8111929614601446896551645 3041973605475542586206867)
              ·
                refine ⟨4562960408213313879310301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041973605475542586206867 4562960408213313879310301)
                ·
                  refine ⟨1711110153079992704741363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4562960408213313879310301 1711110153079992704741363)
                  ·
                    refine ⟨2566665229619989057112045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1711110153079992704741363 2566665229619989057112045)
                    ·
                      refine ⟨962499461107495896417017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2566665229619989057112045 962499461107495896417017)
                      ·
                        rfl

theorem cell23_1874461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1874461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874461 prefixEnd_1874461 := by exact prefixLift 1874461
  have htrace : WordTrace (prefixWord ++ tailWord_1874461) baseStart_1874461 baseEnd_1874461 := by
    simpa [prefixWord, tailWord_1874461, baseEnd_1874461] using wordTrace_append hprefix tailTrace_1874461
  have hstable : (prefixWord ++ tailWord_1874461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874461).length < 2 ^ (prefixWord ++ tailWord_1874461).sum := by decide
  have hdescent : baseEnd_1874461 < baseStart_1874461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874468 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 6]
def baseStart_1874468 : Nat := 118140960795 + 1874468 * 2 ^ 59
def prefixEnd_1874468 : Nat := 4983230072969 + 3 ^ 40 * 1874468 * 2
def baseEnd_1874468 : Nat := 106944783941341929892165

theorem tailTrace_1874468 : CollatzResearch.WordTrace tailWord_1874468 prefixEnd_1874468 106944783941341929892165 := by
  unfold tailWord_1874468
  simp only [CollatzResearch.WordTrace]
  refine ⟨34183732286565022246184029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45578309715420029661578705 34183732286565022246184029)
  ·
    refine ⟨12818899607461883342319011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34183732286565022246184029 12818899607461883342319011)
    ·
      refine ⟨19228349411192825013478517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12818899607461883342319011 19228349411192825013478517)
      ·
        refine ⟨1802657757299327345013611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19228349411192825013478517 1802657757299327345013611)
        ·
          refine ⟨2703986635948991017520417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802657757299327345013611 2703986635948991017520417)
          ·
            refine ⟨2027989976961743263140313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2703986635948991017520417 2027989976961743263140313)
            ·
              refine ⟨1520992482721307447355235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027989976961743263140313 1520992482721307447355235)
              ·
                refine ⟨2281488724081961171032853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520992482721307447355235 2281488724081961171032853)
                ·
                  refine ⟨106944783941341929892165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2281488724081961171032853 106944783941341929892165)
                  ·
                    rfl

theorem cell23_1874468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_1874468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874468 prefixEnd_1874468 := by exact prefixLift 1874468
  have htrace : WordTrace (prefixWord ++ tailWord_1874468) baseStart_1874468 baseEnd_1874468 := by
    simpa [prefixWord, tailWord_1874468, baseEnd_1874468] using wordTrace_append hprefix tailTrace_1874468
  have hstable : (prefixWord ++ tailWord_1874468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874468).length < 2 ^ (prefixWord ++ tailWord_1874468).sum := by decide
  have hdescent : baseEnd_1874468 < baseStart_1874468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874501 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 1, 1, 4]
def baseStart_1874501 : Nat := 118140960795 + 1874501 * 2 ^ 59
def prefixEnd_1874501 : Nat := 4983230072969 + 3 ^ 40 * 1874501 * 2
def baseEnd_1874501 : Nat := 962520000333675739916833

theorem tailTrace_1874501 : CollatzResearch.WordTrace tailWord_1874501 prefixEnd_1874501 962520000333675739916833 := by
  unfold tailWord_1874501
  simp only [CollatzResearch.WordTrace]
  refine ⟨68368668182010491128319357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45579112121340327418879571 68368668182010491128319357)
  ·
    refine ⟨25638250568253934173119759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68368668182010491128319357 25638250568253934173119759)
    ·
      refine ⟨38457375852380901259679639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25638250568253934173119759 38457375852380901259679639)
      ·
        refine ⟨57686063778571351889519459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38457375852380901259679639 57686063778571351889519459)
        ·
          refine ⟨86529095667857027834279189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57686063778571351889519459 86529095667857027834279189)
          ·
            refine ⟨4056051359430798179731837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86529095667857027834279189 4056051359430798179731837)
            ·
              refine ⟨1521019259786549317399439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4056051359430798179731837 1521019259786549317399439)
              ·
                refine ⟨2281528889679823976099159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521019259786549317399439 2281528889679823976099159)
                ·
                  refine ⟨3422293334519735964148739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281528889679823976099159 3422293334519735964148739)
                  ·
                    refine ⟨5133440001779603946223109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3422293334519735964148739 5133440001779603946223109)
                    ·
                      refine ⟨962520000333675739916833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5133440001779603946223109 962520000333675739916833)
                      ·
                        rfl

theorem cell23_1874501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_1874501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874501 prefixEnd_1874501 := by exact prefixLift 1874501
  have htrace : WordTrace (prefixWord ++ tailWord_1874501) baseStart_1874501 baseEnd_1874501 := by
    simpa [prefixWord, tailWord_1874501, baseEnd_1874501] using wordTrace_append hprefix tailTrace_1874501
  have hstable : (prefixWord ++ tailWord_1874501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874501).length < 2 ^ (prefixWord ++ tailWord_1874501).sum := by decide
  have hdescent : baseEnd_1874501 < baseStart_1874501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874504 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_1874504 : Nat := 118140960795 + 1874504 * 2 ^ 59
def prefixEnd_1874504 : Nat := 4983230072969 + 3 ^ 40 * 1874504 * 2
def baseEnd_1874504 : Nat := 962521540775639228179319

theorem tailTrace_1874504 : CollatzResearch.WordTrace tailWord_1874504 prefixEnd_1874504 962521540775639228179319 := by
  unfold tailWord_1874504
  simp only [CollatzResearch.WordTrace]
  refine ⟨34184388800499811320339283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45579185067333081760452377 34184388800499811320339283)
  ·
    refine ⟨51276583200749716980508925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34184388800499811320339283 51276583200749716980508925)
    ·
      refine ⟨19228718700281143867690847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51276583200749716980508925 19228718700281143867690847)
      ·
        refine ⟨28843078050421715801536271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19228718700281143867690847 28843078050421715801536271)
        ·
          refine ⟨43264617075632573702304407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28843078050421715801536271 43264617075632573702304407)
          ·
            refine ⟨64896925613448860553456611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43264617075632573702304407 64896925613448860553456611)
            ·
              refine ⟨97345388420173290830184917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64896925613448860553456611 97345388420173290830184917)
              ·
                refine ⟨2281532541097811503832459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97345388420173290830184917 2281532541097811503832459)
                ·
                  refine ⟨3422298811646717255748689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281532541097811503832459 3422298811646717255748689)
                  ·
                    refine ⟨2566724108735037941811517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3422298811646717255748689 2566724108735037941811517)
                    ·
                      refine ⟨962521540775639228179319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2566724108735037941811517 962521540775639228179319)
                      ·
                        rfl

theorem cell23_1874504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_1874504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874504 prefixEnd_1874504 := by exact prefixLift 1874504
  have htrace : WordTrace (prefixWord ++ tailWord_1874504) baseStart_1874504 baseEnd_1874504 := by
    simpa [prefixWord, tailWord_1874504, baseEnd_1874504] using wordTrace_append hprefix tailTrace_1874504
  have hstable : (prefixWord ++ tailWord_1874504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874504).length < 2 ^ (prefixWord ++ tailWord_1874504).sum := by decide
  have hdescent : baseEnd_1874504 < baseStart_1874504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874567 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 4, 6]
def baseStart_1874567 : Nat := 118140960795 + 1874567 * 2 ^ 59
def prefixEnd_1874567 : Nat := 4983230072969 + 3 ^ 40 * 1874567 * 2
def baseEnd_1874567 : Nat := 320851296685624160563843

theorem tailTrace_1874567 : CollatzResearch.WordTrace tailWord_1874567 prefixEnd_1874567 320851296685624160563843 := by
  unfold tailWord_1874567
  simp only [CollatzResearch.WordTrace]
  refine ⟨68371075399771384400221955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45580716933180922933481303 68371075399771384400221955)
  ·
    refine ⟨102556613099657076600332933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68371075399771384400221955 102556613099657076600332933)
    ·
      refine ⟨19229364956185701862562425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102556613099657076600332933 19229364956185701862562425)
      ·
        refine ⟨14422023717139276396921819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19229364956185701862562425 14422023717139276396921819)
        ·
          refine ⟨21633035575708914595382729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14422023717139276396921819 21633035575708914595382729)
          ·
            refine ⟨16224776681781685946537047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21633035575708914595382729 16224776681781685946537047)
            ·
              refine ⟨24337165022672528919805571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16224776681781685946537047 24337165022672528919805571)
              ·
                refine ⟨36505747534008793379708357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24337165022672528919805571 36505747534008793379708357)
                ·
                  refine ⟨6844827662626648758695317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36505747534008793379708357 6844827662626648758695317)
                  ·
                    refine ⟨320851296685624160563843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6844827662626648758695317 320851296685624160563843)
                    ·
                      rfl

theorem cell23_1874567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_1874567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874567 prefixEnd_1874567 := by exact prefixLift 1874567
  have htrace : WordTrace (prefixWord ++ tailWord_1874567) baseStart_1874567 baseEnd_1874567 := by
    simpa [prefixWord, tailWord_1874567, baseEnd_1874567] using wordTrace_append hprefix tailTrace_1874567
  have hstable : (prefixWord ++ tailWord_1874567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874567).length < 2 ^ (prefixWord ++ tailWord_1874567).sum := by decide
  have hdescent : baseEnd_1874567 < baseStart_1874567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874661 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_1874661 : Nat := 118140960795 + 1874661 * 2 ^ 59
def prefixEnd_1874661 : Nat := 4983230072969 + 3 ^ 40 * 1874661 * 2
def baseEnd_1874661 : Nat := 320867385746131704638699

theorem tailTrace_1874661 : CollatzResearch.WordTrace tailWord_1874661 prefixEnd_1874661 320867385746131704638699 := by
  unfold tailWord_1874661
  simp only [CollatzResearch.WordTrace]
  refine ⟨68374503861430838454143837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45583002574287225636095891 68374503861430838454143837)
  ·
    refine ⟨25640438948036564420303939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68374503861430838454143837 25640438948036564420303939)
    ·
      refine ⟨38460658422054846630455909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25640438948036564420303939 38460658422054846630455909)
      ·
        refine ⟨7211373454135283743210483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38460658422054846630455909 7211373454135283743210483)
        ·
          refine ⟨10817060181202925614815725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7211373454135283743210483 10817060181202925614815725)
          ·
            refine ⟨4056397567951097105555897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10817060181202925614815725 4056397567951097105555897)
            ·
              refine ⟨3042298175963322829166923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4056397567951097105555897 3042298175963322829166923)
              ·
                refine ⟨4563447263944984243750385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042298175963322829166923 4563447263944984243750385)
                ·
                  refine ⟨3422585447958738182812789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4563447263944984243750385 3422585447958738182812789)
                  ·
                    refine ⟨320867385746131704638699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3422585447958738182812789 320867385746131704638699)
                    ·
                      rfl

theorem cell23_1874661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_1874661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874661 prefixEnd_1874661 := by exact prefixLift 1874661
  have htrace : WordTrace (prefixWord ++ tailWord_1874661) baseStart_1874661 baseEnd_1874661 := by
    simpa [prefixWord, tailWord_1874661, baseEnd_1874661] using wordTrace_append hprefix tailTrace_1874661
  have hstable : (prefixWord ++ tailWord_1874661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874661).length < 2 ^ (prefixWord ++ tailWord_1874661).sum := by decide
  have hdescent : baseEnd_1874661 < baseStart_1874661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874788 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_1874788 : Nat := 118140960795 + 1874788 * 2 ^ 59
def prefixEnd_1874788 : Nat := 4983230072969 + 3 ^ 40 * 1874788 * 2
def baseEnd_1874788 : Nat := 962667369281516117028013

theorem tailTrace_1874788 : CollatzResearch.WordTrace tailWord_1874788 prefixEnd_1874788 962667369281516117028013 := by
  unfold tailWord_1874788
  simp only [CollatzResearch.WordTrace]
  refine ⟨34189567965985369572008509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45586090621313826096011345 34189567965985369572008509)
  ·
    refine ⟨12821087987244513589503191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34189567965985369572008509 12821087987244513589503191)
    ·
      refine ⟨19231631980866770384254787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12821087987244513589503191 19231631980866770384254787)
      ·
        refine ⟨28847447971300155576382181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19231631980866770384254787 28847447971300155576382181)
        ·
          refine ⟨5408896494618779170571659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28847447971300155576382181 5408896494618779170571659)
          ·
            refine ⟨8113344741928168755857489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408896494618779170571659 8113344741928168755857489)
            ·
              refine ⟨6085008556446126566893117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8113344741928168755857489 6085008556446126566893117)
              ·
                refine ⟨2281878208667297462584919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6085008556446126566893117 2281878208667297462584919)
                ·
                  refine ⟨3422817313000946193877379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281878208667297462584919 3422817313000946193877379)
                  ·
                    refine ⟨5134225969501419290816069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3422817313000946193877379 5134225969501419290816069)
                    ·
                      refine ⟨962667369281516117028013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5134225969501419290816069 962667369281516117028013)
                      ·
                        rfl

theorem cell23_1874788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_1874788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874788 prefixEnd_1874788 := by exact prefixLift 1874788
  have htrace : WordTrace (prefixWord ++ tailWord_1874788) baseStart_1874788 baseEnd_1874788 := by
    simpa [prefixWord, tailWord_1874788, baseEnd_1874788] using wordTrace_append hprefix tailTrace_1874788
  have hstable : (prefixWord ++ tailWord_1874788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874788).length < 2 ^ (prefixWord ++ tailWord_1874788).sum := by decide
  have hdescent : baseEnd_1874788 < baseStart_1874788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874791 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1874791 : Nat := 118140960795 + 1874791 * 2 ^ 59
def prefixEnd_1874791 : Nat := 4983230072969 + 3 ^ 40 * 1874791 * 2
def baseEnd_1874791 : Nat := 962668909723479605290499

theorem tailTrace_1874791 : CollatzResearch.WordTrace tailWord_1874791 prefixEnd_1874791 962668909723479605290499 := by
  unfold tailWord_1874791
  simp only [CollatzResearch.WordTrace]
  refine ⟨68379245350959870656376227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45586163567306580437584151 68379245350959870656376227)
  ·
    refine ⟨102568868026439805984564341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68379245350959870656376227 102568868026439805984564341)
    ·
      refine ⟨9615831377478731811052907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102568868026439805984564341 9615831377478731811052907)
      ·
        refine ⟨14423747066218097716579361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9615831377478731811052907 14423747066218097716579361)
        ·
          refine ⟨10817810299663573287434521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14423747066218097716579361 10817810299663573287434521)
          ·
            refine ⟨8113357724747679965575891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10817810299663573287434521 8113357724747679965575891)
            ·
              refine ⟨12170036587121519948363837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8113357724747679965575891 12170036587121519948363837)
              ·
                refine ⟨4563763720170569980636439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12170036587121519948363837 4563763720170569980636439)
                ·
                  refine ⟨6845645580255854970954659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563763720170569980636439 6845645580255854970954659)
                  ·
                    refine ⟨10268468370383782456431989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6845645580255854970954659 10268468370383782456431989)
                    ·
                      refine ⟨962668909723479605290499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10268468370383782456431989 962668909723479605290499)
                      ·
                        rfl

theorem cell23_1874791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1874791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874791 prefixEnd_1874791 := by exact prefixLift 1874791
  have htrace : WordTrace (prefixWord ++ tailWord_1874791) baseStart_1874791 baseEnd_1874791 := by
    simpa [prefixWord, tailWord_1874791, baseEnd_1874791] using wordTrace_append hprefix tailTrace_1874791
  have hstable : (prefixWord ++ tailWord_1874791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874791).length < 2 ^ (prefixWord ++ tailWord_1874791).sum := by decide
  have hdescent : baseEnd_1874791 < baseStart_1874791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874825 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 3]
def baseStart_1874825 : Nat := 118140960795 + 1874825 * 2 ^ 59
def prefixEnd_1874825 : Nat := 4983230072969 + 3 ^ 40 * 1874825 * 2
def baseEnd_1874825 : Nat := 962686368065732472265343

theorem tailTrace_1874825 : CollatzResearch.WordTrace tailWord_1874825 prefixEnd_1874825 962686368065732472265343 := by
  unfold tailWord_1874825
  simp only [CollatzResearch.WordTrace]
  refine ⟨68380485432836694463113929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45586990288557796308742619 68380485432836694463113929)
  ·
    refine ⟨51285364074627520847335447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68380485432836694463113929 51285364074627520847335447)
    ·
      refine ⟨76928046111941281271003171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51285364074627520847335447 76928046111941281271003171)
      ·
        refine ⟨115392069167911921906504757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76928046111941281271003171 115392069167911921906504757)
        ·
          refine ⟨10818006484491742678734821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115392069167911921906504757 10818006484491742678734821)
          ·
            refine ⟨2028376215842201752262779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10818006484491742678734821 2028376215842201752262779)
            ·
              refine ⟨3042564323763302628394169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028376215842201752262779 3042564323763302628394169)
              ·
                refine ⟨2281923242822476971295627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3042564323763302628394169 2281923242822476971295627)
                ·
                  refine ⟨3422884864233715456943441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281923242822476971295627 3422884864233715456943441)
                  ·
                    refine ⟨2567163648175286592707581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3422884864233715456943441 2567163648175286592707581)
                    ·
                      refine ⟨962686368065732472265343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567163648175286592707581 962686368065732472265343)
                      ·
                        rfl

theorem cell23_1874825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 3].length) (baseStart_1874825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874825 prefixEnd_1874825 := by exact prefixLift 1874825
  have htrace : WordTrace (prefixWord ++ tailWord_1874825) baseStart_1874825 baseEnd_1874825 := by
    simpa [prefixWord, tailWord_1874825, baseEnd_1874825] using wordTrace_append hprefix tailTrace_1874825
  have hstable : (prefixWord ++ tailWord_1874825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874825).length < 2 ^ (prefixWord ++ tailWord_1874825).sum := by decide
  have hdescent : baseEnd_1874825 < baseStart_1874825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874842 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3]
def baseStart_1874842 : Nat := 118140960795 + 1874842 * 2 ^ 59
def prefixEnd_1874842 : Nat := 4983230072969 + 3 ^ 40 * 1874842 * 2
def baseEnd_1874842 : Nat := 962695097236858905752765

theorem tailTrace_1874842 : CollatzResearch.WordTrace tailWord_1874842 prefixEnd_1874842 962695097236858905752765 := by
  unfold tailWord_1874842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17095276368443776591620695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45587403649183404244321853 17095276368443776591620695)
  ·
    refine ⟨25642914552665664887431043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17095276368443776591620695 25642914552665664887431043)
    ·
      refine ⟨38464371828998497331146565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25642914552665664887431043 38464371828998497331146565)
      ·
        refine ⟨7212069717937218249589981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38464371828998497331146565 7212069717937218249589981)
        ·
          refine ⟨2704526144226456843596243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7212069717937218249589981 2704526144226456843596243)
          ·
            refine ⟨4056789216339685265394365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704526144226456843596243 4056789216339685265394365)
            ·
              refine ⟨1521295956127381974522887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4056789216339685265394365 1521295956127381974522887)
              ·
                refine ⟨2281943934191072961784331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521295956127381974522887 2281943934191072961784331)
                ·
                  refine ⟨3422915901286609442676497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281943934191072961784331 3422915901286609442676497)
                  ·
                    refine ⟨2567186925964957082007373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3422915901286609442676497 2567186925964957082007373)
                    ·
                      refine ⟨962695097236858905752765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567186925964957082007373 962695097236858905752765)
                      ·
                        rfl

theorem cell23_1874842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_1874842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874842 prefixEnd_1874842 := by exact prefixLift 1874842
  have htrace : WordTrace (prefixWord ++ tailWord_1874842) baseStart_1874842 baseEnd_1874842 := by
    simpa [prefixWord, tailWord_1874842, baseEnd_1874842] using wordTrace_append hprefix tailTrace_1874842
  have hstable : (prefixWord ++ tailWord_1874842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874842).length < 2 ^ (prefixWord ++ tailWord_1874842).sum := by decide
  have hdescent : baseEnd_1874842 < baseStart_1874842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874893 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1874893 : Nat := 118140960795 + 1874893 * 2 ^ 59
def prefixEnd_1874893 : Nat := 4983230072969 + 3 ^ 40 * 1874893 * 2
def baseEnd_1874893 : Nat := 962721284750238206215031

theorem tailTrace_1874893 : CollatzResearch.WordTrace tailWord_1874893 prefixEnd_1874893 962721284750238206215031 := by
  unfold tailWord_1874893
  simp only [CollatzResearch.WordTrace]
  refine ⟨68382965596590342076589333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45588643731060228051059555 68382965596590342076589333)
  ·
    refine ⟨3205451512340172284840125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68382965596590342076589333 3205451512340172284840125)
    ·
      refine ⟨1202044317127564606815047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3205451512340172284840125 1202044317127564606815047)
      ·
        refine ⟨1803066475691346910222571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202044317127564606815047 1803066475691346910222571)
        ·
          refine ⟨2704599713537020365333857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803066475691346910222571 2704599713537020365333857)
          ·
            refine ⟨2028449785152765274000393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704599713537020365333857 2028449785152765274000393)
            ·
              refine ⟨1521337338864573955500295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2028449785152765274000393 1521337338864573955500295)
              ·
                refine ⟨2282006008296860933250443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521337338864573955500295 2282006008296860933250443)
                ·
                  refine ⟨3423009012445291399875665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282006008296860933250443 3423009012445291399875665)
                  ·
                    refine ⟨2567256759333968549906749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3423009012445291399875665 2567256759333968549906749)
                    ·
                      refine ⟨962721284750238206215031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567256759333968549906749 962721284750238206215031)
                      ·
                        rfl

theorem cell23_1874893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1874893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874893 prefixEnd_1874893 := by exact prefixLift 1874893
  have htrace : WordTrace (prefixWord ++ tailWord_1874893) baseStart_1874893 baseEnd_1874893 := by
    simpa [prefixWord, tailWord_1874893, baseEnd_1874893] using wordTrace_append hprefix tailTrace_1874893
  have hstable : (prefixWord ++ tailWord_1874893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874893).length < 2 ^ (prefixWord ++ tailWord_1874893).sum := by decide
  have hdescent : baseEnd_1874893 < baseStart_1874893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874929 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 2, 2, 2]
def baseStart_1874929 : Nat := 118140960795 + 1874929 * 2 ^ 59
def prefixEnd_1874929 : Nat := 4983230072969 + 3 ^ 40 * 1874929 * 2
def baseEnd_1874929 : Nat := 962739770053800065364865

theorem tailTrace_1874929 : CollatzResearch.WordTrace tailWord_1874929 prefixEnd_1874929 962739770053800065364865 := by
  unfold tailWord_1874929
  simp only [CollatzResearch.WordTrace]
  refine ⟨68384278624459920224899841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45589519082973280149933227 68384278624459920224899841)
  ·
    refine ⟨51288208968344940168674881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68384278624459920224899841 51288208968344940168674881)
    ·
      refine ⟨38466156726258705126506161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51288208968344940168674881 38466156726258705126506161)
      ·
        refine ⟨28849617544694028844879621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38466156726258705126506161 28849617544694028844879621)
        ·
          refine ⟨5409303289630130408414929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28849617544694028844879621 5409303289630130408414929)
          ·
            refine ⟨4056977467222597806311197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5409303289630130408414929 4056977467222597806311197)
            ·
              refine ⟨1521366550208474177366699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4056977467222597806311197 1521366550208474177366699)
              ·
                refine ⟨2282049825312711266050049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521366550208474177366699 2282049825312711266050049)
                ·
                  refine ⟨1711537368984533449537537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2282049825312711266050049 1711537368984533449537537)
                  ·
                    refine ⟨1283653026738400087153153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1711537368984533449537537 1283653026738400087153153)
                    ·
                      refine ⟨962739770053800065364865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283653026738400087153153 962739770053800065364865)
                      ·
                        rfl

theorem cell23_1874929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_1874929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874929 prefixEnd_1874929 := by exact prefixLift 1874929
  have htrace : WordTrace (prefixWord ++ tailWord_1874929) baseStart_1874929 baseEnd_1874929 := by
    simpa [prefixWord, tailWord_1874929, baseEnd_1874929] using wordTrace_append hprefix tailTrace_1874929
  have hstable : (prefixWord ++ tailWord_1874929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874929).length < 2 ^ (prefixWord ++ tailWord_1874929).sum := by decide
  have hdescent : baseEnd_1874929 < baseStart_1874929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874938 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2]
def baseStart_1874938 : Nat := 118140960795 + 1874938 * 2 ^ 59
def prefixEnd_1874938 : Nat := 4983230072969 + 3 ^ 40 * 1874938 * 2
def baseEnd_1874938 : Nat := 962744391379690530152323

theorem tailTrace_1874938 : CollatzResearch.WordTrace tailWord_1874938 prefixEnd_1874938 962744391379690530152323 := by
  unfold tailWord_1874938
  simp only [CollatzResearch.WordTrace]
  refine ⟨17096151720356828690494367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45589737920951543174651645 17096151720356828690494367)
  ·
    refine ⟨25644227580535243035741551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17096151720356828690494367 25644227580535243035741551)
    ·
      refine ⟨38466341370802864553612327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25644227580535243035741551 38466341370802864553612327)
      ·
        refine ⟨57699512056204296830418491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38466341370802864553612327 57699512056204296830418491)
        ·
          refine ⟨86549268084306445245627737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57699512056204296830418491 86549268084306445245627737)
          ·
            refine ⟨64911951063229833934220803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86549268084306445245627737 64911951063229833934220803)
            ·
              refine ⟨97367926594844750901331205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64911951063229833934220803 97367926594844750901331205)
              ·
                refine ⟨18256486236533390793999601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97367926594844750901331205 18256486236533390793999601)
                ·
                  refine ⟨13692364677400043095499701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18256486236533390793999601 13692364677400043095499701)
                  ·
                    refine ⟨1283659188506254040203097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13692364677400043095499701 1283659188506254040203097)
                    ·
                      refine ⟨962744391379690530152323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283659188506254040203097 962744391379690530152323)
                      ·
                        rfl

theorem cell23_1874938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_1874938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874938 prefixEnd_1874938 := by exact prefixLift 1874938
  have htrace : WordTrace (prefixWord ++ tailWord_1874938) baseStart_1874938 baseEnd_1874938 := by
    simpa [prefixWord, tailWord_1874938, baseEnd_1874938] using wordTrace_append hprefix tailTrace_1874938
  have hstable : (prefixWord ++ tailWord_1874938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874938).length < 2 ^ (prefixWord ++ tailWord_1874938).sum := by decide
  have hdescent : baseEnd_1874938 < baseStart_1874938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874941 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_1874941 : Nat := 118140960795 + 1874941 * 2 ^ 59
def prefixEnd_1874941 : Nat := 4983230072969 + 3 ^ 40 * 1874941 * 2
def baseEnd_1874941 : Nat := 962745931821654018414809

theorem tailTrace_1874941 : CollatzResearch.WordTrace tailWord_1874941 prefixEnd_1874941 962745931821654018414809 := by
  unfold tailWord_1874941
  simp only [CollatzResearch.WordTrace]
  refine ⟨68384716300416446274336677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45589810866944297516224451 68384716300416446274336677)
  ·
    refine ⟨12822134306328083676438127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68384716300416446274336677 12822134306328083676438127)
    ·
      refine ⟨19233201459492125514657191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12822134306328083676438127 19233201459492125514657191)
      ·
        refine ⟨28849802189238188271985787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19233201459492125514657191 28849802189238188271985787)
        ·
          refine ⟨43274703283857282407978681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28849802189238188271985787 43274703283857282407978681)
          ·
            refine ⟨32456027462892961805984011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43274703283857282407978681 32456027462892961805984011)
            ·
              refine ⟨48684041194339442708976017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32456027462892961805984011 48684041194339442708976017)
              ·
                refine ⟨36513030895754582031732013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48684041194339442708976017 36513030895754582031732013)
                ·
                  refine ⟨13692386585907968261899505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36513030895754582031732013 13692386585907968261899505)
                  ·
                    refine ⟨10269289939430976196424629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13692386585907968261899505 10269289939430976196424629)
                    ·
                      refine ⟨962745931821654018414809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10269289939430976196424629 962745931821654018414809)
                      ·
                        rfl

theorem cell23_1874941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_1874941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874941 prefixEnd_1874941 := by exact prefixLift 1874941
  have htrace : WordTrace (prefixWord ++ tailWord_1874941) baseStart_1874941 baseEnd_1874941 := by
    simpa [prefixWord, tailWord_1874941, baseEnd_1874941] using wordTrace_append hprefix tailTrace_1874941
  have hstable : (prefixWord ++ tailWord_1874941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874941).length < 2 ^ (prefixWord ++ tailWord_1874941).sum := by decide
  have hdescent : baseEnd_1874941 < baseStart_1874941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874968 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1874968 : Nat := 118140960795 + 1874968 * 2 ^ 59
def prefixEnd_1874968 : Nat := 4983230072969 + 3 ^ 40 * 1874968 * 2
def baseEnd_1874968 : Nat := 962759795799325412777185

theorem tailTrace_1874968 : CollatzResearch.WordTrace tailWord_1874968 prefixEnd_1874968 962759795799325412777185 := by
  unfold tailWord_1874968
  simp only [CollatzResearch.WordTrace]
  refine ⟨34192850535659314942784779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45590467380879086590379705 34192850535659314942784779)
  ·
    refine ⟨51289275803488972414177169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34192850535659314942784779 51289275803488972414177169)
    ·
      refine ⟨38466956852616729310632877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51289275803488972414177169 38466956852616729310632877)
      ·
        refine ⟨14425108819731273491487329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38466956852616729310632877 14425108819731273491487329)
        ·
          refine ⟨10818831614798455118615497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14425108819731273491487329 10818831614798455118615497)
          ·
            refine ⟨8114123711098841338961623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10818831614798455118615497 8114123711098841338961623)
            ·
              refine ⟨12171185566648262008442435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8114123711098841338961623 12171185566648262008442435)
              ·
                refine ⟨18256778349972393012663653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12171185566648262008442435 18256778349972393012663653)
                ·
                  refine ⟨3423145940619823689874435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18256778349972393012663653 3423145940619823689874435)
                  ·
                    refine ⟨5134718910929735534811653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3423145940619823689874435 5134718910929735534811653)
                    ·
                      refine ⟨962759795799325412777185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5134718910929735534811653 962759795799325412777185)
                      ·
                        rfl

theorem cell23_1874968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1874968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874968 prefixEnd_1874968 := by exact prefixLift 1874968
  have htrace : WordTrace (prefixWord ++ tailWord_1874968) baseStart_1874968 baseEnd_1874968 := by
    simpa [prefixWord, tailWord_1874968, baseEnd_1874968] using wordTrace_append hprefix tailTrace_1874968
  have hstable : (prefixWord ++ tailWord_1874968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874968).length < 2 ^ (prefixWord ++ tailWord_1874968).sum := by decide
  have hdescent : baseEnd_1874968 < baseStart_1874968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874988 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_1874988 : Nat := 118140960795 + 1874988 * 2 ^ 59
def prefixEnd_1874988 : Nat := 4983230072969 + 3 ^ 40 * 1874988 * 2
def baseEnd_1874988 : Nat := 962770065412415334527093

theorem tailTrace_1874988 : CollatzResearch.WordTrace tailWord_1874988 prefixEnd_1874988 962770065412415334527093 := by
  unfold tailWord_1874988
  simp only [CollatzResearch.WordTrace]
  refine ⟨34193215265623086650648809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45590953687497448867531745 34193215265623086650648809)
  ·
    refine ⟨25644911449217314987986607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34193215265623086650648809 25644911449217314987986607)
    ·
      refine ⟨38467367173825972481979911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25644911449217314987986607 38467367173825972481979911)
      ·
        refine ⟨57701050760738958722969867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38467367173825972481979911 57701050760738958722969867)
        ·
          refine ⟨86551576141108438084454801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57701050760738958722969867 86551576141108438084454801)
          ·
            refine ⟨64913682105831328563341101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86551576141108438084454801 64913682105831328563341101)
            ·
              refine ⟨24342630789686748211252913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64913682105831328563341101 24342630789686748211252913)
              ·
                refine ⟨18256973092265061158439685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24342630789686748211252913 18256973092265061158439685)
                ·
                  refine ⟨3423182454799698967207441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18256973092265061158439685 3423182454799698967207441)
                  ·
                    refine ⟨2567386841099774225405581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3423182454799698967207441 2567386841099774225405581)
                    ·
                      refine ⟨962770065412415334527093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567386841099774225405581 962770065412415334527093)
                      ·
                        rfl

theorem cell23_1874988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_1874988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1874988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1874988 prefixEnd_1874988 := by exact prefixLift 1874988
  have htrace : WordTrace (prefixWord ++ tailWord_1874988) baseStart_1874988 baseEnd_1874988 := by
    simpa [prefixWord, tailWord_1874988, baseEnd_1874988] using wordTrace_append hprefix tailTrace_1874988
  have hstable : (prefixWord ++ tailWord_1874988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874988).length < 2 ^ (prefixWord ++ tailWord_1874988).sum := by decide
  have hdescent : baseEnd_1874988 < baseStart_1874988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875005 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1875005 : Nat := 118140960795 + 1875005 * 2 ^ 59
def prefixEnd_1875005 : Nat := 4983230072969 + 3 ^ 40 * 1875005 * 2
def baseEnd_1875005 : Nat := 962778794583541768014515

theorem tailTrace_1875005 : CollatzResearch.WordTrace tailWord_1875005 prefixEnd_1875005 962778794583541768014515 := by
  unfold tailWord_1875005
  simp only [CollatzResearch.WordTrace]
  refine ⟨68387050572184585204666469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45591367048123056803110979 68387050572184585204666469)
  ·
    refine ⟨12822571982284609725874963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68387050572184585204666469 12822571982284609725874963)
    ·
      refine ⟨19233857973426914588812445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12822571982284609725874963 19233857973426914588812445)
      ·
        refine ⟨7212696740035092970804667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19233857973426914588812445 7212696740035092970804667)
        ·
          refine ⟨10819045110052639456207001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212696740035092970804667 10819045110052639456207001)
          ·
            refine ⟨8114283832539479592155251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10819045110052639456207001 8114283832539479592155251)
            ·
              refine ⟨12171425748809219388232877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8114283832539479592155251 12171425748809219388232877)
              ·
                refine ⟨4564284655803457270587329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12171425748809219388232877 4564284655803457270587329)
                ·
                  refine ⟨3423213491852592952940497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4564284655803457270587329 3423213491852592952940497)
                  ·
                    refine ⟨2567410118889444714705373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3423213491852592952940497 2567410118889444714705373)
                    ·
                      refine ⟨962778794583541768014515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567410118889444714705373 962778794583541768014515)
                      ·
                        rfl

theorem cell23_1875005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1875005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875005 prefixEnd_1875005 := by exact prefixLift 1875005
  have htrace : WordTrace (prefixWord ++ tailWord_1875005) baseStart_1875005 baseEnd_1875005 := by
    simpa [prefixWord, tailWord_1875005, baseEnd_1875005] using wordTrace_append hprefix tailTrace_1875005
  have hstable : (prefixWord ++ tailWord_1875005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875005).length < 2 ^ (prefixWord ++ tailWord_1875005).sum := by decide
  have hdescent : baseEnd_1875005 < baseStart_1875005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875045 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 1, 5, 2]
def baseStart_1875045 : Nat := 118140960795 + 1875045 * 2 ^ 59
def prefixEnd_1875045 : Nat := 4983230072969 + 3 ^ 40 * 1875045 * 2
def baseEnd_1875045 : Nat := 962799333809721611514331

theorem tailTrace_1875045 : CollatzResearch.WordTrace tailWord_1875045 prefixEnd_1875045 962799333809721611514331 := by
  unfold tailWord_1875045
  simp only [CollatzResearch.WordTrace]
  refine ⟨68388509492039672036122589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45592339661359781357415059 68388509492039672036122589)
  ·
    refine ⟨25645691059514877013545971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68388509492039672036122589 25645691059514877013545971)
    ·
      refine ⟨38468536589272315520318957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25645691059514877013545971 38468536589272315520318957)
      ·
        refine ⟨14425701220977118320119609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38468536589272315520318957 14425701220977118320119609)
        ·
          refine ⟨10819275915732838740089707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14425701220977118320119609 10819275915732838740089707)
          ·
            refine ⟨16228913873599258110134561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819275915732838740089707 16228913873599258110134561)
            ·
              refine ⟨12171685405199443582600921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16228913873599258110134561 12171685405199443582600921)
              ·
                refine ⟨9128764053899582686950691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12171685405199443582600921 9128764053899582686950691)
                ·
                  refine ⟨13693146080849374030426037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9128764053899582686950691 13693146080849374030426037)
                  ·
                    refine ⟨1283732445079628815352441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13693146080849374030426037 1283732445079628815352441)
                    ·
                      refine ⟨962799333809721611514331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283732445079628815352441 962799333809721611514331)
                      ·
                        rfl

theorem cell23_1875045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_1875045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875045 prefixEnd_1875045 := by exact prefixLift 1875045
  have htrace : WordTrace (prefixWord ++ tailWord_1875045) baseStart_1875045 baseEnd_1875045 := by
    simpa [prefixWord, tailWord_1875045, baseEnd_1875045] using wordTrace_append hprefix tailTrace_1875045
  have hstable : (prefixWord ++ tailWord_1875045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875045).length < 2 ^ (prefixWord ++ tailWord_1875045).sum := by decide
  have hdescent : baseEnd_1875045 < baseStart_1875045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875062 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_1875062 : Nat := 118140960795 + 1875062 * 2 ^ 59
def prefixEnd_1875062 : Nat := 4983230072969 + 3 ^ 40 * 1875062 * 2
def baseEnd_1875062 : Nat := 962808062980848045001753

theorem tailTrace_1875062 : CollatzResearch.WordTrace tailWord_1875062 prefixEnd_1875062 962808062980848045001753 := by
  unfold tailWord_1875062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4274320595811130246218215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45592753021985389292994293 4274320595811130246218215)
  ·
    refine ⟨6411480893716695369327323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4274320595811130246218215 6411480893716695369327323)
    ·
      refine ⟨9617221340575043053990985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6411480893716695369327323 9617221340575043053990985)
      ·
        refine ⟨7212916005431282290493239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9617221340575043053990985 7212916005431282290493239)
        ·
          refine ⟨10819374008146923435739859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212916005431282290493239 10819374008146923435739859)
          ·
            refine ⟨16229061012220385153609789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819374008146923435739859 16229061012220385153609789)
            ·
              refine ⟨6085897879582644432603671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16229061012220385153609789 6085897879582644432603671)
              ·
                refine ⟨9128846819373966648905507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6085897879582644432603671 9128846819373966648905507)
                ·
                  refine ⟨13693270229060949973358261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9128846819373966648905507 13693270229060949973358261)
                  ·
                    refine ⟨1283744083974464060002337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13693270229060949973358261 1283744083974464060002337)
                    ·
                      refine ⟨962808062980848045001753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283744083974464060002337 962808062980848045001753)
                      ·
                        rfl

theorem cell23_1875062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_1875062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875062 prefixEnd_1875062 := by exact prefixLift 1875062
  have htrace : WordTrace (prefixWord ++ tailWord_1875062) baseStart_1875062 baseEnd_1875062 := by
    simpa [prefixWord, tailWord_1875062, baseEnd_1875062] using wordTrace_append hprefix tailTrace_1875062
  have hstable : (prefixWord ++ tailWord_1875062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875062).length < 2 ^ (prefixWord ++ tailWord_1875062).sum := by decide
  have hdescent : baseEnd_1875062 < baseStart_1875062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875068 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_1875068 : Nat := 118140960795 + 1875068 * 2 ^ 59
def prefixEnd_1875068 : Nat := 4983230072969 + 3 ^ 40 * 1875068 * 2
def baseEnd_1875068 : Nat := 320937047954925007175575

theorem tailTrace_1875068 : CollatzResearch.WordTrace tailWord_1875068 prefixEnd_1875068 320937047954925007175575 := by
  unfold tailWord_1875068
  simp only [CollatzResearch.WordTrace]
  refine ⟨34194674185478173482104929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45592898913970897976139905 34194674185478173482104929)
  ·
    refine ⟨25646005639108630111578697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34194674185478173482104929 25646005639108630111578697)
    ·
      refine ⟨19234504229331472583684023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25646005639108630111578697 19234504229331472583684023)
      ·
        refine ⟨28851756343997208875526035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19234504229331472583684023 28851756343997208875526035)
        ·
          refine ⟨43277634515995813313289053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28851756343997208875526035 43277634515995813313289053)
          ·
            refine ⟨16229112943498429992483395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43277634515995813313289053 16229112943498429992483395)
            ·
              refine ⟨24343669415247644988725093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16229112943498429992483395 24343669415247644988725093)
              ·
                refine ⟨4564438015358933435385955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24343669415247644988725093 4564438015358933435385955)
                ·
                  refine ⟨6846657023038400153078933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564438015358933435385955 6846657023038400153078933)
                  ·
                    refine ⟨320937047954925007175575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6846657023038400153078933 320937047954925007175575)
                    ·
                      rfl

theorem cell23_1875068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_1875068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875068 prefixEnd_1875068 := by exact prefixLift 1875068
  have htrace : WordTrace (prefixWord ++ tailWord_1875068) baseStart_1875068 baseEnd_1875068 := by
    simpa [prefixWord, tailWord_1875068, baseEnd_1875068] using wordTrace_append hprefix tailTrace_1875068
  have hstable : (prefixWord ++ tailWord_1875068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875068).length < 2 ^ (prefixWord ++ tailWord_1875068).sum := by decide
  have hdescent : baseEnd_1875068 < baseStart_1875068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875069 : List Nat := [1, 4, 1, 1, 3, 1, 4, 3, 1, 1, 3]
def baseStart_1875069 : Nat := 118140960795 + 1875069 * 2 ^ 59
def prefixEnd_1875069 : Nat := 4983230072969 + 3 ^ 40 * 1875069 * 2
def baseEnd_1875069 : Nat := 962811657345429517614221

theorem tailTrace_1875069 : CollatzResearch.WordTrace tailWord_1875069 prefixEnd_1875069 962811657345429517614221 := by
  unfold tailWord_1875069
  simp only [CollatzResearch.WordTrace]
  refine ⟨68389384843952724134996261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45592923229301816089997507 68389384843952724134996261)
  ·
    refine ⟨12823009658241135775311799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68389384843952724134996261 12823009658241135775311799)
    ·
      refine ⟨19234514487361703662967699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12823009658241135775311799 19234514487361703662967699)
      ·
        refine ⟨28851771731042555494451549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19234514487361703662967699 28851771731042555494451549)
        ·
          refine ⟨10819414399140958310419331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28851771731042555494451549 10819414399140958310419331)
          ·
            refine ⟨16229121598711437465628997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819414399140958310419331 16229121598711437465628997)
            ·
              refine ⟨3042960299758394524805437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16229121598711437465628997 3042960299758394524805437)
              ·
                refine ⟨1141110112409397946802039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3042960299758394524805437 1141110112409397946802039)
                ·
                  refine ⟨1711665168614096920203059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141110112409397946802039 1711665168614096920203059)
                  ·
                    refine ⟨2567497752921145380304589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1711665168614096920203059 2567497752921145380304589)
                    ·
                      refine ⟨962811657345429517614221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567497752921145380304589 962811657345429517614221)
                      ·
                        rfl

theorem cell23_1875069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_1875069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875069 prefixEnd_1875069 := by exact prefixLift 1875069
  have htrace : WordTrace (prefixWord ++ tailWord_1875069) baseStart_1875069 baseEnd_1875069 := by
    simpa [prefixWord, tailWord_1875069, baseEnd_1875069] using wordTrace_append hprefix tailTrace_1875069
  have hstable : (prefixWord ++ tailWord_1875069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875069).length < 2 ^ (prefixWord ++ tailWord_1875069).sum := by decide
  have hdescent : baseEnd_1875069 < baseStart_1875069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875075 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 4]
def baseStart_1875075 : Nat := 118140960795 + 1875075 * 2 ^ 59
def prefixEnd_1875075 : Nat := 4983230072969 + 3 ^ 40 * 1875075 * 2
def baseEnd_1875075 : Nat := 962814738229356494139193

theorem tailTrace_1875075 : CollatzResearch.WordTrace tailWord_1875075 prefixEnd_1875075 962814738229356494139193 := by
  unfold tailWord_1875075
  simp only [CollatzResearch.WordTrace]
  refine ⟨68389603681930987159714679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45593069121287324773143119 68389603681930987159714679)
  ·
    refine ⟨102584405522896480739572019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68389603681930987159714679 102584405522896480739572019)
    ·
      refine ⟨153876608284344721109358029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102584405522896480739572019 153876608284344721109358029)
      ·
        refine ⟨57703728106629270416009261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153876608284344721109358029 57703728106629270416009261)
        ·
          refine ⟨21638898039985976406003473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57703728106629270416009261 21638898039985976406003473)
          ·
            refine ⟨16229173529989482304502605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21638898039985976406003473 16229173529989482304502605)
            ·
              refine ⟨6085940073746055864188477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16229173529989482304502605 6085940073746055864188477)
              ·
                refine ⟨2282227527654770949070679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6085940073746055864188477 2282227527654770949070679)
                ·
                  refine ⟨3423341291482156423606019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282227527654770949070679 3423341291482156423606019)
                  ·
                    refine ⟨5135011937223234635409029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3423341291482156423606019 5135011937223234635409029)
                    ·
                      refine ⟨962814738229356494139193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5135011937223234635409029 962814738229356494139193)
                      ·
                        rfl

theorem cell23_1875075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_1875075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875075 prefixEnd_1875075 := by exact prefixLift 1875075
  have htrace : WordTrace (prefixWord ++ tailWord_1875075) baseStart_1875075 baseEnd_1875075 := by
    simpa [prefixWord, tailWord_1875075, baseEnd_1875075] using wordTrace_append hprefix tailTrace_1875075
  have hstable : (prefixWord ++ tailWord_1875075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875075).length < 2 ^ (prefixWord ++ tailWord_1875075).sum := by decide
  have hdescent : baseEnd_1875075 < baseStart_1875075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
