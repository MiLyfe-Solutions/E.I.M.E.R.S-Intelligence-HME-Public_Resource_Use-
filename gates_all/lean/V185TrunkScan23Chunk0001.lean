import V185TrunkScan23Chunk0000

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5922 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_5922 : Nat := 118140960795 + 5922 * 2 ^ 59
def prefixEnd_5922 : Nat := 4983230072969 + 3 ^ 40 * 5922 * 2
def baseEnd_5922 : Nat := 3040832436031063847771

theorem tailTrace_5922 : CollatzResearch.WordTrace tailWord_5922 prefixEnd_5922 3040832436031063847771 := by
  unfold tailWord_5922
  simp only [CollatzResearch.WordTrace]
  refine ⟨53998271138270060547005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143995389702053494792013 53998271138270060547005)
  ·
    refine ⟨20249351676851272705127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53998271138270060547005 20249351676851272705127)
    ·
      refine ⟨30374027515276909057691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20249351676851272705127 30374027515276909057691)
      ·
        refine ⟨45561041272915363586537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30374027515276909057691 45561041272915363586537)
        ·
          refine ⟨34170780954686522689903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45561041272915363586537 34170780954686522689903)
          ·
            refine ⟨51256171432029784034855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34170780954686522689903 51256171432029784034855)
            ·
              refine ⟨76884257148044676052283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51256171432029784034855 76884257148044676052283)
              ·
                refine ⟨115326385722067014078425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76884257148044676052283 115326385722067014078425)
                ·
                  refine ⟨86494789291550260558819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115326385722067014078425 86494789291550260558819)
                  ·
                    refine ⟨129742183937325390838229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86494789291550260558819 129742183937325390838229)
                    ·
                      refine ⟨3040832436031063847771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129742183937325390838229 3040832436031063847771)
                      ·
                        rfl

theorem cell23_5922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_5922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5922 prefixEnd_5922 := by exact prefixLift 5922
  have htrace : WordTrace (prefixWord ++ tailWord_5922) baseStart_5922 baseEnd_5922 := by
    simpa [prefixWord, tailWord_5922, baseEnd_5922] using wordTrace_append hprefix tailTrace_5922
  have hstable : (prefixWord ++ tailWord_5922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5922).length < 2 ^ (prefixWord ++ tailWord_5922).sum := by decide
  have hdescent : baseEnd_5922 < baseStart_5922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5946 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_5946 : Nat := 118140960795 + 5946 * 2 ^ 59
def prefixEnd_5946 : Nat := 4983230072969 + 3 ^ 40 * 5946 * 2
def baseEnd_5946 : Nat := 1017718657246323315887

theorem tailTrace_5946 : CollatzResearch.WordTrace tailWord_5946 prefixEnd_5946 1017718657246323315887 := by
  unfold tailWord_5946
  simp only [CollatzResearch.WordTrace]
  refine ⟨54217109116533085265423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144578957644088227374461 54217109116533085265423)
  ·
    refine ⟨81325663674799627898135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54217109116533085265423 81325663674799627898135)
    ·
      refine ⟨121988495512199441847203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81325663674799627898135 121988495512199441847203)
      ·
        refine ⟨182982743268299162770805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121988495512199441847203 182982743268299162770805)
        ·
          refine ⟨17154632181403046509763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182982743268299162770805 17154632181403046509763)
          ·
            refine ⟨25731948272104569764645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17154632181403046509763 25731948272104569764645)
            ·
              refine ⟨4824740301019606830871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25731948272104569764645 4824740301019606830871)
              ·
                refine ⟨7237110451529410246307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4824740301019606830871 7237110451529410246307)
                ·
                  refine ⟨10855665677294115369461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7237110451529410246307 10855665677294115369461)
                  ·
                    refine ⟨1017718657246323315887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10855665677294115369461 1017718657246323315887)
                    ·
                      rfl

theorem cell23_5946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_5946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5946 prefixEnd_5946 := by exact prefixLift 5946
  have htrace : WordTrace (prefixWord ++ tailWord_5946) baseStart_5946 baseEnd_5946 := by
    simpa [prefixWord, tailWord_5946, baseEnd_5946] using wordTrace_append hprefix tailTrace_5946
  have hstable : (prefixWord ++ tailWord_5946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5946).length < 2 ^ (prefixWord ++ tailWord_5946).sum := by decide
  have hdescent : baseEnd_5946 < baseStart_5946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_5962 : Nat := 118140960795 + 5962 * 2 ^ 59
def prefixEnd_5962 : Nat := 4983230072969 + 3 ^ 40 * 5962 * 2
def baseEnd_5962 : Nat := 3061371662210907347587

theorem tailTrace_5962 : CollatzResearch.WordTrace tailWord_5962 prefixEnd_5962 3061371662210907347587 := by
  unfold tailWord_5962
  simp only [CollatzResearch.WordTrace]
  refine ⟨54363001102041768411035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144968002938778049096093 54363001102041768411035)
  ·
    refine ⟨81544501653062652616553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54363001102041768411035 81544501653062652616553)
    ·
      refine ⟨61158376239796989462415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81544501653062652616553 61158376239796989462415)
      ·
        refine ⟨91737564359695484193623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61158376239796989462415 91737564359695484193623)
        ·
          refine ⟨137606346539543226290435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91737564359695484193623 137606346539543226290435)
          ·
            refine ⟨206409519809314839435653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137606346539543226290435 206409519809314839435653)
            ·
              refine ⟨38701784964246532394185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206409519809314839435653 38701784964246532394185)
              ·
                refine ⟨29026338723184899295639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38701784964246532394185 29026338723184899295639)
                ·
                  refine ⟨43539508084777348943459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29026338723184899295639 43539508084777348943459)
                  ·
                    refine ⟨65309262127166023415189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43539508084777348943459 65309262127166023415189)
                    ·
                      refine ⟨3061371662210907347587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65309262127166023415189 3061371662210907347587)
                      ·
                        rfl

theorem cell23_5962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_5962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962 prefixEnd_5962 := by exact prefixLift 5962
  have htrace : WordTrace (prefixWord ++ tailWord_5962) baseStart_5962 baseEnd_5962 := by
    simpa [prefixWord, tailWord_5962, baseEnd_5962] using wordTrace_append hprefix tailTrace_5962
  have hstable : (prefixWord ++ tailWord_5962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962).length < 2 ^ (prefixWord ++ tailWord_5962).sum := by decide
  have hdescent : baseEnd_5962 < baseStart_5962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5969 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_5969 : Nat := 118140960795 + 5969 * 2 ^ 59
def prefixEnd_5969 : Nat := 4983230072969 + 3 ^ 40 * 5969 * 2
def baseEnd_5969 : Nat := 3064966026792379960055

theorem tailTrace_5969 : CollatzResearch.WordTrace tailWord_5969 prefixEnd_5969 3064966026792379960055 := by
  unfold tailWord_5969
  simp only [CollatzResearch.WordTrace]
  refine ⟨217707315382807269148961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145138210255204846099307 217707315382807269148961)
  ·
    refine ⟨163280486537105451861721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217707315382807269148961 163280486537105451861721)
    ·
      refine ⟨122460364902829088896291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163280486537105451861721 122460364902829088896291)
      ·
        refine ⟨183690547354243633344437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122460364902829088896291 183690547354243633344437)
        ·
          refine ⟨17220988814460340626041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183690547354243633344437 17220988814460340626041)
          ·
            refine ⟨12915741610845255469531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17220988814460340626041 12915741610845255469531)
            ·
              refine ⟨19373612416267883204297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12915741610845255469531 19373612416267883204297)
              ·
                refine ⟨14530209312200912403223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19373612416267883204297 14530209312200912403223)
                ·
                  refine ⟨21795313968301368604835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14530209312200912403223 21795313968301368604835)
                  ·
                    refine ⟨32692970952452052907253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21795313968301368604835 32692970952452052907253)
                    ·
                      refine ⟨3064966026792379960055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32692970952452052907253 3064966026792379960055)
                      ·
                        rfl

theorem cell23_5969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_5969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5969 prefixEnd_5969 := by exact prefixLift 5969
  have htrace : WordTrace (prefixWord ++ tailWord_5969) baseStart_5969 baseEnd_5969 := by
    simpa [prefixWord, tailWord_5969, baseEnd_5969] using wordTrace_append hprefix tailTrace_5969
  have hstable : (prefixWord ++ tailWord_5969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5969).length < 2 ^ (prefixWord ++ tailWord_5969).sum := by decide
  have hdescent : baseEnd_5969 < baseStart_5969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5994 : List Nat := [3, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5994 : Nat := 118140960795 + 5994 * 2 ^ 59
def prefixEnd_5994 : Nat := 4983230072969 + 3 ^ 40 * 5994 * 2
def baseEnd_5994 : Nat := 3077803043154782147441

theorem tailTrace_5994 : CollatzResearch.WordTrace tailWord_5994 prefixEnd_5994 3077803043154782147441 := by
  unfold tailWord_5994
  simp only [CollatzResearch.WordTrace]
  refine ⟨54654785073059134702259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145746093528157692539357 54654785073059134702259)
  ·
    refine ⟨81982177609588702053389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54654785073059134702259 81982177609588702053389)
    ·
      refine ⟨30743316603595763270021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81982177609588702053389 30743316603595763270021)
      ·
        refine ⟨5764371863174205613129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30743316603595763270021 5764371863174205613129)
        ·
          refine ⟨4323278897380654209847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5764371863174205613129 4323278897380654209847)
          ·
            refine ⟨6484918346070981314771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323278897380654209847 6484918346070981314771)
            ·
              refine ⟨9727377519106471972157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6484918346070981314771 9727377519106471972157)
              ·
                refine ⟨3647766569664926989559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9727377519106471972157 3647766569664926989559)
                ·
                  refine ⟨5471649854497390484339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647766569664926989559 5471649854497390484339)
                  ·
                    refine ⟨8207474781746085726509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5471649854497390484339 8207474781746085726509)
                    ·
                      refine ⟨3077803043154782147441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8207474781746085726509 3077803043154782147441)
                      ·
                        rfl

theorem cell23_5994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5994 prefixEnd_5994 := by exact prefixLift 5994
  have htrace : WordTrace (prefixWord ++ tailWord_5994) baseStart_5994 baseEnd_5994 := by
    simpa [prefixWord, tailWord_5994, baseEnd_5994] using wordTrace_append hprefix tailTrace_5994
  have hstable : (prefixWord ++ tailWord_5994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5994).length < 2 ^ (prefixWord ++ tailWord_5994).sum := by decide
  have hdescent : baseEnd_5994 < baseStart_5994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6002 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_6002 : Nat := 118140960795 + 6002 * 2 ^ 59
def prefixEnd_6002 : Nat := 4983230072969 + 3 ^ 40 * 6002 * 2
def baseEnd_6002 : Nat := 1027303629463583615801

theorem tailTrace_6002 : CollatzResearch.WordTrace tailWord_6002 prefixEnd_6002 1027303629463583615801 := by
  unfold tailWord_6002
  simp only [CollatzResearch.WordTrace]
  refine ⟨54727731065813476275065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145940616175502603400173 54727731065813476275065)
  ·
    refine ⟨41045798299360107206299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54727731065813476275065 41045798299360107206299)
    ·
      refine ⟨61568697449040160809449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41045798299360107206299 61568697449040160809449)
      ·
        refine ⟨46176523086780120607087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61568697449040160809449 46176523086780120607087)
        ·
          refine ⟨69264784630170180910631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46176523086780120607087 69264784630170180910631)
          ·
            refine ⟨103897176945255271365947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69264784630170180910631 103897176945255271365947)
            ·
              refine ⟨155845765417882907048921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103897176945255271365947 155845765417882907048921)
              ·
                refine ⟨116884324063412180286691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155845765417882907048921 116884324063412180286691)
                ·
                  refine ⟨175326486095118270430037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116884324063412180286691 175326486095118270430037)
                  ·
                    refine ⟨1027303629463583615801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 175326486095118270430037 1027303629463583615801)
                    ·
                      rfl

theorem cell23_6002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_6002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6002 prefixEnd_6002 := by exact prefixLift 6002
  have htrace : WordTrace (prefixWord ++ tailWord_6002) baseStart_6002 baseEnd_6002 := by
    simpa [prefixWord, tailWord_6002, baseEnd_6002] using wordTrace_append hprefix tailTrace_6002
  have hstable : (prefixWord ++ tailWord_6002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6002).length < 2 ^ (prefixWord ++ tailWord_6002).sum := by decide
  have hdescent : baseEnd_6002 < baseStart_6002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6006 : List Nat := [5, 1, 1, 3, 2, 2, 9]
def baseStart_6006 : Nat := 118140960795 + 6006 * 2 ^ 59
def prefixEnd_6006 : Nat := 4983230072969 + 3 ^ 40 * 6006 * 2
def baseEnd_6006 : Nat := 38073639642083150585

theorem tailTrace_6006 : CollatzResearch.WordTrace tailWord_6006 prefixEnd_6006 38073639642083150585 := by
  unfold tailWord_6006
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691051015547661765367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146037877499175058830581 13691051015547661765367)
  ·
    refine ⟨20536576523321492648051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13691051015547661765367 20536576523321492648051)
    ·
      refine ⟨30804864784982238972077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20536576523321492648051 30804864784982238972077)
      ·
        refine ⟨11551824294368339614529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30804864784982238972077 11551824294368339614529)
        ·
          refine ⟨8663868220776254710897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11551824294368339614529 8663868220776254710897)
          ·
            refine ⟨6497901165582191033173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8663868220776254710897 6497901165582191033173)
            ·
              refine ⟨38073639642083150585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6497901165582191033173 38073639642083150585)
              ·
                rfl

theorem cell23_6006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 9].length) (baseStart_6006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6006 prefixEnd_6006 := by exact prefixLift 6006
  have htrace : WordTrace (prefixWord ++ tailWord_6006) baseStart_6006 baseEnd_6006 := by
    simpa [prefixWord, tailWord_6006, baseEnd_6006] using wordTrace_append hprefix tailTrace_6006
  have hstable : (prefixWord ++ tailWord_6006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6006).length < 2 ^ (prefixWord ++ tailWord_6006).sum := by decide
  have hdescent : baseEnd_6006 < baseStart_6006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 2, 1, 3]
def baseStart_6016 : Nat := 118140960795 + 6016 * 2 ^ 59
def prefixEnd_6016 : Nat := 4983230072969 + 3 ^ 40 * 6016 * 2
def baseEnd_6016 : Nat := 3089099617553696072339

theorem tailTrace_6016 : CollatzResearch.WordTrace tailWord_6016 prefixEnd_6016 3089099617553696072339 := by
  unfold tailWord_6016
  simp only [CollatzResearch.WordTrace]
  refine ⟨109710773106267148054951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146281030808356197406601 109710773106267148054951)
  ·
    refine ⟨164566159659400722082427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109710773106267148054951 164566159659400722082427)
    ·
      refine ⟨246849239489101083123641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164566159659400722082427 246849239489101083123641)
      ·
        refine ⟨185136929616825812342731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246849239489101083123641 185136929616825812342731)
        ·
          refine ⟨277705394425238718514097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185136929616825812342731 277705394425238718514097)
          ·
            refine ⟨208279045818929038885573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277705394425238718514097 208279045818929038885573)
            ·
              refine ⟨39052321091049194791045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208279045818929038885573 39052321091049194791045)
              ·
                refine ⟨7322310204571724023321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39052321091049194791045 7322310204571724023321)
                ·
                  refine ⟨5491732653428793017491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7322310204571724023321 5491732653428793017491)
                  ·
                    refine ⟨8237598980143189526237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5491732653428793017491 8237598980143189526237)
                    ·
                      refine ⟨3089099617553696072339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8237598980143189526237 3089099617553696072339)
                      ·
                        rfl

theorem cell23_6016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_6016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016 prefixEnd_6016 := by exact prefixLift 6016
  have htrace : WordTrace (prefixWord ++ tailWord_6016) baseStart_6016 baseEnd_6016 := by
    simpa [prefixWord, tailWord_6016, baseEnd_6016] using wordTrace_append hprefix tailTrace_6016
  have hstable : (prefixWord ++ tailWord_6016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016).length < 2 ^ (prefixWord ++ tailWord_6016).sum := by decide
  have hdescent : baseEnd_6016 < baseStart_6016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6017 : Nat := 118140960795 + 6017 * 2 ^ 59
def prefixEnd_6017 : Nat := 4983230072969 + 3 ^ 40 * 6017 * 2
def baseEnd_6017 : Nat := 3089613098208192159835

theorem tailTrace_6017 : CollatzResearch.WordTrace tailWord_6017 prefixEnd_6017 3089613098208192159835 := by
  unfold tailWord_6017
  simp only [CollatzResearch.WordTrace]
  refine ⟨219458019208911466896305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146305346139274311264203 219458019208911466896305)
  ·
    refine ⟨164593514406683600172229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219458019208911466896305 164593514406683600172229)
    ·
      refine ⟨30861283951253175032293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164593514406683600172229 30861283951253175032293)
      ·
        refine ⟨5786490740859970318555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30861283951253175032293 5786490740859970318555)
        ·
          refine ⟨8679736111289955477833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5786490740859970318555 8679736111289955477833)
          ·
            refine ⟨6509802083467466608375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8679736111289955477833 6509802083467466608375)
            ·
              refine ⟨9764703125201199912563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509802083467466608375 9764703125201199912563)
              ·
                refine ⟨14647054687801799868845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9764703125201199912563 14647054687801799868845)
                ·
                  refine ⟨5492645507925674950817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14647054687801799868845 5492645507925674950817)
                  ·
                    refine ⟨4119484130944256213113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5492645507925674950817 4119484130944256213113)
                    ·
                      refine ⟨3089613098208192159835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119484130944256213113 3089613098208192159835)
                      ·
                        rfl

theorem cell23_6017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017 prefixEnd_6017 := by exact prefixLift 6017
  have htrace : WordTrace (prefixWord ++ tailWord_6017) baseStart_6017 baseEnd_6017 := by
    simpa [prefixWord, tailWord_6017, baseEnd_6017] using wordTrace_append hprefix tailTrace_6017
  have hstable : (prefixWord ++ tailWord_6017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017).length < 2 ^ (prefixWord ++ tailWord_6017).sum := by decide
  have hdescent : baseEnd_6017 < baseStart_6017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6033 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 2, 1, 3]
def baseStart_6033 : Nat := 118140960795 + 6033 * 2 ^ 59
def prefixEnd_6033 : Nat := 4983230072969 + 3 ^ 40 * 6033 * 2
def baseEnd_6033 : Nat := 3097828788680129559761

theorem tailTrace_6033 : CollatzResearch.WordTrace tailWord_6033 prefixEnd_6033 3097828788680129559761 := by
  unfold tailWord_6033
  simp only [CollatzResearch.WordTrace]
  refine ⟨220041587150946199478753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146694391433964132985835 220041587150946199478753)
  ·
    refine ⟨165031190363209649609065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220041587150946199478753 165031190363209649609065)
    ·
      refine ⟨123773392772407237206799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165031190363209649609065 123773392772407237206799)
      ·
        refine ⟨185660089158610855810199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123773392772407237206799 185660089158610855810199)
        ·
          refine ⟨278490133737916283715299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185660089158610855810199 278490133737916283715299)
          ·
            refine ⟨417735200606874425572949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278490133737916283715299 417735200606874425572949)
            ·
              refine ⟨4895334382111809674683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 417735200606874425572949 4895334382111809674683)
              ·
                refine ⟨7343001573167714512025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4895334382111809674683 7343001573167714512025)
                ·
                  refine ⟨5507251179875785884019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7343001573167714512025 5507251179875785884019)
                  ·
                    refine ⟨8260876769813678826029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5507251179875785884019 8260876769813678826029)
                    ·
                      refine ⟨3097828788680129559761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8260876769813678826029 3097828788680129559761)
                      ·
                        rfl

theorem cell23_6033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_6033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6033 prefixEnd_6033 := by exact prefixLift 6033
  have htrace : WordTrace (prefixWord ++ tailWord_6033) baseStart_6033 baseEnd_6033 := by
    simpa [prefixWord, tailWord_6033, baseEnd_6033] using wordTrace_append hprefix tailTrace_6033
  have hstable : (prefixWord ++ tailWord_6033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6033).length < 2 ^ (prefixWord ++ tailWord_6033).sum := by decide
  have hdescent : baseEnd_6033 < baseStart_6033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068 : List Nat := [2, 5, 2, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6068 : Nat := 118140960795 + 6068 * 2 ^ 59
def prefixEnd_6068 : Nat := 4983230072969 + 3 ^ 40 * 6068 * 2
def baseEnd_6068 : Nat := 3115800611587492622101

theorem tailTrace_6068 : CollatzResearch.WordTrace tailWord_6068 prefixEnd_6068 3115800611587492622101 := by
  unfold tailWord_6068
  simp only [CollatzResearch.WordTrace]
  refine ⟨110659071012073588501429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147545428016098118001905 110659071012073588501429)
  ·
    refine ⟨10374287907381898922009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110659071012073588501429 10374287907381898922009)
    ·
      refine ⟨7780715930536424191507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10374287907381898922009 7780715930536424191507)
      ·
        refine ⟨11671073895804636287261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7780715930536424191507 11671073895804636287261)
        ·
          refine ⟨4376652710926738607723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11671073895804636287261 4376652710926738607723)
          ·
            refine ⟨6564979066390107911585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4376652710926738607723 6564979066390107911585)
            ·
              refine ⟨4923734299792580933689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6564979066390107911585 4923734299792580933689)
              ·
                refine ⟨3692800724844435700267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923734299792580933689 3692800724844435700267)
                ·
                  refine ⟨5539201087266653550401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3692800724844435700267 5539201087266653550401)
                  ·
                    refine ⟨4154400815449990162801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5539201087266653550401 4154400815449990162801)
                    ·
                      refine ⟨3115800611587492622101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154400815449990162801 3115800611587492622101)
                      ·
                        rfl

theorem cell23_6068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068 prefixEnd_6068 := by exact prefixLift 6068
  have htrace : WordTrace (prefixWord ++ tailWord_6068) baseStart_6068 baseEnd_6068 := by
    simpa [prefixWord, tailWord_6068, baseEnd_6068] using wordTrace_append hprefix tailTrace_6068
  have hstable : (prefixWord ++ tailWord_6068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068).length < 2 ^ (prefixWord ++ tailWord_6068).sum := by decide
  have hdescent : baseEnd_6068 < baseStart_6068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 3]
def baseStart_6089 : Nat := 118140960795 + 6089 * 2 ^ 59
def prefixEnd_6089 : Nat := 4983230072969 + 3 ^ 40 * 6089 * 2
def baseEnd_6089 : Nat := 3126583705331910459503

theorem tailTrace_6089 : CollatzResearch.WordTrace tailWord_6089 prefixEnd_6089 3126583705331910459503 := by
  unfold tailWord_6089
  simp only [CollatzResearch.WordTrace]
  refine ⟨222084074948067763517321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148056049965378509011547 222084074948067763517321)
  ·
    refine ⟨166563056211050822637991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222084074948067763517321 166563056211050822637991)
    ·
      refine ⟨249844584316576233956987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166563056211050822637991 249844584316576233956987)
      ·
        refine ⟨374766876474864350935481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249844584316576233956987 374766876474864350935481)
        ·
          refine ⟨281075157356148263201611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374766876474864350935481 281075157356148263201611)
          ·
            refine ⟨421612736034222394802417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281075157356148263201611 421612736034222394802417)
            ·
              refine ⟨316209552025666796101813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421612736034222394802417 316209552025666796101813)
              ·
                refine ⟨29644645502406262134545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 316209552025666796101813 29644645502406262134545)
                ·
                  refine ⟨22233484126804696600909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29644645502406262134545 22233484126804696600909)
                  ·
                    refine ⟨8337556547551761225341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22233484126804696600909 8337556547551761225341)
                    ·
                      refine ⟨3126583705331910459503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8337556547551761225341 3126583705331910459503)
                      ·
                        rfl

theorem cell23_6089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_6089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089 prefixEnd_6089 := by exact prefixLift 6089
  have htrace : WordTrace (prefixWord ++ tailWord_6089) baseStart_6089 baseEnd_6089 := by
    simpa [prefixWord, tailWord_6089, baseEnd_6089] using wordTrace_append hprefix tailTrace_6089
  have hstable : (prefixWord ++ tailWord_6089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089).length < 2 ^ (prefixWord ++ tailWord_6089).sum := by decide
  have hdescent : baseEnd_6089 < baseStart_6089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_6156 : Nat := 118140960795 + 6156 * 2 ^ 59
def prefixEnd_6156 : Nat := 4983230072969 + 3 ^ 40 * 6156 * 2
def baseEnd_6156 : Nat := 1053662303061049440565

theorem tailTrace_6156 : CollatzResearch.WordTrace tailWord_6156 prefixEnd_6156 1053662303061049440565 := by
  unfold tailWord_6156
  simp only [CollatzResearch.WordTrace]
  refine ⟨112263882852669103103161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149685177136892137470881 112263882852669103103161)
  ·
    refine ⟨84197912139501827327371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112263882852669103103161 84197912139501827327371)
    ·
      refine ⟨126296868209252740991057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84197912139501827327371 126296868209252740991057)
      ·
        refine ⟨94722651156939555743293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126296868209252740991057 94722651156939555743293)
        ·
          refine ⟨35520994183852333403735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94722651156939555743293 35520994183852333403735)
          ·
            refine ⟨53281491275778500105603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35520994183852333403735 53281491275778500105603)
            ·
              refine ⟨79922236913667750158405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53281491275778500105603 79922236913667750158405)
              ·
                refine ⟨14985419421312703154701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79922236913667750158405 14985419421312703154701)
                ·
                  refine ⟨5619532282992263683013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14985419421312703154701 5619532282992263683013)
                  ·
                    refine ⟨1053662303061049440565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5619532282992263683013 1053662303061049440565)
                    ·
                      rfl

theorem cell23_6156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_6156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156 prefixEnd_6156 := by exact prefixLift 6156
  have htrace : WordTrace (prefixWord ++ tailWord_6156) baseStart_6156 baseEnd_6156 := by
    simpa [prefixWord, tailWord_6156, baseEnd_6156] using wordTrace_append hprefix tailTrace_6156
  have hstable : (prefixWord ++ tailWord_6156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156).length < 2 ^ (prefixWord ++ tailWord_6156).sum := by decide
  have hdescent : baseEnd_6156 < baseStart_6156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164 : List Nat := [2, 4, 3, 2, 2, 1, 1, 3, 5]
def baseStart_6164 : Nat := 118140960795 + 6164 * 2 ^ 59
def prefixEnd_6164 : Nat := 4983230072969 + 3 ^ 40 * 6164 * 2
def baseEnd_6164 : Nat := 351677194935457446851

theorem tailTrace_6164 : CollatzResearch.WordTrace tailWord_6164 prefixEnd_6164 351677194935457446851 := by
  unfold tailWord_6164
  simp only [CollatzResearch.WordTrace]
  refine ⟨112409774838177786248773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149879699784237048331697 112409774838177786248773)
  ·
    refine ⟨21076832782158334921645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112409774838177786248773 21076832782158334921645)
    ·
      refine ⟨7903812293309375595617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21076832782158334921645 7903812293309375595617)
      ·
        refine ⟨5927859219982031696713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7903812293309375595617 5927859219982031696713)
        ·
          refine ⟨4445894414986523772535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5927859219982031696713 4445894414986523772535)
          ·
            refine ⟨6668841622479785658803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445894414986523772535 6668841622479785658803)
            ·
              refine ⟨10003262433719678488205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668841622479785658803 10003262433719678488205)
              ·
                refine ⟨3751223412644879433077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10003262433719678488205 3751223412644879433077)
                ·
                  refine ⟨351677194935457446851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3751223412644879433077 351677194935457446851)
                  ·
                    rfl

theorem cell23_6164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_6164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164 prefixEnd_6164 := by exact prefixLift 6164
  have htrace : WordTrace (prefixWord ++ tailWord_6164) baseStart_6164 baseEnd_6164 := by
    simpa [prefixWord, tailWord_6164, baseEnd_6164] using wordTrace_append hprefix tailTrace_6164
  have hstable : (prefixWord ++ tailWord_6164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164).length < 2 ^ (prefixWord ++ tailWord_6164).sum := by decide
  have hdescent : baseEnd_6164 < baseStart_6164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 8]
def baseStart_6186 : Nat := 118140960795 + 6186 * 2 ^ 59
def prefixEnd_6186 : Nat := 4983230072969 + 3 ^ 40 * 6186 * 2
def baseEnd_6186 : Nat := 352932369868670105173

theorem tailTrace_6186 : CollatzResearch.WordTrace tailWord_6186 prefixEnd_6186 352932369868670105173 := by
  unfold tailWord_6186
  simp only [CollatzResearch.WordTrace]
  refine ⟨56405488899163332449603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150414637064435553198941 56405488899163332449603)
  ·
    refine ⟨84608233348744998674405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56405488899163332449603 84608233348744998674405)
    ·
      refine ⟨15864043752889687251451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84608233348744998674405 15864043752889687251451)
      ·
        refine ⟨23796065629334530877177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15864043752889687251451 23796065629334530877177)
        ·
          refine ⟨17847049222000898157883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23796065629334530877177 17847049222000898157883)
          ·
            refine ⟨26770573833001347236825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17847049222000898157883 26770573833001347236825)
            ·
              refine ⟨20077930374751010427619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26770573833001347236825 20077930374751010427619)
              ·
                refine ⟨30116895562126515641429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20077930374751010427619 30116895562126515641429)
                ·
                  refine ⟨352932369868670105173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30116895562126515641429 352932369868670105173)
                  ·
                    rfl

theorem cell23_6186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_6186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186 prefixEnd_6186 := by exact prefixLift 6186
  have htrace : WordTrace (prefixWord ++ tailWord_6186) baseStart_6186 baseEnd_6186 := by
    simpa [prefixWord, tailWord_6186, baseEnd_6186] using wordTrace_append hprefix tailTrace_6186
  have hstable : (prefixWord ++ tailWord_6186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186).length < 2 ^ (prefixWord ++ tailWord_6186).sum := by decide
  have hdescent : baseEnd_6186 < baseStart_6186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6190 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_6190 : Nat := 118140960795 + 6190 * 2 ^ 59
def prefixEnd_6190 : Nat := 4983230072969 + 3 ^ 40 * 6190 * 2
def baseEnd_6190 : Nat := 1059481750478671765513

theorem tailTrace_6190 : CollatzResearch.WordTrace tailWord_6190 prefixEnd_6190 1059481750478671765513 := by
  unfold tailWord_6190
  simp only [CollatzResearch.WordTrace]
  refine ⟨28220980947770251618003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150511898388108008629349 28220980947770251618003)
  ·
    refine ⟨42331471421655377427005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28220980947770251618003 42331471421655377427005)
    ·
      refine ⟨15874301783120766535127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42331471421655377427005 15874301783120766535127)
      ·
        refine ⟨23811452674681149802691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15874301783120766535127 23811452674681149802691)
        ·
          refine ⟨35717179012021724704037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23811452674681149802691 35717179012021724704037)
          ·
            refine ⟨6696971064754073382007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35717179012021724704037 6696971064754073382007)
            ·
              refine ⟨10045456597131110073011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6696971064754073382007 10045456597131110073011)
              ·
                refine ⟨15068184895696665109517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10045456597131110073011 15068184895696665109517)
                ·
                  refine ⟨5650569335886249416069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15068184895696665109517 5650569335886249416069)
                  ·
                    refine ⟨1059481750478671765513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5650569335886249416069 1059481750478671765513)
                    ·
                      rfl

theorem cell23_6190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_6190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6190 prefixEnd_6190 := by exact prefixLift 6190
  have htrace : WordTrace (prefixWord ++ tailWord_6190) baseStart_6190 baseEnd_6190 := by
    simpa [prefixWord, tailWord_6190, baseEnd_6190] using wordTrace_append hprefix tailTrace_6190
  have hstable : (prefixWord ++ tailWord_6190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6190).length < 2 ^ (prefixWord ++ tailWord_6190).sum := by decide
  have hdescent : baseEnd_6190 < baseStart_6190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 1, 5]
def baseStart_6216 : Nat := 118140960795 + 6216 * 2 ^ 59
def prefixEnd_6216 : Nat := 4983230072969 + 3 ^ 40 * 6216 * 2
def baseEnd_6216 : Nat := 1063931916150971190473

theorem tailTrace_6216 : CollatzResearch.WordTrace tailWord_6216 prefixEnd_6216 1063931916150971190473 := by
  unfold tailWord_6216
  simp only [CollatzResearch.WordTrace]
  refine ⟨113358072743984226695251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151144096991978968927001 113358072743984226695251)
  ·
    refine ⟨170037109115976340042877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113358072743984226695251 170037109115976340042877)
    ·
      refine ⟨63763915918491127516079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170037109115976340042877 63763915918491127516079)
      ·
        refine ⟨95645873877736691274119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63763915918491127516079 95645873877736691274119)
        ·
          refine ⟨143468810816605036911179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95645873877736691274119 143468810816605036911179)
          ·
            refine ⟨215203216224907555366769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143468810816605036911179 215203216224907555366769)
            ·
              refine ⟨161402412168680666525077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215203216224907555366769 161402412168680666525077)
              ·
                refine ⟨7565738070406906243363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161402412168680666525077 7565738070406906243363)
                ·
                  refine ⟨11348607105610359365045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565738070406906243363 11348607105610359365045)
                  ·
                    refine ⟨1063931916150971190473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11348607105610359365045 1063931916150971190473)
                    ·
                      rfl

theorem cell23_6216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_6216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216 prefixEnd_6216 := by exact prefixLift 6216
  have htrace : WordTrace (prefixWord ++ tailWord_6216) baseStart_6216 baseEnd_6216 := by
    simpa [prefixWord, tailWord_6216, baseEnd_6216] using wordTrace_append hprefix tailTrace_6216
  have hstable : (prefixWord ++ tailWord_6216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216).length < 2 ^ (prefixWord ++ tailWord_6216).sum := by decide
  have hdescent : baseEnd_6216 < baseStart_6216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 4]
def baseStart_6219 : Nat := 118140960795 + 6219 * 2 ^ 59
def prefixEnd_6219 : Nat := 4983230072969 + 3 ^ 40 * 6219 * 2
def baseEnd_6219 : Nat := 3193336190416401833905

theorem tailTrace_6219 : CollatzResearch.WordTrace tailWord_6219 prefixEnd_6219 3193336190416401833905 := by
  unfold tailWord_6219
  simp only [CollatzResearch.WordTrace]
  refine ⟨226825564477099965749711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151217042984733310499807 226825564477099965749711)
  ·
    refine ⟨340238346715649948624567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226825564477099965749711 340238346715649948624567)
    ·
      refine ⟨510357520073474922936851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340238346715649948624567 510357520073474922936851)
      ·
        refine ⟨765536280110212384405277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510357520073474922936851 765536280110212384405277)
        ·
          refine ⟨287076105041329644151979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 765536280110212384405277 287076105041329644151979)
          ·
            refine ⟨430614157561994466227969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287076105041329644151979 430614157561994466227969)
            ·
              refine ⟨322960618171495849670977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430614157561994466227969 322960618171495849670977)
              ·
                refine ⟨242220463628621887253233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322960618171495849670977 242220463628621887253233)
                ·
                  refine ⟨181665347721466415439925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242220463628621887253233 181665347721466415439925)
                  ·
                    refine ⟨17031126348887476447493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181665347721466415439925 17031126348887476447493)
                    ·
                      refine ⟨3193336190416401833905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17031126348887476447493 3193336190416401833905)
                      ·
                        rfl

theorem cell23_6219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 4].length) (baseStart_6219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219 prefixEnd_6219 := by exact prefixLift 6219
  have htrace : WordTrace (prefixWord ++ tailWord_6219) baseStart_6219 baseEnd_6219 := by
    simpa [prefixWord, tailWord_6219, baseEnd_6219] using wordTrace_append hprefix tailTrace_6219
  have hstable : (prefixWord ++ tailWord_6219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219).length < 2 ^ (prefixWord ++ tailWord_6219).sum := by decide
  have hdescent : baseEnd_6219 < baseStart_6219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6233 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 1, 5]
def baseStart_6233 : Nat := 118140960795 + 6233 * 2 ^ 59
def prefixEnd_6233 : Nat := 4983230072969 + 3 ^ 40 * 6233 * 2
def baseEnd_6233 : Nat := 1066841639859782352947

theorem tailTrace_6233 : CollatzResearch.WordTrace tailWord_6233 prefixEnd_6233 1066841639859782352947 := by
  unfold tailWord_6233
  simp only [CollatzResearch.WordTrace]
  refine ⟨227336186426380356759353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151557457617586904506235 227336186426380356759353)
  ·
    refine ⟨170502139819785267569515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227336186426380356759353 170502139819785267569515)
    ·
      refine ⟨255753209729677901354273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170502139819785267569515 255753209729677901354273)
      ·
        refine ⟨191814907297258426015705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255753209729677901354273 191814907297258426015705)
        ·
          refine ⟨143861180472943819511779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191814907297258426015705 143861180472943819511779)
          ·
            refine ⟨215791770709415729267669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143861180472943819511779 215791770709415729267669)
            ·
              refine ⟨5057619626001931154711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 215791770709415729267669 5057619626001931154711)
              ·
                refine ⟨7586429439002896732067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057619626001931154711 7586429439002896732067)
                ·
                  refine ⟨11379644158504345098101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7586429439002896732067 11379644158504345098101)
                  ·
                    refine ⟨1066841639859782352947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11379644158504345098101 1066841639859782352947)
                    ·
                      rfl

theorem cell23_6233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 5].length) (baseStart_6233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6233 prefixEnd_6233 := by exact prefixLift 6233
  have htrace : WordTrace (prefixWord ++ tailWord_6233) baseStart_6233 baseEnd_6233 := by
    simpa [prefixWord, tailWord_6233, baseEnd_6233] using wordTrace_append hprefix tailTrace_6233
  have hstable : (prefixWord ++ tailWord_6233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6233).length < 2 ^ (prefixWord ++ tailWord_6233).sum := by decide
  have hdescent : baseEnd_6233 < baseStart_6233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 2, 4]
def baseStart_6263 : Nat := 118140960795 + 6263 * 2 ^ 59
def prefixEnd_6263 : Nat := 4983230072969 + 3 ^ 40 * 6263 * 2
def baseEnd_6263 : Nat := 1071976446404743227901

theorem tailTrace_6263 : CollatzResearch.WordTrace tailWord_6263 prefixEnd_6263 1071976446404743227901 := by
  unfold tailWord_6263
  simp only [CollatzResearch.WordTrace]
  refine ⟨228430376317695480351443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152286917545130320234295 228430376317695480351443)
  ·
    refine ⟨342645564476543220527165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228430376317695480351443 342645564476543220527165)
    ·
      refine ⟨128492086678703707697687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342645564476543220527165 128492086678703707697687)
      ·
        refine ⟨192738130018055561546531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128492086678703707697687 192738130018055561546531)
        ·
          refine ⟨289107195027083342319797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192738130018055561546531 289107195027083342319797)
          ·
            refine ⟨27103799533789063342481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 289107195027083342319797 27103799533789063342481)
            ·
              refine ⟨20327849650341797506861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27103799533789063342481 20327849650341797506861)
              ·
                refine ⟨7622943618878174065073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20327849650341797506861 7622943618878174065073)
                ·
                  refine ⟨5717207714158630548805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7622943618878174065073 5717207714158630548805)
                  ·
                    refine ⟨1071976446404743227901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5717207714158630548805 1071976446404743227901)
                    ·
                      rfl

theorem cell23_6263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_6263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263 prefixEnd_6263 := by exact prefixLift 6263
  have htrace : WordTrace (prefixWord ++ tailWord_6263) baseStart_6263 baseEnd_6263 := by
    simpa [prefixWord, tailWord_6263, baseEnd_6263] using wordTrace_append hprefix tailTrace_6263
  have hstable : (prefixWord ++ tailWord_6263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263).length < 2 ^ (prefixWord ++ tailWord_6263).sum := by decide
  have hdescent : baseEnd_6263 < baseStart_6263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6290 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_6290 : Nat := 118140960795 + 6290 * 2 ^ 59
def prefixEnd_6290 : Nat := 4983230072969 + 3 ^ 40 * 6290 * 2
def baseEnd_6290 : Nat := 3229793316885624046079

theorem tailTrace_6290 : CollatzResearch.WordTrace tailWord_6290 prefixEnd_6290 3229793316885624046079 := by
  unfold tailWord_6290
  simp only [CollatzResearch.WordTrace]
  refine ⟨57353786804969772896081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152943431479919394389549 57353786804969772896081)
  ·
    refine ⟨43015340103727329672061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57353786804969772896081 43015340103727329672061)
    ·
      refine ⟨16130752538897748627023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43015340103727329672061 16130752538897748627023)
      ·
        refine ⟨24196128808346622940535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16130752538897748627023 24196128808346622940535)
        ·
          refine ⟨36294193212519934410803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24196128808346622940535 36294193212519934410803)
          ·
            refine ⟨54441289818779901616205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36294193212519934410803 54441289818779901616205)
            ·
              refine ⟨20415483682042463106077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54441289818779901616205 20415483682042463106077)
              ·
                refine ⟨7655806380765923664779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20415483682042463106077 7655806380765923664779)
                ·
                  refine ⟨11483709571148885497169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7655806380765923664779 11483709571148885497169)
                  ·
                    refine ⟨8612782178361664122877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11483709571148885497169 8612782178361664122877)
                    ·
                      refine ⟨3229793316885624046079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8612782178361664122877 3229793316885624046079)
                      ·
                        rfl

theorem cell23_6290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_6290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6290 prefixEnd_6290 := by exact prefixLift 6290
  have htrace : WordTrace (prefixWord ++ tailWord_6290) baseStart_6290 baseEnd_6290 := by
    simpa [prefixWord, tailWord_6290, baseEnd_6290] using wordTrace_append hprefix tailTrace_6290
  have hstable : (prefixWord ++ tailWord_6290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6290).length < 2 ^ (prefixWord ++ tailWord_6290).sum := by decide
  have hdescent : baseEnd_6290 < baseStart_6290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6314 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_6314 : Nat := 118140960795 + 6314 * 2 ^ 59
def prefixEnd_6314 : Nat := 4983230072969 + 3 ^ 40 * 6314 * 2
def baseEnd_6314 : Nat := 1080705617531176715323

theorem tailTrace_6314 : CollatzResearch.WordTrace tailWord_6314 prefixEnd_6314 1080705617531176715323 := by
  unfold tailWord_6314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57572624783232797614499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153526999421954126971997 57572624783232797614499)
  ·
    refine ⟨86358937174849196421749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57572624783232797614499 86358937174849196421749)
    ·
      refine ⟨8096150360142112164539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86358937174849196421749 8096150360142112164539)
      ·
        refine ⟨12144225540213168246809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8096150360142112164539 12144225540213168246809)
        ·
          refine ⟨9108169155159876185107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12144225540213168246809 9108169155159876185107)
          ·
            refine ⟨13662253732739814277661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108169155159876185107 13662253732739814277661)
            ·
              refine ⟨5123345149777430354123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13662253732739814277661 5123345149777430354123)
              ·
                refine ⟨7685017724666145531185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123345149777430354123 7685017724666145531185)
                ·
                  refine ⟨5763763293499609148389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7685017724666145531185 5763763293499609148389)
                  ·
                    refine ⟨1080705617531176715323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5763763293499609148389 1080705617531176715323)
                    ·
                      rfl

theorem cell23_6314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_6314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6314 prefixEnd_6314 := by exact prefixLift 6314
  have htrace : WordTrace (prefixWord ++ tailWord_6314) baseStart_6314 baseEnd_6314 := by
    simpa [prefixWord, tailWord_6314, baseEnd_6314] using wordTrace_append hprefix tailTrace_6314
  have hstable : (prefixWord ++ tailWord_6314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6314).length < 2 ^ (prefixWord ++ tailWord_6314).sum := by decide
  have hdescent : baseEnd_6314 < baseStart_6314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6330 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2]
def baseStart_6330 : Nat := 118140960795 + 6330 * 2 ^ 59
def prefixEnd_6330 : Nat := 4983230072969 + 3 ^ 40 * 6330 * 2
def baseEnd_6330 : Nat := 3250332543065467545895

theorem tailTrace_6330 : CollatzResearch.WordTrace tailWord_6330 prefixEnd_6330 3250332543065467545895 := by
  unfold tailWord_6330
  simp only [CollatzResearch.WordTrace]
  refine ⟨57718516768741480760111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153916044716643948693629 57718516768741480760111)
  ·
    refine ⟨86577775153112221140167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57718516768741480760111 86577775153112221140167)
    ·
      refine ⟨129866662729668331710251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86577775153112221140167 129866662729668331710251)
      ·
        refine ⟨194799994094502497565377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129866662729668331710251 194799994094502497565377)
        ·
          refine ⟨146099995570876873174033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194799994094502497565377 146099995570876873174033)
          ·
            refine ⟨109574996678157654880525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146099995570876873174033 109574996678157654880525)
            ·
              refine ⟨41090623754309120580197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109574996678157654880525 41090623754309120580197)
              ·
                refine ⟨7704491953932960108787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41090623754309120580197 7704491953932960108787)
                ·
                  refine ⟨11556737930899440163181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7704491953932960108787 11556737930899440163181)
                  ·
                    refine ⟨4333776724087290061193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11556737930899440163181 4333776724087290061193)
                    ·
                      refine ⟨3250332543065467545895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4333776724087290061193 3250332543065467545895)
                      ·
                        rfl

theorem cell23_6330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_6330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6330 prefixEnd_6330 := by exact prefixLift 6330
  have htrace : WordTrace (prefixWord ++ tailWord_6330) baseStart_6330 baseEnd_6330 := by
    simpa [prefixWord, tailWord_6330, baseEnd_6330] using wordTrace_append hprefix tailTrace_6330
  have hstable : (prefixWord ++ tailWord_6330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6330).length < 2 ^ (prefixWord ++ tailWord_6330).sum := by decide
  have hdescent : baseEnd_6330 < baseStart_6330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6338 : List Nat := [3, 5, 1, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_6338 : Nat := 118140960795 + 6338 * 2 ^ 59
def prefixEnd_6338 : Nat := 4983230072969 + 3 ^ 40 * 6338 * 2
def baseEnd_6338 : Nat := 3254440388301436245859

theorem tailTrace_6338 : CollatzResearch.WordTrace tailWord_6338 prefixEnd_6338 3254440388301436245859 := by
  unfold tailWord_6338
  simp only [CollatzResearch.WordTrace]
  refine ⟨57791462761495822332917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154110567363988859554445 57791462761495822332917)
  ·
    refine ⟨5417949633890233343711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57791462761495822332917 5417949633890233343711)
    ·
      refine ⟨8126924450835350015567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5417949633890233343711 8126924450835350015567)
      ·
        refine ⟨12190386676253025023351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126924450835350015567 12190386676253025023351)
        ·
          refine ⟨18285580014379537535027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12190386676253025023351 18285580014379537535027)
          ·
            refine ⟨27428370021569306302541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18285580014379537535027 27428370021569306302541)
            ·
              refine ⟨10285638758088489863453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27428370021569306302541 10285638758088489863453)
              ·
                refine ⟨3857114534283183698795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10285638758088489863453 3857114534283183698795)
                ·
                  refine ⟨5785671801424775548193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3857114534283183698795 5785671801424775548193)
                  ·
                    refine ⟨4339253851068581661145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5785671801424775548193 4339253851068581661145)
                    ·
                      refine ⟨3254440388301436245859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4339253851068581661145 3254440388301436245859)
                      ·
                        rfl

theorem cell23_6338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_6338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6338 prefixEnd_6338 := by exact prefixLift 6338
  have htrace : WordTrace (prefixWord ++ tailWord_6338) baseStart_6338 baseEnd_6338 := by
    simpa [prefixWord, tailWord_6338, baseEnd_6338] using wordTrace_append hprefix tailTrace_6338
  have hstable : (prefixWord ++ tailWord_6338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6338).length < 2 ^ (prefixWord ++ tailWord_6338).sum := by decide
  have hdescent : baseEnd_6338 < baseStart_6338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6371 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6371 : Nat := 118140960795 + 6371 * 2 ^ 59
def prefixEnd_6371 : Nat := 4983230072969 + 3 ^ 40 * 6371 * 2
def baseEnd_6371 : Nat := 3271385249899807133207

theorem tailTrace_6371 : CollatzResearch.WordTrace tailWord_6371 prefixEnd_6371 3271385249899807133207 := by
  unfold tailWord_6371
  simp only [CollatzResearch.WordTrace]
  refine ⟨232369459926429925282967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154912973284286616855311 232369459926429925282967)
  ·
    refine ⟨348554189889644887924451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232369459926429925282967 348554189889644887924451)
    ·
      refine ⟨522831284834467331886677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348554189889644887924451 522831284834467331886677)
      ·
        refine ⟨6126929119153914045547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 522831284834467331886677 6126929119153914045547)
        ·
          refine ⟨9190393678730871068321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6126929119153914045547 9190393678730871068321)
          ·
            refine ⟨6892795259048153301241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9190393678730871068321 6892795259048153301241)
            ·
              refine ⟨5169596444286114975931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6892795259048153301241 5169596444286114975931)
              ·
                refine ⟨7754394666429172463897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169596444286114975931 7754394666429172463897)
                ·
                  refine ⟨5815795999821879347923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7754394666429172463897 5815795999821879347923)
                  ·
                    refine ⟨8723693999732819021885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5815795999821879347923 8723693999732819021885)
                    ·
                      refine ⟨3271385249899807133207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8723693999732819021885 3271385249899807133207)
                      ·
                        rfl

theorem cell23_6371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6371 prefixEnd_6371 := by exact prefixLift 6371
  have htrace : WordTrace (prefixWord ++ tailWord_6371) baseStart_6371 baseEnd_6371 := by
    simpa [prefixWord, tailWord_6371, baseEnd_6371] using wordTrace_append hprefix tailTrace_6371
  have hstable : (prefixWord ++ tailWord_6371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6371).length < 2 ^ (prefixWord ++ tailWord_6371).sum := by decide
  have hdescent : baseEnd_6371 < baseStart_6371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6381 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_6381 : Nat := 118140960795 + 6381 * 2 ^ 59
def prefixEnd_6381 : Nat := 4983230072969 + 3 ^ 40 * 6381 * 2
def baseEnd_6381 : Nat := 3276520056444768008161

theorem tailTrace_6381 : CollatzResearch.WordTrace tailWord_6381 prefixEnd_6381 3276520056444768008161 := by
  unfold tailWord_6381
  simp only [CollatzResearch.WordTrace]
  refine ⟨232734189890201633146997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155156126593467755431331 232734189890201633146997)
  ·
    refine ⟨21818830302206403107531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 232734189890201633146997 21818830302206403107531)
    ·
      refine ⟨32728245453309604661297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21818830302206403107531 32728245453309604661297)
      ·
        refine ⟨24546184089982203495973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32728245453309604661297 24546184089982203495973)
        ·
          refine ⟨4602409516871663155495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24546184089982203495973 4602409516871663155495)
          ·
            refine ⟨6903614275307494733243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602409516871663155495 6903614275307494733243)
            ·
              refine ⟨10355421412961242099865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6903614275307494733243 10355421412961242099865)
              ·
                refine ⟨7766566059720931574899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10355421412961242099865 7766566059720931574899)
                ·
                  refine ⟨11649849089581397362349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7766566059720931574899 11649849089581397362349)
                  ·
                    refine ⟨4368693408593024010881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11649849089581397362349 4368693408593024010881)
                    ·
                      refine ⟨3276520056444768008161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4368693408593024010881 3276520056444768008161)
                      ·
                        rfl

theorem cell23_6381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_6381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6381 prefixEnd_6381 := by exact prefixLift 6381
  have htrace : WordTrace (prefixWord ++ tailWord_6381) baseStart_6381 baseEnd_6381 := by
    simpa [prefixWord, tailWord_6381, baseEnd_6381] using wordTrace_append hprefix tailTrace_6381
  have hstable : (prefixWord ++ tailWord_6381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6381).length < 2 ^ (prefixWord ++ tailWord_6381).sum := by decide
  have hdescent : baseEnd_6381 < baseStart_6381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417 : List Nat := [1, 2, 2, 1, 1, 7, 2, 2, 5]
def baseStart_6417 : Nat := 118140960795 + 6417 * 2 ^ 59
def prefixEnd_6417 : Nat := 4983230072969 + 3 ^ 40 * 6417 * 2
def baseEnd_6417 : Nat := 366111706667403017555

theorem tailTrace_6417 : CollatzResearch.WordTrace tailWord_6417 prefixEnd_6417 366111706667403017555 := by
  unfold tailWord_6417
  simp only [CollatzResearch.WordTrace]
  refine ⟨234047217759779781457505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156031478506519854305003 234047217759779781457505)
  ·
    refine ⟨175535413319834836093129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234047217759779781457505 175535413319834836093129)
    ·
      refine ⟨131651559989876127069847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175535413319834836093129 131651559989876127069847)
      ·
        refine ⟨197477339984814190604771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131651559989876127069847 197477339984814190604771)
        ·
          refine ⟨296216009977221285907157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197477339984814190604771 296216009977221285907157)
          ·
            refine ⟨6942562733841123888449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 296216009977221285907157 6942562733841123888449)
            ·
              refine ⟨5206922050380842916337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6942562733841123888449 5206922050380842916337)
              ·
                refine ⟨3905191537785632187253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5206922050380842916337 3905191537785632187253)
                ·
                  refine ⟨366111706667403017555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3905191537785632187253 366111706667403017555)
                  ·
                    rfl

theorem cell23_6417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 5].length) (baseStart_6417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417 prefixEnd_6417 := by exact prefixLift 6417
  have htrace : WordTrace (prefixWord ++ tailWord_6417) baseStart_6417 baseEnd_6417 := by
    simpa [prefixWord, tailWord_6417, baseEnd_6417] using wordTrace_append hprefix tailTrace_6417
  have hstable : (prefixWord ++ tailWord_6417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417).length < 2 ^ (prefixWord ++ tailWord_6417).sum := by decide
  have hdescent : baseEnd_6417 < baseStart_6417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6423 : Nat := 118140960795 + 6423 * 2 ^ 59
def prefixEnd_6423 : Nat := 4983230072969 + 3 ^ 40 * 6423 * 2
def baseEnd_6423 : Nat := 3298086243933603682967

theorem tailTrace_6423 : CollatzResearch.WordTrace tailWord_6423 prefixEnd_6423 3298086243933603682967 := by
  unfold tailWord_6423
  simp only [CollatzResearch.WordTrace]
  refine ⟨234266055738042806175923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156177370492028537450615 234266055738042806175923)
  ·
    refine ⟨351399083607064209263885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234266055738042806175923 351399083607064209263885)
    ·
      refine ⟨131774656352649078473957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351399083607064209263885 131774656352649078473957)
      ·
        refine ⟨24707748066121702213867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131774656352649078473957 24707748066121702213867)
        ·
          refine ⟨37061622099182553320801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24707748066121702213867 37061622099182553320801)
          ·
            refine ⟨27796216574386914990601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37061622099182553320801 27796216574386914990601)
            ·
              refine ⟨20847162430790186242951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27796216574386914990601 20847162430790186242951)
              ·
                refine ⟨31270743646185279364427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20847162430790186242951 31270743646185279364427)
                ·
                  refine ⟨46906115469277919046641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31270743646185279364427 46906115469277919046641)
                  ·
                    refine ⟨35179586601958439284981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46906115469277919046641 35179586601958439284981)
                    ·
                      refine ⟨3298086243933603682967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35179586601958439284981 3298086243933603682967)
                      ·
                        rfl

theorem cell23_6423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423 prefixEnd_6423 := by exact prefixLift 6423
  have htrace : WordTrace (prefixWord ++ tailWord_6423) baseStart_6423 baseEnd_6423 := by
    simpa [prefixWord, tailWord_6423, baseEnd_6423] using wordTrace_append hprefix tailTrace_6423
  have hstable : (prefixWord ++ tailWord_6423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423).length < 2 ^ (prefixWord ++ tailWord_6423).sum := by decide
  have hdescent : baseEnd_6423 < baseStart_6423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_6433 : Nat := 118140960795 + 6433 * 2 ^ 59
def prefixEnd_6433 : Nat := 4983230072969 + 3 ^ 40 * 6433 * 2
def baseEnd_6433 : Nat := 3303221050478564557921

theorem tailTrace_6433 : CollatzResearch.WordTrace tailWord_6433 prefixEnd_6433 3303221050478564557921 := by
  unfold tailWord_6433
  simp only [CollatzResearch.WordTrace]
  refine ⟨234630785701814514039953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156420523801209676026635 234630785701814514039953)
  ·
    refine ⟨175973089276360885529965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234630785701814514039953 175973089276360885529965)
    ·
      refine ⟨65989908478635332073737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175973089276360885529965 65989908478635332073737)
      ·
        refine ⟨49492431358976499055303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65989908478635332073737 49492431358976499055303)
        ·
          refine ⟨74238647038464748582955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49492431358976499055303 74238647038464748582955)
          ·
            refine ⟨111357970557697122874433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74238647038464748582955 111357970557697122874433)
            ·
              refine ⟨83518477918272842155825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111357970557697122874433 83518477918272842155825)
              ·
                refine ⟨62638858438704631616869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83518477918272842155825 62638858438704631616869)
                ·
                  refine ⟨11744785957257118428163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62638858438704631616869 11744785957257118428163)
                  ·
                    refine ⟨17617178935885677642245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11744785957257118428163 17617178935885677642245)
                    ·
                      refine ⟨3303221050478564557921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17617178935885677642245 3303221050478564557921)
                      ·
                        rfl

theorem cell23_6433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_6433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433 prefixEnd_6433 := by exact prefixLift 6433
  have htrace : WordTrace (prefixWord ++ tailWord_6433) baseStart_6433 baseEnd_6433 := by
    simpa [prefixWord, tailWord_6433, baseEnd_6433] using wordTrace_append hprefix tailTrace_6433
  have hstable : (prefixWord ++ tailWord_6433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433).length < 2 ^ (prefixWord ++ tailWord_6433).sum := by decide
  have hdescent : baseEnd_6433 < baseStart_6433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6450 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_6450 : Nat := 118140960795 + 6450 * 2 ^ 59
def prefixEnd_6450 : Nat := 4983230072969 + 3 ^ 40 * 6450 * 2
def baseEnd_6450 : Nat := 3311950221604998045343

theorem tailTrace_6450 : CollatzResearch.WordTrace tailWord_6450 prefixEnd_6450 3311950221604998045343 := by
  unfold tailWord_6450
  simp only [CollatzResearch.WordTrace]
  refine ⟨58812706660056604352201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156833884426817611605869 58812706660056604352201)
  ·
    refine ⟨44109529995042453264151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58812706660056604352201 44109529995042453264151)
    ·
      refine ⟨66164294992563679896227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44109529995042453264151 66164294992563679896227)
      ·
        refine ⟨99246442488845519844341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66164294992563679896227 99246442488845519844341)
        ·
          refine ⟨9304353983329267485407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99246442488845519844341 9304353983329267485407)
          ·
            refine ⟨13956530974993901228111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304353983329267485407 13956530974993901228111)
            ·
              refine ⟨20934796462490851842167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13956530974993901228111 20934796462490851842167)
              ·
                refine ⟨31402194693736277763251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20934796462490851842167 31402194693736277763251)
                ·
                  refine ⟨47103292040604416644877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31402194693736277763251 47103292040604416644877)
                  ·
                    refine ⟨17663734515226656241829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47103292040604416644877 17663734515226656241829)
                    ·
                      refine ⟨3311950221604998045343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17663734515226656241829 3311950221604998045343)
                      ·
                        rfl

theorem cell23_6450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_6450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6450 prefixEnd_6450 := by exact prefixLift 6450
  have htrace : WordTrace (prefixWord ++ tailWord_6450) baseStart_6450 baseEnd_6450 := by
    simpa [prefixWord, tailWord_6450, baseEnd_6450] using wordTrace_append hprefix tailTrace_6450
  have hstable : (prefixWord ++ tailWord_6450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6450).length < 2 ^ (prefixWord ++ tailWord_6450).sum := by decide
  have hdescent : baseEnd_6450 < baseStart_6450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_6553 : Nat := 118140960795 + 6553 * 2 ^ 59
def prefixEnd_6553 : Nat := 4983230072969 + 3 ^ 40 * 6553 * 2
def baseEnd_6553 : Nat := 3364838729018095057369

theorem tailTrace_6553 : CollatzResearch.WordTrace tailWord_6553 prefixEnd_6553 3364838729018095057369 := by
  unfold tailWord_6553
  simp only [CollatzResearch.WordTrace]
  refine ⟨239007545267075008408313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159338363511383338938875 239007545267075008408313)
  ·
    refine ⟨179255658950306256306235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239007545267075008408313 179255658950306256306235)
    ·
      refine ⟨268883488425459384459353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179255658950306256306235 268883488425459384459353)
      ·
        refine ⟨201662616319094538344515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268883488425459384459353 201662616319094538344515)
        ·
          refine ⟨302493924478641807516773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201662616319094538344515 302493924478641807516773)
          ·
            refine ⟨56717610839745338909395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302493924478641807516773 56717610839745338909395)
            ·
              refine ⟨85076416259618008364093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56717610839745338909395 85076416259618008364093)
              ·
                refine ⟨31903656097356753136535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85076416259618008364093 31903656097356753136535)
                ·
                  refine ⟨47855484146035129704803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31903656097356753136535 47855484146035129704803)
                  ·
                    refine ⟨71783226219052694557205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47855484146035129704803 71783226219052694557205)
                    ·
                      refine ⟨3364838729018095057369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71783226219052694557205 3364838729018095057369)
                      ·
                        rfl

theorem cell23_6553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_6553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553 prefixEnd_6553 := by exact prefixLift 6553
  have htrace : WordTrace (prefixWord ++ tailWord_6553) baseStart_6553 baseEnd_6553 := by
    simpa [prefixWord, tailWord_6553, baseEnd_6553] using wordTrace_append hprefix tailTrace_6553
  have hstable : (prefixWord ++ tailWord_6553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553).length < 2 ^ (prefixWord ++ tailWord_6553).sum := by decide
  have hdescent : baseEnd_6553 < baseStart_6553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6557 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_6557 : Nat := 118140960795 + 6557 * 2 ^ 59
def prefixEnd_6557 : Nat := 4983230072969 + 3 ^ 40 * 6557 * 2
def baseEnd_6557 : Nat := 3366892651636079407351

theorem tailTrace_6557 : CollatzResearch.WordTrace tailWord_6557 prefixEnd_6557 3366892651636079407351 := by
  unfold tailWord_6557
  simp only [CollatzResearch.WordTrace]
  refine ⟨239153437252583691553925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159435624835055794369283 239153437252583691553925)
  ·
    refine ⟨44841269484859442166361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239153437252583691553925 44841269484859442166361)
    ·
      refine ⟨33630952113644581624771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44841269484859442166361 33630952113644581624771)
      ·
        refine ⟨50446428170466872437157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33630952113644581624771 50446428170466872437157)
        ·
          refine ⟨9458705281962538581967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50446428170466872437157 9458705281962538581967)
          ·
            refine ⟨14188057922943807872951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9458705281962538581967 14188057922943807872951)
            ·
              refine ⟨21282086884415711809427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14188057922943807872951 21282086884415711809427)
              ·
                refine ⟨31923130326623567714141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21282086884415711809427 31923130326623567714141)
                ·
                  refine ⟨11971173872483837892803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31923130326623567714141 11971173872483837892803)
                  ·
                    refine ⟨17956760808725756839205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11971173872483837892803 17956760808725756839205)
                    ·
                      refine ⟨3366892651636079407351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17956760808725756839205 3366892651636079407351)
                      ·
                        rfl

theorem cell23_6557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_6557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6557 prefixEnd_6557 := by exact prefixLift 6557
  have htrace : WordTrace (prefixWord ++ tailWord_6557) baseStart_6557 baseEnd_6557 := by
    simpa [prefixWord, tailWord_6557, baseEnd_6557] using wordTrace_append hprefix tailTrace_6557
  have hstable : (prefixWord ++ tailWord_6557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6557).length < 2 ^ (prefixWord ++ tailWord_6557).sum := by decide
  have hdescent : baseEnd_6557 < baseStart_6557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_6561 : Nat := 118140960795 + 6561 * 2 ^ 59
def prefixEnd_6561 : Nat := 4983230072969 + 3 ^ 40 * 6561 * 2
def baseEnd_6561 : Nat := 3368946574254063757333

theorem tailTrace_6561 : CollatzResearch.WordTrace tailWord_6561 prefixEnd_6561 3368946574254063757333 := by
  unfold tailWord_6561
  simp only [CollatzResearch.WordTrace]
  refine ⟨239299329238092374699537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159532886158728249799691 239299329238092374699537)
  ·
    refine ⟨179474496928569281024653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239299329238092374699537 179474496928569281024653)
    ·
      refine ⟨67302936348213480384245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179474496928569281024653 67302936348213480384245)
      ·
        refine ⟨6309650282645013786023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67302936348213480384245 6309650282645013786023)
        ·
          refine ⟨9464475423967520679035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6309650282645013786023 9464475423967520679035)
          ·
            refine ⟨14196713135951281018553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9464475423967520679035 14196713135951281018553)
            ·
              refine ⟨10647534851963460763915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14196713135951281018553 10647534851963460763915)
              ·
                refine ⟨15971302277945191145873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10647534851963460763915 15971302277945191145873)
                ·
                  refine ⟨11978476708458893359405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15971302277945191145873 11978476708458893359405)
                  ·
                    refine ⟨4491928765672085009777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11978476708458893359405 4491928765672085009777)
                    ·
                      refine ⟨3368946574254063757333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4491928765672085009777 3368946574254063757333)
                      ·
                        rfl

theorem cell23_6561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_6561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561 prefixEnd_6561 := by exact prefixLift 6561
  have htrace : WordTrace (prefixWord ++ tailWord_6561) baseStart_6561 baseEnd_6561 := by
    simpa [prefixWord, tailWord_6561, baseEnd_6561] using wordTrace_append hprefix tailTrace_6561
  have hstable : (prefixWord ++ tailWord_6561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561).length < 2 ^ (prefixWord ++ tailWord_6561).sum := by decide
  have hdescent : baseEnd_6561 < baseStart_6561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563 : List Nat := [1, 1, 1, 4, 1, 4, 2, 9]
def baseStart_6563 : Nat := 118140960795 + 6563 * 2 ^ 59
def prefixEnd_6563 : Nat := 4983230072969 + 3 ^ 40 * 6563 * 2
def baseEnd_6563 : Nat := 124813834650483553049

theorem tailTrace_6563 : CollatzResearch.WordTrace tailWord_6563 prefixEnd_6563 124813834650483553049 := by
  unfold tailWord_6563
  simp only [CollatzResearch.WordTrace]
  refine ⟨239372275230846716272343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159581516820564477514895 239372275230846716272343)
  ·
    refine ⟨359058412846270074408515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239372275230846716272343 359058412846270074408515)
    ·
      refine ⟨538587619269405111612773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359058412846270074408515 538587619269405111612773)
      ·
        refine ⟨100985178613013458427395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 538587619269405111612773 100985178613013458427395)
        ·
          refine ⟨151477767919520187641093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100985178613013458427395 151477767919520187641093)
          ·
            refine ⟨28402081484910035182705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151477767919520187641093 28402081484910035182705)
            ·
              refine ⟨21301561113682526387029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28402081484910035182705 21301561113682526387029)
              ·
                refine ⟨124813834650483553049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21301561113682526387029 124813834650483553049)
                ·
                  rfl

theorem cell23_6563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 9].length) (baseStart_6563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563 prefixEnd_6563 := by exact prefixLift 6563
  have htrace : WordTrace (prefixWord ++ tailWord_6563) baseStart_6563 baseEnd_6563 := by
    simpa [prefixWord, tailWord_6563, baseEnd_6563] using wordTrace_append hprefix tailTrace_6563
  have hstable : (prefixWord ++ tailWord_6563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563).length < 2 ^ (prefixWord ++ tailWord_6563).sum := by decide
  have hdescent : baseEnd_6563 < baseStart_6563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 5]
def baseStart_6577 : Nat := 118140960795 + 6577 * 2 ^ 59
def prefixEnd_6577 : Nat := 4983230072969 + 3 ^ 40 * 6577 * 2
def baseEnd_6577 : Nat := 3377162264726001157259

theorem tailTrace_6577 : CollatzResearch.WordTrace tailWord_6577 prefixEnd_6577 3377162264726001157259 := by
  unfold tailWord_6577
  simp only [CollatzResearch.WordTrace]
  refine ⟨239882897180127107281985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159921931453418071521323 239882897180127107281985)
  ·
    refine ⟨179912172885095330461489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239882897180127107281985 179912172885095330461489)
    ·
      refine ⟨134934129663821497846117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179912172885095330461489 134934129663821497846117)
      ·
        refine ⟨25300149311966530846147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134934129663821497846117 25300149311966530846147)
        ·
          refine ⟨37950223967949796269221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25300149311966530846147 37950223967949796269221)
          ·
            refine ⟨7115666993990586800479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37950223967949796269221 7115666993990586800479)
            ·
              refine ⟨10673500490985880200719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7115666993990586800479 10673500490985880200719)
              ·
                refine ⟨16010250736478820301079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10673500490985880200719 16010250736478820301079)
                ·
                  refine ⟨24015376104718230451619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16010250736478820301079 24015376104718230451619)
                  ·
                    refine ⟨36023064157077345677429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24015376104718230451619 36023064157077345677429)
                    ·
                      refine ⟨3377162264726001157259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36023064157077345677429 3377162264726001157259)
                      ·
                        rfl

theorem cell23_6577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_6577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577 prefixEnd_6577 := by exact prefixLift 6577
  have htrace : WordTrace (prefixWord ++ tailWord_6577) baseStart_6577 baseEnd_6577 := by
    simpa [prefixWord, tailWord_6577, baseEnd_6577] using wordTrace_append hprefix tailTrace_6577
  have hstable : (prefixWord ++ tailWord_6577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577).length < 2 ^ (prefixWord ++ tailWord_6577).sum := by decide
  have hdescent : baseEnd_6577 < baseStart_6577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 5]
def baseStart_6603 : Nat := 118140960795 + 6603 * 2 ^ 59
def prefixEnd_6603 : Nat := 4983230072969 + 3 ^ 40 * 6603 * 2
def baseEnd_6603 : Nat := 3390512761742899432139

theorem tailTrace_6603 : CollatzResearch.WordTrace tailWord_6603 prefixEnd_6603 3390512761742899432139 := by
  unfold tailWord_6603
  simp only [CollatzResearch.WordTrace]
  refine ⟨240831195085933547728463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160554130057289031818975 240831195085933547728463)
  ·
    refine ⟨361246792628900321592695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240831195085933547728463 361246792628900321592695)
    ·
      refine ⟨541870188943350482389043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361246792628900321592695 541870188943350482389043)
      ·
        refine ⟨812805283415025723583565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541870188943350482389043 812805283415025723583565)
        ·
          refine ⟨304801981280634646343837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812805283415025723583565 304801981280634646343837)
          ·
            refine ⟨114300742980237992378939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304801981280634646343837 114300742980237992378939)
            ·
              refine ⟨171451114470356988568409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114300742980237992378939 171451114470356988568409)
              ·
                refine ⟨128588335852767741426307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171451114470356988568409 128588335852767741426307)
                ·
                  refine ⟨192882503779151612139461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128588335852767741426307 192882503779151612139461)
                  ·
                    refine ⟨36165469458590927276149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192882503779151612139461 36165469458590927276149)
                    ·
                      refine ⟨3390512761742899432139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36165469458590927276149 3390512761742899432139)
                      ·
                        rfl

theorem cell23_6603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_6603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603 prefixEnd_6603 := by exact prefixLift 6603
  have htrace : WordTrace (prefixWord ++ tailWord_6603) baseStart_6603 baseEnd_6603 := by
    simpa [prefixWord, tailWord_6603, baseEnd_6603] using wordTrace_append hprefix tailTrace_6603
  have hstable : (prefixWord ++ tailWord_6603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603).length < 2 ^ (prefixWord ++ tailWord_6603).sum := by decide
  have hdescent : baseEnd_6603 < baseStart_6603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 3, 3, 2]
def baseStart_6617 : Nat := 118140960795 + 6617 * 2 ^ 59
def prefixEnd_6617 : Nat := 4983230072969 + 3 ^ 40 * 6617 * 2
def baseEnd_6617 : Nat := 3397701490905844657075

theorem tailTrace_6617 : CollatzResearch.WordTrace tailWord_6617 prefixEnd_6617 3397701490905844657075 := by
  unfold tailWord_6617
  simp only [CollatzResearch.WordTrace]
  refine ⟨241341817035213938738105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160894544690142625825403 241341817035213938738105)
  ·
    refine ⟨181006362776410454053579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241341817035213938738105 181006362776410454053579)
    ·
      refine ⟨271509544164615681080369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181006362776410454053579 271509544164615681080369)
      ·
        refine ⟨203632158123461760810277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271509544164615681080369 203632158123461760810277)
        ·
          refine ⟨38181029648149080151927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203632158123461760810277 38181029648149080151927)
          ·
            refine ⟨57271544472223620227891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38181029648149080151927 57271544472223620227891)
            ·
              refine ⟨85907316708335430341837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57271544472223620227891 85907316708335430341837)
              ·
                refine ⟨32215243765625786378189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85907316708335430341837 32215243765625786378189)
                ·
                  refine ⟨12080716412109669891821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32215243765625786378189 12080716412109669891821)
                  ·
                    refine ⟨4530268654541126209433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12080716412109669891821 4530268654541126209433)
                    ·
                      refine ⟨3397701490905844657075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530268654541126209433 3397701490905844657075)
                      ·
                        rfl

theorem cell23_6617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_6617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617 prefixEnd_6617 := by exact prefixLift 6617
  have htrace : WordTrace (prefixWord ++ tailWord_6617) baseStart_6617 baseEnd_6617 := by
    simpa [prefixWord, tailWord_6617, baseEnd_6617] using wordTrace_append hprefix tailTrace_6617
  have hstable : (prefixWord ++ tailWord_6617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617).length < 2 ^ (prefixWord ++ tailWord_6617).sum := by decide
  have hdescent : baseEnd_6617 < baseStart_6617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6650 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_6650 : Nat := 118140960795 + 6650 * 2 ^ 59
def prefixEnd_6650 : Nat := 4983230072969 + 3 ^ 40 * 6650 * 2
def baseEnd_6650 : Nat := 3414646352504215544423

theorem tailTrace_6650 : CollatzResearch.WordTrace tailWord_6650 prefixEnd_6650 3414646352504215544423 := by
  unfold tailWord_6650
  simp only [CollatzResearch.WordTrace]
  refine ⟨60636356478915143672351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161696950610440383126269 60636356478915143672351)
  ·
    refine ⟨90954534718372715508527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60636356478915143672351 90954534718372715508527)
    ·
      refine ⟨136431802077559073262791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90954534718372715508527 136431802077559073262791)
      ·
        refine ⟨204647703116338609894187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136431802077559073262791 204647703116338609894187)
        ·
          refine ⟨306971554674507914841281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204647703116338609894187 306971554674507914841281)
          ·
            refine ⟨230228666005880936130961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306971554674507914841281 230228666005880936130961)
            ·
              refine ⟨172671499504410702098221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230228666005880936130961 172671499504410702098221)
              ·
                refine ⟨64751812314154013286833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172671499504410702098221 64751812314154013286833)
                ·
                  refine ⟨48563859235615509965125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64751812314154013286833 48563859235615509965125)
                  ·
                    refine ⟨9105723606677908118461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48563859235615509965125 9105723606677908118461)
                    ·
                      refine ⟨3414646352504215544423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9105723606677908118461 3414646352504215544423)
                      ·
                        rfl

theorem cell23_6650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_6650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6650 prefixEnd_6650 := by exact prefixLift 6650
  have htrace : WordTrace (prefixWord ++ tailWord_6650) baseStart_6650 baseEnd_6650 := by
    simpa [prefixWord, tailWord_6650, baseEnd_6650] using wordTrace_append hprefix tailTrace_6650
  have hstable : (prefixWord ++ tailWord_6650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6650).length < 2 ^ (prefixWord ++ tailWord_6650).sum := by decide
  have hdescent : baseEnd_6650 < baseStart_6650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6658 : Nat := 118140960795 + 6658 * 2 ^ 59
def prefixEnd_6658 : Nat := 4983230072969 + 3 ^ 40 * 6658 * 2
def baseEnd_6658 : Nat := 3418754197740184244387

theorem tailTrace_6658 : CollatzResearch.WordTrace tailWord_6658 prefixEnd_6658 3418754197740184244387 := by
  unfold tailWord_6658
  simp only [CollatzResearch.WordTrace]
  refine ⟨60709302471669485245157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161891473257785293987085 60709302471669485245157)
  ·
    refine ⟨11382994213438028483467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60709302471669485245157 11382994213438028483467)
    ·
      refine ⟨17074491320157042725201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11382994213438028483467 17074491320157042725201)
      ·
        refine ⟨12805868490117782043901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17074491320157042725201 12805868490117782043901)
        ·
          refine ⟨4802200683794168266463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12805868490117782043901 4802200683794168266463)
          ·
            refine ⟨7203301025691252399695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802200683794168266463 7203301025691252399695)
            ·
              refine ⟨10804951538536878599543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7203301025691252399695 10804951538536878599543)
              ·
                refine ⟨16207427307805317899315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10804951538536878599543 16207427307805317899315)
                ·
                  refine ⟨24311140961707976848973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16207427307805317899315 24311140961707976848973)
                  ·
                    refine ⟨9116677860640491318365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24311140961707976848973 9116677860640491318365)
                    ·
                      refine ⟨3418754197740184244387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116677860640491318365 3418754197740184244387)
                      ·
                        rfl

theorem cell23_6658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658 prefixEnd_6658 := by exact prefixLift 6658
  have htrace : WordTrace (prefixWord ++ tailWord_6658) baseStart_6658 baseEnd_6658 := by
    simpa [prefixWord, tailWord_6658, baseEnd_6658] using wordTrace_append hprefix tailTrace_6658
  have hstable : (prefixWord ++ tailWord_6658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658).length < 2 ^ (prefixWord ++ tailWord_6658).sum := by decide
  have hdescent : baseEnd_6658 < baseStart_6658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6707 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 2, 5, 2]
def baseStart_6707 : Nat := 118140960795 + 6707 * 2 ^ 59
def prefixEnd_6707 : Nat := 4983230072969 + 3 ^ 40 * 6707 * 2
def baseEnd_6707 : Nat := 3443914749810492531661

theorem tailTrace_6707 : CollatzResearch.WordTrace tailWord_6707 prefixEnd_6707 3443914749810492531661 := by
  unfold tailWord_6707
  simp only [CollatzResearch.WordTrace]
  refine ⟨244624386709159309514375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163082924472772873009583 244624386709159309514375)
  ·
    refine ⟨366936580063738964271563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244624386709159309514375 366936580063738964271563)
    ·
      refine ⟨550404870095608446407345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366936580063738964271563 550404870095608446407345)
      ·
        refine ⟨412803652571706334805509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550404870095608446407345 412803652571706334805509)
        ·
          refine ⟨77400684857194937776033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412803652571706334805509 77400684857194937776033)
          ·
            refine ⟨58050513642896203332025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77400684857194937776033 58050513642896203332025)
            ·
              refine ⟨43537885232172152499019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58050513642896203332025 43537885232172152499019)
              ·
                refine ⟨65306827848258228748529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43537885232172152499019 65306827848258228748529)
                ·
                  refine ⟨48980120886193671561397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65306827848258228748529 48980120886193671561397)
                  ·
                    refine ⟨4591886333080656708881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48980120886193671561397 4591886333080656708881)
                    ·
                      refine ⟨3443914749810492531661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4591886333080656708881 3443914749810492531661)
                      ·
                        rfl

theorem cell23_6707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 5, 2].length) (baseStart_6707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6707 prefixEnd_6707 := by exact prefixLift 6707
  have htrace : WordTrace (prefixWord ++ tailWord_6707) baseStart_6707 baseEnd_6707 := by
    simpa [prefixWord, tailWord_6707, baseEnd_6707] using wordTrace_append hprefix tailTrace_6707
  have hstable : (prefixWord ++ tailWord_6707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6707).length < 2 ^ (prefixWord ++ tailWord_6707).sum := by decide
  have hdescent : baseEnd_6707 < baseStart_6707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6720 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_6720 : Nat := 118140960795 + 6720 * 2 ^ 59
def prefixEnd_6720 : Nat := 4983230072969 + 3 ^ 40 * 6720 * 2
def baseEnd_6720 : Nat := 3450589998318941669101

theorem tailTrace_6720 : CollatzResearch.WordTrace tailWord_6720 prefixEnd_6720 3450589998318941669101 := by
  unfold tailWord_6720
  simp only [CollatzResearch.WordTrace]
  refine ⟨122549267831031264868807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163399023774708353158409 122549267831031264868807)
  ·
    refine ⟨183823901746546897303211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122549267831031264868807 183823901746546897303211)
    ·
      refine ⟨275735852619820345954817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183823901746546897303211 275735852619820345954817)
      ·
        refine ⟨206801889464865259466113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275735852619820345954817 206801889464865259466113)
        ·
          refine ⟨155101417098648944599585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206801889464865259466113 155101417098648944599585)
          ·
            refine ⟨116326062823986708449689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155101417098648944599585 116326062823986708449689)
            ·
              refine ⟨87244547117990031337267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116326062823986708449689 87244547117990031337267)
              ·
                refine ⟨130866820676985047005901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87244547117990031337267 130866820676985047005901)
                ·
                  refine ⟨49075057753869392627213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130866820676985047005901 49075057753869392627213)
                  ·
                    refine ⟨18403146657701022235205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49075057753869392627213 18403146657701022235205)
                    ·
                      refine ⟨3450589998318941669101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18403146657701022235205 3450589998318941669101)
                      ·
                        rfl

theorem cell23_6720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_6720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6720 prefixEnd_6720 := by exact prefixLift 6720
  have htrace : WordTrace (prefixWord ++ tailWord_6720) baseStart_6720 baseEnd_6720 := by
    simpa [prefixWord, tailWord_6720, baseEnd_6720] using wordTrace_append hprefix tailTrace_6720
  have hstable : (prefixWord ++ tailWord_6720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6720).length < 2 ^ (prefixWord ++ tailWord_6720).sum := by decide
  have hdescent : baseEnd_6720 < baseStart_6720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_6737 : Nat := 118140960795 + 6737 * 2 ^ 59
def prefixEnd_6737 : Nat := 4983230072969 + 3 ^ 40 * 6737 * 2
def baseEnd_6737 : Nat := 3459319169445375156523

theorem tailTrace_6737 : CollatzResearch.WordTrace tailWord_6737 prefixEnd_6737 3459319169445375156523 := by
  unfold tailWord_6737
  simp only [CollatzResearch.WordTrace]
  refine ⟨245718576600474433106465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163812384400316288737643 245718576600474433106465)
  ·
    refine ⟨184288932450355824829849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245718576600474433106465 184288932450355824829849)
    ·
      refine ⟨138216699337766868622387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184288932450355824829849 138216699337766868622387)
      ·
        refine ⟨207325049006650302933581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138216699337766868622387 207325049006650302933581)
        ·
          refine ⟨77746893377493863600093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207325049006650302933581 77746893377493863600093)
          ·
            refine ⟨29155085016560198850035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77746893377493863600093 29155085016560198850035)
            ·
              refine ⟨43732627524840298275053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29155085016560198850035 43732627524840298275053)
              ·
                refine ⟨16399735321815111853145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43732627524840298275053 16399735321815111853145)
                ·
                  refine ⟨12299801491361333889859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16399735321815111853145 12299801491361333889859)
                  ·
                    refine ⟨18449702237042000834789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12299801491361333889859 18449702237042000834789)
                    ·
                      refine ⟨3459319169445375156523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18449702237042000834789 3459319169445375156523)
                      ·
                        rfl

theorem cell23_6737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_6737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737 prefixEnd_6737 := by exact prefixLift 6737
  have htrace : WordTrace (prefixWord ++ tailWord_6737) baseStart_6737 baseEnd_6737 := by
    simpa [prefixWord, tailWord_6737, baseEnd_6737] using wordTrace_append hprefix tailTrace_6737
  have hstable : (prefixWord ++ tailWord_6737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737).length < 2 ^ (prefixWord ++ tailWord_6737).sum := by decide
  have hdescent : baseEnd_6737 < baseStart_6737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6777 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 6]
def baseStart_6777 : Nat := 118140960795 + 6777 * 2 ^ 59
def prefixEnd_6777 : Nat := 4983230072969 + 3 ^ 40 * 6777 * 2
def baseEnd_6777 : Nat := 386650932847246517371

theorem tailTrace_6777 : CollatzResearch.WordTrace tailWord_6777 prefixEnd_6777 386650932847246517371 := by
  unfold tailWord_6777
  simp only [CollatzResearch.WordTrace]
  refine ⟨247177496455561264562585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164784997637040843041723 247177496455561264562585)
  ·
    refine ⟨185383122341670948421939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247177496455561264562585 185383122341670948421939)
    ·
      refine ⟨278074683512506422632909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185383122341670948421939 278074683512506422632909)
      ·
        refine ⟨104278006317189908487341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278074683512506422632909 104278006317189908487341)
        ·
          refine ⟨39104252368946215682753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104278006317189908487341 39104252368946215682753)
          ·
            refine ⟨29328189276709661762065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39104252368946215682753 29328189276709661762065)
            ·
              refine ⟨21996141957532246321549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29328189276709661762065 21996141957532246321549)
              ·
                refine ⟨8248553234074592370581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21996141957532246321549 8248553234074592370581)
                ·
                  refine ⟨386650932847246517371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8248553234074592370581 386650932847246517371)
                  ·
                    rfl

theorem cell23_6777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 6].length) (baseStart_6777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6777 prefixEnd_6777 := by exact prefixLift 6777
  have htrace : WordTrace (prefixWord ++ tailWord_6777) baseStart_6777 baseEnd_6777 := by
    simpa [prefixWord, tailWord_6777, baseEnd_6777] using wordTrace_append hprefix tailTrace_6777
  have hstable : (prefixWord ++ tailWord_6777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6777).length < 2 ^ (prefixWord ++ tailWord_6777).sum := by decide
  have hdescent : baseEnd_6777 < baseStart_6777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6800 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_6800 : Nat := 118140960795 + 6800 * 2 ^ 59
def prefixEnd_6800 : Nat := 4983230072969 + 3 ^ 40 * 6800 * 2
def baseEnd_6800 : Nat := 3491668450678628668733

theorem tailTrace_6800 : CollatzResearch.WordTrace tailWord_6800 prefixEnd_6800 3491668450678628668733 := by
  unfold tailWord_6800
  simp only [CollatzResearch.WordTrace]
  refine ⟨124008187686118096324927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165344250248157461766569 124008187686118096324927)
  ·
    refine ⟨186012281529177144487391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124008187686118096324927 186012281529177144487391)
    ·
      refine ⟨279018422293765716731087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186012281529177144487391 279018422293765716731087)
      ·
        refine ⟨418527633440648575096631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279018422293765716731087 418527633440648575096631)
        ·
          refine ⟨627791450160972862644947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418527633440648575096631 627791450160972862644947)
          ·
            refine ⟨941687175241459293967421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627791450160972862644947 941687175241459293967421)
            ·
              refine ⟨353132690715547235237783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 941687175241459293967421 353132690715547235237783)
              ·
                refine ⟨529699036073320852856675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353132690715547235237783 529699036073320852856675)
                ·
                  refine ⟨794548554109981279285013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529699036073320852856675 794548554109981279285013)
                  ·
                    refine ⟨37244463473905372466485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 794548554109981279285013 37244463473905372466485)
                    ·
                      refine ⟨3491668450678628668733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37244463473905372466485 3491668450678628668733)
                      ·
                        rfl

theorem cell23_6800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_6800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6800 prefixEnd_6800 := by exact prefixLift 6800
  have htrace : WordTrace (prefixWord ++ tailWord_6800) baseStart_6800 baseEnd_6800 := by
    simpa [prefixWord, tailWord_6800, baseEnd_6800] using wordTrace_append hprefix tailTrace_6800
  have hstable : (prefixWord ++ tailWord_6800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6800).length < 2 ^ (prefixWord ++ tailWord_6800).sum := by decide
  have hdescent : baseEnd_6800 < baseStart_6800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_6844 : Nat := 118140960795 + 6844 * 2 ^ 59
def prefixEnd_6844 : Nat := 4983230072969 + 3 ^ 40 * 6844 * 2
def baseEnd_6844 : Nat := 3514261599476456518531

theorem tailTrace_6844 : CollatzResearch.WordTrace tailWord_6844 prefixEnd_6844 3514261599476456518531 := by
  unfold tailWord_6844
  simp only [CollatzResearch.WordTrace]
  refine ⟨124810593606415853625793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166414124808554471501057 124810593606415853625793)
  ·
    refine ⟨93607945204811890219345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124810593606415853625793 93607945204811890219345)
    ·
      refine ⟨70205958903608917664509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93607945204811890219345 70205958903608917664509)
      ·
        refine ⟨26327234588853344124191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70205958903608917664509 26327234588853344124191)
        ·
          refine ⟨39490851883280016186287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26327234588853344124191 39490851883280016186287)
          ·
            refine ⟨59236277824920024279431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39490851883280016186287 59236277824920024279431)
            ·
              refine ⟨88854416737380036419147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59236277824920024279431 88854416737380036419147)
              ·
                refine ⟨133281625106070054628721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88854416737380036419147 133281625106070054628721)
                ·
                  refine ⟨99961218829552540971541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133281625106070054628721 99961218829552540971541)
                  ·
                    refine ⟨4685682132635275358041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99961218829552540971541 4685682132635275358041)
                    ·
                      refine ⟨3514261599476456518531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685682132635275358041 3514261599476456518531)
                      ·
                        rfl

theorem cell23_6844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_6844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844 prefixEnd_6844 := by exact prefixLift 6844
  have htrace : WordTrace (prefixWord ++ tailWord_6844) baseStart_6844 baseEnd_6844 := by
    simpa [prefixWord, tailWord_6844, baseEnd_6844] using wordTrace_append hprefix tailTrace_6844
  have hstable : (prefixWord ++ tailWord_6844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844).length < 2 ^ (prefixWord ++ tailWord_6844).sum := by decide
  have hdescent : baseEnd_6844 < baseStart_6844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6898 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_6898 : Nat := 118140960795 + 6898 * 2 ^ 59
def prefixEnd_6898 : Nat := 4983230072969 + 3 ^ 40 * 6898 * 2
def baseEnd_6898 : Nat := 3541989554819245243283

theorem tailTrace_6898 : CollatzResearch.WordTrace tailWord_6898 prefixEnd_6898 3541989554819245243283 := by
  unfold tailWord_6898
  simp only [CollatzResearch.WordTrace]
  refine ⟨62897682254299732429337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167727152678132619811565 62897682254299732429337)
  ·
    refine ⟨47173261690724799322003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62897682254299732429337 47173261690724799322003)
    ·
      refine ⟨70759892536087198983005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47173261690724799322003 70759892536087198983005)
      ·
        refine ⟨26534959701032699618627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70759892536087198983005 26534959701032699618627)
        ·
          refine ⟨39802439551549049427941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26534959701032699618627 39802439551549049427941)
          ·
            refine ⟨7462957415915446767739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39802439551549049427941 7462957415915446767739)
            ·
              refine ⟨11194436123873170151609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462957415915446767739 11194436123873170151609)
              ·
                refine ⟨8395827092904877613707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11194436123873170151609 8395827092904877613707)
                ·
                  refine ⟨12593740639357316420561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8395827092904877613707 12593740639357316420561)
                  ·
                    refine ⟨9445305479517987315421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12593740639357316420561 9445305479517987315421)
                    ·
                      refine ⟨3541989554819245243283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9445305479517987315421 3541989554819245243283)
                      ·
                        rfl

theorem cell23_6898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_6898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6898 prefixEnd_6898 := by exact prefixLift 6898
  have htrace : WordTrace (prefixWord ++ tailWord_6898) baseStart_6898 baseEnd_6898 := by
    simpa [prefixWord, tailWord_6898, baseEnd_6898] using wordTrace_append hprefix tailTrace_6898
  have hstable : (prefixWord ++ tailWord_6898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6898).length < 2 ^ (prefixWord ++ tailWord_6898).sum := by decide
  have hdescent : baseEnd_6898 < baseStart_6898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6917 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_6917 : Nat := 118140960795 + 6917 * 2 ^ 59
def prefixEnd_6917 : Nat := 4983230072969 + 3 ^ 40 * 6917 * 2
def baseEnd_6917 : Nat := 3551745687254670905695

theorem tailTrace_6917 : CollatzResearch.WordTrace tailWord_6917 prefixEnd_6917 3551745687254670905695 := by
  unfold tailWord_6917
  simp only [CollatzResearch.WordTrace]
  refine ⟨252283715948365174659005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168189143965576783106003 252283715948365174659005)
  ·
    refine ⟨94606393480636940497127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252283715948365174659005 94606393480636940497127)
    ·
      refine ⟨141909590220955410745691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94606393480636940497127 141909590220955410745691)
      ·
        refine ⟨212864385331433116118537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141909590220955410745691 212864385331433116118537)
        ·
          refine ⟨159648288998574837088903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212864385331433116118537 159648288998574837088903)
          ·
            refine ⟨239472433497862255633355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159648288998574837088903 239472433497862255633355)
            ·
              refine ⟨359208650246793383450033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239472433497862255633355 359208650246793383450033)
              ·
                refine ⟨269406487685095037587525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359208650246793383450033 269406487685095037587525)
                ·
                  refine ⟨50513716440955319547661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269406487685095037587525 50513716440955319547661)
                  ·
                    refine ⟨18942643665358244830373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50513716440955319547661 18942643665358244830373)
                    ·
                      refine ⟨3551745687254670905695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18942643665358244830373 3551745687254670905695)
                      ·
                        rfl

theorem cell23_6917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_6917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6917 prefixEnd_6917 := by exact prefixLift 6917
  have htrace : WordTrace (prefixWord ++ tailWord_6917) baseStart_6917 baseEnd_6917 := by
    simpa [prefixWord, tailWord_6917, baseEnd_6917] using wordTrace_append hprefix tailTrace_6917
  have hstable : (prefixWord ++ tailWord_6917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6917).length < 2 ^ (prefixWord ++ tailWord_6917).sum := by decide
  have hdescent : baseEnd_6917 < baseStart_6917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6921 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 1, 3, 2]
def baseStart_6921 : Nat := 118140960795 + 6921 * 2 ^ 59
def prefixEnd_6921 : Nat := 4983230072969 + 3 ^ 40 * 6921 * 2
def baseEnd_6921 : Nat := 3553799609872655255677

theorem tailTrace_6921 : CollatzResearch.WordTrace tailWord_6921 prefixEnd_6921 3553799609872655255677 := by
  unfold tailWord_6921
  simp only [CollatzResearch.WordTrace]
  refine ⟨252429607933873857804617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168286405289249238536411 252429607933873857804617)
  ·
    refine ⟨189322205950405393353463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252429607933873857804617 189322205950405393353463)
    ·
      refine ⟨283983308925608090030195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189322205950405393353463 283983308925608090030195)
      ·
        refine ⟨425974963388412135045293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283983308925608090030195 425974963388412135045293)
        ·
          refine ⟨159740611270654550641985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425974963388412135045293 159740611270654550641985)
          ·
            refine ⟨119805458452990912981489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159740611270654550641985 119805458452990912981489)
            ·
              refine ⟨89854093839743184736117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119805458452990912981489 89854093839743184736117)
              ·
                refine ⟨8423821297475923569011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89854093839743184736117 8423821297475923569011)
                ·
                  refine ⟨12635731946213885353517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8423821297475923569011 12635731946213885353517)
                  ·
                    refine ⟨4738399479830207007569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12635731946213885353517 4738399479830207007569)
                    ·
                      refine ⟨3553799609872655255677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4738399479830207007569 3553799609872655255677)
                      ·
                        rfl

theorem cell23_6921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 3, 2].length) (baseStart_6921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6921 prefixEnd_6921 := by exact prefixLift 6921
  have htrace : WordTrace (prefixWord ++ tailWord_6921) baseStart_6921 baseEnd_6921 := by
    simpa [prefixWord, tailWord_6921, baseEnd_6921] using wordTrace_append hprefix tailTrace_6921
  have hstable : (prefixWord ++ tailWord_6921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6921).length < 2 ^ (prefixWord ++ tailWord_6921).sum := by decide
  have hdescent : baseEnd_6921 < baseStart_6921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 2, 6]
def baseStart_6927 : Nat := 118140960795 + 6927 * 2 ^ 59
def prefixEnd_6927 : Nat := 4983230072969 + 3 ^ 40 * 6927 * 2
def baseEnd_6927 : Nat := 1185626831266543926883

theorem tailTrace_6927 : CollatzResearch.WordTrace tailWord_6927 prefixEnd_6927 1185626831266543926883 := by
  unfold tailWord_6927
  simp only [CollatzResearch.WordTrace]
  refine ⟨252648445912136882523035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168432297274757921682023 252648445912136882523035)
  ·
    refine ⟨378972668868205323784553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252648445912136882523035 378972668868205323784553)
    ·
      refine ⟨284229501651153992838415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378972668868205323784553 284229501651153992838415)
      ·
        refine ⟨426344252476730989257623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284229501651153992838415 426344252476730989257623)
        ·
          refine ⟨639516378715096483886435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426344252476730989257623 639516378715096483886435)
          ·
            refine ⟨959274568072644725829653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639516378715096483886435 959274568072644725829653)
            ·
              refine ⟨44965995378405221523265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 959274568072644725829653 44965995378405221523265)
              ·
                refine ⟨33724496533803916142449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44965995378405221523265 33724496533803916142449)
                ·
                  refine ⟨25293372400352937106837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33724496533803916142449 25293372400352937106837)
                  ·
                    refine ⟨1185626831266543926883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25293372400352937106837 1185626831266543926883)
                    ·
                      rfl

theorem cell23_6927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_6927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927 prefixEnd_6927 := by exact prefixLift 6927
  have htrace : WordTrace (prefixWord ++ tailWord_6927) baseStart_6927 baseEnd_6927 := by
    simpa [prefixWord, tailWord_6927, baseEnd_6927] using wordTrace_append hprefix tailTrace_6927
  have hstable : (prefixWord ++ tailWord_6927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927).length < 2 ^ (prefixWord ++ tailWord_6927).sum := by decide
  have hdescent : baseEnd_6927 < baseStart_6927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6937 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_6937 : Nat := 118140960795 + 6937 * 2 ^ 59
def prefixEnd_6937 : Nat := 4983230072969 + 3 ^ 40 * 6937 * 2
def baseEnd_6937 : Nat := 3562015300344592655603

theorem tailTrace_6937 : CollatzResearch.WordTrace tailWord_6937 prefixEnd_6937 3562015300344592655603 := by
  unfold tailWord_6937
  simp only [CollatzResearch.WordTrace]
  refine ⟨253013175875908590387065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168675450583939060258043 253013175875908590387065)
  ·
    refine ⟨189759881906931442790299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253013175875908590387065 189759881906931442790299)
    ·
      refine ⟨284639822860397164185449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189759881906931442790299 284639822860397164185449)
      ·
        refine ⟨213479867145297873139087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284639822860397164185449 213479867145297873139087)
        ·
          refine ⟨320219800717946809708631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213479867145297873139087 320219800717946809708631)
          ·
            refine ⟨480329701076920214562947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320219800717946809708631 480329701076920214562947)
            ·
              refine ⟨720494551615380321844421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480329701076920214562947 720494551615380321844421)
              ·
                refine ⟨135092728427883810345829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720494551615380321844421 135092728427883810345829)
                ·
                  refine ⟨25329886580228214439843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135092728427883810345829 25329886580228214439843)
                  ·
                    refine ⟨37994829870342321659765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25329886580228214439843 37994829870342321659765)
                    ·
                      refine ⟨3562015300344592655603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37994829870342321659765 3562015300344592655603)
                      ·
                        rfl

theorem cell23_6937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_6937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6937 prefixEnd_6937 := by exact prefixLift 6937
  have htrace : WordTrace (prefixWord ++ tailWord_6937) baseStart_6937 baseEnd_6937 := by
    simpa [prefixWord, tailWord_6937, baseEnd_6937] using wordTrace_append hprefix tailTrace_6937
  have hstable : (prefixWord ++ tailWord_6937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6937).length < 2 ^ (prefixWord ++ tailWord_6937).sum := by decide
  have hdescent : baseEnd_6937 < baseStart_6937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 2, 6]
def baseStart_6944 : Nat := 118140960795 + 6944 * 2 ^ 59
def prefixEnd_6944 : Nat := 4983230072969 + 3 ^ 40 * 6944 * 2
def baseEnd_6944 : Nat := 1188536554975355089357

theorem tailTrace_6944 : CollatzResearch.WordTrace tailWord_6944 prefixEnd_6944 1188536554975355089357 := by
  unfold tailWord_6944
  simp only [CollatzResearch.WordTrace]
  refine ⟨126634243425274392945943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168845657900365857261257 126634243425274392945943)
  ·
    refine ⟨189951365137911589418915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126634243425274392945943 189951365137911589418915)
    ·
      refine ⟨284927047706867384128373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189951365137911589418915 284927047706867384128373)
      ·
        refine ⟨26711910722518817262035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284927047706867384128373 26711910722518817262035)
        ·
          refine ⟨40067866083778225893053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26711910722518817262035 40067866083778225893053)
          ·
            refine ⟨15025449781416834709895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40067866083778225893053 15025449781416834709895)
            ·
              refine ⟨22538174672125252064843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15025449781416834709895 22538174672125252064843)
              ·
                refine ⟨33807262008187878097265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22538174672125252064843 33807262008187878097265)
                ·
                  refine ⟨25355446506140908572949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33807262008187878097265 25355446506140908572949)
                  ·
                    refine ⟨1188536554975355089357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25355446506140908572949 1188536554975355089357)
                    ·
                      rfl

theorem cell23_6944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_6944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944 prefixEnd_6944 := by exact prefixLift 6944
  have htrace : WordTrace (prefixWord ++ tailWord_6944) baseStart_6944 baseEnd_6944 := by
    simpa [prefixWord, tailWord_6944, baseEnd_6944] using wordTrace_append hprefix tailTrace_6944
  have hstable : (prefixWord ++ tailWord_6944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944).length < 2 ^ (prefixWord ++ tailWord_6944).sum := by decide
  have hdescent : baseEnd_6944 < baseStart_6944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_6984 : Nat := 118140960795 + 6984 * 2 ^ 59
def prefixEnd_6984 : Nat := 4983230072969 + 3 ^ 40 * 6984 * 2
def baseEnd_6984 : Nat := 3586148891105908767887

theorem tailTrace_6984 : CollatzResearch.WordTrace tailWord_6984 prefixEnd_6984 3586148891105908767887 := by
  unfold tailWord_6984
  simp only [CollatzResearch.WordTrace]
  refine ⟨127363703352817808674003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169818271137090411565337 127363703352817808674003)
  ·
    refine ⟨191045555029226713011005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127363703352817808674003 191045555029226713011005)
    ·
      refine ⟨71642083135960017379127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191045555029226713011005 71642083135960017379127)
      ·
        refine ⟨107463124703940026068691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71642083135960017379127 107463124703940026068691)
        ·
          refine ⟨161194687055910039103037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107463124703940026068691 161194687055910039103037)
          ·
            refine ⟨60448007645966264663639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161194687055910039103037 60448007645966264663639)
            ·
              refine ⟨90672011468949396995459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60448007645966264663639 90672011468949396995459)
              ·
                refine ⟨136008017203424095493189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90672011468949396995459 136008017203424095493189)
                ·
                  refine ⟨25501503225642017904973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136008017203424095493189 25501503225642017904973)
                  ·
                    refine ⟨9563063709615756714365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25501503225642017904973 9563063709615756714365)
                    ·
                      refine ⟨3586148891105908767887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9563063709615756714365 3586148891105908767887)
                      ·
                        rfl

theorem cell23_6984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_6984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984 prefixEnd_6984 := by exact prefixLift 6984
  have htrace : WordTrace (prefixWord ++ tailWord_6984) baseStart_6984 baseEnd_6984 := by
    simpa [prefixWord, tailWord_6984, baseEnd_6984] using wordTrace_append hprefix tailTrace_6984
  have hstable : (prefixWord ++ tailWord_6984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984).length < 2 ^ (prefixWord ++ tailWord_6984).sum := by decide
  have hdescent : baseEnd_6984 < baseStart_6984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 2, 2, 2]
def baseStart_6985 : Nat := 118140960795 + 6985 * 2 ^ 59
def prefixEnd_6985 : Nat := 4983230072969 + 3 ^ 40 * 6985 * 2
def baseEnd_6985 : Nat := 3586662371760404855383

theorem tailTrace_6985 : CollatzResearch.WordTrace tailWord_6985 prefixEnd_6985 3586662371760404855383 := by
  unfold tailWord_6985
  simp only [CollatzResearch.WordTrace]
  refine ⟨254763879702012788134409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169842586468008525422939 254763879702012788134409)
  ·
    refine ⟨191072909776509591100807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254763879702012788134409 191072909776509591100807)
    ·
      refine ⟨286609364664764386651211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191072909776509591100807 286609364664764386651211)
      ·
        refine ⟨429914046997146579976817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286609364664764386651211 429914046997146579976817)
        ·
          refine ⟨322435535247859934982613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429914046997146579976817 322435535247859934982613)
          ·
            refine ⟨7557082857371717226155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 322435535247859934982613 7557082857371717226155)
            ·
              refine ⟨11335624286057575839233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7557082857371717226155 11335624286057575839233)
              ·
                refine ⟨8501718214543181879425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11335624286057575839233 8501718214543181879425)
                ·
                  refine ⟨6376288660907386409569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8501718214543181879425 6376288660907386409569)
                  ·
                    refine ⟨4782216495680539807177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6376288660907386409569 4782216495680539807177)
                    ·
                      refine ⟨3586662371760404855383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782216495680539807177 3586662371760404855383)
                      ·
                        rfl

theorem cell23_6985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 2, 2].length) (baseStart_6985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985 prefixEnd_6985 := by exact prefixLift 6985
  have htrace : WordTrace (prefixWord ++ tailWord_6985) baseStart_6985 baseEnd_6985 := by
    simpa [prefixWord, tailWord_6985, baseEnd_6985] using wordTrace_append hprefix tailTrace_6985
  have hstable : (prefixWord ++ tailWord_6985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985).length < 2 ^ (prefixWord ++ tailWord_6985).sum := by decide
  have hdescent : baseEnd_6985 < baseStart_6985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_7024 : Nat := 118140960795 + 7024 * 2 ^ 59
def prefixEnd_7024 : Nat := 4983230072969 + 3 ^ 40 * 7024 * 2
def baseEnd_7024 : Nat := 3606688117285752267703

theorem tailTrace_7024 : CollatzResearch.WordTrace tailWord_7024 prefixEnd_7024 3606688117285752267703 := by
  unfold tailWord_7024
  simp only [CollatzResearch.WordTrace]
  refine ⟨128093163280361224402063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170790884373814965869417 128093163280361224402063)
  ·
    refine ⟨192139744920541836603095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128093163280361224402063 192139744920541836603095)
    ·
      refine ⟨288209617380812754904643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192139744920541836603095 288209617380812754904643)
      ·
        refine ⟨432314426071219132356965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288209617380812754904643 432314426071219132356965)
        ·
          refine ⟨81058954888353587316931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432314426071219132356965 81058954888353587316931)
          ·
            refine ⟨121588432332530380975397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81058954888353587316931 121588432332530380975397)
            ·
              refine ⟨22797831062349446432887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121588432332530380975397 22797831062349446432887)
              ·
                refine ⟨34196746593524169649331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22797831062349446432887 34196746593524169649331)
                ·
                  refine ⟨51295119890286254473997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34196746593524169649331 51295119890286254473997)
                  ·
                    refine ⟨19235669958857345427749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51295119890286254473997 19235669958857345427749)
                    ·
                      refine ⟨3606688117285752267703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19235669958857345427749 3606688117285752267703)
                      ·
                        rfl

theorem cell23_7024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_7024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024 prefixEnd_7024 := by exact prefixLift 7024
  have htrace : WordTrace (prefixWord ++ tailWord_7024) baseStart_7024 baseEnd_7024 := by
    simpa [prefixWord, tailWord_7024, baseEnd_7024] using wordTrace_append hprefix tailTrace_7024
  have hstable : (prefixWord ++ tailWord_7024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024).length < 2 ^ (prefixWord ++ tailWord_7024).sum := by decide
  have hdescent : baseEnd_7024 < baseStart_7024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7042 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 7]
def baseStart_7042 : Nat := 118140960795 + 7042 * 2 ^ 59
def prefixEnd_7042 : Nat := 4983230072969 + 3 ^ 40 * 7042 * 2
def baseEnd_7042 : Nat := 401770085451853538069

theorem tailTrace_7042 : CollatzResearch.WordTrace tailWord_7042 prefixEnd_7042 401770085451853538069 := by
  unfold tailWord_7042
  simp only [CollatzResearch.WordTrace]
  refine ⟨64210710123877880739845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 171228560330341015306253 64210710123877880739845)
  ·
    refine ⟨12039508148227102638721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64210710123877880739845 12039508148227102638721)
    ·
      refine ⟨9029631111170326979041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12039508148227102638721 9029631111170326979041)
      ·
        refine ⟨6772223333377745234281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9029631111170326979041 6772223333377745234281)
        ·
          refine ⟨5079167500033308925711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6772223333377745234281 5079167500033308925711)
          ·
            refine ⟨7618751250049963388567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5079167500033308925711 7618751250049963388567)
            ·
              refine ⟨11428126875074945082851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7618751250049963388567 11428126875074945082851)
              ·
                refine ⟨17142190312612417624277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11428126875074945082851 17142190312612417624277)
                ·
                  refine ⟨401770085451853538069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17142190312612417624277 401770085451853538069)
                  ·
                    rfl

theorem cell23_7042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_7042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7042 prefixEnd_7042 := by exact prefixLift 7042
  have htrace : WordTrace (prefixWord ++ tailWord_7042) baseStart_7042 baseEnd_7042 := by
    simpa [prefixWord, tailWord_7042, baseEnd_7042] using wordTrace_append hprefix tailTrace_7042
  have hstable : (prefixWord ++ tailWord_7042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7042).length < 2 ^ (prefixWord ++ tailWord_7042).sum := by decide
  have hdescent : baseEnd_7042 < baseStart_7042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7051 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 3, 4]
def baseStart_7051 : Nat := 118140960795 + 7051 * 2 ^ 59
def prefixEnd_7051 : Nat := 4983230072969 + 3 ^ 40 * 7051 * 2
def baseEnd_7051 : Nat := 1206850698319048876693

theorem tailTrace_7051 : CollatzResearch.WordTrace tailWord_7051 prefixEnd_7051 1206850698319048876693 := by
  unfold tailWord_7051
  simp only [CollatzResearch.WordTrace]
  refine ⟨257171097462906060037007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171447398308604040024671 257171097462906060037007)
  ·
    refine ⟨385756646194359090055511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257171097462906060037007 385756646194359090055511)
    ·
      refine ⟨578634969291538635083267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385756646194359090055511 578634969291538635083267)
      ·
        refine ⟨867952453937307952624901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578634969291538635083267 867952453937307952624901)
        ·
          refine ⟨162741085113245241117169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 867952453937307952624901 162741085113245241117169)
          ·
            refine ⟨122055813834933930837877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162741085113245241117169 122055813834933930837877)
            ·
              refine ⟨11442732547025056016051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122055813834933930837877 11442732547025056016051)
              ·
                refine ⟨17164098820537584024077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11442732547025056016051 17164098820537584024077)
                ·
                  refine ⟨6436537057701594009029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17164098820537584024077 6436537057701594009029)
                  ·
                    refine ⟨1206850698319048876693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6436537057701594009029 1206850698319048876693)
                    ·
                      rfl

theorem cell23_7051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 4].length) (baseStart_7051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7051 prefixEnd_7051 := by exact prefixLift 7051
  have htrace : WordTrace (prefixWord ++ tailWord_7051) baseStart_7051 baseEnd_7051 := by
    simpa [prefixWord, tailWord_7051, baseEnd_7051] using wordTrace_append hprefix tailTrace_7051
  have hstable : (prefixWord ++ tailWord_7051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7051).length < 2 ^ (prefixWord ++ tailWord_7051).sum := by decide
  have hdescent : baseEnd_7051 < baseStart_7051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7091 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 3]
def baseStart_7091 : Nat := 118140960795 + 7091 * 2 ^ 59
def prefixEnd_7091 : Nat := 4983230072969 + 3 ^ 40 * 7091 * 2
def baseEnd_7091 : Nat := 3641091321136990129895

theorem tailTrace_7091 : CollatzResearch.WordTrace tailWord_7091 prefixEnd_7091 3641091321136990129895 := by
  unfold tailWord_7091
  simp only [CollatzResearch.WordTrace]
  refine ⟨258630017317992891493127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172420011545328594328751 258630017317992891493127)
  ·
    refine ⟨387945025976989337239691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258630017317992891493127 387945025976989337239691)
    ·
      refine ⟨581917538965484005859537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387945025976989337239691 581917538965484005859537)
      ·
        refine ⟨436438154224113004394653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581917538965484005859537 436438154224113004394653)
        ·
          refine ⟨163664307834042376647995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436438154224113004394653 163664307834042376647995)
          ·
            refine ⟨245496461751063564971993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163664307834042376647995 245496461751063564971993)
            ·
              refine ⟨184122346313297673728995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245496461751063564971993 184122346313297673728995)
              ·
                refine ⟨276183519469946510593493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184122346313297673728995 276183519469946510593493)
                ·
                  refine ⟨6473051237576871342035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 276183519469946510593493 6473051237576871342035)
                  ·
                    refine ⟨9709576856365307013053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6473051237576871342035 9709576856365307013053)
                    ·
                      refine ⟨3641091321136990129895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9709576856365307013053 3641091321136990129895)
                      ·
                        rfl

theorem cell23_7091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 3].length) (baseStart_7091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7091 prefixEnd_7091 := by exact prefixLift 7091
  have htrace : WordTrace (prefixWord ++ tailWord_7091) baseStart_7091 baseEnd_7091 := by
    simpa [prefixWord, tailWord_7091, baseEnd_7091] using wordTrace_append hprefix tailTrace_7091
  have hstable : (prefixWord ++ tailWord_7091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7091).length < 2 ^ (prefixWord ++ tailWord_7091).sum := by decide
  have hdescent : baseEnd_7091 < baseStart_7091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_7125 : Nat := 118140960795 + 7125 * 2 ^ 59
def prefixEnd_7125 : Nat := 4983230072969 + 3 ^ 40 * 7125 * 2
def baseEnd_7125 : Nat := 3658549663389857104739

theorem tailTrace_7125 : CollatzResearch.WordTrace tailWord_7125 prefixEnd_7125 3658549663389857104739 := by
  unfold tailWord_7125
  simp only [CollatzResearch.WordTrace]
  refine ⟨259870099194816698230829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173246732796544465487219 259870099194816698230829)
  ·
    refine ⟨97451287198056261836561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259870099194816698230829 97451287198056261836561)
    ·
      refine ⟨73088465398542196377421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97451287198056261836561 73088465398542196377421)
      ·
        refine ⟨27408174524453323641533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73088465398542196377421 27408174524453323641533)
        ·
          refine ⟨10278065446669996365575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27408174524453323641533 10278065446669996365575)
          ·
            refine ⟨15417098170004994548363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278065446669996365575 15417098170004994548363)
            ·
              refine ⟨23125647255007491822545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15417098170004994548363 23125647255007491822545)
              ·
                refine ⟨17344235441255618866909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23125647255007491822545 17344235441255618866909)
                ·
                  refine ⟨6504088290470857075091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17344235441255618866909 6504088290470857075091)
                  ·
                    refine ⟨9756132435706285612637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6504088290470857075091 9756132435706285612637)
                    ·
                      refine ⟨3658549663389857104739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9756132435706285612637 3658549663389857104739)
                      ·
                        rfl

theorem cell23_7125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_7125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125 prefixEnd_7125 := by exact prefixLift 7125
  have htrace : WordTrace (prefixWord ++ tailWord_7125) baseStart_7125 baseEnd_7125 := by
    simpa [prefixWord, tailWord_7125, baseEnd_7125] using wordTrace_append hprefix tailTrace_7125
  have hstable : (prefixWord ++ tailWord_7125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125).length < 2 ^ (prefixWord ++ tailWord_7125).sum := by decide
  have hdescent : baseEnd_7125 < baseStart_7125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 2, 4]
def baseStart_7175 : Nat := 118140960795 + 7175 * 2 ^ 59
def prefixEnd_7175 : Nat := 4983230072969 + 3 ^ 40 * 7175 * 2
def baseEnd_7175 : Nat := 1228074565371553826503

theorem tailTrace_7175 : CollatzResearch.WordTrace tailWord_7175 prefixEnd_7175 1228074565371553826503 := by
  unfold tailWord_7175
  simp only [CollatzResearch.WordTrace]
  refine ⟨261693749013675237550979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174462499342450158367319 261693749013675237550979)
  ·
    refine ⟨392540623520512856326469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261693749013675237550979 392540623520512856326469)
    ·
      refine ⟨73601366910096160561213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392540623520512856326469 73601366910096160561213)
      ·
        refine ⟨27600512591286060210455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73601366910096160561213 27600512591286060210455)
        ·
          refine ⟨41400768886929090315683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27600512591286060210455 41400768886929090315683)
          ·
            refine ⟨62101153330393635473525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41400768886929090315683 62101153330393635473525)
            ·
              refine ⟨5821983124724403325643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62101153330393635473525 5821983124724403325643)
              ·
                refine ⟨8732974687086604988465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821983124724403325643 8732974687086604988465)
                ·
                  refine ⟨6549731015314953741349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8732974687086604988465 6549731015314953741349)
                  ·
                    refine ⟨1228074565371553826503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6549731015314953741349 1228074565371553826503)
                    ·
                      rfl

theorem cell23_7175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_7175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175 prefixEnd_7175 := by exact prefixLift 7175
  have htrace : WordTrace (prefixWord ++ tailWord_7175) baseStart_7175 baseEnd_7175 := by
    simpa [prefixWord, tailWord_7175, baseEnd_7175] using wordTrace_append hprefix tailTrace_7175
  have hstable : (prefixWord ++ tailWord_7175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175).length < 2 ^ (prefixWord ++ tailWord_7175).sum := by decide
  have hdescent : baseEnd_7175 < baseStart_7175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_7178 : Nat := 118140960795 + 7178 * 2 ^ 59
def prefixEnd_7178 : Nat := 4983230072969 + 3 ^ 40 * 7178 * 2
def baseEnd_7178 : Nat := 3685764138078149741995

theorem tailTrace_7178 : CollatzResearch.WordTrace tailWord_7178 prefixEnd_7178 3685764138078149741995 := by
  unfold tailWord_7178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65450792000701687477547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174535445335204499940125 65450792000701687477547)
  ·
    refine ⟨98176188001052531216321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65450792000701687477547 98176188001052531216321)
    ·
      refine ⟨73632141000789398412241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98176188001052531216321 73632141000789398412241)
      ·
        refine ⟨55224105750592048809181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73632141000789398412241 55224105750592048809181)
        ·
          refine ⟨20709039656472018303443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55224105750592048809181 20709039656472018303443)
          ·
            refine ⟨31063559484708027455165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20709039656472018303443 31063559484708027455165)
            ·
              refine ⟨11648834806765510295687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31063559484708027455165 11648834806765510295687)
              ·
                refine ⟨17473252210148265443531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11648834806765510295687 17473252210148265443531)
                ·
                  refine ⟨26209878315222398165297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17473252210148265443531 26209878315222398165297)
                  ·
                    refine ⟨19657408736416798623973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26209878315222398165297 19657408736416798623973)
                    ·
                      refine ⟨3685764138078149741995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19657408736416798623973 3685764138078149741995)
                      ·
                        rfl

theorem cell23_7178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_7178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178 prefixEnd_7178 := by exact prefixLift 7178
  have htrace : WordTrace (prefixWord ++ tailWord_7178) baseStart_7178 baseEnd_7178 := by
    simpa [prefixWord, tailWord_7178, baseEnd_7178] using wordTrace_append hprefix tailTrace_7178
  have hstable : (prefixWord ++ tailWord_7178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178).length < 2 ^ (prefixWord ++ tailWord_7178).sum := by decide
  have hdescent : baseEnd_7178 < baseStart_7178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7199 : List Nat := [1, 1, 2, 4, 1, 5, 1, 3, 1, 2, 2]
def baseStart_7199 : Nat := 118140960795 + 7199 * 2 ^ 59
def prefixEnd_7199 : Nat := 4983230072969 + 3 ^ 40 * 7199 * 2
def baseEnd_7199 : Nat := 3696547231822567579399

theorem tailTrace_7199 : CollatzResearch.WordTrace tailWord_7199 prefixEnd_7199 3696547231822567579399 := by
  unfold tailWord_7199
  simp only [CollatzResearch.WordTrace]
  refine ⟨262569100926727336424651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175046067284484890949767 262569100926727336424651)
  ·
    refine ⟨393853651390091004636977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262569100926727336424651 393853651390091004636977)
    ·
      refine ⟨295390238542568253477733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393853651390091004636977 295390238542568253477733)
      ·
        refine ⟨55385669726731547527075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295390238542568253477733 55385669726731547527075)
        ·
          refine ⟨83078504590097321290613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55385669726731547527075 83078504590097321290613)
          ·
            refine ⟨7788609805321623870995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83078504590097321290613 7788609805321623870995)
            ·
              refine ⟨11682914707982435806493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7788609805321623870995 11682914707982435806493)
              ·
                refine ⟨4381093015493413427435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11682914707982435806493 4381093015493413427435)
                ·
                  refine ⟨6571639523240120141153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4381093015493413427435 6571639523240120141153)
                  ·
                    refine ⟨4928729642430090105865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6571639523240120141153 4928729642430090105865)
                    ·
                      refine ⟨3696547231822567579399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4928729642430090105865 3696547231822567579399)
                      ·
                        rfl

theorem cell23_7199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_7199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7199 prefixEnd_7199 := by exact prefixLift 7199
  have htrace : WordTrace (prefixWord ++ tailWord_7199) baseStart_7199 baseEnd_7199 := by
    simpa [prefixWord, tailWord_7199, baseEnd_7199] using wordTrace_append hprefix tailTrace_7199
  have hstable : (prefixWord ++ tailWord_7199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7199).length < 2 ^ (prefixWord ++ tailWord_7199).sum := by decide
  have hdescent : baseEnd_7199 < baseStart_7199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7221 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_7221 : Nat := 118140960795 + 7221 * 2 ^ 59
def prefixEnd_7221 : Nat := 4983230072969 + 3 ^ 40 * 7221 * 2
def baseEnd_7221 : Nat := 3707843806221481504297

theorem tailTrace_7221 : CollatzResearch.WordTrace tailWord_7221 prefixEnd_7221 3707843806221481504297 := by
  unfold tailWord_7221
  simp only [CollatzResearch.WordTrace]
  refine ⟨263371506847025093725517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175581004564683395817011 263371506847025093725517)
  ·
    refine ⟨98764315067634410147069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263371506847025093725517 98764315067634410147069)
    ·
      refine ⟨37036618150362903805151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98764315067634410147069 37036618150362903805151)
      ·
        refine ⟨55554927225544355707727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37036618150362903805151 55554927225544355707727)
        ·
          refine ⟨83332390838316533561591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55554927225544355707727 83332390838316533561591)
          ·
            refine ⟨124998586257474800342387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83332390838316533561591 124998586257474800342387)
            ·
              refine ⟨187497879386212200513581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124998586257474800342387 187497879386212200513581)
              ·
                refine ⟨70311704769829575192593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187497879386212200513581 70311704769829575192593)
                ·
                  refine ⟨52733778577372181394445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70311704769829575192593 52733778577372181394445)
                  ·
                    refine ⟨19775166966514568022917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52733778577372181394445 19775166966514568022917)
                    ·
                      refine ⟨3707843806221481504297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19775166966514568022917 3707843806221481504297)
                      ·
                        rfl

theorem cell23_7221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_7221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7221 prefixEnd_7221 := by exact prefixLift 7221
  have htrace : WordTrace (prefixWord ++ tailWord_7221) baseStart_7221 baseEnd_7221 := by
    simpa [prefixWord, tailWord_7221, baseEnd_7221] using wordTrace_append hprefix tailTrace_7221
  have hstable : (prefixWord ++ tailWord_7221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7221).length < 2 ^ (prefixWord ++ tailWord_7221).sum := by decide
  have hdescent : baseEnd_7221 < baseStart_7221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 3]
def baseStart_7241 : Nat := 118140960795 + 7241 * 2 ^ 59
def prefixEnd_7241 : Nat := 4983230072969 + 3 ^ 40 * 7241 * 2
def baseEnd_7241 : Nat := 3718113419311403254205

theorem tailTrace_7241 : CollatzResearch.WordTrace tailWord_7241 prefixEnd_7241 3718113419311403254205 := by
  unfold tailWord_7241
  simp only [CollatzResearch.WordTrace]
  refine ⟨264100966774568509453577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176067311183045672969051 264100966774568509453577)
  ·
    refine ⟨198075725080926382090183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264100966774568509453577 198075725080926382090183)
    ·
      refine ⟨297113587621389573135275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198075725080926382090183 297113587621389573135275)
      ·
        refine ⟨445670381432084359702913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297113587621389573135275 445670381432084359702913)
        ·
          refine ⟨334252786074063269777185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445670381432084359702913 334252786074063269777185)
          ·
            refine ⟨250689589555547452332889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334252786074063269777185 250689589555547452332889)
            ·
              refine ⟨188017192166660589249667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250689589555547452332889 188017192166660589249667)
              ·
                refine ⟨282025788249990883874501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188017192166660589249667 282025788249990883874501)
                ·
                  refine ⟨52879835296873290726469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282025788249990883874501 52879835296873290726469)
                  ·
                    refine ⟨9914969118163742011213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52879835296873290726469 9914969118163742011213)
                    ·
                      refine ⟨3718113419311403254205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9914969118163742011213 3718113419311403254205)
                      ·
                        rfl

theorem cell23_7241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_7241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241 prefixEnd_7241 := by exact prefixLift 7241
  have htrace : WordTrace (prefixWord ++ tailWord_7241) baseStart_7241 baseEnd_7241 := by
    simpa [prefixWord, tailWord_7241, baseEnd_7241] using wordTrace_append hprefix tailTrace_7241
  have hstable : (prefixWord ++ tailWord_7241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241).length < 2 ^ (prefixWord ++ tailWord_7241).sum := by decide
  have hdescent : baseEnd_7241 < baseStart_7241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7291 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 4, 5]
def baseStart_7291 : Nat := 118140960795 + 7291 * 2 ^ 59
def prefixEnd_7291 : Nat := 4983230072969 + 3 ^ 40 * 7291 * 2
def baseEnd_7291 : Nat := 1247929150678735876325

theorem tailTrace_7291 : CollatzResearch.WordTrace tailWord_7291 prefixEnd_7291 1247929150678735876325 := by
  unfold tailWord_7291
  simp only [CollatzResearch.WordTrace]
  refine ⟨265924616593427048773727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177283077728951365849151 265924616593427048773727)
  ·
    refine ⟨398886924890140573160591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265924616593427048773727 398886924890140573160591)
    ·
      refine ⟨598330387335210859740887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398886924890140573160591 598330387335210859740887)
      ·
        refine ⟨897495581002816289611331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598330387335210859740887 897495581002816289611331)
        ·
          refine ⟨1346243371504224434416997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897495581002816289611331 1346243371504224434416997)
          ·
            refine ⟨252420632157042081453187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1346243371504224434416997 252420632157042081453187)
            ·
              refine ⟨378630948235563122179781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252420632157042081453187 378630948235563122179781)
              ·
                refine ⟨70993302794168085408709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378630948235563122179781 70993302794168085408709)
                ·
                  refine ⟨13311244273906516014133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70993302794168085408709 13311244273906516014133)
                  ·
                    refine ⟨1247929150678735876325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13311244273906516014133 1247929150678735876325)
                    ·
                      rfl

theorem cell23_7291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 5].length) (baseStart_7291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7291 prefixEnd_7291 := by exact prefixLift 7291
  have htrace : WordTrace (prefixWord ++ tailWord_7291) baseStart_7291 baseEnd_7291 := by
    simpa [prefixWord, tailWord_7291, baseEnd_7291] using wordTrace_append hprefix tailTrace_7291
  have hstable : (prefixWord ++ tailWord_7291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7291).length < 2 ^ (prefixWord ++ tailWord_7291).sum := by decide
  have hdescent : baseEnd_7291 < baseStart_7291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_7328 : Nat := 118140960795 + 7328 * 2 ^ 59
def prefixEnd_7328 : Nat := 4983230072969 + 3 ^ 40 * 7328 * 2
def baseEnd_7328 : Nat := 3762786236252562866305

theorem tailTrace_7328 : CollatzResearch.WordTrace tailWord_7328 prefixEnd_7328 3762786236252562866305 := by
  unfold tailWord_7328
  simp only [CollatzResearch.WordTrace]
  refine ⟨133637058729691183935319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178182744972921578580425 133637058729691183935319)
  ·
    refine ⟨200455588094536775902979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133637058729691183935319 200455588094536775902979)
    ·
      refine ⟨300683382141805163854469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200455588094536775902979 300683382141805163854469)
      ·
        refine ⟨56378134151588468222713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300683382141805163854469 56378134151588468222713)
        ·
          refine ⟨42283600613691351167035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56378134151588468222713 42283600613691351167035)
          ·
            refine ⟨63425400920537026750553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42283600613691351167035 63425400920537026750553)
            ·
              refine ⟨47569050690402770062915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63425400920537026750553 47569050690402770062915)
              ·
                refine ⟨71353576035604155094373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47569050690402770062915 71353576035604155094373)
                ·
                  refine ⟨13378795506675779080195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71353576035604155094373 13378795506675779080195)
                  ·
                    refine ⟨20068193260013668620293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13378795506675779080195 20068193260013668620293)
                    ·
                      refine ⟨3762786236252562866305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20068193260013668620293 3762786236252562866305)
                      ·
                        rfl

theorem cell23_7328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_7328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328 prefixEnd_7328 := by exact prefixLift 7328
  have htrace : WordTrace (prefixWord ++ tailWord_7328) baseStart_7328 baseEnd_7328 := by
    simpa [prefixWord, tailWord_7328, baseEnd_7328] using wordTrace_append hprefix tailTrace_7328
  have hstable : (prefixWord ++ tailWord_7328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328).length < 2 ^ (prefixWord ++ tailWord_7328).sum := by decide
  have hdescent : baseEnd_7328 < baseStart_7328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7331 : Nat := 118140960795 + 7331 * 2 ^ 59
def prefixEnd_7331 : Nat := 4983230072969 + 3 ^ 40 * 7331 * 2
def baseEnd_7331 : Nat := 3764326678216051128791

theorem tailTrace_7331 : CollatzResearch.WordTrace tailWord_7331 prefixEnd_7331 3764326678216051128791 := by
  unfold tailWord_7331
  simp only [CollatzResearch.WordTrace]
  refine ⟨267383536448513880229847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178255690965675920153231 267383536448513880229847)
  ·
    refine ⟨401075304672770820344771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267383536448513880229847 401075304672770820344771)
    ·
      refine ⟨601612957009156230517157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401075304672770820344771 601612957009156230517157)
      ·
        refine ⟨112802429439216793221967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 601612957009156230517157 112802429439216793221967)
        ·
          refine ⟨169203644158825189832951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112802429439216793221967 169203644158825189832951)
          ·
            refine ⟨253805466238237784749427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169203644158825189832951 253805466238237784749427)
            ·
              refine ⟨380708199357356677124141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253805466238237784749427 380708199357356677124141)
              ·
                refine ⟨142765574759008753921553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380708199357356677124141 142765574759008753921553)
                ·
                  refine ⟨107074181069256565441165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142765574759008753921553 107074181069256565441165)
                  ·
                    refine ⟨40152817900971212040437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107074181069256565441165 40152817900971212040437)
                    ·
                      refine ⟨3764326678216051128791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40152817900971212040437 3764326678216051128791)
                      ·
                        rfl

theorem cell23_7331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331 prefixEnd_7331 := by exact prefixLift 7331
  have htrace : WordTrace (prefixWord ++ tailWord_7331) baseStart_7331 baseEnd_7331 := by
    simpa [prefixWord, tailWord_7331, baseEnd_7331] using wordTrace_append hprefix tailTrace_7331
  have hstable : (prefixWord ++ tailWord_7331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331).length < 2 ^ (prefixWord ++ tailWord_7331).sum := by decide
  have hdescent : baseEnd_7331 < baseStart_7331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7371 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 8]
def baseStart_7371 : Nat := 118140960795 + 7371 * 2 ^ 59
def prefixEnd_7371 : Nat := 4983230072969 + 3 ^ 40 * 7371 * 2
def baseEnd_7371 : Nat := 3784865904395894628607

theorem tailTrace_7371 : CollatzResearch.WordTrace tailWord_7371 prefixEnd_7371 3784865904395894628607 := by
  unfold tailWord_7371
  simp only [CollatzResearch.WordTrace]
  refine ⟨268842456303600711685967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179228304202400474457311 268842456303600711685967)
  ·
    refine ⟨403263684455401067528951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268842456303600711685967 403263684455401067528951)
    ·
      refine ⟨604895526683101601293427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403263684455401067528951 604895526683101601293427)
      ·
        refine ⟨907343290024652401940141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604895526683101601293427 907343290024652401940141)
        ·
          refine ⟨340253733759244650727553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 907343290024652401940141 340253733759244650727553)
          ·
            refine ⟨255190300319433488045665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340253733759244650727553 255190300319433488045665)
            ·
              refine ⟨191392725239575116034249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255190300319433488045665 191392725239575116034249)
              ·
                refine ⟨143544543929681337025687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191392725239575116034249 143544543929681337025687)
                ·
                  refine ⟨215316815894522005538531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143544543929681337025687 215316815894522005538531)
                  ·
                    refine ⟨322975223841783008307797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 215316815894522005538531 322975223841783008307797)
                    ·
                      refine ⟨3784865904395894628607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 322975223841783008307797 3784865904395894628607)
                      ·
                        rfl

theorem cell23_7371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_7371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7371 prefixEnd_7371 := by exact prefixLift 7371
  have htrace : WordTrace (prefixWord ++ tailWord_7371) baseStart_7371 baseEnd_7371 := by
    simpa [prefixWord, tailWord_7371, baseEnd_7371] using wordTrace_append hprefix tailTrace_7371
  have hstable : (prefixWord ++ tailWord_7371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7371).length < 2 ^ (prefixWord ++ tailWord_7371).sum := by decide
  have hdescent : baseEnd_7371 < baseStart_7371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_7389 : Nat := 118140960795 + 7389 * 2 ^ 59
def prefixEnd_7389 : Nat := 4983230072969 + 3 ^ 40 * 7389 * 2
def baseEnd_7389 : Nat := 1264702852058941401175

theorem tailTrace_7389 : CollatzResearch.WordTrace tailWord_7389 prefixEnd_7389 1264702852058941401175 := by
  unfold tailWord_7389
  simp only [CollatzResearch.WordTrace]
  refine ⟨269498970238389785841221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179665980158926523894147 269498970238389785841221)
  ·
    refine ⟨50531056919698084845229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269498970238389785841221 50531056919698084845229)
    ·
      refine ⟨18949146344886781816961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50531056919698084845229 18949146344886781816961)
      ·
        refine ⟨14211859758665086362721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18949146344886781816961 14211859758665086362721)
        ·
          refine ⟨10658894818998814772041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14211859758665086362721 10658894818998814772041)
          ·
            refine ⟨7994171114249111079031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10658894818998814772041 7994171114249111079031)
            ·
              refine ⟨11991256671373666618547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7994171114249111079031 11991256671373666618547)
              ·
                refine ⟨17986885007060499927821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11991256671373666618547 17986885007060499927821)
                ·
                  refine ⟨6745081877647687472933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17986885007060499927821 6745081877647687472933)
                  ·
                    refine ⟨1264702852058941401175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6745081877647687472933 1264702852058941401175)
                    ·
                      rfl

theorem cell23_7389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_7389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389 prefixEnd_7389 := by exact prefixLift 7389
  have htrace : WordTrace (prefixWord ++ tailWord_7389) baseStart_7389 baseEnd_7389 := by
    simpa [prefixWord, tailWord_7389, baseEnd_7389] using wordTrace_append hprefix tailTrace_7389
  have hstable : (prefixWord ++ tailWord_7389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389).length < 2 ^ (prefixWord ++ tailWord_7389).sum := by decide
  have hdescent : baseEnd_7389 < baseStart_7389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7402 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 6]
def baseStart_7402 : Nat := 118140960795 + 7402 * 2 ^ 59
def prefixEnd_7402 : Nat := 4983230072969 + 3 ^ 40 * 7402 * 2
def baseEnd_7402 : Nat := 422309311631697037885

theorem tailTrace_7402 : CollatzResearch.WordTrace tailWord_7402 prefixEnd_7402 422309311631697037885 := by
  unfold tailWord_7402
  simp only [CollatzResearch.WordTrace]
  refine ⟨67493279797823251516115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179982079460862004042973 67493279797823251516115)
  ·
    refine ⟨101239919696734877274173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67493279797823251516115 101239919696734877274173)
    ·
      refine ⟨37964969886275578977815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101239919696734877274173 37964969886275578977815)
      ·
        refine ⟨56947454829413368466723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37964969886275578977815 56947454829413368466723)
        ·
          refine ⟨85421182244120052700085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56947454829413368466723 85421182244120052700085)
          ·
            refine ⟨8008235835386254940633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85421182244120052700085 8008235835386254940633)
            ·
              refine ⟨6006176876539691205475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8008235835386254940633 6006176876539691205475)
              ·
                refine ⟨9009265314809536808213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006176876539691205475 9009265314809536808213)
                ·
                  refine ⟨422309311631697037885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9009265314809536808213 422309311631697037885)
                  ·
                    rfl

theorem cell23_7402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_7402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7402 prefixEnd_7402 := by exact prefixLift 7402
  have htrace : WordTrace (prefixWord ++ tailWord_7402) baseStart_7402 baseEnd_7402 := by
    simpa [prefixWord, tailWord_7402, baseEnd_7402] using wordTrace_append hprefix tailTrace_7402
  have hstable : (prefixWord ++ tailWord_7402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7402).length < 2 ^ (prefixWord ++ tailWord_7402).sum := by decide
  have hdescent : baseEnd_7402 < baseStart_7402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475 : List Nat := [1, 1, 1, 2, 5, 3, 3, 7]
def baseStart_7475 : Nat := 118140960795 + 7475 * 2 ^ 59
def prefixEnd_7475 : Nat := 4983230072969 + 3 ^ 40 * 7475 * 2
def baseEnd_7475 : Nat := 142158070091240286227

theorem tailTrace_7475 : CollatzResearch.WordTrace tailWord_7475 prefixEnd_7475 142158070091240286227 := by
  unfold tailWord_7475
  simp only [CollatzResearch.WordTrace]
  refine ⟨272635647926826473471879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181757098617884315647919 272635647926826473471879)
  ·
    refine ⟨408953471890239710207819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272635647926826473471879 408953471890239710207819)
    ·
      refine ⟨613430207835359565311729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408953471890239710207819 613430207835359565311729)
      ·
        refine ⟨460072655876519673983797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613430207835359565311729 460072655876519673983797)
        ·
          refine ⟨43131811488423719435981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 460072655876519673983797 43131811488423719435981)
          ·
            refine ⟨16174429308158894788493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43131811488423719435981 16174429308158894788493)
            ·
              refine ⟨6065410990559585545685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16174429308158894788493 6065410990559585545685)
              ·
                refine ⟨142158070091240286227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6065410990559585545685 142158070091240286227)
                ·
                  rfl

theorem cell23_7475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 7].length) (baseStart_7475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475 prefixEnd_7475 := by exact prefixLift 7475
  have htrace : WordTrace (prefixWord ++ tailWord_7475) baseStart_7475 baseEnd_7475 := by
    simpa [prefixWord, tailWord_7475, baseEnd_7475] using wordTrace_append hprefix tailTrace_7475
  have hstable : (prefixWord ++ tailWord_7475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475).length < 2 ^ (prefixWord ++ tailWord_7475).sum := by decide
  have hdescent : baseEnd_7475 < baseStart_7475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7489 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_7489 : Nat := 118140960795 + 7489 * 2 ^ 59
def prefixEnd_7489 : Nat := 4983230072969 + 3 ^ 40 * 7489 * 2
def baseEnd_7489 : Nat := 3845456621626432953065

theorem tailTrace_7489 : CollatzResearch.WordTrace tailWord_7489 prefixEnd_7489 3845456621626432953065 := by
  unfold tailWord_7489
  simp only [CollatzResearch.WordTrace]
  refine ⟨273146269876106864481521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182097513250737909654347 273146269876106864481521)
  ·
    refine ⟨204859702407080148361141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273146269876106864481521 204859702407080148361141)
    ·
      refine ⟨19205597100663763908857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204859702407080148361141 19205597100663763908857)
      ·
        refine ⟨14404197825497822931643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19205597100663763908857 14404197825497822931643)
        ·
          refine ⟨21606296738246734397465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14404197825497822931643 21606296738246734397465)
          ·
            refine ⟨16204722553685050798099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21606296738246734397465 16204722553685050798099)
            ·
              refine ⟨24307083830527576197149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16204722553685050798099 24307083830527576197149)
              ·
                refine ⟨9115156436447841073931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24307083830527576197149 9115156436447841073931)
                ·
                  refine ⟨13672734654671761610897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115156436447841073931 13672734654671761610897)
                  ·
                    refine ⟨10254550991003821208173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13672734654671761610897 10254550991003821208173)
                    ·
                      refine ⟨3845456621626432953065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10254550991003821208173 3845456621626432953065)
                      ·
                        rfl

theorem cell23_7489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_7489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7489 prefixEnd_7489 := by exact prefixLift 7489
  have htrace : WordTrace (prefixWord ++ tailWord_7489) baseStart_7489 baseEnd_7489 := by
    simpa [prefixWord, tailWord_7489, baseEnd_7489] using wordTrace_append hprefix tailTrace_7489
  have hstable : (prefixWord ++ tailWord_7489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7489).length < 2 ^ (prefixWord ++ tailWord_7489).sum := by decide
  have hdescent : baseEnd_7489 < baseStart_7489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_7502 : Nat := 118140960795 + 7502 * 2 ^ 59
def prefixEnd_7502 : Nat := 4983230072969 + 3 ^ 40 * 7502 * 2
def baseEnd_7502 : Nat := 3852131870134882090505

theorem tailTrace_7502 : CollatzResearch.WordTrace tailWord_7502 prefixEnd_7502 3852131870134882090505 := by
  unfold tailWord_7502
  simp only [CollatzResearch.WordTrace]
  refine ⟨34202552353626260588095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182413612552673389803173 34202552353626260588095)
  ·
    refine ⟨51303828530439390882143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34202552353626260588095 51303828530439390882143)
    ·
      refine ⟨76955742795659086323215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51303828530439390882143 76955742795659086323215)
      ·
        refine ⟨115433614193488629484823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76955742795659086323215 115433614193488629484823)
        ·
          refine ⟨173150421290232944227235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115433614193488629484823 173150421290232944227235)
          ·
            refine ⟨259725631935349416340853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173150421290232944227235 259725631935349416340853)
            ·
              refine ⟨24349277993939007781955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259725631935349416340853 24349277993939007781955)
              ·
                refine ⟨36523916990908511672933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24349277993939007781955 36523916990908511672933)
                ·
                  refine ⟨6848234435795345938675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36523916990908511672933 6848234435795345938675)
                  ·
                    refine ⟨10272351653693018908013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6848234435795345938675 10272351653693018908013)
                    ·
                      refine ⟨3852131870134882090505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10272351653693018908013 3852131870134882090505)
                      ·
                        rfl

theorem cell23_7502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_7502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502 prefixEnd_7502 := by exact prefixLift 7502
  have htrace : WordTrace (prefixWord ++ tailWord_7502) baseStart_7502 baseEnd_7502 := by
    simpa [prefixWord, tailWord_7502, baseEnd_7502] using wordTrace_append hprefix tailTrace_7502
  have hstable : (prefixWord ++ tailWord_7502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502).length < 2 ^ (prefixWord ++ tailWord_7502).sum := by decide
  have hdescent : baseEnd_7502 < baseStart_7502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7559 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_7559 : Nat := 118140960795 + 7559 * 2 ^ 59
def prefixEnd_7559 : Nat := 4983230072969 + 3 ^ 40 * 7559 * 2
def baseEnd_7559 : Nat := 3881400267441159077743

theorem tailTrace_7559 : CollatzResearch.WordTrace tailWord_7559 prefixEnd_7559 3881400267441159077743 := by
  unfold tailWord_7559
  simp only [CollatzResearch.WordTrace]
  refine ⟨275699379622508819529731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183799586415005879686487 275699379622508819529731)
  ·
    refine ⟨413549069433763229294597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275699379622508819529731 413549069433763229294597)
    ·
      refine ⟨77540450518830605492737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413549069433763229294597 77540450518830605492737)
      ·
        refine ⟨58155337889122954119553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77540450518830605492737 58155337889122954119553)
        ·
          refine ⟨43616503416842215589665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58155337889122954119553 43616503416842215589665)
          ·
            refine ⟨32712377562631661692249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43616503416842215589665 32712377562631661692249)
            ·
              refine ⟨24534283171973746269187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32712377562631661692249 24534283171973746269187)
              ·
                refine ⟨36801424757960619403781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24534283171973746269187 36801424757960619403781)
                ·
                  refine ⟨6900267142117616138209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36801424757960619403781 6900267142117616138209)
                  ·
                    refine ⟨5175200356588212103657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6900267142117616138209 5175200356588212103657)
                    ·
                      refine ⟨3881400267441159077743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5175200356588212103657 3881400267441159077743)
                      ·
                        rfl

theorem cell23_7559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_7559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7559 prefixEnd_7559 := by exact prefixLift 7559
  have htrace : WordTrace (prefixWord ++ tailWord_7559) baseStart_7559 baseEnd_7559 := by
    simpa [prefixWord, tailWord_7559, baseEnd_7559] using wordTrace_append hprefix tailTrace_7559
  have hstable : (prefixWord ++ tailWord_7559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7559).length < 2 ^ (prefixWord ++ tailWord_7559).sum := by decide
  have hdescent : baseEnd_7559 < baseStart_7559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7570 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7570 : Nat := 118140960795 + 7570 * 2 ^ 59
def prefixEnd_7570 : Nat := 4983230072969 + 3 ^ 40 * 7570 * 2
def baseEnd_7570 : Nat := 3887048554640616040193

theorem tailTrace_7570 : CollatzResearch.WordTrace tailWord_7570 prefixEnd_7570 3887048554640616040193 := by
  unfold tailWord_7570
  simp only [CollatzResearch.WordTrace]
  refine ⟨69025145645664424545041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184067055055105132120109 69025145645664424545041)
  ·
    refine ⟨51768859234248318408781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69025145645664424545041 51768859234248318408781)
    ·
      refine ⟨19413322212843119403293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51768859234248318408781 19413322212843119403293)
      ·
        refine ⟨7279995829816169776235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19413322212843119403293 7279995829816169776235)
        ·
          refine ⟨10919993744724254664353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7279995829816169776235 10919993744724254664353)
          ·
            refine ⟨8189995308543190998265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10919993744724254664353 8189995308543190998265)
            ·
              refine ⟨6142496481407393248699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8189995308543190998265 6142496481407393248699)
              ·
                refine ⟨9213744722111089873049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6142496481407393248699 9213744722111089873049)
                ·
                  refine ⟨6910308541583317404787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9213744722111089873049 6910308541583317404787)
                  ·
                    refine ⟨10365462812374976107181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910308541583317404787 10365462812374976107181)
                    ·
                      refine ⟨3887048554640616040193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10365462812374976107181 3887048554640616040193)
                      ·
                        rfl

theorem cell23_7570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7570 prefixEnd_7570 := by exact prefixLift 7570
  have htrace : WordTrace (prefixWord ++ tailWord_7570) baseStart_7570 baseEnd_7570 := by
    simpa [prefixWord, tailWord_7570, baseEnd_7570] using wordTrace_append hprefix tailTrace_7570
  have hstable : (prefixWord ++ tailWord_7570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7570).length < 2 ^ (prefixWord ++ tailWord_7570).sum := by decide
  have hdescent : baseEnd_7570 < baseStart_7570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_7575 : Nat := 118140960795 + 7575 * 2 ^ 59
def prefixEnd_7575 : Nat := 4983230072969 + 3 ^ 40 * 7575 * 2
def baseEnd_7575 : Nat := 3889615957913096477669

theorem tailTrace_7575 : CollatzResearch.WordTrace tailWord_7575 prefixEnd_7575 3889615957913096477669 := by
  unfold tailWord_7575
  simp only [CollatzResearch.WordTrace]
  refine ⟨276282947564543552112179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184188631709695701408119 276282947564543552112179)
  ·
    refine ⟨414424421346815328168269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276282947564543552112179 414424421346815328168269)
    ·
      refine ⟨155409158005055748063101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414424421346815328168269 155409158005055748063101)
      ·
        refine ⟨58278434251895905523663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155409158005055748063101 58278434251895905523663)
        ·
          refine ⟨87417651377843858285495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58278434251895905523663 87417651377843858285495)
          ·
            refine ⟨131126477066765787428243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87417651377843858285495 131126477066765787428243)
            ·
              refine ⟨196689715600148681142365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131126477066765787428243 196689715600148681142365)
              ·
                refine ⟨73758643350055755428387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196689715600148681142365 73758643350055755428387)
                ·
                  refine ⟨110637965025083633142581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73758643350055755428387 110637965025083633142581)
                  ·
                    refine ⟨10372309221101590607117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110637965025083633142581 10372309221101590607117)
                    ·
                      refine ⟨3889615957913096477669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10372309221101590607117 3889615957913096477669)
                      ·
                        rfl

theorem cell23_7575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_7575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575 prefixEnd_7575 := by exact prefixLift 7575
  have htrace : WordTrace (prefixWord ++ tailWord_7575) baseStart_7575 baseEnd_7575 := by
    simpa [prefixWord, tailWord_7575, baseEnd_7575] using wordTrace_append hprefix tailTrace_7575
  have hstable : (prefixWord ++ tailWord_7575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575).length < 2 ^ (prefixWord ++ tailWord_7575).sum := by decide
  have hdescent : baseEnd_7575 < baseStart_7575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7580 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7580 : Nat := 118140960795 + 7580 * 2 ^ 59
def prefixEnd_7580 : Nat := 4983230072969 + 3 ^ 40 * 7580 * 2
def baseEnd_7580 : Nat := 3892183361185576915147

theorem tailTrace_7580 : CollatzResearch.WordTrace tailWord_7580 prefixEnd_7580 3892183361185576915147 := by
  unfold tailWord_7580
  simp only [CollatzResearch.WordTrace]
  refine ⟨138232656273214703022097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184310208364286270696129 138232656273214703022097)
  ·
    refine ⟨103674492204911027266573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138232656273214703022097 103674492204911027266573)
    ·
      refine ⟨38877934576841635224965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103674492204911027266573 38877934576841635224965)
      ·
        refine ⟨7289612733157806604681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38877934576841635224965 7289612733157806604681)
        ·
          refine ⟨5467209549868354953511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7289612733157806604681 5467209549868354953511)
          ·
            refine ⟨8200814324802532430267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467209549868354953511 8200814324802532430267)
            ·
              refine ⟨12301221487203798645401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200814324802532430267 12301221487203798645401)
              ·
                refine ⟨9225916115402848984051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12301221487203798645401 9225916115402848984051)
                ·
                  refine ⟨13838874173104273476077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9225916115402848984051 13838874173104273476077)
                  ·
                    refine ⟨5189577814914102553529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13838874173104273476077 5189577814914102553529)
                    ·
                      refine ⟨3892183361185576915147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5189577814914102553529 3892183361185576915147)
                      ·
                        rfl

theorem cell23_7580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7580 prefixEnd_7580 := by exact prefixLift 7580
  have htrace : WordTrace (prefixWord ++ tailWord_7580) baseStart_7580 baseEnd_7580 := by
    simpa [prefixWord, tailWord_7580, baseEnd_7580] using wordTrace_append hprefix tailTrace_7580
  have hstable : (prefixWord ++ tailWord_7580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7580).length < 2 ^ (prefixWord ++ tailWord_7580).sum := by decide
  have hdescent : baseEnd_7580 < baseStart_7580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 2, 4, 2]
def baseStart_7632 : Nat := 118140960795 + 7632 * 2 ^ 59
def prefixEnd_7632 : Nat := 4983230072969 + 3 ^ 40 * 7632 * 2
def baseEnd_7632 : Nat := 3918884355219373464907

theorem tailTrace_7632 : CollatzResearch.WordTrace tailWord_7632 prefixEnd_7632 3918884355219373464907 := by
  unfold tailWord_7632
  simp only [CollatzResearch.WordTrace]
  refine ⟨139180954179021143468575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185574605572028191291433 139180954179021143468575)
  ·
    refine ⟨208771431268531715202863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139180954179021143468575 208771431268531715202863)
    ·
      refine ⟨313157146902797572804295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208771431268531715202863 313157146902797572804295)
      ·
        refine ⟨469735720354196359206443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313157146902797572804295 469735720354196359206443)
        ·
          refine ⟨704603580531294538809665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469735720354196359206443 704603580531294538809665)
          ·
            refine ⟨528452685398470904107249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704603580531294538809665 528452685398470904107249)
            ·
              refine ⟨396339514048853178080437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528452685398470904107249 396339514048853178080437)
              ·
                refine ⟨37156829442079985445041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396339514048853178080437 37156829442079985445041)
                ·
                  refine ⟨27867622081559989083781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37156829442079985445041 27867622081559989083781)
                  ·
                    refine ⟨5225179140292497953209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27867622081559989083781 5225179140292497953209)
                    ·
                      refine ⟨3918884355219373464907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225179140292497953209 3918884355219373464907)
                      ·
                        rfl

theorem cell23_7632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 4, 2].length) (baseStart_7632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632 prefixEnd_7632 := by exact prefixLift 7632
  have htrace : WordTrace (prefixWord ++ tailWord_7632) baseStart_7632 baseEnd_7632 := by
    simpa [prefixWord, tailWord_7632, baseEnd_7632] using wordTrace_append hprefix tailTrace_7632
  have hstable : (prefixWord ++ tailWord_7632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632).length < 2 ^ (prefixWord ++ tailWord_7632).sum := by decide
  have hdescent : baseEnd_7632 < baseStart_7632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_7642 : Nat := 118140960795 + 7642 * 2 ^ 59
def prefixEnd_7642 : Nat := 4983230072969 + 3 ^ 40 * 7642 * 2
def baseEnd_7642 : Nat := 1308006387254778113287

theorem tailTrace_7642 : CollatzResearch.WordTrace tailWord_7642 prefixEnd_7642 1308006387254778113287 := by
  unfold tailWord_7642
  simp only [CollatzResearch.WordTrace]
  refine ⟨69681659580453498700295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185817758881209329867453 69681659580453498700295)
  ·
    refine ⟨104522489370680248050443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69681659580453498700295 104522489370680248050443)
    ·
      refine ⟨156783734056020372075665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104522489370680248050443 156783734056020372075665)
      ·
        refine ⟨117587800542015279056749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156783734056020372075665 117587800542015279056749)
        ·
          refine ⟨44095425203255729646281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117587800542015279056749 44095425203255729646281)
          ·
            refine ⟨33071568902441797234711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44095425203255729646281 33071568902441797234711)
            ·
              refine ⟨49607353353662695852067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33071568902441797234711 49607353353662695852067)
              ·
                refine ⟨74411030030494043778101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49607353353662695852067 74411030030494043778101)
                ·
                  refine ⟨6976034065358816604197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74411030030494043778101 6976034065358816604197)
                  ·
                    refine ⟨1308006387254778113287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6976034065358816604197 1308006387254778113287)
                    ·
                      rfl

theorem cell23_7642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_7642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642 prefixEnd_7642 := by exact prefixLift 7642
  have htrace : WordTrace (prefixWord ++ tailWord_7642) baseStart_7642 baseEnd_7642 := by
    simpa [prefixWord, tailWord_7642, baseEnd_7642] using wordTrace_append hprefix tailTrace_7642
  have hstable : (prefixWord ++ tailWord_7642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642).length < 2 ^ (prefixWord ++ tailWord_7642).sum := by decide
  have hdescent : baseEnd_7642 < baseStart_7642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_7649 : Nat := 118140960795 + 7649 * 2 ^ 59
def prefixEnd_7649 : Nat := 4983230072969 + 3 ^ 40 * 7649 * 2
def baseEnd_7649 : Nat := 3927613526345806952329

theorem tailTrace_7649 : CollatzResearch.WordTrace tailWord_7649 prefixEnd_7649 3927613526345806952329 := by
  unfold tailWord_7649
  simp only [CollatzResearch.WordTrace]
  refine ⟨278981949296454190306001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185987966197636126870667 278981949296454190306001)
  ·
    refine ⟨209236461972340642729501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278981949296454190306001 209236461972340642729501)
    ·
      refine ⟨78463673239627741023563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209236461972340642729501 78463673239627741023563)
      ·
        refine ⟨117695509859441611535345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78463673239627741023563 117695509859441611535345)
        ·
          refine ⟨88271632394581208651509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117695509859441611535345 88271632394581208651509)
          ·
            refine ⟨8275465536991988311079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88271632394581208651509 8275465536991988311079)
            ·
              refine ⟨12413198305487982466619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275465536991988311079 12413198305487982466619)
              ·
                refine ⟨18619797458231973699929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12413198305487982466619 18619797458231973699929)
                ·
                  refine ⟨13964848093673980274947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18619797458231973699929 13964848093673980274947)
                  ·
                    refine ⟨20947272140510970412421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13964848093673980274947 20947272140510970412421)
                    ·
                      refine ⟨3927613526345806952329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20947272140510970412421 3927613526345806952329)
                      ·
                        rfl

theorem cell23_7649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_7649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649 prefixEnd_7649 := by exact prefixLift 7649
  have htrace : WordTrace (prefixWord ++ tailWord_7649) baseStart_7649 baseEnd_7649 := by
    simpa [prefixWord, tailWord_7649, baseEnd_7649] using wordTrace_append hprefix tailTrace_7649
  have hstable : (prefixWord ++ tailWord_7649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649).length < 2 ^ (prefixWord ++ tailWord_7649).sum := by decide
  have hdescent : baseEnd_7649 < baseStart_7649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7672 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 6]
def baseStart_7672 : Nat := 118140960795 + 7672 * 2 ^ 59
def prefixEnd_7672 : Nat := 4983230072969 + 3 ^ 40 * 7672 * 2
def baseEnd_7672 : Nat := 437713731266579662747

theorem tailTrace_7672 : CollatzResearch.WordTrace tailWord_7672 prefixEnd_7672 437713731266579662747 := by
  unfold tailWord_7672
  simp only [CollatzResearch.WordTrace]
  refine ⟨139910414106564559196635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186547218808752745595513 139910414106564559196635)
  ·
    refine ⟨209865621159846838794953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139910414106564559196635 209865621159846838794953)
    ·
      refine ⟨157399215869885129096215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209865621159846838794953 157399215869885129096215)
      ·
        refine ⟨236098823804827693644323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157399215869885129096215 236098823804827693644323)
        ·
          refine ⟨354148235707241540466485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236098823804827693644323 354148235707241540466485)
          ·
            refine ⟨33201397097553894418733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 354148235707241540466485 33201397097553894418733)
            ·
              refine ⟨12450523911582710407025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33201397097553894418733 12450523911582710407025)
              ·
                refine ⟨9337892933687032805269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12450523911582710407025 9337892933687032805269)
                ·
                  refine ⟨437713731266579662747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9337892933687032805269 437713731266579662747)
                  ·
                    rfl

theorem cell23_7672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 6].length) (baseStart_7672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7672 prefixEnd_7672 := by exact prefixLift 7672
  have htrace : WordTrace (prefixWord ++ tailWord_7672) baseStart_7672 baseEnd_7672 := by
    simpa [prefixWord, tailWord_7672, baseEnd_7672] using wordTrace_append hprefix tailTrace_7672
  have hstable : (prefixWord ++ tailWord_7672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7672).length < 2 ^ (prefixWord ++ tailWord_7672).sum := by decide
  have hdescent : baseEnd_7672 < baseStart_7672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 3]
def baseStart_7699 : Nat := 118140960795 + 7699 * 2 ^ 59
def prefixEnd_7699 : Nat := 4983230072969 + 3 ^ 40 * 7699 * 2
def baseEnd_7699 : Nat := 3953287559070611327099

theorem tailTrace_7699 : CollatzResearch.WordTrace tailWord_7699 prefixEnd_7699 3953287559070611327099 := by
  unfold tailWord_7699
  simp only [CollatzResearch.WordTrace]
  refine ⟨280805599115312729626151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187203732743541819750767 280805599115312729626151)
  ·
    refine ⟨421208398672969094439227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280805599115312729626151 421208398672969094439227)
    ·
      refine ⟨631812598009453641658841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421208398672969094439227 631812598009453641658841)
      ·
        refine ⟨473859448507090231244131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631812598009453641658841 473859448507090231244131)
        ·
          refine ⟨710789172760635346866197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473859448507090231244131 710789172760635346866197)
          ·
            refine ⟨33318242473154781884353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 710789172760635346866197 33318242473154781884353)
            ·
              refine ⟨24988681854866086413265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33318242473154781884353 24988681854866086413265)
              ·
                refine ⟨18741511391149564809949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24988681854866086413265 18741511391149564809949)
                ·
                  refine ⟨7028066771681086803731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18741511391149564809949 7028066771681086803731)
                  ·
                    refine ⟨10542100157521630205597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7028066771681086803731 10542100157521630205597)
                    ·
                      refine ⟨3953287559070611327099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10542100157521630205597 3953287559070611327099)
                      ·
                        rfl

theorem cell23_7699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 3].length) (baseStart_7699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699 prefixEnd_7699 := by exact prefixLift 7699
  have htrace : WordTrace (prefixWord ++ tailWord_7699) baseStart_7699 baseEnd_7699 := by
    simpa [prefixWord, tailWord_7699, baseEnd_7699] using wordTrace_append hprefix tailTrace_7699
  have hstable : (prefixWord ++ tailWord_7699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699).length < 2 ^ (prefixWord ++ tailWord_7699).sum := by decide
  have hdescent : baseEnd_7699 < baseStart_7699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_7709 : Nat := 118140960795 + 7709 * 2 ^ 59
def prefixEnd_7709 : Nat := 4983230072969 + 3 ^ 40 * 7709 * 2
def baseEnd_7709 : Nat := 3958422365615572202053

theorem tailTrace_7709 : CollatzResearch.WordTrace tailWord_7709 prefixEnd_7709 3958422365615572202053 := by
  unfold tailWord_7709
  simp only [CollatzResearch.WordTrace]
  refine ⟨281170329079084437490181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187446886052722958326787 281170329079084437490181)
  ·
    refine ⟨52719436702328332029409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281170329079084437490181 52719436702328332029409)
    ·
      refine ⟨39539577526746249022057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52719436702328332029409 39539577526746249022057)
      ·
        refine ⟨29654683145059686766543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39539577526746249022057 29654683145059686766543)
        ·
          refine ⟨44482024717589530149815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29654683145059686766543 44482024717589530149815)
          ·
            refine ⟨66723037076384295224723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44482024717589530149815 66723037076384295224723)
            ·
              refine ⟨100084555614576442837085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66723037076384295224723 100084555614576442837085)
              ·
                refine ⟨37531708355466166063907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100084555614576442837085 37531708355466166063907)
                ·
                  refine ⟨56297562533199249095861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37531708355466166063907 56297562533199249095861)
                  ·
                    refine ⟨5277896487487429602737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56297562533199249095861 5277896487487429602737)
                    ·
                      refine ⟨3958422365615572202053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5277896487487429602737 3958422365615572202053)
                      ·
                        rfl

theorem cell23_7709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_7709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709 prefixEnd_7709 := by exact prefixLift 7709
  have htrace : WordTrace (prefixWord ++ tailWord_7709) baseStart_7709 baseEnd_7709 := by
    simpa [prefixWord, tailWord_7709, baseEnd_7709] using wordTrace_append hprefix tailTrace_7709
  have hstable : (prefixWord ++ tailWord_7709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709).length < 2 ^ (prefixWord ++ tailWord_7709).sum := by decide
  have hdescent : baseEnd_7709 < baseStart_7709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7726 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_7726 : Nat := 118140960795 + 7726 * 2 ^ 59
def prefixEnd_7726 : Nat := 4983230072969 + 3 ^ 40 * 7726 * 2
def baseEnd_7726 : Nat := 3967151536742005689475

theorem tailTrace_7726 : CollatzResearch.WordTrace tailWord_7726 prefixEnd_7726 3967151536742005689475 := by
  unfold tailWord_7726
  simp only [CollatzResearch.WordTrace]
  refine ⟨35223796252187042607379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187860246678330893906021 35223796252187042607379)
  ·
    refine ⟨52835694378280563911069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35223796252187042607379 52835694378280563911069)
    ·
      refine ⟨19813385391855211466651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52835694378280563911069 19813385391855211466651)
      ·
        refine ⟨29720078087782817199977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19813385391855211466651 29720078087782817199977)
        ·
          refine ⟨22290058565837112899983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29720078087782817199977 22290058565837112899983)
          ·
            refine ⟨33435087848755669349975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22290058565837112899983 33435087848755669349975)
            ·
              refine ⟨50152631773133504024963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33435087848755669349975 50152631773133504024963)
              ·
                refine ⟨75228947659700256037445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50152631773133504024963 75228947659700256037445)
                ·
                  refine ⟨14105427686193798007021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75228947659700256037445 14105427686193798007021)
                  ·
                    refine ⟨5289535382322674252633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14105427686193798007021 5289535382322674252633)
                    ·
                      refine ⟨3967151536742005689475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5289535382322674252633 3967151536742005689475)
                      ·
                        rfl

theorem cell23_7726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_7726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7726 prefixEnd_7726 := by exact prefixLift 7726
  have htrace : WordTrace (prefixWord ++ tailWord_7726) baseStart_7726 baseEnd_7726 := by
    simpa [prefixWord, tailWord_7726, baseEnd_7726] using wordTrace_append hprefix tailTrace_7726
  have hstable : (prefixWord ++ tailWord_7726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7726).length < 2 ^ (prefixWord ++ tailWord_7726).sum := by decide
  have hdescent : baseEnd_7726 < baseStart_7726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7749 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_7749 : Nat := 118140960795 + 7749 * 2 ^ 59
def prefixEnd_7749 : Nat := 4983230072969 + 3 ^ 40 * 7749 * 2
def baseEnd_7749 : Nat := 1326320530598471900623

theorem tailTrace_7749 : CollatzResearch.WordTrace tailWord_7749 prefixEnd_7749 1326320530598471900623 := by
  unfold tailWord_7749
  simp only [CollatzResearch.WordTrace]
  refine ⟨282629248934171268946301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188419499289447512630867 282629248934171268946301)
  ·
    refine ⟨105985968350314225854863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282629248934171268946301 105985968350314225854863)
    ·
      refine ⟨158978952525471338782295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105985968350314225854863 158978952525471338782295)
      ·
        refine ⟨238468428788207008173443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158978952525471338782295 238468428788207008173443)
        ·
          refine ⟨357702643182310512260165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238468428788207008173443 357702643182310512260165)
          ·
            refine ⟨67069245596683221048781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 357702643182310512260165 67069245596683221048781)
            ·
              refine ⟨25150967098756207893293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67069245596683221048781 25150967098756207893293)
              ·
                refine ⟨9431612662033577959985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25150967098756207893293 9431612662033577959985)
                ·
                  refine ⟨7073709496525183469989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9431612662033577959985 7073709496525183469989)
                  ·
                    refine ⟨1326320530598471900623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7073709496525183469989 1326320530598471900623)
                    ·
                      rfl

theorem cell23_7749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_7749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7749 prefixEnd_7749 := by exact prefixLift 7749
  have htrace : WordTrace (prefixWord ++ tailWord_7749) baseStart_7749 baseEnd_7749 := by
    simpa [prefixWord, tailWord_7749, baseEnd_7749] using wordTrace_append hprefix tailTrace_7749
  have hstable : (prefixWord ++ tailWord_7749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7749).length < 2 ^ (prefixWord ++ tailWord_7749).sum := by decide
  have hdescent : baseEnd_7749 < baseStart_7749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 1, 1, 4]
def baseStart_7756 : Nat := 118140960795 + 7756 * 2 ^ 59
def prefixEnd_7756 : Nat := 4983230072969 + 3 ^ 40 * 7756 * 2
def baseEnd_7756 : Nat := 3982555956376888314337

theorem tailTrace_7756 : CollatzResearch.WordTrace tailWord_7756 prefixEnd_7756 3982555956376888314337 := by
  unfold tailWord_7756
  simp only [CollatzResearch.WordTrace]
  refine ⟨141442279954405732225561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188589706605874309634081 141442279954405732225561)
  ·
    refine ⟨106081709965804299169171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141442279954405732225561 106081709965804299169171)
    ·
      refine ⟨159122564948706448753757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106081709965804299169171 159122564948706448753757)
      ·
        refine ⟨59670961855764918282659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159122564948706448753757 59670961855764918282659)
        ·
          refine ⟨89506442783647377423989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59670961855764918282659 89506442783647377423989)
          ·
            refine ⟨8391229010966941633499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89506442783647377423989 8391229010966941633499)
            ·
              refine ⟨12586843516450412450249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391229010966941633499 12586843516450412450249)
              ·
                refine ⟨9440132637337809337687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12586843516450412450249 9440132637337809337687)
                ·
                  refine ⟨14160198956006714006531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9440132637337809337687 14160198956006714006531)
                  ·
                    refine ⟨21240298434010071009797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14160198956006714006531 21240298434010071009797)
                    ·
                      refine ⟨3982555956376888314337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21240298434010071009797 3982555956376888314337)
                      ·
                        rfl

theorem cell23_7756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_7756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756 prefixEnd_7756 := by exact prefixLift 7756
  have htrace : WordTrace (prefixWord ++ tailWord_7756) baseStart_7756 baseEnd_7756 := by
    simpa [prefixWord, tailWord_7756, baseEnd_7756] using wordTrace_append hprefix tailTrace_7756
  have hstable : (prefixWord ++ tailWord_7756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756).length < 2 ^ (prefixWord ++ tailWord_7756).sum := by decide
  have hdescent : baseEnd_7756 < baseStart_7756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7762 : List Nat := [3, 2, 2, 1, 2, 2, 2, 9]
def baseStart_7762 : Nat := 118140960795 + 7762 * 2 ^ 59
def prefixEnd_7762 : Nat := 4983230072969 + 3 ^ 40 * 7762 * 2
def baseEnd_7762 : Nat := 147616179270513512567

theorem tailTrace_7762 : CollatzResearch.WordTrace tailWord_7762 prefixEnd_7762 147616179270513512567 := by
  unfold tailWord_7762
  simp only [CollatzResearch.WordTrace]
  refine ⟨70775849471768622292385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188735598591382992779693 70775849471768622292385)
  ·
    refine ⟨53081887103826466719289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70775849471768622292385 53081887103826466719289)
    ·
      refine ⟨39811415327869850039467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53081887103826466719289 39811415327869850039467)
      ·
        refine ⟨59717122991804775059201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39811415327869850039467 59717122991804775059201)
        ·
          refine ⟨44787842243853581294401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59717122991804775059201 44787842243853581294401)
          ·
            refine ⟨33590881682890185970801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44787842243853581294401 33590881682890185970801)
            ·
              refine ⟨25193161262167639478101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33590881682890185970801 25193161262167639478101)
              ·
                refine ⟨147616179270513512567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25193161262167639478101 147616179270513512567)
                ·
                  rfl

theorem cell23_7762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 9].length) (baseStart_7762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7762 prefixEnd_7762 := by exact prefixLift 7762
  have htrace : WordTrace (prefixWord ++ tailWord_7762) baseStart_7762 baseEnd_7762 := by
    simpa [prefixWord, tailWord_7762, baseEnd_7762] using wordTrace_append hprefix tailTrace_7762
  have hstable : (prefixWord ++ tailWord_7762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7762).length < 2 ^ (prefixWord ++ tailWord_7762).sum := by decide
  have hdescent : baseEnd_7762 < baseStart_7762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7792 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 2, 7]
def baseStart_7792 : Nat := 118140960795 + 7792 * 2 ^ 59
def prefixEnd_7792 : Nat := 4983230072969 + 3 ^ 40 * 7792 * 2
def baseEnd_7792 : Nat := 1333680419979582488057

theorem tailTrace_7792 : CollatzResearch.WordTrace tailWord_7792 prefixEnd_7792 1333680419979582488057 := by
  unfold tailWord_7792
  simp only [CollatzResearch.WordTrace]
  refine ⟨142098793889194806380815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189465058518926408507753 142098793889194806380815)
  ·
    refine ⟨213148190833792209571223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142098793889194806380815 213148190833792209571223)
    ·
      refine ⟨319722286250688314356835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213148190833792209571223 319722286250688314356835)
      ·
        refine ⟨479583429376032471535253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319722286250688314356835 479583429376032471535253)
        ·
          refine ⟨22480473252001522103215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 479583429376032471535253 22480473252001522103215)
          ·
            refine ⟨33720709878002283154823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22480473252001522103215 33720709878002283154823)
            ·
              refine ⟨50581064817003424732235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33720709878002283154823 50581064817003424732235)
              ·
                refine ⟨75871597225505137098353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50581064817003424732235 75871597225505137098353)
                ·
                  refine ⟨56903697919128852823765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75871597225505137098353 56903697919128852823765)
                  ·
                    refine ⟨1333680419979582488057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56903697919128852823765 1333680419979582488057)
                    ·
                      rfl

theorem cell23_7792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_7792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7792 prefixEnd_7792 := by exact prefixLift 7792
  have htrace : WordTrace (prefixWord ++ tailWord_7792) baseStart_7792 baseEnd_7792 := by
    simpa [prefixWord, tailWord_7792, baseEnd_7792] using wordTrace_append hprefix tailTrace_7792
  have hstable : (prefixWord ++ tailWord_7792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7792).length < 2 ^ (prefixWord ++ tailWord_7792).sum := by decide
  have hdescent : baseEnd_7792 < baseStart_7792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7863 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 1, 4, 2]
def baseStart_7863 : Nat := 118140960795 + 7863 * 2 ^ 59
def prefixEnd_7863 : Nat := 4983230072969 + 3 ^ 40 * 7863 * 2
def baseEnd_7863 : Nat := 4037498386407969676345

theorem tailTrace_7863 : CollatzResearch.WordTrace tailWord_7863 prefixEnd_7863 4037498386407969676345 := by
  unfold tailWord_7863
  simp only [CollatzResearch.WordTrace]
  refine ⟨286787170521168738596243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191191447014112492397495 286787170521168738596243)
  ·
    refine ⟨430180755781753107894365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286787170521168738596243 430180755781753107894365)
    ·
      refine ⟨161317783418157415460387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430180755781753107894365 161317783418157415460387)
      ·
        refine ⟨241976675127236123190581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161317783418157415460387 241976675127236123190581)
        ·
          refine ⟨22685313293178386549117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241976675127236123190581 22685313293178386549117)
          ·
            refine ⟨8506992484941894955919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22685313293178386549117 8506992484941894955919)
            ·
              refine ⟨12760488727412842433879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506992484941894955919 12760488727412842433879)
              ·
                refine ⟨19140733091119263650819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12760488727412842433879 19140733091119263650819)
                ·
                  refine ⟨28711099636678895476229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19140733091119263650819 28711099636678895476229)
                  ·
                    refine ⟨5383331181877292901793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28711099636678895476229 5383331181877292901793)
                    ·
                      refine ⟨4037498386407969676345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5383331181877292901793 4037498386407969676345)
                      ·
                        rfl

theorem cell23_7863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_7863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7863 prefixEnd_7863 := by exact prefixLift 7863
  have htrace : WordTrace (prefixWord ++ tailWord_7863) baseStart_7863 baseEnd_7863 := by
    simpa [prefixWord, tailWord_7863, baseEnd_7863] using wordTrace_append hprefix tailTrace_7863
  have hstable : (prefixWord ++ tailWord_7863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7863).length < 2 ^ (prefixWord ++ tailWord_7863).sum := by decide
  have hdescent : baseEnd_7863 < baseStart_7863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_7909 : Nat := 118140960795 + 7909 * 2 ^ 59
def prefixEnd_7909 : Nat := 4983230072969 + 3 ^ 40 * 7909 * 2
def baseEnd_7909 : Nat := 4061118496514789701133

theorem tailTrace_7909 : CollatzResearch.WordTrace tailWord_7909 prefixEnd_7909 4061118496514789701133 := by
  unfold tailWord_7909
  simp only [CollatzResearch.WordTrace]
  refine ⟨288464928354518594770781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192309952236345729847187 288464928354518594770781)
  ·
    refine ⟨108174348132944473039043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288464928354518594770781 108174348132944473039043)
    ·
      refine ⟨162261522199416709558565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108174348132944473039043 162261522199416709558565)
      ·
        refine ⟨30424035412390633042231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162261522199416709558565 30424035412390633042231)
        ·
          refine ⟨45636053118585949563347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30424035412390633042231 45636053118585949563347)
          ·
            refine ⟨68454079677878924345021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45636053118585949563347 68454079677878924345021)
            ·
              refine ⟨25670279879204596629383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68454079677878924345021 25670279879204596629383)
              ·
                refine ⟨38505419818806894944075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25670279879204596629383 38505419818806894944075)
                ·
                  refine ⟨57758129728210342416113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38505419818806894944075 57758129728210342416113)
                  ·
                    refine ⟨43318597296157756812085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57758129728210342416113 43318597296157756812085)
                    ·
                      refine ⟨4061118496514789701133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43318597296157756812085 4061118496514789701133)
                      ·
                        rfl

theorem cell23_7909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_7909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909 prefixEnd_7909 := by exact prefixLift 7909
  have htrace : WordTrace (prefixWord ++ tailWord_7909) baseStart_7909 baseEnd_7909 := by
    simpa [prefixWord, tailWord_7909, baseEnd_7909] using wordTrace_append hprefix tailTrace_7909
  have hstable : (prefixWord ++ tailWord_7909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909).length < 2 ^ (prefixWord ++ tailWord_7909).sum := by decide
  have hdescent : baseEnd_7909 < baseStart_7909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7919 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_7919 : Nat := 118140960795 + 7919 * 2 ^ 59
def prefixEnd_7919 : Nat := 4983230072969 + 3 ^ 40 * 7919 * 2
def baseEnd_7919 : Nat := 4066253303059750576087

theorem tailTrace_7919 : CollatzResearch.WordTrace tailWord_7919 prefixEnd_7919 4066253303059750576087 := by
  unfold tailWord_7919
  simp only [CollatzResearch.WordTrace]
  refine ⟨288829658318290302634811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192553105545526868423207 288829658318290302634811)
  ·
    refine ⟨433244487477435453952217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288829658318290302634811 433244487477435453952217)
    ·
      refine ⟨324933365608076590464163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433244487477435453952217 324933365608076590464163)
      ·
        refine ⟨487400048412114885696245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324933365608076590464163 487400048412114885696245)
        ·
          refine ⟨45693754538635770534023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 487400048412114885696245 45693754538635770534023)
          ·
            refine ⟨68540631807953655801035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45693754538635770534023 68540631807953655801035)
            ·
              refine ⟨102810947711930483701553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68540631807953655801035 102810947711930483701553)
              ·
                refine ⟨77108210783947862776165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102810947711930483701553 77108210783947862776165)
                ·
                  refine ⟨14457789521990224270531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77108210783947862776165 14457789521990224270531)
                  ·
                    refine ⟨21686684282985336405797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14457789521990224270531 21686684282985336405797)
                    ·
                      refine ⟨4066253303059750576087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21686684282985336405797 4066253303059750576087)
                      ·
                        rfl

theorem cell23_7919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_7919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7919 prefixEnd_7919 := by exact prefixLift 7919
  have htrace : WordTrace (prefixWord ++ tailWord_7919) baseStart_7919 baseEnd_7919 := by
    simpa [prefixWord, tailWord_7919, baseEnd_7919] using wordTrace_append hprefix tailTrace_7919
  have hstable : (prefixWord ++ tailWord_7919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7919).length < 2 ^ (prefixWord ++ tailWord_7919).sum := by decide
  have hdescent : baseEnd_7919 < baseStart_7919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7939 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 3]
def baseStart_7939 : Nat := 118140960795 + 7939 * 2 ^ 59
def prefixEnd_7939 : Nat := 4983230072969 + 3 ^ 40 * 7939 * 2
def baseEnd_7939 : Nat := 4076522916149672325995

theorem tailTrace_7939 : CollatzResearch.WordTrace tailWord_7939 prefixEnd_7939 4076522916149672325995 := by
  unfold tailWord_7939
  simp only [CollatzResearch.WordTrace]
  refine ⟨289559118245833718362871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193039412163889145575247 289559118245833718362871)
  ·
    refine ⟨434338677368750577544307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289559118245833718362871 434338677368750577544307)
    ·
      refine ⟨651508016053125866316461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434338677368750577544307 651508016053125866316461)
      ·
        refine ⟨244315506019922199868673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 651508016053125866316461 244315506019922199868673)
        ·
          refine ⟨183236629514941649901505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244315506019922199868673 183236629514941649901505)
          ·
            refine ⟨137427472136206237426129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183236629514941649901505 137427472136206237426129)
            ·
              refine ⟨103070604102154678069597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137427472136206237426129 103070604102154678069597)
              ·
                refine ⟨38651476538308004276099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103070604102154678069597 38651476538308004276099)
                ·
                  refine ⟨57977214807462006414149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38651476538308004276099 57977214807462006414149)
                  ·
                    refine ⟨10870727776399126202653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57977214807462006414149 10870727776399126202653)
                    ·
                      refine ⟨4076522916149672325995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10870727776399126202653 4076522916149672325995)
                      ·
                        rfl

theorem cell23_7939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_7939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7939 prefixEnd_7939 := by exact prefixLift 7939
  have htrace : WordTrace (prefixWord ++ tailWord_7939) baseStart_7939 baseEnd_7939 := by
    simpa [prefixWord, tailWord_7939, baseEnd_7939] using wordTrace_append hprefix tailTrace_7939
  have hstable : (prefixWord ++ tailWord_7939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7939).length < 2 ^ (prefixWord ++ tailWord_7939).sum := by decide
  have hdescent : baseEnd_7939 < baseStart_7939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7976 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 6]
def baseStart_7976 : Nat := 118140960795 + 7976 * 2 ^ 59
def prefixEnd_7976 : Nat := 4983230072969 + 3 ^ 40 * 7976 * 2
def baseEnd_7976 : Nat := 455057966707336395925

theorem tailTrace_7976 : CollatzResearch.WordTrace tailWord_7976 prefixEnd_7976 455057966707336395925 := by
  unfold tailWord_7976
  simp only [CollatzResearch.WordTrace]
  refine ⟨145454309555894518729891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193939079407859358306521 145454309555894518729891)
  ·
    refine ⟨218181464333841778094837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145454309555894518729891 218181464333841778094837)
    ·
      refine ⟨20454512281297666696391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218181464333841778094837 20454512281297666696391)
      ·
        refine ⟨30681768421946500044587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20454512281297666696391 30681768421946500044587)
        ·
          refine ⟨46022652632919750066881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30681768421946500044587 46022652632919750066881)
          ·
            refine ⟨34516989474689812550161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46022652632919750066881 34516989474689812550161)
            ·
              refine ⟨25887742106017359412621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34516989474689812550161 25887742106017359412621)
              ·
                refine ⟨9707903289756509779733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25887742106017359412621 9707903289756509779733)
                ·
                  refine ⟨455057966707336395925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9707903289756509779733 455057966707336395925)
                  ·
                    rfl

theorem cell23_7976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 6].length) (baseStart_7976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7976 prefixEnd_7976 := by exact prefixLift 7976
  have htrace : WordTrace (prefixWord ++ tailWord_7976) baseStart_7976 baseEnd_7976 := by
    simpa [prefixWord, tailWord_7976, baseEnd_7976] using wordTrace_append hprefix tailTrace_7976
  have hstable : (prefixWord ++ tailWord_7976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7976).length < 2 ^ (prefixWord ++ tailWord_7976).sum := by decide
  have hdescent : baseEnd_7976 < baseStart_7976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_7990 : Nat := 118140960795 + 7990 * 2 ^ 59
def prefixEnd_7990 : Nat := 4983230072969 + 3 ^ 40 * 7990 * 2
def baseEnd_7990 : Nat := 4102710429528972788261

theorem tailTrace_7990 : CollatzResearch.WordTrace tailWord_7990 prefixEnd_7990 4102710429528972788261 := by
  unfold tailWord_7990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18213702566316839279339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194279494040712952312949 18213702566316839279339)
  ·
    refine ⟨27320553849475258919009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18213702566316839279339 27320553849475258919009)
    ·
      refine ⟨20490415387106444189257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27320553849475258919009 20490415387106444189257)
      ·
        refine ⟨15367811540329833141943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20490415387106444189257 15367811540329833141943)
        ·
          refine ⟨23051717310494749712915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15367811540329833141943 23051717310494749712915)
          ·
            refine ⟨34577575965742124569373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23051717310494749712915 34577575965742124569373)
            ·
              refine ⟨12966590987153296713515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34577575965742124569373 12966590987153296713515)
              ·
                refine ⟨19449886480729945070273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12966590987153296713515 19449886480729945070273)
                ·
                  refine ⟨14587414860547458802705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19449886480729945070273 14587414860547458802705)
                  ·
                    refine ⟨10940561145410594102029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14587414860547458802705 10940561145410594102029)
                    ·
                      refine ⟨4102710429528972788261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10940561145410594102029 4102710429528972788261)
                      ·
                        rfl

theorem cell23_7990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_7990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990 prefixEnd_7990 := by exact prefixLift 7990
  have htrace : WordTrace (prefixWord ++ tailWord_7990) baseStart_7990 baseEnd_7990 := by
    simpa [prefixWord, tailWord_7990, baseEnd_7990] using wordTrace_append hprefix tailTrace_7990
  have hstable : (prefixWord ++ tailWord_7990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990).length < 2 ^ (prefixWord ++ tailWord_7990).sum := by decide
  have hdescent : baseEnd_7990 < baseStart_7990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8020 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_8020 : Nat := 118140960795 + 8020 * 2 ^ 59
def prefixEnd_8020 : Nat := 4983230072969 + 3 ^ 40 * 8020 * 2
def baseEnd_8020 : Nat := 4118114849163855413123

theorem tailTrace_8020 : CollatzResearch.WordTrace tailWord_8020 prefixEnd_8020 4118114849163855413123 := by
  unfold tailWord_8020
  simp only [CollatzResearch.WordTrace]
  refine ⟨146256715476192276030757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195008953968256368041009 146256715476192276030757)
  ·
    refine ⟨27423134151786051755767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146256715476192276030757 27423134151786051755767)
    ·
      refine ⟨41134701227679077633651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27423134151786051755767 41134701227679077633651)
      ·
        refine ⟨61702051841518616450477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41134701227679077633651 61702051841518616450477)
        ·
          refine ⟨23138269440569481168929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61702051841518616450477 23138269440569481168929)
          ·
            refine ⟨17353702080427110876697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23138269440569481168929 17353702080427110876697)
            ·
              refine ⟨13015276560320333157523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17353702080427110876697 13015276560320333157523)
              ·
                refine ⟨19522914840480499736285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13015276560320333157523 19522914840480499736285)
                ·
                  refine ⟨7321093065180187401107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19522914840480499736285 7321093065180187401107)
                  ·
                    refine ⟨10981639597770281101661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7321093065180187401107 10981639597770281101661)
                    ·
                      refine ⟨4118114849163855413123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10981639597770281101661 4118114849163855413123)
                      ·
                        rfl

theorem cell23_8020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_8020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8020 prefixEnd_8020 := by exact prefixLift 8020
  have htrace : WordTrace (prefixWord ++ tailWord_8020) baseStart_8020 baseEnd_8020 := by
    simpa [prefixWord, tailWord_8020, baseEnd_8020] using wordTrace_append hprefix tailTrace_8020
  have hstable : (prefixWord ++ tailWord_8020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8020).length < 2 ^ (prefixWord ++ tailWord_8020).sum := by decide
  have hdescent : baseEnd_8020 < baseStart_8020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8049 : List Nat := [1, 2, 2, 2, 1, 3, 3, 9]
def baseStart_8049 : Nat := 118140960795 + 8049 * 2 ^ 59
def prefixEnd_8049 : Nat := 4983230072969 + 3 ^ 40 * 8049 * 2
def baseEnd_8049 : Nat := 153074288449786738907

theorem tailTrace_8049 : CollatzResearch.WordTrace tailWord_8049 prefixEnd_8049 153074288449786738907 := by
  unfold tailWord_8049
  simp only [CollatzResearch.WordTrace]
  refine ⟨293571147847322504867201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195714098564881669911467 293571147847322504867201)
  ·
    refine ⟨220178360885491878650401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293571147847322504867201 220178360885491878650401)
    ·
      refine ⟨165133770664118908987801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220178360885491878650401 165133770664118908987801)
      ·
        refine ⟨123850327998089181740851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165133770664118908987801 123850327998089181740851)
        ·
          refine ⟨185775491997133772611277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123850327998089181740851 185775491997133772611277)
          ·
            refine ⟨69665809498925164729229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185775491997133772611277 69665809498925164729229)
            ·
              refine ⟨26124678562096936773461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69665809498925164729229 26124678562096936773461)
              ·
                refine ⟨153074288449786738907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26124678562096936773461 153074288449786738907)
                ·
                  rfl

theorem cell23_8049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 9].length) (baseStart_8049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8049 prefixEnd_8049 := by exact prefixLift 8049
  have htrace : WordTrace (prefixWord ++ tailWord_8049) baseStart_8049 baseEnd_8049 := by
    simpa [prefixWord, tailWord_8049, baseEnd_8049] using wordTrace_append hprefix tailTrace_8049
  have hstable : (prefixWord ++ tailWord_8049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8049).length < 2 ^ (prefixWord ++ tailWord_8049).sum := by decide
  have hdescent : baseEnd_8049 < baseStart_8049 := by decide
  rcases family_descends (prefixWord ++ tailWord_8049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8094 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_8094 : Nat := 118140960795 + 8094 * 2 ^ 59
def prefixEnd_8094 : Nat := 4983230072969 + 3 ^ 40 * 8094 * 2
def baseEnd_8094 : Nat := 4156112417596565887783

theorem tailTrace_8094 : CollatzResearch.WordTrace tailWord_8094 prefixEnd_8094 4156112417596565887783 := by
  unfold tailWord_8094
  simp only [CollatzResearch.WordTrace]
  refine ⟨36901554085536898781917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196808288456196793503557 36901554085536898781917)
  ·
    refine ⟨13838082782076337043219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36901554085536898781917 13838082782076337043219)
    ·
      refine ⟨20757124173114505564829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13838082782076337043219 20757124173114505564829)
      ·
        refine ⟨7783921564917939586811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20757124173114505564829 7783921564917939586811)
        ·
          refine ⟨11675882347376909380217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7783921564917939586811 11675882347376909380217)
          ·
            refine ⟨8756911760532682035163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11675882347376909380217 8756911760532682035163)
            ·
              refine ⟨13135367640799023052745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8756911760532682035163 13135367640799023052745)
              ·
                refine ⟨9851525730599267289559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13135367640799023052745 9851525730599267289559)
                ·
                  refine ⟨14777288595898900934339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9851525730599267289559 14777288595898900934339)
                  ·
                    refine ⟨22165932893848351401509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14777288595898900934339 22165932893848351401509)
                    ·
                      refine ⟨4156112417596565887783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22165932893848351401509 4156112417596565887783)
                      ·
                        rfl

theorem cell23_8094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_8094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8094 prefixEnd_8094 := by exact prefixLift 8094
  have htrace : WordTrace (prefixWord ++ tailWord_8094) baseStart_8094 baseEnd_8094 := by
    simpa [prefixWord, tailWord_8094, baseEnd_8094] using wordTrace_append hprefix tailTrace_8094
  have hstable : (prefixWord ++ tailWord_8094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8094).length < 2 ^ (prefixWord ++ tailWord_8094).sum := by decide
  have hdescent : baseEnd_8094 < baseStart_8094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8097 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_8097 : Nat := 118140960795 + 8097 * 2 ^ 59
def prefixEnd_8097 : Nat := 4983230072969 + 3 ^ 40 * 8097 * 2
def baseEnd_8097 : Nat := 4157652859560054150269

theorem tailTrace_8097 : CollatzResearch.WordTrace tailWord_8097 prefixEnd_8097 4157652859560054150269 := by
  unfold tailWord_8097
  simp only [CollatzResearch.WordTrace]
  refine ⟨295321851673426702614545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196881234448951135076363 295321851673426702614545)
  ·
    refine ⟨221491388755070026960909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295321851673426702614545 221491388755070026960909)
    ·
      refine ⟨83059270783151260110341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221491388755070026960909 83059270783151260110341)
      ·
        refine ⟨15573613271840861270689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83059270783151260110341 15573613271840861270689)
        ·
          refine ⟨11680209953880645953017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15573613271840861270689 11680209953880645953017)
          ·
            refine ⟨8760157465410484464763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11680209953880645953017 8760157465410484464763)
            ·
              refine ⟨13140236198115726697145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8760157465410484464763 13140236198115726697145)
              ·
                refine ⟨9855177148586795022859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13140236198115726697145 9855177148586795022859)
                ·
                  refine ⟨14782765722880192534289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9855177148586795022859 14782765722880192534289)
                  ·
                    refine ⟨11087074292160144400717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14782765722880192534289 11087074292160144400717)
                    ·
                      refine ⟨4157652859560054150269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11087074292160144400717 4157652859560054150269)
                      ·
                        rfl

theorem cell23_8097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_8097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8097 prefixEnd_8097 := by exact prefixLift 8097
  have htrace : WordTrace (prefixWord ++ tailWord_8097) baseStart_8097 baseEnd_8097 := by
    simpa [prefixWord, tailWord_8097, baseEnd_8097] using wordTrace_append hprefix tailTrace_8097
  have hstable : (prefixWord ++ tailWord_8097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8097).length < 2 ^ (prefixWord ++ tailWord_8097).sum := by decide
  have hdescent : baseEnd_8097 < baseStart_8097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8099 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 8]
def baseStart_8099 : Nat := 118140960795 + 8099 * 2 ^ 59
def prefixEnd_8099 : Nat := 4983230072969 + 3 ^ 40 * 8099 * 2
def baseEnd_8099 : Nat := 4158679820869046325259

theorem tailTrace_8099 : CollatzResearch.WordTrace tailWord_8099 prefixEnd_8099 4158679820869046325259 := by
  unfold tailWord_8099
  simp only [CollatzResearch.WordTrace]
  refine ⟨295394797666181044187351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196929865110787362791567 295394797666181044187351)
  ·
    refine ⟨443092196499271566281027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295394797666181044187351 443092196499271566281027)
    ·
      refine ⟨664638294748907349421541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443092196499271566281027 664638294748907349421541)
      ·
        refine ⟨124619680265420128016539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 664638294748907349421541 124619680265420128016539)
        ·
          refine ⟨186929520398130192024809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124619680265420128016539 186929520398130192024809)
          ·
            refine ⟨140197140298597644018607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186929520398130192024809 140197140298597644018607)
            ·
              refine ⟨210295710447896466027911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140197140298597644018607 210295710447896466027911)
              ·
                refine ⟨315443565671844699041867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210295710447896466027911 315443565671844699041867)
                ·
                  refine ⟨473165348507767048562801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315443565671844699041867 473165348507767048562801)
                  ·
                    refine ⟨354874011380825286422101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 473165348507767048562801 354874011380825286422101)
                    ·
                      refine ⟨4158679820869046325259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 354874011380825286422101 4158679820869046325259)
                      ·
                        rfl

theorem cell23_8099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_8099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8099 prefixEnd_8099 := by exact prefixLift 8099
  have htrace : WordTrace (prefixWord ++ tailWord_8099) baseStart_8099 baseEnd_8099 := by
    simpa [prefixWord, tailWord_8099, baseEnd_8099] using wordTrace_append hprefix tailTrace_8099
  have hstable : (prefixWord ++ tailWord_8099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8099).length < 2 ^ (prefixWord ++ tailWord_8099).sum := by decide
  have hdescent : baseEnd_8099 < baseStart_8099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_8190 : Nat := 118140960795 + 8190 * 2 ^ 59
def prefixEnd_8190 : Nat := 4983230072969 + 3 ^ 40 * 8190 * 2
def baseEnd_8190 : Nat := 467267395603132254149

theorem tailTrace_8190 : CollatzResearch.WordTrace tailWord_8190 prefixEnd_8190 467267395603132254149 := by
  unfold tailWord_8190
  simp only [CollatzResearch.WordTrace]
  refine ⟨37339230042062948218753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199142560224335723833349 37339230042062948218753)
  ·
    refine ⟨28004422531547211164065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37339230042062948218753 28004422531547211164065)
    ·
      refine ⟨21003316898660408373049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28004422531547211164065 21003316898660408373049)
      ·
        refine ⟨15752487673995306279787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21003316898660408373049 15752487673995306279787)
        ·
          refine ⟨23628731510992959419681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15752487673995306279787 23628731510992959419681)
          ·
            refine ⟨17721548633244719564761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23628731510992959419681 17721548633244719564761)
            ·
              refine ⟨13291161474933539673571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17721548633244719564761 13291161474933539673571)
              ·
                refine ⟨19936742212400309510357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13291161474933539673571 19936742212400309510357)
                ·
                  refine ⟨467267395603132254149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19936742212400309510357 467267395603132254149)
                  ·
                    rfl

theorem cell23_8190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_8190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190 prefixEnd_8190 := by exact prefixLift 8190
  have htrace : WordTrace (prefixWord ++ tailWord_8190) baseStart_8190 baseEnd_8190 := by
    simpa [prefixWord, tailWord_8190, baseEnd_8190] using wordTrace_append hprefix tailTrace_8190
  have hstable : (prefixWord ++ tailWord_8190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190).length < 2 ^ (prefixWord ++ tailWord_8190).sum := by decide
  have hdescent : baseEnd_8190 < baseStart_8190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8216 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 2, 8]
def baseStart_8216 : Nat := 118140960795 + 8216 * 2 ^ 59
def prefixEnd_8216 : Nat := 4983230072969 + 3 ^ 40 * 8216 * 2
def baseEnd_8216 : Nat := 1406252352481696187407

theorem tailTrace_8216 : CollatzResearch.WordTrace tailWord_8216 prefixEnd_8216 1406252352481696187407 := by
  unfold tailWord_8216
  simp only [CollatzResearch.WordTrace]
  refine ⟨149831069121155013098251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199774758828206684131001 149831069121155013098251)
  ·
    refine ⟨224746603681732519647377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149831069121155013098251 224746603681732519647377)
    ·
      refine ⟨168559952761299389735533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224746603681732519647377 168559952761299389735533)
      ·
        refine ⟨63209982285487271150825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168559952761299389735533 63209982285487271150825)
        ·
          refine ⟨47407486714115453363119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63209982285487271150825 47407486714115453363119)
          ·
            refine ⟨71111230071173180044679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47407486714115453363119 71111230071173180044679)
            ·
              refine ⟨106666845106759770067019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71111230071173180044679 106666845106759770067019)
              ·
                refine ⟨160000267660139655100529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106666845106759770067019 160000267660139655100529)
                ·
                  refine ⟨120000200745104741325397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160000267660139655100529 120000200745104741325397)
                  ·
                    refine ⟨1406252352481696187407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120000200745104741325397 1406252352481696187407)
                    ·
                      rfl

theorem cell23_8216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_8216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8216 prefixEnd_8216 := by exact prefixLift 8216
  have htrace : WordTrace (prefixWord ++ tailWord_8216) baseStart_8216 baseEnd_8216 := by
    simpa [prefixWord, tailWord_8216, baseEnd_8216] using wordTrace_append hprefix tailTrace_8216
  have hstable : (prefixWord ++ tailWord_8216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8216).length < 2 ^ (prefixWord ++ tailWord_8216).sum := by decide
  have hdescent : baseEnd_8216 < baseStart_8216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8223 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_8223 : Nat := 118140960795 + 8223 * 2 ^ 59
def prefixEnd_8223 : Nat := 4983230072969 + 3 ^ 40 * 8223 * 2
def baseEnd_8223 : Nat := 4222351422026561174689

theorem tailTrace_8223 : CollatzResearch.WordTrace tailWord_8223 prefixEnd_8223 4222351422026561174689 := by
  unfold tailWord_8223
  simp only [CollatzResearch.WordTrace]
  refine ⟨299917449216950221701323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199944966144633481134215 299917449216950221701323)
  ·
    refine ⟨449876173825425332551985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299917449216950221701323 449876173825425332551985)
    ·
      refine ⟨337407130369068999413989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449876173825425332551985 337407130369068999413989)
      ·
        refine ⟨63263836944200437390123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337407130369068999413989 63263836944200437390123)
        ·
          refine ⟨94895755416300656085185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63263836944200437390123 94895755416300656085185)
          ·
            refine ⟨71171816562225492063889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94895755416300656085185 71171816562225492063889)
            ·
              refine ⟨53378862421669119047917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71171816562225492063889 53378862421669119047917)
              ·
                refine ⟨20017073408125919642969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53378862421669119047917 20017073408125919642969)
                ·
                  refine ⟨15012805056094439732227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20017073408125919642969 15012805056094439732227)
                  ·
                    refine ⟨22519207584141659598341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15012805056094439732227 22519207584141659598341)
                    ·
                      refine ⟨4222351422026561174689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22519207584141659598341 4222351422026561174689)
                      ·
                        rfl

theorem cell23_8223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_8223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8223 prefixEnd_8223 := by exact prefixLift 8223
  have htrace : WordTrace (prefixWord ++ tailWord_8223) baseStart_8223 baseEnd_8223 := by
    simpa [prefixWord, tailWord_8223, baseEnd_8223] using wordTrace_append hprefix tailTrace_8223
  have hstable : (prefixWord ++ tailWord_8223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8223).length < 2 ^ (prefixWord ++ tailWord_8223).sum := by decide
  have hdescent : baseEnd_8223 < baseStart_8223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8236 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_8236 : Nat := 118140960795 + 8236 * 2 ^ 59
def prefixEnd_8236 : Nat := 4983230072969 + 3 ^ 40 * 8236 * 2
def baseEnd_8236 : Nat := 4229026670535010312129

theorem tailTrace_8236 : CollatzResearch.WordTrace tailWord_8236 prefixEnd_8236 4229026670535010312129 := by
  unfold tailWord_8236
  simp only [CollatzResearch.WordTrace]
  refine ⟨150195799084926720962281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200261065446568961283041 150195799084926720962281)
  ·
    refine ⟨112646849313695040721711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150195799084926720962281 112646849313695040721711)
    ·
      refine ⟨168970273970542561082567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112646849313695040721711 168970273970542561082567)
      ·
        refine ⟨253455410955813841623851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168970273970542561082567 253455410955813841623851)
        ·
          refine ⟨380183116433720762435777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253455410955813841623851 380183116433720762435777)
          ·
            refine ⟨285137337325290571826833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380183116433720762435777 285137337325290571826833)
            ·
              refine ⟨213853002993967928870125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285137337325290571826833 213853002993967928870125)
              ·
                refine ⟨80194876122737973326297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213853002993967928870125 80194876122737973326297)
                ·
                  refine ⟨60146157092053479994723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80194876122737973326297 60146157092053479994723)
                  ·
                    refine ⟨90219235638080219992085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60146157092053479994723 90219235638080219992085)
                    ·
                      refine ⟨4229026670535010312129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90219235638080219992085 4229026670535010312129)
                      ·
                        rfl

theorem cell23_8236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_8236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8236 prefixEnd_8236 := by exact prefixLift 8236
  have htrace : WordTrace (prefixWord ++ tailWord_8236) baseStart_8236 baseEnd_8236 := by
    simpa [prefixWord, tailWord_8236, baseEnd_8236] using wordTrace_append hprefix tailTrace_8236
  have hstable : (prefixWord ++ tailWord_8236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8236).length < 2 ^ (prefixWord ++ tailWord_8236).sum := by decide
  have hdescent : baseEnd_8236 < baseStart_8236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8243 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 3]
def baseStart_8243 : Nat := 118140960795 + 8243 * 2 ^ 59
def prefixEnd_8243 : Nat := 4983230072969 + 3 ^ 40 * 8243 * 2
def baseEnd_8243 : Nat := 4232621035116482924597

theorem tailTrace_8243 : CollatzResearch.WordTrace tailWord_8243 prefixEnd_8243 4232621035116482924597 := by
  unfold tailWord_8243
  simp only [CollatzResearch.WordTrace]
  refine ⟨300646909144493637429383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200431272762995758286255 300646909144493637429383)
  ·
    refine ⟨450970363716740456144075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300646909144493637429383 450970363716740456144075)
    ·
      refine ⟨676455545575110684216113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450970363716740456144075 676455545575110684216113)
      ·
        refine ⟨507341659181333013162085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676455545575110684216113 507341659181333013162085)
        ·
          refine ⟨95126561096499939967891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 507341659181333013162085 95126561096499939967891)
          ·
            refine ⟨142689841644749909951837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95126561096499939967891 142689841644749909951837)
            ·
              refine ⟨53508690616781216231939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142689841644749909951837 53508690616781216231939)
              ·
                refine ⟨80263035925171824347909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53508690616781216231939 80263035925171824347909)
                ·
                  refine ⟨15049319235969717065233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80263035925171824347909 15049319235969717065233)
                  ·
                    refine ⟨11286989426977287798925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15049319235969717065233 11286989426977287798925)
                    ·
                      refine ⟨4232621035116482924597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11286989426977287798925 4232621035116482924597)
                      ·
                        rfl

theorem cell23_8243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_8243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8243 prefixEnd_8243 := by exact prefixLift 8243
  have htrace : WordTrace (prefixWord ++ tailWord_8243) baseStart_8243 baseEnd_8243 := by
    simpa [prefixWord, tailWord_8243, baseEnd_8243] using wordTrace_append hprefix tailTrace_8243
  have hstable : (prefixWord ++ tailWord_8243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8243).length < 2 ^ (prefixWord ++ tailWord_8243).sum := by decide
  have hdescent : baseEnd_8243 < baseStart_8243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8263 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 6]
def baseStart_8263 : Nat := 118140960795 + 8263 * 2 ^ 59
def prefixEnd_8263 : Nat := 4983230072969 + 3 ^ 40 * 8263 * 2
def baseEnd_8263 : Nat := 471432294245156074945

theorem tailTrace_8263 : CollatzResearch.WordTrace tailWord_8263 prefixEnd_8263 471432294245156074945 := by
  unfold tailWord_8263
  simp only [CollatzResearch.WordTrace]
  refine ⟨301376369072037053157443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200917579381358035438295 301376369072037053157443)
  ·
    refine ⟨452064553608055579736165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301376369072037053157443 452064553608055579736165)
    ·
      refine ⟨84762103801510421200531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452064553608055579736165 84762103801510421200531)
      ·
        refine ⟨127143155702265631800797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84762103801510421200531 127143155702265631800797)
        ·
          refine ⟨47678683388349611925299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127143155702265631800797 47678683388349611925299)
          ·
            refine ⟨71518025082524417887949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47678683388349611925299 71518025082524417887949)
            ·
              refine ⟨26819259405946656707981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71518025082524417887949 26819259405946656707981)
              ·
                refine ⟨10057222277229996265493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26819259405946656707981 10057222277229996265493)
                ·
                  refine ⟨471432294245156074945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10057222277229996265493 471432294245156074945)
                  ·
                    rfl

theorem cell23_8263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 6].length) (baseStart_8263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8263 prefixEnd_8263 := by exact prefixLift 8263
  have htrace : WordTrace (prefixWord ++ tailWord_8263) baseStart_8263 baseEnd_8263 := by
    simpa [prefixWord, tailWord_8263, baseEnd_8263] using wordTrace_append hprefix tailTrace_8263
  have hstable : (prefixWord ++ tailWord_8263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8263).length < 2 ^ (prefixWord ++ tailWord_8263).sum := by decide
  have hdescent : baseEnd_8263 < baseStart_8263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8310 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_8310 : Nat := 118140960795 + 8310 * 2 ^ 59
def prefixEnd_8310 : Nat := 4983230072969 + 3 ^ 40 * 8310 * 2
def baseEnd_8310 : Nat := 1422341412989240262263

theorem tailTrace_8310 : CollatzResearch.WordTrace tailWord_8310 prefixEnd_8310 1422341412989240262263 := by
  unfold tailWord_8310
  simp only [CollatzResearch.WordTrace]
  refine ⟨18943162493860255007399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202060399934509386745589 18943162493860255007399)
  ·
    refine ⟨28414743740790382511099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18943162493860255007399 28414743740790382511099)
    ·
      refine ⟨42622115611185573766649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28414743740790382511099 42622115611185573766649)
      ·
        refine ⟨31966586708389180324987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42622115611185573766649 31966586708389180324987)
        ·
          refine ⟨47949880062583770487481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31966586708389180324987 47949880062583770487481)
          ·
            refine ⟨35962410046937827865611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47949880062583770487481 35962410046937827865611)
            ·
              refine ⟨53943615070406741798417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35962410046937827865611 53943615070406741798417)
              ·
                refine ⟨40457711302805056348813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53943615070406741798417 40457711302805056348813)
                ·
                  refine ⟨15171641738551896130805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40457711302805056348813 15171641738551896130805)
                  ·
                    refine ⟨1422341412989240262263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15171641738551896130805 1422341412989240262263)
                    ·
                      rfl

theorem cell23_8310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_8310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8310 prefixEnd_8310 := by exact prefixLift 8310
  have htrace : WordTrace (prefixWord ++ tailWord_8310) baseStart_8310 baseEnd_8310 := by
    simpa [prefixWord, tailWord_8310, baseEnd_8310] using wordTrace_append hprefix tailTrace_8310
  have hstable : (prefixWord ++ tailWord_8310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8310).length < 2 ^ (prefixWord ++ tailWord_8310).sum := by decide
  have hdescent : baseEnd_8310 < baseStart_8310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8323 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 1, 6]
def baseStart_8323 : Nat := 118140960795 + 8323 * 2 ^ 59
def prefixEnd_8323 : Nat := 4983230072969 + 3 ^ 40 * 8323 * 2
def baseEnd_8323 : Nat := 1424566495825389974743

theorem tailTrace_8323 : CollatzResearch.WordTrace tailWord_8323 prefixEnd_8323 1424566495825389974743 := by
  unfold tailWord_8323
  simp only [CollatzResearch.WordTrace]
  refine ⟨303564748854667300341623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202376499236444866894415 303564748854667300341623)
  ·
    refine ⟨455347123282000950512435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303564748854667300341623 455347123282000950512435)
    ·
      refine ⟨683020684923001425768653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455347123282000950512435 683020684923001425768653)
      ·
        refine ⟨256132756846125534663245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 683020684923001425768653 256132756846125534663245)
        ·
          refine ⟨96049783817297075498717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256132756846125534663245 96049783817297075498717)
          ·
            refine ⟨36018668931486403312019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96049783817297075498717 36018668931486403312019)
            ·
              refine ⟨54028003397229604968029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36018668931486403312019 54028003397229604968029)
              ·
                refine ⟨20260501273961101863011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54028003397229604968029 20260501273961101863011)
                ·
                  refine ⟨30390751910941652794517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20260501273961101863011 30390751910941652794517)
                  ·
                    refine ⟨1424566495825389974743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30390751910941652794517 1424566495825389974743)
                    ·
                      rfl

theorem cell23_8323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 6].length) (baseStart_8323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8323 prefixEnd_8323 := by exact prefixLift 8323
  have htrace : WordTrace (prefixWord ++ tailWord_8323) baseStart_8323 baseEnd_8323 := by
    simpa [prefixWord, tailWord_8323, baseEnd_8323] using wordTrace_append hprefix tailTrace_8323
  have hstable : (prefixWord ++ tailWord_8323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8323).length < 2 ^ (prefixWord ++ tailWord_8323).sum := by decide
  have hdescent : baseEnd_8323 < baseStart_8323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_8330 : Nat := 118140960795 + 8330 * 2 ^ 59
def prefixEnd_8330 : Nat := 4983230072969 + 3 ^ 40 * 8330 * 2
def baseEnd_8330 : Nat := 4277293852057642536697

theorem tailTrace_8330 : CollatzResearch.WordTrace tailWord_8330 prefixEnd_8330 4277293852057642536697 := by
  unfold tailWord_8330
  simp only [CollatzResearch.WordTrace]
  refine ⟨75955014957326873961611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202546706552871663897629 75955014957326873961611)
  ·
    refine ⟨113932522435990310942417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75955014957326873961611 113932522435990310942417)
    ·
      refine ⟨85449391826992733206813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113932522435990310942417 85449391826992733206813)
      ·
        refine ⟨32043521935122274952555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85449391826992733206813 32043521935122274952555)
        ·
          refine ⟨48065282902683412428833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32043521935122274952555 48065282902683412428833)
          ·
            refine ⟨36048962177012559321625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48065282902683412428833 36048962177012559321625)
            ·
              refine ⟨27036721632759419491219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36048962177012559321625 27036721632759419491219)
              ·
                refine ⟨40555082449139129236829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27036721632759419491219 40555082449139129236829)
                ·
                  refine ⟨15208155918427173463811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40555082449139129236829 15208155918427173463811)
                  ·
                    refine ⟨22812233877640760195717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15208155918427173463811 22812233877640760195717)
                    ·
                      refine ⟨4277293852057642536697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22812233877640760195717 4277293852057642536697)
                      ·
                        rfl

theorem cell23_8330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_8330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330 prefixEnd_8330 := by exact prefixLift 8330
  have htrace : WordTrace (prefixWord ++ tailWord_8330) baseStart_8330 baseEnd_8330 := by
    simpa [prefixWord, tailWord_8330, baseEnd_8330] using wordTrace_append hprefix tailTrace_8330
  have hstable : (prefixWord ++ tailWord_8330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330).length < 2 ^ (prefixWord ++ tailWord_8330).sum := by decide
  have hdescent : baseEnd_8330 < baseStart_8330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8344 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 1, 5]
def baseStart_8344 : Nat := 118140960795 + 8344 * 2 ^ 59
def prefixEnd_8344 : Nat := 4983230072969 + 3 ^ 40 * 8344 * 2
def baseEnd_8344 : Nat := 1428160860406862587211

theorem tailTrace_8344 : CollatzResearch.WordTrace tailWord_8344 prefixEnd_8344 1428160860406862587211 := by
  unfold tailWord_8344
  simp only [CollatzResearch.WordTrace]
  refine ⟨152165340889293943428043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202887121185725257904057 152165340889293943428043)
  ·
    refine ⟨228248011333940915142065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152165340889293943428043 228248011333940915142065)
    ·
      refine ⟨171186008500455686356549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228248011333940915142065 171186008500455686356549)
      ·
        refine ⟨32097376593835441191853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171186008500455686356549 32097376593835441191853)
        ·
          refine ⟨12036516222688290446945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32097376593835441191853 12036516222688290446945)
          ·
            refine ⟨9027387167016217835209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12036516222688290446945 9027387167016217835209)
            ·
              refine ⟨6770540375262163376407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9027387167016217835209 6770540375262163376407)
              ·
                refine ⟨10155810562893245064611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6770540375262163376407 10155810562893245064611)
                ·
                  refine ⟨15233715844339867596917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10155810562893245064611 15233715844339867596917)
                  ·
                    refine ⟨1428160860406862587211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15233715844339867596917 1428160860406862587211)
                    ·
                      rfl

theorem cell23_8344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_8344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8344 prefixEnd_8344 := by exact prefixLift 8344
  have htrace : WordTrace (prefixWord ++ tailWord_8344) baseStart_8344 baseEnd_8344 := by
    simpa [prefixWord, tailWord_8344, baseEnd_8344] using wordTrace_append hprefix tailTrace_8344
  have hstable : (prefixWord ++ tailWord_8344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8344).length < 2 ^ (prefixWord ++ tailWord_8344).sum := by decide
  have hdescent : baseEnd_8344 < baseStart_8344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353 : List Nat := [1, 2, 3, 3, 1, 3, 10]
def baseStart_8353 : Nat := 118140960795 + 8353 * 2 ^ 59
def prefixEnd_8353 : Nat := 4983230072969 + 3 ^ 40 * 8353 * 2
def baseEnd_8353 : Nat := 52951900087790772211

theorem tailTrace_8353 : CollatzResearch.WordTrace tailWord_8353 prefixEnd_8353 52951900087790772211 := by
  unfold tailWord_8353
  simp only [CollatzResearch.WordTrace]
  refine ⟨304658938745982423933713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203105959163988282622475 304658938745982423933713)
  ·
    refine ⟨228494204059486817950285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304658938745982423933713 228494204059486817950285)
    ·
      refine ⟨85685326522307556731357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228494204059486817950285 85685326522307556731357)
      ·
        refine ⟨32131997445865333774259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85685326522307556731357 32131997445865333774259)
        ·
          refine ⟨48197996168798000661389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32131997445865333774259 48197996168798000661389)
          ·
            refine ⟨18074248563299250248021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48197996168798000661389 18074248563299250248021)
            ·
              refine ⟨52951900087790772211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18074248563299250248021 52951900087790772211)
              ·
                rfl

theorem cell23_8353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 10].length) (baseStart_8353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353 prefixEnd_8353 := by exact prefixLift 8353
  have htrace : WordTrace (prefixWord ++ tailWord_8353) baseStart_8353 baseEnd_8353 := by
    simpa [prefixWord, tailWord_8353, baseEnd_8353] using wordTrace_append hprefix tailTrace_8353
  have hstable : (prefixWord ++ tailWord_8353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353).length < 2 ^ (prefixWord ++ tailWord_8353).sum := by decide
  have hdescent : baseEnd_8353 < baseStart_8353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8398 : List Nat := [4, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2]
def baseStart_8398 : Nat := 118140960795 + 8398 * 2 ^ 59
def prefixEnd_8398 : Nat := 4983230072969 + 3 ^ 40 * 8398 * 2
def baseEnd_8398 : Nat := 4312210536563376486385

theorem tailTrace_8398 : CollatzResearch.WordTrace tailWord_8398 prefixEnd_8398 4312210536563376486385 := by
  unfold tailWord_8398
  simp only [CollatzResearch.WordTrace]
  refine ⟨38287527947869388665231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 204200149055303406214565 38287527947869388665231)
  ·
    refine ⟨57431291921804082997847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38287527947869388665231 57431291921804082997847)
    ·
      refine ⟨86146937882706124496771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57431291921804082997847 86146937882706124496771)
      ·
        refine ⟨129220406824059186745157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86146937882706124496771 129220406824059186745157)
        ·
          refine ⟨24228826279511097514717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129220406824059186745157 24228826279511097514717)
          ·
            refine ⟨9085809854816661568019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24228826279511097514717 9085809854816661568019)
            ·
              refine ⟨13628714782224992352029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9085809854816661568019 13628714782224992352029)
              ·
                refine ⟨5110768043334372132011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13628714782224992352029 5110768043334372132011)
                ·
                  refine ⟨7666152065001558198017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5110768043334372132011 7666152065001558198017)
                  ·
                    refine ⟨5749614048751168648513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7666152065001558198017 5749614048751168648513)
                    ·
                      refine ⟨4312210536563376486385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5749614048751168648513 4312210536563376486385)
                      ·
                        rfl

theorem cell23_8398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_8398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8398 prefixEnd_8398 := by exact prefixLift 8398
  have htrace : WordTrace (prefixWord ++ tailWord_8398) baseStart_8398 baseEnd_8398 := by
    simpa [prefixWord, tailWord_8398, baseEnd_8398] using wordTrace_append hprefix tailTrace_8398
  have hstable : (prefixWord ++ tailWord_8398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8398).length < 2 ^ (prefixWord ++ tailWord_8398).sum := by decide
  have hdescent : baseEnd_8398 < baseStart_8398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8431 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 2, 1, 3]
def baseStart_8431 : Nat := 118140960795 + 8431 * 2 ^ 59
def prefixEnd_8431 : Nat := 4983230072969 + 3 ^ 40 * 8431 * 2
def baseEnd_8431 : Nat := 4329155398161747373733

theorem tailTrace_8431 : CollatzResearch.WordTrace tailWord_8431 prefixEnd_8431 4329155398161747373733 := by
  unfold tailWord_8431
  simp only [CollatzResearch.WordTrace]
  refine ⟨307503832463401745273147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 205002554975601163515431 307503832463401745273147)
  ·
    refine ⟨461255748695102617909721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 307503832463401745273147 461255748695102617909721)
    ·
      refine ⟨345941811521326963432291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 461255748695102617909721 345941811521326963432291)
      ·
        refine ⟨518912717281990445148437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345941811521326963432291 518912717281990445148437)
        ·
          refine ⟨24324033622593302116333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 518912717281990445148437 24324033622593302116333)
          ·
            refine ⟨9121512608472488293625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24324033622593302116333 9121512608472488293625)
            ·
              refine ⟨6841134456354366220219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9121512608472488293625 6841134456354366220219)
              ·
                refine ⟨10261701684531549330329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6841134456354366220219 10261701684531549330329)
                ·
                  refine ⟨7696276263398661997747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10261701684531549330329 7696276263398661997747)
                  ·
                    refine ⟨11544414395097992996621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7696276263398661997747 11544414395097992996621)
                    ·
                      refine ⟨4329155398161747373733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11544414395097992996621 4329155398161747373733)
                      ·
                        rfl

theorem cell23_8431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 1, 3].length) (baseStart_8431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8431 prefixEnd_8431 := by exact prefixLift 8431
  have htrace : WordTrace (prefixWord ++ tailWord_8431) baseStart_8431 baseEnd_8431 := by
    simpa [prefixWord, tailWord_8431, baseEnd_8431] using wordTrace_append hprefix tailTrace_8431
  have hstable : (prefixWord ++ tailWord_8431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8431).length < 2 ^ (prefixWord ++ tailWord_8431).sum := by decide
  have hdescent : baseEnd_8431 < baseStart_8431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8453 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_8453 : Nat := 118140960795 + 8453 * 2 ^ 59
def prefixEnd_8453 : Nat := 4983230072969 + 3 ^ 40 * 8453 * 2
def baseEnd_8453 : Nat := 4340451972560661298631

theorem tailTrace_8453 : CollatzResearch.WordTrace tailWord_8453 prefixEnd_8453 4340451972560661298631 := by
  unfold tailWord_8453
  simp only [CollatzResearch.WordTrace]
  refine ⟨308306238383699502574013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 205537492255799668382675 308306238383699502574013)
  ·
    refine ⟨115614839393887313465255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 308306238383699502574013 115614839393887313465255)
    ·
      refine ⟨173422259090830970197883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115614839393887313465255 173422259090830970197883)
      ·
        refine ⟨260133388636246455296825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173422259090830970197883 260133388636246455296825)
        ·
          refine ⟨195100041477184841472619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260133388636246455296825 195100041477184841472619)
          ·
            refine ⟨292650062215777262208929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195100041477184841472619 292650062215777262208929)
            ·
              refine ⟨219487546661832946656697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292650062215777262208929 219487546661832946656697)
              ·
                refine ⟨164615659996374709992523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219487546661832946656697 164615659996374709992523)
                ·
                  refine ⟨246923489994562064988785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164615659996374709992523 246923489994562064988785)
                  ·
                    refine ⟨185192617495921548741589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 246923489994562064988785 185192617495921548741589)
                    ·
                      refine ⟨4340451972560661298631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 185192617495921548741589 4340451972560661298631)
                      ·
                        rfl

theorem cell23_8453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_8453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8453 prefixEnd_8453 := by exact prefixLift 8453
  have htrace : WordTrace (prefixWord ++ tailWord_8453) baseStart_8453 baseEnd_8453 := by
    simpa [prefixWord, tailWord_8453, baseEnd_8453] using wordTrace_append hprefix tailTrace_8453
  have hstable : (prefixWord ++ tailWord_8453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8453).length < 2 ^ (prefixWord ++ tailWord_8453).sum := by decide
  have hdescent : baseEnd_8453 < baseStart_8453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8471 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 2, 2, 2]
def baseStart_8471 : Nat := 118140960795 + 8471 * 2 ^ 59
def prefixEnd_8471 : Nat := 4983230072969 + 3 ^ 40 * 8471 * 2
def baseEnd_8471 : Nat := 4349694624341590873549

theorem tailTrace_8471 : CollatzResearch.WordTrace tailWord_8471 prefixEnd_8471 4349694624341590873549 := by
  unfold tailWord_8471
  simp only [CollatzResearch.WordTrace]
  refine ⟨308962752318488576729267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 205975168212325717819511 308962752318488576729267)
  ·
    refine ⟨463444128477732865093901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 308962752318488576729267 463444128477732865093901)
    ·
      refine ⟨173791548179149824410213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 463444128477732865093901 173791548179149824410213)
      ·
        refine ⟨32585915283590592076915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173791548179149824410213 32585915283590592076915)
        ·
          refine ⟨48878872925385888115373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32585915283590592076915 48878872925385888115373)
          ·
            refine ⟨18329577347019708043265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48878872925385888115373 18329577347019708043265)
            ·
              refine ⟨13747183010264781032449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18329577347019708043265 13747183010264781032449)
              ·
                refine ⟨10310387257698585774337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13747183010264781032449 10310387257698585774337)
                ·
                  refine ⟨7732790443273939330753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10310387257698585774337 7732790443273939330753)
                  ·
                    refine ⟨5799592832455454498065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7732790443273939330753 5799592832455454498065)
                    ·
                      refine ⟨4349694624341590873549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5799592832455454498065 4349694624341590873549)
                      ·
                        rfl

theorem cell23_8471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_8471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8471 prefixEnd_8471 := by exact prefixLift 8471
  have htrace : WordTrace (prefixWord ++ tailWord_8471) baseStart_8471 baseEnd_8471 := by
    simpa [prefixWord, tailWord_8471, baseEnd_8471] using wordTrace_append hprefix tailTrace_8471
  have hstable : (prefixWord ++ tailWord_8471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8471).length < 2 ^ (prefixWord ++ tailWord_8471).sum := by decide
  have hdescent : baseEnd_8471 < baseStart_8471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8494 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_8494 : Nat := 118140960795 + 8494 * 2 ^ 59
def prefixEnd_8494 : Nat := 4983230072969 + 3 ^ 40 * 8494 * 2
def baseEnd_8494 : Nat := 484611631043888987327

theorem tailTrace_8494 : CollatzResearch.WordTrace tailWord_8494 prefixEnd_8494 484611631043888987327 := by
  unfold tailWord_8494
  simp only [CollatzResearch.WordTrace]
  refine ⟨38725203904395438102067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 206534420823442336544357 38725203904395438102067)
  ·
    refine ⟨58087805856593157153101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38725203904395438102067 58087805856593157153101)
    ·
      refine ⟨21782927196222433932413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58087805856593157153101 21782927196222433932413)
      ·
        refine ⟨8168597698583412724655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21782927196222433932413 8168597698583412724655)
        ·
          refine ⟨12252896547875119086983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8168597698583412724655 12252896547875119086983)
          ·
            refine ⟨18379344821812678630475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12252896547875119086983 18379344821812678630475)
            ·
              refine ⟨27569017232719017945713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18379344821812678630475 27569017232719017945713)
              ·
                refine ⟨20676762924539263459285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27569017232719017945713 20676762924539263459285)
                ·
                  refine ⟨484611631043888987327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20676762924539263459285 484611631043888987327)
                  ·
                    rfl

theorem cell23_8494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_8494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8494 prefixEnd_8494 := by exact prefixLift 8494
  have htrace : WordTrace (prefixWord ++ tailWord_8494) baseStart_8494 baseEnd_8494 := by
    simpa [prefixWord, tailWord_8494, baseEnd_8494] using wordTrace_append hprefix tailTrace_8494
  have hstable : (prefixWord ++ tailWord_8494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8494).length < 2 ^ (prefixWord ++ tailWord_8494).sum := by decide
  have hdescent : baseEnd_8494 < baseStart_8494 := by decide
  rcases family_descends (prefixWord ++ tailWord_8494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8530 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_8530 : Nat := 118140960795 + 8530 * 2 ^ 59
def prefixEnd_8530 : Nat := 4983230072969 + 3 ^ 40 * 8530 * 2
def baseEnd_8530 : Nat := 4379989982956860035777

theorem tailTrace_8530 : CollatzResearch.WordTrace tailWord_8530 prefixEnd_8530 4379989982956860035777 := by
  unfold tailWord_8530
  simp only [CollatzResearch.WordTrace]
  refine ⟨77778664776185413281761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 207409772736494435418029 77778664776185413281761)
  ·
    refine ⟨58333998582139059961321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77778664776185413281761 58333998582139059961321)
    ·
      refine ⟨43750498936604294970991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58333998582139059961321 43750498936604294970991)
      ·
        refine ⟨65625748404906442456487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43750498936604294970991 65625748404906442456487)
        ·
          refine ⟨98438622607359663684731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65625748404906442456487 98438622607359663684731)
          ·
            refine ⟨147657933911039495527097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98438622607359663684731 147657933911039495527097)
            ·
              refine ⟨110743450433279621645323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147657933911039495527097 110743450433279621645323)
              ·
                refine ⟨166115175649919432467985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110743450433279621645323 166115175649919432467985)
                ·
                  refine ⟨124586381737439574350989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166115175649919432467985 124586381737439574350989)
                  ·
                    refine ⟨46719893151539840381621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124586381737439574350989 46719893151539840381621)
                    ·
                      refine ⟨4379989982956860035777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 46719893151539840381621 4379989982956860035777)
                      ·
                        rfl

theorem cell23_8530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_8530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8530 prefixEnd_8530 := by exact prefixLift 8530
  have htrace : WordTrace (prefixWord ++ tailWord_8530) baseStart_8530 baseEnd_8530 := by
    simpa [prefixWord, tailWord_8530, baseEnd_8530] using wordTrace_append hprefix tailTrace_8530
  have hstable : (prefixWord ++ tailWord_8530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8530).length < 2 ^ (prefixWord ++ tailWord_8530).sum := by decide
  have hdescent : baseEnd_8530 < baseStart_8530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8554 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_8554 : Nat := 118140960795 + 8554 * 2 ^ 59
def prefixEnd_8554 : Nat := 4983230072969 + 3 ^ 40 * 8554 * 2
def baseEnd_8554 : Nat := 1464104506221588711889

theorem tailTrace_8554 : CollatzResearch.WordTrace tailWord_8554 prefixEnd_8554 1464104506221588711889 := by
  unfold tailWord_8554
  simp only [CollatzResearch.WordTrace]
  refine ⟨77997502754448438000179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 207993340678529168000477 77997502754448438000179)
  ·
    refine ⟨116996254131672657000269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77997502754448438000179 116996254131672657000269)
    ·
      refine ⟨43873595299377246375101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116996254131672657000269 43873595299377246375101)
      ·
        refine ⟨16452598237266467390663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43873595299377246375101 16452598237266467390663)
        ·
          refine ⟨24678897355899701085995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16452598237266467390663 24678897355899701085995)
          ·
            refine ⟨37018346033849551628993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24678897355899701085995 37018346033849551628993)
            ·
              refine ⟨27763759525387163721745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37018346033849551628993 27763759525387163721745)
              ·
                refine ⟨20822819644040372791309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27763759525387163721745 20822819644040372791309)
                ·
                  refine ⟨7808557366515139796741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20822819644040372791309 7808557366515139796741)
                  ·
                    refine ⟨1464104506221588711889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7808557366515139796741 1464104506221588711889)
                    ·
                      rfl

theorem cell23_8554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_8554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8554 prefixEnd_8554 := by exact prefixLift 8554
  have htrace : WordTrace (prefixWord ++ tailWord_8554) baseStart_8554 baseEnd_8554 := by
    simpa [prefixWord, tailWord_8554, baseEnd_8554] using wordTrace_append hprefix tailTrace_8554
  have hstable : (prefixWord ++ tailWord_8554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8554).length < 2 ^ (prefixWord ++ tailWord_8554).sum := by decide
  have hdescent : baseEnd_8554 < baseStart_8554 := by decide
  rcases family_descends (prefixWord ++ tailWord_8554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8571 : List Nat := [1, 1, 1, 1, 1, 9, 1, 3, 1, 4]
def baseStart_8571 : Nat := 118140960795 + 8571 * 2 ^ 59
def prefixEnd_8571 : Nat := 4983230072969 + 3 ^ 40 * 8571 * 2
def baseEnd_8571 : Nat := 1467014229930399874363

theorem tailTrace_8571 : CollatzResearch.WordTrace tailWord_8571 prefixEnd_8571 1467014229930399874363 := by
  unfold tailWord_8571
  simp only [CollatzResearch.WordTrace]
  refine ⟨312610051956205655369567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 208406701304137103579711 312610051956205655369567)
  ·
    refine ⟨468915077934308483054351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 312610051956205655369567 468915077934308483054351)
    ·
      refine ⟨703372616901462724581527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468915077934308483054351 703372616901462724581527)
      ·
        refine ⟨1055058925352194086872291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703372616901462724581527 1055058925352194086872291)
        ·
          refine ⟨1582588388028291130308437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055058925352194086872291 1582588388028291130308437)
          ·
            refine ⟨9272978836103268341651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1582588388028291130308437 9272978836103268341651)
            ·
              refine ⟨13909468254154902512477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9272978836103268341651 13909468254154902512477)
              ·
                refine ⟨5216050595308088442179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13909468254154902512477 5216050595308088442179)
                ·
                  refine ⟨7824075892962132663269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5216050595308088442179 7824075892962132663269)
                  ·
                    refine ⟨1467014229930399874363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7824075892962132663269 1467014229930399874363)
                    ·
                      rfl

theorem cell23_8571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 4].length) (baseStart_8571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8571 prefixEnd_8571 := by exact prefixLift 8571
  have htrace : WordTrace (prefixWord ++ tailWord_8571) baseStart_8571 baseEnd_8571 := by
    simpa [prefixWord, tailWord_8571, baseEnd_8571] using wordTrace_append hprefix tailTrace_8571
  have hstable : (prefixWord ++ tailWord_8571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8571).length < 2 ^ (prefixWord ++ tailWord_8571).sum := by decide
  have hdescent : baseEnd_8571 < baseStart_8571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8617 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 2, 6, 2]
def baseStart_8617 : Nat := 118140960795 + 8617 * 2 ^ 59
def prefixEnd_8617 : Nat := 4983230072969 + 3 ^ 40 * 8617 * 2
def baseEnd_8617 : Nat := 4424662799898019647877

theorem tailTrace_8617 : CollatzResearch.WordTrace tailWord_8617 prefixEnd_8617 4424662799898019647877 := by
  unfold tailWord_8617
  simp only [CollatzResearch.WordTrace]
  refine ⟨314287809789555511544105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 209525206526370341029403 314287809789555511544105)
  ·
    refine ⟨235715857342166633658079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 314287809789555511544105 235715857342166633658079)
    ·
      refine ⟨353573786013249950487119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235715857342166633658079 353573786013249950487119)
      ·
        refine ⟨530360679019874925730679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353573786013249950487119 530360679019874925730679)
        ·
          refine ⟨795541018529812388596019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530360679019874925730679 795541018529812388596019)
          ·
            refine ⟨1193311527794718582894029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795541018529812388596019 1193311527794718582894029)
            ·
              refine ⟨447491822923019468585261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1193311527794718582894029 447491822923019468585261)
              ·
                refine ⟨167809433596132300719473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 447491822923019468585261 167809433596132300719473)
                ·
                  refine ⟨125857075197099225539605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167809433596132300719473 125857075197099225539605)
                  ·
                    refine ⟨5899550399864026197169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 125857075197099225539605 5899550399864026197169)
                    ·
                      refine ⟨4424662799898019647877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5899550399864026197169 4424662799898019647877)
                      ·
                        rfl

theorem cell23_8617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 6, 2].length) (baseStart_8617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8617 prefixEnd_8617 := by exact prefixLift 8617
  have htrace : WordTrace (prefixWord ++ tailWord_8617) baseStart_8617 baseEnd_8617 := by
    simpa [prefixWord, tailWord_8617, baseEnd_8617] using wordTrace_append hprefix tailTrace_8617
  have hstable : (prefixWord ++ tailWord_8617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8617).length < 2 ^ (prefixWord ++ tailWord_8617).sum := by decide
  have hdescent : baseEnd_8617 < baseStart_8617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8684 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 3]
def baseStart_8684 : Nat := 118140960795 + 8684 * 2 ^ 59
def prefixEnd_8684 : Nat := 4983230072969 + 3 ^ 40 * 8684 * 2
def baseEnd_8684 : Nat := 4459066003749257510069

theorem tailTrace_8684 : CollatzResearch.WordTrace tailWord_8684 prefixEnd_8684 4459066003749257510069 := by
  unfold tailWord_8684
  simp only [CollatzResearch.WordTrace]
  refine ⟨158365750273412977116553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 211154333697883969488737 158365750273412977116553)
  ·
    refine ⟨118774312705059732837415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158365750273412977116553 118774312705059732837415)
    ·
      refine ⟨178161469057589599256123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118774312705059732837415 178161469057589599256123)
      ·
        refine ⟨267242203586384398884185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178161469057589599256123 267242203586384398884185)
        ·
          refine ⟨200431652689788299163139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267242203586384398884185 200431652689788299163139)
          ·
            refine ⟨300647479034682448744709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200431652689788299163139 300647479034682448744709)
            ·
              refine ⟨56371402319002959139633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 300647479034682448744709 56371402319002959139633)
              ·
                refine ⟨42278551739252219354725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56371402319002959139633 42278551739252219354725)
                ·
                  refine ⟨7927228451109791129011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42278551739252219354725 7927228451109791129011)
                  ·
                    refine ⟨11890842676664686693517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7927228451109791129011 11890842676664686693517)
                    ·
                      refine ⟨4459066003749257510069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11890842676664686693517 4459066003749257510069)
                      ·
                        rfl

theorem cell23_8684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_8684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8684 prefixEnd_8684 := by exact prefixLift 8684
  have htrace : WordTrace (prefixWord ++ tailWord_8684) baseStart_8684 baseEnd_8684 := by
    simpa [prefixWord, tailWord_8684, baseEnd_8684] using wordTrace_append hprefix tailTrace_8684
  have hstable : (prefixWord ++ tailWord_8684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8684).length < 2 ^ (prefixWord ++ tailWord_8684).sum := by decide
  have hdescent : baseEnd_8684 < baseStart_8684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8685 : List Nat := [1, 5, 1, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_8685 : Nat := 118140960795 + 8685 * 2 ^ 59
def prefixEnd_8685 : Nat := 4983230072969 + 3 ^ 40 * 8685 * 2
def baseEnd_8685 : Nat := 4459579484403753597565

theorem tailTrace_8685 : CollatzResearch.WordTrace tailWord_8685 prefixEnd_8685 4459579484403753597565 := by
  unfold tailWord_8685
  simp only [CollatzResearch.WordTrace]
  refine ⟨316767973543203125019509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 211178649028802083346339 316767973543203125019509)
  ·
    refine ⟨29696997519675292970579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 316767973543203125019509 29696997519675292970579)
    ·
      refine ⟨44545496279512939455869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29696997519675292970579 44545496279512939455869)
      ·
        refine ⟨16704561104817352295951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44545496279512939455869 16704561104817352295951)
        ·
          refine ⟨25056841657226028443927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16704561104817352295951 25056841657226028443927)
          ·
            refine ⟨37585262485839042665891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25056841657226028443927 37585262485839042665891)
            ·
              refine ⟨56377893728758563998837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37585262485839042665891 56377893728758563998837)
              ·
                refine ⟨5285427537071115374891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56377893728758563998837 5285427537071115374891)
                ·
                  refine ⟨7928141305606673062337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5285427537071115374891 7928141305606673062337)
                  ·
                    refine ⟨5946105979205004796753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7928141305606673062337 5946105979205004796753)
                    ·
                      refine ⟨4459579484403753597565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5946105979205004796753 4459579484403753597565)
                      ·
                        rfl

theorem cell23_8685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_8685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8685 prefixEnd_8685 := by exact prefixLift 8685
  have htrace : WordTrace (prefixWord ++ tailWord_8685) baseStart_8685 baseEnd_8685 := by
    simpa [prefixWord, tailWord_8685, baseEnd_8685] using wordTrace_append hprefix tailTrace_8685
  have hstable : (prefixWord ++ tailWord_8685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8685).length < 2 ^ (prefixWord ++ tailWord_8685).sum := by decide
  have hdescent : baseEnd_8685 < baseStart_8685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8728 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 1, 3, 2]
def baseStart_8728 : Nat := 118140960795 + 8728 * 2 ^ 59
def prefixEnd_8728 : Nat := 4983230072969 + 3 ^ 40 * 8728 * 2
def baseEnd_8728 : Nat := 4481659152547085359867

theorem tailTrace_8728 : CollatzResearch.WordTrace tailWord_8728 prefixEnd_8728 4481659152547085359867 := by
  unfold tailWord_8728
  simp only [CollatzResearch.WordTrace]
  refine ⟨159168156193710734417419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 212224208258280979223225 159168156193710734417419)
  ·
    refine ⟨238752234290566101626129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159168156193710734417419 238752234290566101626129)
    ·
      refine ⟨179064175717924576219597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238752234290566101626129 179064175717924576219597)
      ·
        refine ⟨67149065894221716082349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179064175717924576219597 67149065894221716082349)
        ·
          refine ⟨25180899710333143530881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67149065894221716082349 25180899710333143530881)
          ·
            refine ⟨18885674782749857648161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25180899710333143530881 18885674782749857648161)
            ·
              refine ⟨14164256087062393236121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18885674782749857648161 14164256087062393236121)
              ·
                refine ⟨10623192065296794927091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14164256087062393236121 10623192065296794927091)
                ·
                  refine ⟨15934788097945192390637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10623192065296794927091 15934788097945192390637)
                  ·
                    refine ⟨5975545536729447146489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15934788097945192390637 5975545536729447146489)
                    ·
                      refine ⟨4481659152547085359867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5975545536729447146489 4481659152547085359867)
                      ·
                        rfl

theorem cell23_8728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_8728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8728 prefixEnd_8728 := by exact prefixLift 8728
  have htrace : WordTrace (prefixWord ++ tailWord_8728) baseStart_8728 baseEnd_8728 := by
    simpa [prefixWord, tailWord_8728, baseEnd_8728] using wordTrace_append hprefix tailTrace_8728
  have hstable : (prefixWord ++ tailWord_8728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8728).length < 2 ^ (prefixWord ++ tailWord_8728).sum := by decide
  have hdescent : baseEnd_8728 < baseStart_8728 := by decide
  rcases family_descends (prefixWord ++ tailWord_8728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8741 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 4, 2, 2]
def baseStart_8741 : Nat := 118140960795 + 8741 * 2 ^ 59
def prefixEnd_8741 : Nat := 4983230072969 + 3 ^ 40 * 8741 * 2
def baseEnd_8741 : Nat := 4488334401055534497307

theorem tailTrace_8741 : CollatzResearch.WordTrace tailWord_8741 prefixEnd_8741 4488334401055534497307 := by
  unfold tailWord_8741
  simp only [CollatzResearch.WordTrace]
  refine ⟨318810461340324689058077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 212540307560216459372051 318810461340324689058077)
  ·
    refine ⟨119553923002621758396779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 318810461340324689058077 119553923002621758396779)
    ·
      refine ⟨179330884503932637595169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119553923002621758396779 179330884503932637595169)
      ·
        refine ⟨134498163377949478196377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179330884503932637595169 134498163377949478196377)
        ·
          refine ⟨100873622533462108647283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134498163377949478196377 100873622533462108647283)
          ·
            refine ⟨151310433800193162970925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100873622533462108647283 151310433800193162970925)
            ·
              refine ⟨56741412675072436114097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151310433800193162970925 56741412675072436114097)
              ·
                refine ⟨42556059506304327085573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56741412675072436114097 42556059506304327085573)
                ·
                  refine ⟨7979261157432061328545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42556059506304327085573 7979261157432061328545)
                  ·
                    refine ⟨5984445868074045996409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7979261157432061328545 5984445868074045996409)
                    ·
                      refine ⟨4488334401055534497307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5984445868074045996409 4488334401055534497307)
                      ·
                        rfl

theorem cell23_8741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_8741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8741 prefixEnd_8741 := by exact prefixLift 8741
  have htrace : WordTrace (prefixWord ++ tailWord_8741) baseStart_8741 baseEnd_8741 := by
    simpa [prefixWord, tailWord_8741, baseEnd_8741] using wordTrace_append hprefix tailTrace_8741
  have hstable : (prefixWord ++ tailWord_8741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8741).length < 2 ^ (prefixWord ++ tailWord_8741).sum := by decide
  have hdescent : baseEnd_8741 < baseStart_8741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8744 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_8744 : Nat := 118140960795 + 8744 * 2 ^ 59
def prefixEnd_8744 : Nat := 4983230072969 + 3 ^ 40 * 8744 * 2
def baseEnd_8744 : Nat := 4489874843019022759793

theorem tailTrace_8744 : CollatzResearch.WordTrace tailWord_8744 prefixEnd_8744 4489874843019022759793 := by
  unfold tailWord_8744
  simp only [CollatzResearch.WordTrace]
  refine ⟨159459940164728100708643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 212613253552970800944857 159459940164728100708643)
  ·
    refine ⟨239189910247092151062965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159459940164728100708643 239189910247092151062965)
    ·
      refine ⟨22424054085664889162153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 239189910247092151062965 22424054085664889162153)
      ·
        refine ⟨16818040564248666871615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22424054085664889162153 16818040564248666871615)
        ·
          refine ⟨25227060846373000307423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16818040564248666871615 25227060846373000307423)
          ·
            refine ⟨37840591269559500461135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25227060846373000307423 37840591269559500461135)
            ·
              refine ⟨56760886904339250691703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37840591269559500461135 56760886904339250691703)
              ·
                refine ⟨85141330356508876037555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56760886904339250691703 85141330356508876037555)
                ·
                  refine ⟨127711995534763314056333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85141330356508876037555 127711995534763314056333)
                  ·
                    refine ⟨47891998325536242771125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127711995534763314056333 47891998325536242771125)
                    ·
                      refine ⟨4489874843019022759793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 47891998325536242771125 4489874843019022759793)
                      ·
                        rfl

theorem cell23_8744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_8744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8744 prefixEnd_8744 := by exact prefixLift 8744
  have htrace : WordTrace (prefixWord ++ tailWord_8744) baseStart_8744 baseEnd_8744 := by
    simpa [prefixWord, tailWord_8744, baseEnd_8744] using wordTrace_append hprefix tailTrace_8744
  have hstable : (prefixWord ++ tailWord_8744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8744).length < 2 ^ (prefixWord ++ tailWord_8744).sum := by decide
  have hdescent : baseEnd_8744 < baseStart_8744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8757 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_8757 : Nat := 118140960795 + 8757 * 2 ^ 59
def prefixEnd_8757 : Nat := 4983230072969 + 3 ^ 40 * 8757 * 2
def baseEnd_8757 : Nat := 4496550091527471897233

theorem tailTrace_8757 : CollatzResearch.WordTrace tailWord_8757 prefixEnd_8757 4496550091527471897233 := by
  unfold tailWord_8757
  simp only [CollatzResearch.WordTrace]
  refine ⟨319394029282359421640525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 212929352854906281093683 319394029282359421640525)
  ·
    refine ⟨119772760980884783115197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 319394029282359421640525 119772760980884783115197)
    ·
      refine ⟨44914785367831793668199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119772760980884783115197 44914785367831793668199)
      ·
        refine ⟨67372178051747690502299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44914785367831793668199 67372178051747690502299)
        ·
          refine ⟨101058267077621535753449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67372178051747690502299 101058267077621535753449)
          ·
            refine ⟨75793700308216151815087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101058267077621535753449 75793700308216151815087)
            ·
              refine ⟨113690550462324227722631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75793700308216151815087 113690550462324227722631)
              ·
                refine ⟨170535825693486341583947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113690550462324227722631 170535825693486341583947)
                ·
                  refine ⟨255803738540229512375921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170535825693486341583947 255803738540229512375921)
                  ·
                    refine ⟨191852803905172134281941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 255803738540229512375921 191852803905172134281941)
                    ·
                      refine ⟨4496550091527471897233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 191852803905172134281941 4496550091527471897233)
                      ·
                        rfl

theorem cell23_8757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_8757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8757 prefixEnd_8757 := by exact prefixLift 8757
  have htrace : WordTrace (prefixWord ++ tailWord_8757) baseStart_8757 baseEnd_8757 := by
    simpa [prefixWord, tailWord_8757, baseEnd_8757] using wordTrace_append hprefix tailTrace_8757
  have hstable : (prefixWord ++ tailWord_8757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8757).length < 2 ^ (prefixWord ++ tailWord_8757).sum := by decide
  have hdescent : baseEnd_8757 < baseStart_8757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8764 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 7]
def baseStart_8764 : Nat := 118140960795 + 8764 * 2 ^ 59
def prefixEnd_8764 : Nat := 4983230072969 + 3 ^ 40 * 8764 * 2
def baseEnd_8764 : Nat := 500016050678771612189

theorem tailTrace_8764 : CollatzResearch.WordTrace tailWord_8764 prefixEnd_8764 500016050678771612189 := by
  unfold tailWord_8764
  simp only [CollatzResearch.WordTrace]
  refine ⟨159824670128499808572673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 213099560171333078096897 159824670128499808572673)
  ·
    refine ⟨119868502596374856429505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159824670128499808572673 119868502596374856429505)
    ·
      refine ⟨89901376947281142322129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119868502596374856429505 89901376947281142322129)
      ·
        refine ⟨67426032710460856741597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89901376947281142322129 67426032710460856741597)
        ·
          refine ⟨25284762266422821278099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67426032710460856741597 25284762266422821278099)
          ·
            refine ⟨37927143399634231917149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25284762266422821278099 37927143399634231917149)
            ·
              refine ⟨14222678774862836968931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37927143399634231917149 14222678774862836968931)
              ·
                refine ⟨21334018162294255453397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14222678774862836968931 21334018162294255453397)
                ·
                  refine ⟨500016050678771612189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 21334018162294255453397 500016050678771612189)
                  ·
                    rfl

theorem cell23_8764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_8764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8764 prefixEnd_8764 := by exact prefixLift 8764
  have htrace : WordTrace (prefixWord ++ tailWord_8764) baseStart_8764 baseEnd_8764 := by
    simpa [prefixWord, tailWord_8764, baseEnd_8764] using wordTrace_append hprefix tailTrace_8764
  have hstable : (prefixWord ++ tailWord_8764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8764).length < 2 ^ (prefixWord ++ tailWord_8764).sum := by decide
  have hdescent : baseEnd_8764 < baseStart_8764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8775 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_8775 : Nat := 118140960795 + 8775 * 2 ^ 59
def prefixEnd_8775 : Nat := 4983230072969 + 3 ^ 40 * 8775 * 2
def baseEnd_8775 : Nat := 4505792743308401472151

theorem tailTrace_8775 : CollatzResearch.WordTrace tailWord_8775 prefixEnd_8775 4505792743308401472151 := by
  unfold tailWord_8775
  simp only [CollatzResearch.WordTrace]
  refine ⟨320050543217148495795779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 213367028811432330530519 320050543217148495795779)
  ·
    refine ⟨480075814825722743693669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320050543217148495795779 480075814825722743693669)
    ·
      refine ⟨90014215279823014442563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 480075814825722743693669 90014215279823014442563)
      ·
        refine ⟨135021322919734521663845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90014215279823014442563 135021322919734521663845)
        ·
          refine ⟨25316498047450222811971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135021322919734521663845 25316498047450222811971)
          ·
            refine ⟨37974747071175334217957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25316498047450222811971 37974747071175334217957)
            ·
              refine ⟨7120265075845375165867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37974747071175334217957 7120265075845375165867)
              ·
                refine ⟨10680397613768062748801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7120265075845375165867 10680397613768062748801)
                ·
                  refine ⟨8010298210326047061601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10680397613768062748801 8010298210326047061601)
                  ·
                    refine ⟨6007723657744535296201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8010298210326047061601 6007723657744535296201)
                    ·
                      refine ⟨4505792743308401472151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6007723657744535296201 4505792743308401472151)
                      ·
                        rfl

theorem cell23_8775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_8775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8775 prefixEnd_8775 := by exact prefixLift 8775
  have htrace : WordTrace (prefixWord ++ tailWord_8775) baseStart_8775 baseEnd_8775 := by
    simpa [prefixWord, tailWord_8775, baseEnd_8775] using wordTrace_append hprefix tailTrace_8775
  have hstable : (prefixWord ++ tailWord_8775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8775).length < 2 ^ (prefixWord ++ tailWord_8775).sum := by decide
  have hdescent : baseEnd_8775 < baseStart_8775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8784 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 4, 5, 2]
def baseStart_8784 : Nat := 118140960795 + 8784 * 2 ^ 59
def prefixEnd_8784 : Nat := 4983230072969 + 3 ^ 40 * 8784 * 2
def baseEnd_8784 : Nat := 4510414069198866259609

theorem tailTrace_8784 : CollatzResearch.WordTrace tailWord_8784 prefixEnd_8784 4510414069198866259609 := by
  unfold tailWord_8784
  simp only [CollatzResearch.WordTrace]
  refine ⟨160189400092271516436703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 213585866789695355248937 160189400092271516436703)
  ·
    refine ⟨240284100138407274655055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160189400092271516436703 240284100138407274655055)
    ·
      refine ⟨360426150207610911982583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240284100138407274655055 360426150207610911982583)
      ·
        refine ⟨540639225311416367973875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360426150207610911982583 540639225311416367973875)
        ·
          refine ⟨810958837967124551960813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540639225311416367973875 810958837967124551960813)
          ·
            refine ⟨304109564237671706985305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 810958837967124551960813 304109564237671706985305)
            ·
              refine ⟨228082173178253780238979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304109564237671706985305 228082173178253780238979)
              ·
                refine ⟨342123259767380670358469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228082173178253780238979 342123259767380670358469)
                ·
                  refine ⟨64148111206383875692213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342123259767380670358469 64148111206383875692213)
                  ·
                    refine ⟨6013885425598488346145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64148111206383875692213 6013885425598488346145)
                    ·
                      refine ⟨4510414069198866259609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6013885425598488346145 4510414069198866259609)
                      ·
                        rfl

theorem cell23_8784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 5, 2].length) (baseStart_8784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8784 prefixEnd_8784 := by exact prefixLift 8784
  have htrace : WordTrace (prefixWord ++ tailWord_8784) baseStart_8784 baseEnd_8784 := by
    simpa [prefixWord, tailWord_8784, baseEnd_8784] using wordTrace_append hprefix tailTrace_8784
  have hstable : (prefixWord ++ tailWord_8784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8784).length < 2 ^ (prefixWord ++ tailWord_8784).sum := by decide
  have hdescent : baseEnd_8784 < baseStart_8784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8827 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 6]
def baseStart_8827 : Nat := 118140960795 + 8827 * 2 ^ 59
def prefixEnd_8827 : Nat := 4983230072969 + 3 ^ 40 * 8827 * 2
def baseEnd_8827 : Nat := 4532493737342198021911

theorem tailTrace_8827 : CollatzResearch.WordTrace tailWord_8827 prefixEnd_8827 4532493737342198021911 := by
  unfold tailWord_8827
  simp only [CollatzResearch.WordTrace]
  refine ⟨321947139028761376688735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 214631426019174251125823 321947139028761376688735)
  ·
    refine ⟨482920708543142065033103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 321947139028761376688735 482920708543142065033103)
    ·
      refine ⟨724381062814713097549655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482920708543142065033103 724381062814713097549655)
      ·
        refine ⟨1086571594222069646324483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724381062814713097549655 1086571594222069646324483)
        ·
          refine ⟨1629857391333104469486725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086571594222069646324483 1629857391333104469486725)
          ·
            refine ⟨305598260874957088028761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1629857391333104469486725 305598260874957088028761)
            ·
              refine ⟨229198695656217816021571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305598260874957088028761 229198695656217816021571)
              ·
                refine ⟨343798043484326724032357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229198695656217816021571 343798043484326724032357)
                ·
                  refine ⟨64462133153311260756067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343798043484326724032357 64462133153311260756067)
                  ·
                    refine ⟨96693199729966891134101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64462133153311260756067 96693199729966891134101)
                    ·
                      refine ⟨4532493737342198021911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 96693199729966891134101 4532493737342198021911)
                      ·
                        rfl

theorem cell23_8827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_8827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8827 prefixEnd_8827 := by exact prefixLift 8827
  have htrace : WordTrace (prefixWord ++ tailWord_8827) baseStart_8827 baseEnd_8827 := by
    simpa [prefixWord, tailWord_8827, baseEnd_8827] using wordTrace_append hprefix tailTrace_8827
  have hstable : (prefixWord ++ tailWord_8827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8827).length < 2 ^ (prefixWord ++ tailWord_8827).sum := by decide
  have hdescent : baseEnd_8827 < baseStart_8827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8908 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 1, 5, 2]
def baseStart_8908 : Nat := 118140960795 + 8908 * 2 ^ 59
def prefixEnd_8908 : Nat := 4983230072969 + 3 ^ 40 * 8908 * 2
def baseEnd_8908 : Nat := 4574085670356381109039

theorem tailTrace_8908 : CollatzResearch.WordTrace tailWord_8908 prefixEnd_8908 4574085670356381109039 := by
  unfold tailWord_8908
  simp only [CollatzResearch.WordTrace]
  refine ⟨162450725867656105193689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 216600967823541473591585 162450725867656105193689)
  ·
    refine ⟨121838044400742078895267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162450725867656105193689 121838044400742078895267)
    ·
      refine ⟨182757066601113118342901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121838044400742078895267 182757066601113118342901)
      ·
        refine ⟨17133474993854354844647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 182757066601113118342901 17133474993854354844647)
        ·
          refine ⟨25700212490781532266971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17133474993854354844647 25700212490781532266971)
          ·
            refine ⟨38550318736172298400457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25700212490781532266971 38550318736172298400457)
            ·
              refine ⟨28912739052129223800343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38550318736172298400457 28912739052129223800343)
              ·
                refine ⟨43369108578193835700515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28912739052129223800343 43369108578193835700515)
                ·
                  refine ⟨65053662867290753550773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43369108578193835700515 65053662867290753550773)
                  ·
                    refine ⟨6098780893808508145385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65053662867290753550773 6098780893808508145385)
                    ·
                      refine ⟨4574085670356381109039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6098780893808508145385 4574085670356381109039)
                      ·
                        rfl

theorem cell23_8908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_8908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8908 prefixEnd_8908 := by exact prefixLift 8908
  have htrace : WordTrace (prefixWord ++ tailWord_8908) baseStart_8908 baseEnd_8908 := by
    simpa [prefixWord, tailWord_8908, baseEnd_8908] using wordTrace_append hprefix tailTrace_8908
  have hstable : (prefixWord ++ tailWord_8908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8908).length < 2 ^ (prefixWord ++ tailWord_8908).sum := by decide
  have hdescent : baseEnd_8908 < baseStart_8908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8909 : List Nat := [1, 6, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_8909 : Nat := 118140960795 + 8909 * 2 ^ 59
def prefixEnd_8909 : Nat := 4983230072969 + 3 ^ 40 * 8909 * 2
def baseEnd_8909 : Nat := 1524866383670292398845

theorem tailTrace_8909 : CollatzResearch.WordTrace tailWord_8909 prefixEnd_8909 1524866383670292398845 := by
  unfold tailWord_8909
  simp only [CollatzResearch.WordTrace]
  refine ⟨324937924731689381173781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 216625283154459587449187 324937924731689381173781)
  ·
    refine ⟨15231465221797939742521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 324937924731689381173781 15231465221797939742521)
    ·
      refine ⟨11423598916348454806891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15231465221797939742521 11423598916348454806891)
      ·
        refine ⟨17135398374522682210337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11423598916348454806891 17135398374522682210337)
        ·
          refine ⟨12851548780892011657753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17135398374522682210337 12851548780892011657753)
          ·
            refine ⟨9638661585669008743315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12851548780892011657753 9638661585669008743315)
            ·
              refine ⟨14457992378503513114973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9638661585669008743315 14457992378503513114973)
              ·
                refine ⟨5421747141938817418115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14457992378503513114973 5421747141938817418115)
                ·
                  refine ⟨8132620712908226127173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5421747141938817418115 8132620712908226127173)
                  ·
                    refine ⟨1524866383670292398845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8132620712908226127173 1524866383670292398845)
                    ·
                      rfl

theorem cell23_8909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_8909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8909 prefixEnd_8909 := by exact prefixLift 8909
  have htrace : WordTrace (prefixWord ++ tailWord_8909) baseStart_8909 baseEnd_8909 := by
    simpa [prefixWord, tailWord_8909, baseEnd_8909] using wordTrace_append hprefix tailTrace_8909
  have hstable : (prefixWord ++ tailWord_8909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8909).length < 2 ^ (prefixWord ++ tailWord_8909).sum := by decide
  have hdescent : baseEnd_8909 < baseStart_8909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8921 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 4]
def baseStart_8921 : Nat := 118140960795 + 8921 * 2 ^ 59
def prefixEnd_8921 : Nat := 4983230072969 + 3 ^ 40 * 8921 * 2
def baseEnd_8921 : Nat := 4580760918864830246479

theorem tailTrace_8921 : CollatzResearch.WordTrace tailWord_8921 prefixEnd_8921 4580760918864830246479 := by
  unfold tailWord_8921
  simp only [CollatzResearch.WordTrace]
  refine ⟨325375600688215430610617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 216917067125476953740411 325375600688215430610617)
  ·
    refine ⟨244031700516161572957963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 325375600688215430610617 244031700516161572957963)
    ·
      refine ⟨366047550774242359436945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244031700516161572957963 366047550774242359436945)
      ·
        refine ⟨274535663080681769577709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366047550774242359436945 274535663080681769577709)
        ·
          refine ⟨102950873655255663591641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274535663080681769577709 102950873655255663591641)
          ·
            refine ⟨77213155241441747693731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102950873655255663591641 77213155241441747693731)
            ·
              refine ⟨115819732862162621540597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77213155241441747693731 115819732862162621540597)
              ·
                refine ⟨10858099955827745769431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115819732862162621540597 10858099955827745769431)
                ·
                  refine ⟨16287149933741618654147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10858099955827745769431 16287149933741618654147)
                  ·
                    refine ⟨24430724900612427981221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16287149933741618654147 24430724900612427981221)
                    ·
                      refine ⟨4580760918864830246479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 24430724900612427981221 4580760918864830246479)
                      ·
                        rfl

theorem cell23_8921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_8921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8921 prefixEnd_8921 := by exact prefixLift 8921
  have htrace : WordTrace (prefixWord ++ tailWord_8921) baseStart_8921 baseEnd_8921 := by
    simpa [prefixWord, tailWord_8921, baseEnd_8921] using wordTrace_append hprefix tailTrace_8921
  have hstable : (prefixWord ++ tailWord_8921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8921).length < 2 ^ (prefixWord ++ tailWord_8921).sum := by decide
  have hdescent : baseEnd_8921 < baseStart_8921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8932 : List Nat := [2, 3, 1, 1, 1, 5, 3, 2, 1, 1, 3]
def baseStart_8932 : Nat := 118140960795 + 8932 * 2 ^ 59
def prefixEnd_8932 : Nat := 4983230072969 + 3 ^ 40 * 8932 * 2
def baseEnd_8932 : Nat := 4586409206064287208929

theorem tailTrace_8932 : CollatzResearch.WordTrace tailWord_8932 prefixEnd_8932 4586409206064287208929 := by
  unfold tailWord_8932
  simp only [CollatzResearch.WordTrace]
  refine ⟨162888401824182154630525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 217184535765576206174033 162888401824182154630525)
  ·
    refine ⟨61083150684068307986447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162888401824182154630525 61083150684068307986447)
    ·
      refine ⟨91624726026102461979671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61083150684068307986447 91624726026102461979671)
      ·
        refine ⟨137437089039153692969507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91624726026102461979671 137437089039153692969507)
        ·
          refine ⟨206155633558730539454261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137437089039153692969507 206155633558730539454261)
          ·
            refine ⟨19327090646130988073837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 206155633558730539454261 19327090646130988073837)
            ·
              refine ⟨7247658992299120527689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19327090646130988073837 7247658992299120527689)
              ·
                refine ⟨5435744244224340395767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7247658992299120527689 5435744244224340395767)
                ·
                  refine ⟨8153616366336510593651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5435744244224340395767 8153616366336510593651)
                  ·
                    refine ⟨12230424549504765890477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8153616366336510593651 12230424549504765890477)
                    ·
                      refine ⟨4586409206064287208929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 12230424549504765890477 4586409206064287208929)
                      ·
                        rfl

theorem cell23_8932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_8932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8932 prefixEnd_8932 := by exact prefixLift 8932
  have htrace : WordTrace (prefixWord ++ tailWord_8932) baseStart_8932 baseEnd_8932 := by
    simpa [prefixWord, tailWord_8932, baseEnd_8932] using wordTrace_append hprefix tailTrace_8932
  have hstable : (prefixWord ++ tailWord_8932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8932).length < 2 ^ (prefixWord ++ tailWord_8932).sum := by decide
  have hdescent : baseEnd_8932 < baseStart_8932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8941 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_8941 : Nat := 118140960795 + 8941 * 2 ^ 59
def prefixEnd_8941 : Nat := 4983230072969 + 3 ^ 40 * 8941 * 2
def baseEnd_8941 : Nat := 4591030531954751996387

theorem tailTrace_8941 : CollatzResearch.WordTrace tailWord_8941 prefixEnd_8941 4591030531954751996387 := by
  unfold tailWord_8941
  simp only [CollatzResearch.WordTrace]
  refine ⟨326105060615758846338677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 217403373743839230892451 326105060615758846338677)
  ·
    refine ⟨30572349432727391844251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 326105060615758846338677 30572349432727391844251)
    ·
      refine ⟨45858524149091087766377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30572349432727391844251 45858524149091087766377)
      ·
        refine ⟨34393893111818315824783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45858524149091087766377 34393893111818315824783)
        ·
          refine ⟨51590839667727473737175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34393893111818315824783 51590839667727473737175)
          ·
            refine ⟨77386259501591210605763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51590839667727473737175 77386259501591210605763)
            ·
              refine ⟨116079389252386815908645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77386259501591210605763 116079389252386815908645)
              ·
                refine ⟨21764885484822527982871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116079389252386815908645 21764885484822527982871)
                ·
                  refine ⟨32647328227233791974307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21764885484822527982871 32647328227233791974307)
                  ·
                    refine ⟨48970992340850687961461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32647328227233791974307 48970992340850687961461)
                    ·
                      refine ⟨4591030531954751996387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 48970992340850687961461 4591030531954751996387)
                      ·
                        rfl

theorem cell23_8941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_8941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8941 prefixEnd_8941 := by exact prefixLift 8941
  have htrace : WordTrace (prefixWord ++ tailWord_8941) baseStart_8941 baseEnd_8941 := by
    simpa [prefixWord, tailWord_8941, baseEnd_8941] using wordTrace_append hprefix tailTrace_8941
  have hstable : (prefixWord ++ tailWord_8941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8941).length < 2 ^ (prefixWord ++ tailWord_8941).sum := by decide
  have hdescent : baseEnd_8941 < baseStart_8941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8944 : List Nat := [2, 1, 1, 1, 3, 1, 6, 8]
def baseStart_8944 : Nat := 118140960795 + 8944 * 2 ^ 59
def prefixEnd_8944 : Nat := 4983230072969 + 3 ^ 40 * 8944 * 2
def baseEnd_8944 : Nat := 170095221256231120699

theorem tailTrace_8944 : CollatzResearch.WordTrace tailWord_8944 prefixEnd_8944 170095221256231120699 := by
  unfold tailWord_8944
  simp only [CollatzResearch.WordTrace]
  refine ⟨163107239802445179348943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 217476319736593572465257 163107239802445179348943)
  ·
    refine ⟨244660859703667769023415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163107239802445179348943 244660859703667769023415)
    ·
      refine ⟨366991289555501653535123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244660859703667769023415 366991289555501653535123)
      ·
        refine ⟨550486934333252480302685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366991289555501653535123 550486934333252480302685)
        ·
          refine ⟨206432600374969680113507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 550486934333252480302685 206432600374969680113507)
          ·
            refine ⟨309648900562454520170261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206432600374969680113507 309648900562454520170261)
            ·
              refine ⟨14514792213865055632981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 309648900562454520170261 14514792213865055632981)
              ·
                refine ⟨170095221256231120699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 14514792213865055632981 170095221256231120699)
                ·
                  rfl

theorem cell23_8944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 8].length) (baseStart_8944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8944 prefixEnd_8944 := by exact prefixLift 8944
  have htrace : WordTrace (prefixWord ++ tailWord_8944) baseStart_8944 baseEnd_8944 := by
    simpa [prefixWord, tailWord_8944, baseEnd_8944] using wordTrace_append hprefix tailTrace_8944
  have hstable : (prefixWord ++ tailWord_8944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8944).length < 2 ^ (prefixWord ++ tailWord_8944).sum := by decide
  have hdescent : baseEnd_8944 < baseStart_8944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8978 : List Nat := [3, 2, 4, 1, 3, 10]
def baseStart_8978 : Nat := 118140960795 + 8978 * 2 ^ 59
def prefixEnd_8978 : Nat := 4983230072969 + 3 ^ 40 * 8978 * 2
def baseEnd_8978 : Nat := 18971314058317313719

theorem tailTrace_8978 : CollatzResearch.WordTrace tailWord_8978 prefixEnd_8978 18971314058317313719 := by
  unfold tailWord_8978
  simp only [CollatzResearch.WordTrace]
  refine ⟨81863640370428541358897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 218303040987809443623725 81863640370428541358897)
  ·
    refine ⟨61397730277821406019173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81863640370428541358897 61397730277821406019173)
    ·
      refine ⟨11512074427091513628595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61397730277821406019173 11512074427091513628595)
      ·
        refine ⟨17268111640637270442893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11512074427091513628595 17268111640637270442893)
        ·
          refine ⟨6475541865238976416085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17268111640637270442893 6475541865238976416085)
          ·
            refine ⟨18971314058317313719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6475541865238976416085 18971314058317313719)
            ·
              rfl

theorem cell23_8978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 10].length) (baseStart_8978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8978 prefixEnd_8978 := by exact prefixLift 8978
  have htrace : WordTrace (prefixWord ++ tailWord_8978) baseStart_8978 baseEnd_8978 := by
    simpa [prefixWord, tailWord_8978, baseEnd_8978] using wordTrace_append hprefix tailTrace_8978
  have hstable : (prefixWord ++ tailWord_8978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8978).length < 2 ^ (prefixWord ++ tailWord_8978).sum := by decide
  have hdescent : baseEnd_8978 < baseStart_8978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9045 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_9045 : Nat := 118140960795 + 9045 * 2 ^ 59
def prefixEnd_9045 : Nat := 4983230072969 + 3 ^ 40 * 9045 * 2
def baseEnd_9045 : Nat := 4644432520022345095909

theorem tailTrace_9045 : CollatzResearch.WordTrace tailWord_9045 prefixEnd_9045 4644432520022345095909 := by
  unfold tailWord_9045
  simp only [CollatzResearch.WordTrace]
  refine ⟨329898252238984608124589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 219932168159323072083059 329898252238984608124589)
  ·
    refine ⟨123711844589619228046721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 329898252238984608124589 123711844589619228046721)
    ·
      refine ⟨92783883442214421035041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123711844589619228046721 92783883442214421035041)
      ·
        refine ⟨69587912581660815776281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92783883442214421035041 69587912581660815776281)
        ·
          refine ⟨52190934436245611832211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69587912581660815776281 52190934436245611832211)
          ·
            refine ⟨78286401654368417748317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52190934436245611832211 78286401654368417748317)
            ·
              refine ⟨29357400620388156655619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78286401654368417748317 29357400620388156655619)
              ·
                refine ⟨44036100930582234983429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29357400620388156655619 44036100930582234983429)
                ·
                  refine ⟨8256768924484169059393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44036100930582234983429 8256768924484169059393)
                  ·
                    refine ⟨6192576693363126794545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8256768924484169059393 6192576693363126794545)
                    ·
                      refine ⟨4644432520022345095909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6192576693363126794545 4644432520022345095909)
                      ·
                        rfl

theorem cell23_9045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_9045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9045 prefixEnd_9045 := by exact prefixLift 9045
  have htrace : WordTrace (prefixWord ++ tailWord_9045) baseStart_9045 baseEnd_9045 := by
    simpa [prefixWord, tailWord_9045, baseEnd_9045] using wordTrace_append hprefix tailTrace_9045
  have hstable : (prefixWord ++ tailWord_9045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9045).length < 2 ^ (prefixWord ++ tailWord_9045).sum := by decide
  have hdescent : baseEnd_9045 < baseStart_9045 := by decide
  rcases family_descends (prefixWord ++ tailWord_9045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9081 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 1, 7]
def baseStart_9081 : Nat := 118140960795 + 9081 * 2 ^ 59
def prefixEnd_9081 : Nat := 4983230072969 + 3 ^ 40 * 9081 * 2
def baseEnd_9081 : Nat := 1554305941194734748581

theorem tailTrace_9081 : CollatzResearch.WordTrace tailWord_9081 prefixEnd_9081 1554305941194734748581 := by
  unfold tailWord_9081
  simp only [CollatzResearch.WordTrace]
  refine ⟨331211280108562756435097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 220807520072375170956731 331211280108562756435097)
  ·
    refine ⟨248408460081422067326323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 331211280108562756435097 248408460081422067326323)
    ·
      refine ⟨372612690122133100989485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248408460081422067326323 372612690122133100989485)
      ·
        refine ⟨139729758795799912871057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372612690122133100989485 139729758795799912871057)
        ·
          refine ⟨104797319096849934653293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139729758795799912871057 104797319096849934653293)
          ·
            refine ⟨39298994661318725494985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104797319096849934653293 39298994661318725494985)
            ·
              refine ⟨29474245995989044121239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39298994661318725494985 29474245995989044121239)
              ·
                refine ⟨44211368993983566181859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29474245995989044121239 44211368993983566181859)
                ·
                  refine ⟨66317053490975349272789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44211368993983566181859 66317053490975349272789)
                  ·
                    refine ⟨1554305941194734748581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 66317053490975349272789 1554305941194734748581)
                    ·
                      rfl

theorem cell23_9081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_9081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9081 prefixEnd_9081 := by exact prefixLift 9081
  have htrace : WordTrace (prefixWord ++ tailWord_9081) baseStart_9081 baseEnd_9081 := by
    simpa [prefixWord, tailWord_9081, baseEnd_9081] using wordTrace_append hprefix tailTrace_9081
  have hstable : (prefixWord ++ tailWord_9081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9081).length < 2 ^ (prefixWord ++ tailWord_9081).sum := by decide
  have hdescent : baseEnd_9081 < baseStart_9081 := by decide
  rcases family_descends (prefixWord ++ tailWord_9081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9091 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 5]
def baseStart_9091 : Nat := 118140960795 + 9091 * 2 ^ 59
def prefixEnd_9091 : Nat := 4983230072969 + 3 ^ 40 * 9091 * 2
def baseEnd_9091 : Nat := 4668052630129165120697

theorem tailTrace_9091 : CollatzResearch.WordTrace tailWord_9091 prefixEnd_9091 4668052630129165120697 := by
  unfold tailWord_9091
  simp only [CollatzResearch.WordTrace]
  refine ⟨331576010072334464299127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 221050673381556309532751 331576010072334464299127)
  ·
    refine ⟨497364015108501696448691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 331576010072334464299127 497364015108501696448691)
    ·
      refine ⟨746046022662752544673037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497364015108501696448691 746046022662752544673037)
      ·
        refine ⟨279767258498532204252389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 746046022662752544673037 279767258498532204252389)
        ·
          refine ⟨52456360968474788297323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 279767258498532204252389 52456360968474788297323)
          ·
            refine ⟨78684541452712182445985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52456360968474788297323 78684541452712182445985)
            ·
              refine ⟨59013406089534136834489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78684541452712182445985 59013406089534136834489)
              ·
                refine ⟨44260054567150602625867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59013406089534136834489 44260054567150602625867)
                ·
                  refine ⟨66390081850725903938801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44260054567150602625867 66390081850725903938801)
                  ·
                    refine ⟨49792561388044427954101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66390081850725903938801 49792561388044427954101)
                    ·
                      refine ⟨4668052630129165120697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 49792561388044427954101 4668052630129165120697)
                      ·
                        rfl

theorem cell23_9091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_9091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9091 prefixEnd_9091 := by exact prefixLift 9091
  have htrace : WordTrace (prefixWord ++ tailWord_9091) baseStart_9091 baseEnd_9091 := by
    simpa [prefixWord, tailWord_9091, baseEnd_9091] using wordTrace_append hprefix tailTrace_9091
  have hstable : (prefixWord ++ tailWord_9091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9091).length < 2 ^ (prefixWord ++ tailWord_9091).sum := by decide
  have hdescent : baseEnd_9091 < baseStart_9091 := by decide
  rcases family_descends (prefixWord ++ tailWord_9091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9098 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_9098 : Nat := 118140960795 + 9098 * 2 ^ 59
def prefixEnd_9098 : Nat := 4983230072969 + 3 ^ 40 * 9098 * 2
def baseEnd_9098 : Nat := 1557215664903545911055

theorem tailTrace_9098 : CollatzResearch.WordTrace tailWord_9098 prefixEnd_9098 1557215664903545911055 := by
  unfold tailWord_9098
  simp only [CollatzResearch.WordTrace]
  refine ⟨82957830261743664950987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 221220880697983106535965 82957830261743664950987)
  ·
    refine ⟨124436745392615497426481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82957830261743664950987 124436745392615497426481)
    ·
      refine ⟨93327559044461623069861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124436745392615497426481 93327559044461623069861)
      ·
        refine ⟨17498917320836554325599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93327559044461623069861 17498917320836554325599)
        ·
          refine ⟨26248375981254831488399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17498917320836554325599 26248375981254831488399)
          ·
            refine ⟨39372563971882247232599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26248375981254831488399 39372563971882247232599)
            ·
              refine ⟨59058845957823370848899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39372563971882247232599 59058845957823370848899)
              ·
                refine ⟨88588268936735056273349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59058845957823370848899 88588268936735056273349)
                ·
                  refine ⟨16610300425637823051253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88588268936735056273349 16610300425637823051253)
                  ·
                    refine ⟨1557215664903545911055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16610300425637823051253 1557215664903545911055)
                    ·
                      rfl

theorem cell23_9098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_9098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9098 prefixEnd_9098 := by exact prefixLift 9098
  have htrace : WordTrace (prefixWord ++ tailWord_9098) baseStart_9098 baseEnd_9098 := by
    simpa [prefixWord, tailWord_9098, baseEnd_9098] using wordTrace_append hprefix tailTrace_9098
  have hstable : (prefixWord ++ tailWord_9098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9098).length < 2 ^ (prefixWord ++ tailWord_9098).sum := by decide
  have hdescent : baseEnd_9098 < baseStart_9098 := by decide
  rcases family_descends (prefixWord ++ tailWord_9098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9108 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_9108 : Nat := 118140960795 + 9108 * 2 ^ 59
def prefixEnd_9108 : Nat := 4983230072969 + 3 ^ 40 * 9108 * 2
def baseEnd_9108 : Nat := 4676781801255598608119

theorem tailTrace_9108 : CollatzResearch.WordTrace tailWord_9108 prefixEnd_9108 4676781801255598608119 := by
  unfold tailWord_9108
  simp only [CollatzResearch.WordTrace]
  refine ⟨166098025505373183833989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 221464034007164245111985 166098025505373183833989)
  ·
    refine ⟨31143379782257471968873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166098025505373183833989 31143379782257471968873)
    ·
      refine ⟨23357534836693103976655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31143379782257471968873 23357534836693103976655)
      ·
        refine ⟨35036302255039655964983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23357534836693103976655 35036302255039655964983)
        ·
          refine ⟨52554453382559483947475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35036302255039655964983 52554453382559483947475)
          ·
            refine ⟨78831680073839225921213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52554453382559483947475 78831680073839225921213)
            ·
              refine ⟨29561880027689709720455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78831680073839225921213 29561880027689709720455)
              ·
                refine ⟨44342820041534564580683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29561880027689709720455 44342820041534564580683)
                ·
                  refine ⟨66514230062301846871025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44342820041534564580683 66514230062301846871025)
                  ·
                    refine ⟨49885672546726385153269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66514230062301846871025 49885672546726385153269)
                    ·
                      refine ⟨4676781801255598608119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 49885672546726385153269 4676781801255598608119)
                      ·
                        rfl

theorem cell23_9108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_9108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9108 prefixEnd_9108 := by exact prefixLift 9108
  have htrace : WordTrace (prefixWord ++ tailWord_9108) baseStart_9108 baseEnd_9108 := by
    simpa [prefixWord, tailWord_9108, baseEnd_9108] using wordTrace_append hprefix tailTrace_9108
  have hstable : (prefixWord ++ tailWord_9108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9108).length < 2 ^ (prefixWord ++ tailWord_9108).sum := by decide
  have hdescent : baseEnd_9108 < baseStart_9108 := by decide
  rcases family_descends (prefixWord ++ tailWord_9108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9189 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 3]
def baseStart_9189 : Nat := 118140960795 + 9189 * 2 ^ 59
def prefixEnd_9189 : Nat := 4983230072969 + 3 ^ 40 * 9189 * 2
def baseEnd_9189 : Nat := 4718373734269781695247

theorem tailTrace_9189 : CollatzResearch.WordTrace tailWord_9189 prefixEnd_9189 4718373734269781695247 := by
  unfold tailWord_9189
  simp only [CollatzResearch.WordTrace]
  refine ⟨335150363717297201366621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 223433575811531467577747 335150363717297201366621)
  ·
    refine ⟨125681386393986450512483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 335150363717297201366621 125681386393986450512483)
    ·
      refine ⟨188522079590979675768725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125681386393986450512483 188522079590979675768725)
      ·
        refine ⟨8836972480827172301659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 188522079590979675768725 8836972480827172301659)
        ·
          refine ⟨13255458721240758452489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8836972480827172301659 13255458721240758452489)
          ·
            refine ⟨9941594040930568839367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13255458721240758452489 9941594040930568839367)
            ·
              refine ⟨14912391061395853259051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9941594040930568839367 14912391061395853259051)
              ·
                refine ⟨22368586592093779888577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14912391061395853259051 22368586592093779888577)
                ·
                  refine ⟨16776439944070334916433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22368586592093779888577 16776439944070334916433)
                  ·
                    refine ⟨12582329958052751187325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16776439944070334916433 12582329958052751187325)
                    ·
                      refine ⟨4718373734269781695247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 12582329958052751187325 4718373734269781695247)
                      ·
                        rfl

theorem cell23_9189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_9189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9189 prefixEnd_9189 := by exact prefixLift 9189
  have htrace : WordTrace (prefixWord ++ tailWord_9189) baseStart_9189 baseEnd_9189 := by
    simpa [prefixWord, tailWord_9189, baseEnd_9189] using wordTrace_append hprefix tailTrace_9189
  have hstable : (prefixWord ++ tailWord_9189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9189).length < 2 ^ (prefixWord ++ tailWord_9189).sum := by decide
  have hdescent : baseEnd_9189 < baseStart_9189 := by decide
  rcases family_descends (prefixWord ++ tailWord_9189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9228 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_9228 : Nat := 118140960795 + 9228 * 2 ^ 59
def prefixEnd_9228 : Nat := 4983230072969 + 3 ^ 40 * 9228 * 2
def baseEnd_9228 : Nat := 4738399479795129107567

theorem tailTrace_9228 : CollatzResearch.WordTrace tailWord_9228 prefixEnd_9228 4738399479795129107567 := by
  unfold tailWord_9228
  simp only [CollatzResearch.WordTrace]
  refine ⟨168286405288003431018169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 224381873717337908024225 168286405288003431018169)
  ·
    refine ⟨126214803966002573263627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168286405288003431018169 126214803966002573263627)
    ·
      refine ⟨189322205949003859895441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126214803966002573263627 189322205949003859895441)
      ·
        refine ⟨141991654461752894921581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189322205949003859895441 141991654461752894921581)
        ·
          refine ⟨53246870423157335595593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141991654461752894921581 53246870423157335595593)
          ·
            refine ⟨39935152817368001696695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53246870423157335595593 39935152817368001696695)
            ·
              refine ⟨59902729226052002545043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39935152817368001696695 59902729226052002545043)
              ·
                refine ⟨89854093839078003817565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59902729226052002545043 89854093839078003817565)
                ·
                  refine ⟨33695285189654251431587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89854093839078003817565 33695285189654251431587)
                  ·
                    refine ⟨50542927784481377147381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33695285189654251431587 50542927784481377147381)
                    ·
                      refine ⟨4738399479795129107567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 50542927784481377147381 4738399479795129107567)
                      ·
                        rfl

theorem cell23_9228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_9228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9228 prefixEnd_9228 := by exact prefixLift 9228
  have htrace : WordTrace (prefixWord ++ tailWord_9228) baseStart_9228 baseEnd_9228 := by
    simpa [prefixWord, tailWord_9228, baseEnd_9228] using wordTrace_append hprefix tailTrace_9228
  have hstable : (prefixWord ++ tailWord_9228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9228).length < 2 ^ (prefixWord ++ tailWord_9228).sum := by decide
  have hdescent : baseEnd_9228 < baseStart_9228 := by decide
  rcases family_descends (prefixWord ++ tailWord_9228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9242 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2]
def baseStart_9242 : Nat := 118140960795 + 9242 * 2 ^ 59
def prefixEnd_9242 : Nat := 4983230072969 + 3 ^ 40 * 9242 * 2
def baseEnd_9242 : Nat := 4745588208958074332503

theorem tailTrace_9242 : CollatzResearch.WordTrace tailWord_9242 prefixEnd_9242 4745588208958074332503 := by
  unfold tailWord_9242
  simp only [CollatzResearch.WordTrace]
  refine ⟨84270858131321813261495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 224722288350191502030653 84270858131321813261495)
  ·
    refine ⟨126406287196982719892243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84270858131321813261495 126406287196982719892243)
    ·
      refine ⟨189609430795474079838365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126406287196982719892243 189609430795474079838365)
      ·
        refine ⟨71103536548302779939387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189609430795474079838365 71103536548302779939387)
        ·
          refine ⟨106655304822454169909081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71103536548302779939387 106655304822454169909081)
          ·
            refine ⟨79991478616840627431811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106655304822454169909081 79991478616840627431811)
            ·
              refine ⟨119987217925260941147717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79991478616840627431811 119987217925260941147717)
              ·
                refine ⟨22497603360986426465197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119987217925260941147717 22497603360986426465197)
                ·
                  refine ⟨8436601260369909924449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22497603360986426465197 8436601260369909924449)
                  ·
                    refine ⟨6327450945277432443337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8436601260369909924449 6327450945277432443337)
                    ·
                      refine ⟨4745588208958074332503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6327450945277432443337 4745588208958074332503)
                      ·
                        rfl

theorem cell23_9242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_9242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9242 prefixEnd_9242 := by exact prefixLift 9242
  have htrace : WordTrace (prefixWord ++ tailWord_9242) baseStart_9242 baseEnd_9242 := by
    simpa [prefixWord, tailWord_9242, baseEnd_9242] using wordTrace_append hprefix tailTrace_9242
  have hstable : (prefixWord ++ tailWord_9242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9242).length < 2 ^ (prefixWord ++ tailWord_9242).sum := by decide
  have hdescent : baseEnd_9242 < baseStart_9242 := by decide
  rcases family_descends (prefixWord ++ tailWord_9242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9262 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_9262 : Nat := 118140960795 + 9262 * 2 ^ 59
def prefixEnd_9262 : Nat := 4983230072969 + 3 ^ 40 * 9262 * 2
def baseEnd_9262 : Nat := 4755857822047996082411

theorem tailTrace_9262 : CollatzResearch.WordTrace tailWord_9262 prefixEnd_9262 4755857822047996082411 := by
  unfold tailWord_9262
  simp only [CollatzResearch.WordTrace]
  refine ⟨42226611556603833596755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 225208594968553779182693 42226611556603833596755)
  ·
    refine ⟨63339917334905750395133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42226611556603833596755 63339917334905750395133)
    ·
      refine ⟨23752469000589656398175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63339917334905750395133 23752469000589656398175)
      ·
        refine ⟨35628703500884484597263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23752469000589656398175 35628703500884484597263)
        ·
          refine ⟨53443055251326726895895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35628703500884484597263 53443055251326726895895)
          ·
            refine ⟨80164582876990090343843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53443055251326726895895 80164582876990090343843)
            ·
              refine ⟨120246874315485135515765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80164582876990090343843 120246874315485135515765)
              ·
                refine ⟨11273144467076731454603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120246874315485135515765 11273144467076731454603)
                ·
                  refine ⟨16909716700615097181905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11273144467076731454603 16909716700615097181905)
                  ·
                    refine ⟨12682287525461322886429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16909716700615097181905 12682287525461322886429)
                    ·
                      refine ⟨4755857822047996082411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 12682287525461322886429 4755857822047996082411)
                      ·
                        rfl

theorem cell23_9262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_9262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9262 prefixEnd_9262 := by exact prefixLift 9262
  have htrace : WordTrace (prefixWord ++ tailWord_9262) baseStart_9262 baseEnd_9262 := by
    simpa [prefixWord, tailWord_9262, baseEnd_9262] using wordTrace_append hprefix tailTrace_9262
  have hstable : (prefixWord ++ tailWord_9262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9262).length < 2 ^ (prefixWord ++ tailWord_9262).sum := by decide
  have hdescent : baseEnd_9262 < baseStart_9262 := by decide
  rcases family_descends (prefixWord ++ tailWord_9262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9286 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_9286 : Nat := 118140960795 + 9286 * 2 ^ 59
def prefixEnd_9286 : Nat := 4983230072969 + 3 ^ 40 * 9286 * 2
def baseEnd_9286 : Nat := 1589393785918634060767

theorem tailTrace_9286 : CollatzResearch.WordTrace tailWord_9286 prefixEnd_9286 1589393785918634060767 := by
  unfold tailWord_9286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10584007636433836488991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 225792162910588511765141 10584007636433836488991)
  ·
    refine ⟨15876011454650754733487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10584007636433836488991 15876011454650754733487)
    ·
      refine ⟨23814017181976132100231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15876011454650754733487 23814017181976132100231)
      ·
        refine ⟨35721025772964198150347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23814017181976132100231 35721025772964198150347)
        ·
          refine ⟨53581538659446297225521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35721025772964198150347 53581538659446297225521)
          ·
            refine ⟨40186153994584722919141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53581538659446297225521 40186153994584722919141)
            ·
              refine ⟨7534903873984635547339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40186153994584722919141 7534903873984635547339)
              ·
                refine ⟨11302355810976953321009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7534903873984635547339 11302355810976953321009)
                ·
                  refine ⟨8476766858232714990757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11302355810976953321009 8476766858232714990757)
                  ·
                    refine ⟨1589393785918634060767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8476766858232714990757 1589393785918634060767)
                    ·
                      rfl

theorem cell23_9286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_9286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9286 prefixEnd_9286 := by exact prefixLift 9286
  have htrace : WordTrace (prefixWord ++ tailWord_9286) baseStart_9286 baseEnd_9286 := by
    simpa [prefixWord, tailWord_9286, baseEnd_9286] using wordTrace_append hprefix tailTrace_9286
  have hstable : (prefixWord ++ tailWord_9286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9286).length < 2 ^ (prefixWord ++ tailWord_9286).sum := by decide
  have hdescent : baseEnd_9286 < baseStart_9286 := by decide
  rcases family_descends (prefixWord ++ tailWord_9286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9309 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_9309 : Nat := 118140960795 + 9309 * 2 ^ 59
def prefixEnd_9309 : Nat := 4983230072969 + 3 ^ 40 * 9309 * 2
def baseEnd_9309 : Nat := 4779991412809312194695

theorem tailTrace_9309 : CollatzResearch.WordTrace tailWord_9309 prefixEnd_9309 4779991412809312194695 := by
  unfold tailWord_9309
  simp only [CollatzResearch.WordTrace]
  refine ⟨339527123282557695734981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 226351415521705130489987 339527123282557695734981)
  ·
    refine ⟨63661335615479567950309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 339527123282557695734981 63661335615479567950309)
    ·
      refine ⟨11936500427902418990683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63661335615479567950309 11936500427902418990683)
      ·
        refine ⟨17904750641853628486025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11936500427902418990683 17904750641853628486025)
        ·
          refine ⟨13428562981390221364519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17904750641853628486025 13428562981390221364519)
          ·
            refine ⟨20142844472085332046779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13428562981390221364519 20142844472085332046779)
            ·
              refine ⟨30214266708127998070169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20142844472085332046779 30214266708127998070169)
              ·
                refine ⟨22660700031095998552627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30214266708127998070169 22660700031095998552627)
                ·
                  refine ⟨33991050046643997828941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22660700031095998552627 33991050046643997828941)
                  ·
                    refine ⟨12746643767491499185853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33991050046643997828941 12746643767491499185853)
                    ·
                      refine ⟨4779991412809312194695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 12746643767491499185853 4779991412809312194695)
                      ·
                        rfl

theorem cell23_9309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_9309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9309 prefixEnd_9309 := by exact prefixLift 9309
  have htrace : WordTrace (prefixWord ++ tailWord_9309) baseStart_9309 baseEnd_9309 := by
    simpa [prefixWord, tailWord_9309, baseEnd_9309] using wordTrace_append hprefix tailTrace_9309
  have hstable : (prefixWord ++ tailWord_9309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9309).length < 2 ^ (prefixWord ++ tailWord_9309).sum := by decide
  have hdescent : baseEnd_9309 < baseStart_9309 := by decide
  rcases family_descends (prefixWord ++ tailWord_9309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9345 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_9345 : Nat := 118140960795 + 9345 * 2 ^ 59
def prefixEnd_9345 : Nat := 4983230072969 + 3 ^ 40 * 9345 * 2
def baseEnd_9345 : Nat := 4798476716371171344529

theorem tailTrace_9345 : CollatzResearch.WordTrace tailWord_9345 prefixEnd_9345 4798476716371171344529 := by
  unfold tailWord_9345
  simp only [CollatzResearch.WordTrace]
  refine ⟨340840151152135844045489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 227226767434757229363659 340840151152135844045489)
  ·
    refine ⟨255630113364101883034117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 340840151152135844045489 255630113364101883034117)
    ·
      refine ⟨47930646255769103068897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255630113364101883034117 47930646255769103068897)
      ·
        refine ⟨35947984691826827301673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47930646255769103068897 35947984691826827301673)
        ·
          refine ⟨26960988518870120476255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35947984691826827301673 26960988518870120476255)
          ·
            refine ⟨40441482778305180714383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26960988518870120476255 40441482778305180714383)
            ·
              refine ⟨60662224167457771071575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40441482778305180714383 60662224167457771071575)
              ·
                refine ⟨90993336251186656607363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60662224167457771071575 90993336251186656607363)
                ·
                  refine ⟨136490004376779984911045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90993336251186656607363 136490004376779984911045)
                  ·
                    refine ⟨25591875820646247170821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136490004376779984911045 25591875820646247170821)
                    ·
                      refine ⟨4798476716371171344529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 25591875820646247170821 4798476716371171344529)
                      ·
                        rfl

theorem cell23_9345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_9345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9345 prefixEnd_9345 := by exact prefixLift 9345
  have htrace : WordTrace (prefixWord ++ tailWord_9345) baseStart_9345 baseEnd_9345 := by
    simpa [prefixWord, tailWord_9345, baseEnd_9345] using wordTrace_append hprefix tailTrace_9345
  have hstable : (prefixWord ++ tailWord_9345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9345).length < 2 ^ (prefixWord ++ tailWord_9345).sum := by decide
  have hdescent : baseEnd_9345 < baseStart_9345 := by decide
  rcases family_descends (prefixWord ++ tailWord_9345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9349 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 1, 4, 2]
def baseStart_9349 : Nat := 118140960795 + 9349 * 2 ^ 59
def prefixEnd_9349 : Nat := 4983230072969 + 3 ^ 40 * 9349 * 2
def baseEnd_9349 : Nat := 4800530638989155694511

theorem tailTrace_9349 : CollatzResearch.WordTrace tailWord_9349 prefixEnd_9349 4800530638989155694511 := by
  unfold tailWord_9349
  simp only [CollatzResearch.WordTrace]
  refine ⟨340986043137644527191101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 227324028758429684794067 340986043137644527191101)
  ·
    refine ⟨127869766176616697696663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 340986043137644527191101 127869766176616697696663)
    ·
      refine ⟨191804649264925046544995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127869766176616697696663 191804649264925046544995)
      ·
        refine ⟨287706973897387569817493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191804649264925046544995 287706973897387569817493)
        ·
          refine ⟨13486264401440042335195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 287706973897387569817493 13486264401440042335195)
          ·
            refine ⟨20229396602160063502793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13486264401440042335195 20229396602160063502793)
            ·
              refine ⟨15172047451620047627095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20229396602160063502793 15172047451620047627095)
              ·
                refine ⟨22758071177430071440643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15172047451620047627095 22758071177430071440643)
                ·
                  refine ⟨34137106766145107160965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22758071177430071440643 34137106766145107160965)
                  ·
                    refine ⟨6400707518652207592681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34137106766145107160965 6400707518652207592681)
                    ·
                      refine ⟨4800530638989155694511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6400707518652207592681 4800530638989155694511)
                      ·
                        rfl

theorem cell23_9349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_9349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9349 prefixEnd_9349 := by exact prefixLift 9349
  have htrace : WordTrace (prefixWord ++ tailWord_9349) baseStart_9349 baseEnd_9349 := by
    simpa [prefixWord, tailWord_9349, baseEnd_9349] using wordTrace_append hprefix tailTrace_9349
  have hstable : (prefixWord ++ tailWord_9349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9349).length < 2 ^ (prefixWord ++ tailWord_9349).sum := by decide
  have hdescent : baseEnd_9349 < baseStart_9349 := by decide
  rcases family_descends (prefixWord ++ tailWord_9349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9372 : List Nat := [2, 2, 3, 2, 1, 2, 1, 5, 5]
def baseStart_9372 : Nat := 118140960795 + 9372 * 2 ^ 59
def prefixEnd_9372 : Nat := 4983230072969 + 3 ^ 40 * 9372 * 2
def baseEnd_9372 : Nat := 534704521560285078545

theorem tailTrace_9372 : CollatzResearch.WordTrace tailWord_9372 prefixEnd_9372 534704521560285078545 := by
  unfold tailWord_9372
  simp only [CollatzResearch.WordTrace]
  refine ⟨170912461027159727639185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 227883281369546303518913 170912461027159727639185)
  ·
    refine ⟨128184345770369795729389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170912461027159727639185 128184345770369795729389)
    ·
      refine ⟨48069129663888673398521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128184345770369795729389 48069129663888673398521)
      ·
        refine ⟨36051847247916505048891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48069129663888673398521 36051847247916505048891)
        ·
          refine ⟨54077770871874757573337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36051847247916505048891 54077770871874757573337)
          ·
            refine ⟨40558328153906068180003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54077770871874757573337 40558328153906068180003)
            ·
              refine ⟨60837492230859102270005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40558328153906068180003 60837492230859102270005)
              ·
                refine ⟨5703514896643040837813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60837492230859102270005 5703514896643040837813)
                ·
                  refine ⟨534704521560285078545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5703514896643040837813 534704521560285078545)
                  ·
                    rfl

theorem cell23_9372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_9372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9372 prefixEnd_9372 := by exact prefixLift 9372
  have htrace : WordTrace (prefixWord ++ tailWord_9372) baseStart_9372 baseEnd_9372 := by
    simpa [prefixWord, tailWord_9372, baseEnd_9372] using wordTrace_append hprefix tailTrace_9372
  have hstable : (prefixWord ++ tailWord_9372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9372).length < 2 ^ (prefixWord ++ tailWord_9372).sum := by decide
  have hdescent : baseEnd_9372 < baseStart_9372 := by decide
  rcases family_descends (prefixWord ++ tailWord_9372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9383 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_9383 : Nat := 118140960795 + 9383 * 2 ^ 59
def prefixEnd_9383 : Nat := 4983230072969 + 3 ^ 40 * 9383 * 2
def baseEnd_9383 : Nat := 4817988981242022669355

theorem tailTrace_9383 : CollatzResearch.WordTrace tailWord_9383 prefixEnd_9383 4817988981242022669355 := by
  unfold tailWord_9383
  simp only [CollatzResearch.WordTrace]
  refine ⟨342226125014468333928803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 228150750009645555952535 342226125014468333928803)
  ·
    refine ⟨513339187521702500893205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342226125014468333928803 513339187521702500893205)
    ·
      refine ⟨24062774415079804729369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 513339187521702500893205 24062774415079804729369)
      ·
        refine ⟨18047080811309853547027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24062774415079804729369 18047080811309853547027)
        ·
          refine ⟨27070621216964780320541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18047080811309853547027 27070621216964780320541)
          ·
            refine ⟨10151482956361792620203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27070621216964780320541 10151482956361792620203)
            ·
              refine ⟨15227224434542688930305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10151482956361792620203 15227224434542688930305)
              ·
                refine ⟨11420418325907016697729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15227224434542688930305 11420418325907016697729)
                ·
                  refine ⟨8565313744430262523297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11420418325907016697729 8565313744430262523297)
                  ·
                    refine ⟨6423985308322696892473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8565313744430262523297 6423985308322696892473)
                    ·
                      refine ⟨4817988981242022669355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6423985308322696892473 4817988981242022669355)
                      ·
                        rfl

theorem cell23_9383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_9383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9383 prefixEnd_9383 := by exact prefixLift 9383
  have htrace : WordTrace (prefixWord ++ tailWord_9383) baseStart_9383 baseEnd_9383 := by
    simpa [prefixWord, tailWord_9383, baseEnd_9383] using wordTrace_append hprefix tailTrace_9383
  have hstable : (prefixWord ++ tailWord_9383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9383).length < 2 ^ (prefixWord ++ tailWord_9383).sum := by decide
  have hdescent : baseEnd_9383 < baseStart_9383 := by decide
  rcases family_descends (prefixWord ++ tailWord_9383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9405 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_9405 : Nat := 118140960795 + 9405 * 2 ^ 59
def prefixEnd_9405 : Nat := 4983230072969 + 3 ^ 40 * 9405 * 2
def baseEnd_9405 : Nat := 4829285555640936594253

theorem tailTrace_9405 : CollatzResearch.WordTrace tailWord_9405 prefixEnd_9405 4829285555640936594253 := by
  unfold tailWord_9405
  simp only [CollatzResearch.WordTrace]
  refine ⟨343028530934766091229669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 228685687289844060819779 343028530934766091229669)
  ·
    refine ⟨64317849550268642105563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 343028530934766091229669 64317849550268642105563)
    ·
      refine ⟨96476774325402963158345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64317849550268642105563 96476774325402963158345)
      ·
        refine ⟨72357580744052222368759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96476774325402963158345 72357580744052222368759)
        ·
          refine ⟨108536371116078333553139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72357580744052222368759 108536371116078333553139)
          ·
            refine ⟨162804556674117500329709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108536371116078333553139 162804556674117500329709)
            ·
              refine ⟨61051708752794062623641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162804556674117500329709 61051708752794062623641)
              ·
                refine ⟨45788781564595546967731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61051708752794062623641 45788781564595546967731)
                ·
                  refine ⟨68683172346893320451597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45788781564595546967731 68683172346893320451597)
                  ·
                    refine ⟨25756189630084995169349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68683172346893320451597 25756189630084995169349)
                    ·
                      refine ⟨4829285555640936594253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 25756189630084995169349 4829285555640936594253)
                      ·
                        rfl

theorem cell23_9405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_9405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9405 prefixEnd_9405 := by exact prefixLift 9405
  have htrace : WordTrace (prefixWord ++ tailWord_9405) baseStart_9405 baseEnd_9405 := by
    simpa [prefixWord, tailWord_9405, baseEnd_9405] using wordTrace_append hprefix tailTrace_9405
  have hstable : (prefixWord ++ tailWord_9405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9405).length < 2 ^ (prefixWord ++ tailWord_9405).sum := by decide
  have hdescent : baseEnd_9405 < baseStart_9405 := by decide
  rcases family_descends (prefixWord ++ tailWord_9405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9472 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 5, 1, 3]
def baseStart_9472 : Nat := 118140960795 + 9472 * 2 ^ 59
def prefixEnd_9472 : Nat := 4983230072969 + 3 ^ 40 * 9472 * 2
def baseEnd_9472 : Nat := 4863688759492174456445

theorem tailTrace_9472 : CollatzResearch.WordTrace tailWord_9472 prefixEnd_9472 4863688759492174456445 := by
  unfold tailWord_9472
  simp only [CollatzResearch.WordTrace]
  refine ⟨172736110846018266959335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 230314814461357689279113 172736110846018266959335)
  ·
    refine ⟨259104166269027400439003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172736110846018266959335 259104166269027400439003)
    ·
      refine ⟨388656249403541100658505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259104166269027400439003 388656249403541100658505)
      ·
        refine ⟨291492187052655825493879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388656249403541100658505 291492187052655825493879)
        ·
          refine ⟨437238280578983738240819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291492187052655825493879 437238280578983738240819)
          ·
            refine ⟨655857420868475607361229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437238280578983738240819 655857420868475607361229)
            ·
              refine ⟨245946532825678352760461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 655857420868475607361229 245946532825678352760461)
              ·
                refine ⟨92229949809629382285173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245946532825678352760461 92229949809629382285173)
                ·
                  refine ⟨8646557794652754589235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92229949809629382285173 8646557794652754589235)
                  ·
                    refine ⟨12969836691979131883853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8646557794652754589235 12969836691979131883853)
                    ·
                      refine ⟨4863688759492174456445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 12969836691979131883853 4863688759492174456445)
                      ·
                        rfl

theorem cell23_9472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_9472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9472 prefixEnd_9472 := by exact prefixLift 9472
  have htrace : WordTrace (prefixWord ++ tailWord_9472) baseStart_9472 baseEnd_9472 := by
    simpa [prefixWord, tailWord_9472, baseEnd_9472] using wordTrace_append hprefix tailTrace_9472
  have hstable : (prefixWord ++ tailWord_9472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9472).length < 2 ^ (prefixWord ++ tailWord_9472).sum := by decide
  have hdescent : baseEnd_9472 < baseStart_9472 := by decide
  rcases family_descends (prefixWord ++ tailWord_9472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9505 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 5, 6]
def baseStart_9505 : Nat := 118140960795 + 9505 * 2 ^ 59
def prefixEnd_9505 : Nat := 4983230072969 + 3 ^ 40 * 9505 * 2
def baseEnd_9505 : Nat := 1626877873696848447931

theorem tailTrace_9505 : CollatzResearch.WordTrace tailWord_9505 prefixEnd_9505 1626877873696848447931 := by
  unfold tailWord_9505
  simp only [CollatzResearch.WordTrace]
  refine ⟨346675830572483169869969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 231117220381655446579979 346675830572483169869969)
  ·
    refine ⟨260006872929362377402477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 346675830572483169869969 260006872929362377402477)
    ·
      refine ⟨97502577348510891525929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260006872929362377402477 97502577348510891525929)
      ·
        refine ⟨73126933011383168644447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97502577348510891525929 73126933011383168644447)
        ·
          refine ⟨109690399517074752966671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73126933011383168644447 109690399517074752966671)
          ·
            refine ⟨164535599275612129450007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109690399517074752966671 164535599275612129450007)
            ·
              refine ⟨246803398913418194175011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164535599275612129450007 246803398913418194175011)
              ·
                refine ⟨370205098370127291262517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246803398913418194175011 370205098370127291262517)
                ·
                  refine ⟨34706727972199433555861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 370205098370127291262517 34706727972199433555861)
                  ·
                    refine ⟨1626877873696848447931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34706727972199433555861 1626877873696848447931)
                    ·
                      rfl

theorem cell23_9505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_9505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9505 prefixEnd_9505 := by exact prefixLift 9505
  have htrace : WordTrace (prefixWord ++ tailWord_9505) baseStart_9505 baseEnd_9505 := by
    simpa [prefixWord, tailWord_9505, baseEnd_9505] using wordTrace_append hprefix tailTrace_9505
  have hstable : (prefixWord ++ tailWord_9505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9505).length < 2 ^ (prefixWord ++ tailWord_9505).sum := by decide
  have hdescent : baseEnd_9505 < baseStart_9505 := by decide
  rcases family_descends (prefixWord ++ tailWord_9505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9522 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_9522 : Nat := 118140960795 + 9522 * 2 ^ 59
def prefixEnd_9522 : Nat := 4983230072969 + 3 ^ 40 * 9522 * 2
def baseEnd_9522 : Nat := 1629787597405659610405

theorem tailTrace_9522 : CollatzResearch.WordTrace tailWord_9522 prefixEnd_9522 1629787597405659610405 := by
  unfold tailWord_9522
  simp only [CollatzResearch.WordTrace]
  refine ⟨86823967877723768309705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 231530581007263382159213 86823967877723768309705)
  ·
    refine ⟨65117975908292826232279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86823967877723768309705 65117975908292826232279)
    ·
      refine ⟨97676963862439239348419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65117975908292826232279 97676963862439239348419)
      ·
        refine ⟨146515445793658859022629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97676963862439239348419 146515445793658859022629)
        ·
          refine ⟨27471646086311036066743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146515445793658859022629 27471646086311036066743)
          ·
            refine ⟨41207469129466554100115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27471646086311036066743 41207469129466554100115)
            ·
              refine ⟨61811203694199831150173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41207469129466554100115 61811203694199831150173)
              ·
                refine ⟨23179201385324936681315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61811203694199831150173 23179201385324936681315)
                ·
                  refine ⟨34768802077987405021973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23179201385324936681315 34768802077987405021973)
                  ·
                    refine ⟨1629787597405659610405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34768802077987405021973 1629787597405659610405)
                    ·
                      rfl

theorem cell23_9522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_9522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9522 prefixEnd_9522 := by exact prefixLift 9522
  have htrace : WordTrace (prefixWord ++ tailWord_9522) baseStart_9522 baseEnd_9522 := by
    simpa [prefixWord, tailWord_9522, baseEnd_9522] using wordTrace_append hprefix tailTrace_9522
  have hstable : (prefixWord ++ tailWord_9522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9522).length < 2 ^ (prefixWord ++ tailWord_9522).sum := by decide
  have hdescent : baseEnd_9522 < baseStart_9522 := by decide
  rcases family_descends (prefixWord ++ tailWord_9522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9540 : List Nat := [2, 3, 4, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_9540 : Nat := 118140960795 + 9540 * 2 ^ 59
def prefixEnd_9540 : Nat := 4983230072969 + 3 ^ 40 * 9540 * 2
def baseEnd_9540 : Nat := 4898605443997908406133

theorem tailTrace_9540 : CollatzResearch.WordTrace tailWord_9540 prefixEnd_9540 4898605443997908406133 := by
  unfold tailWord_9540
  simp only [CollatzResearch.WordTrace]
  refine ⟨173976192722842073697037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 231968256963789431596049 173976192722842073697037)
  ·
    refine ⟨65241072271065777636389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173976192722842073697037 65241072271065777636389)
    ·
      refine ⟨12232701050824833306823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65241072271065777636389 12232701050824833306823)
      ·
        refine ⟨18349051576237249960235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12232701050824833306823 18349051576237249960235)
        ·
          refine ⟨27523577364355874940353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18349051576237249960235 27523577364355874940353)
          ·
            refine ⟨20642683023266906205265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27523577364355874940353 20642683023266906205265)
            ·
              refine ⟨15482012267450179653949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20642683023266906205265 15482012267450179653949)
              ·
                refine ⟨5805754600293817370231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15482012267450179653949 5805754600293817370231)
                ·
                  refine ⟨8708631900440726055347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5805754600293817370231 8708631900440726055347)
                  ·
                    refine ⟨13062947850661089083021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8708631900440726055347 13062947850661089083021)
                    ·
                      refine ⟨4898605443997908406133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 13062947850661089083021 4898605443997908406133)
                      ·
                        rfl

theorem cell23_9540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_9540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9540 prefixEnd_9540 := by exact prefixLift 9540
  have htrace : WordTrace (prefixWord ++ tailWord_9540) baseStart_9540 baseEnd_9540 := by
    simpa [prefixWord, tailWord_9540, baseEnd_9540] using wordTrace_append hprefix tailTrace_9540
  have hstable : (prefixWord ++ tailWord_9540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9540).length < 2 ^ (prefixWord ++ tailWord_9540).sum := by decide
  have hdescent : baseEnd_9540 < baseStart_9540 := by decide
  rcases family_descends (prefixWord ++ tailWord_9540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9562 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_9562 : Nat := 118140960795 + 9562 * 2 ^ 59
def prefixEnd_9562 : Nat := 4983230072969 + 3 ^ 40 * 9562 * 2
def baseEnd_9562 : Nat := 4909902018396822331031

theorem tailTrace_9562 : CollatzResearch.WordTrace tailWord_9562 prefixEnd_9562 4909902018396822331031 := by
  unfold tailWord_9562
  simp only [CollatzResearch.WordTrace]
  refine ⟨87188697841495476173735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 232503194243987936463293 87188697841495476173735)
  ·
    refine ⟨130783046762243214260603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87188697841495476173735 130783046762243214260603)
    ·
      refine ⟨196174570143364821390905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130783046762243214260603 196174570143364821390905)
      ·
        refine ⟨147130927607523616043179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196174570143364821390905 147130927607523616043179)
        ·
          refine ⟨220696391411285424064769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147130927607523616043179 220696391411285424064769)
          ·
            refine ⟨165522293558464068048577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220696391411285424064769 165522293558464068048577)
            ·
              refine ⟨124141720168848051036433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165522293558464068048577 124141720168848051036433)
              ·
                refine ⟨93106290126636038277325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124141720168848051036433 93106290126636038277325)
                ·
                  refine ⟨34914858797488514353997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93106290126636038277325 34914858797488514353997)
                  ·
                    refine ⟨13093072049058192882749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34914858797488514353997 13093072049058192882749)
                    ·
                      refine ⟨4909902018396822331031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 13093072049058192882749 4909902018396822331031)
                      ·
                        rfl

theorem cell23_9562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_9562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9562 prefixEnd_9562 := by exact prefixLift 9562
  have htrace : WordTrace (prefixWord ++ tailWord_9562) baseStart_9562 baseEnd_9562 := by
    simpa [prefixWord, tailWord_9562, baseEnd_9562] using wordTrace_append hprefix tailTrace_9562
  have hstable : (prefixWord ++ tailWord_9562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9562).length < 2 ^ (prefixWord ++ tailWord_9562).sum := by decide
  have hdescent : baseEnd_9562 < baseStart_9562 := by decide
  rcases family_descends (prefixWord ++ tailWord_9562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9576 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_9576 : Nat := 118140960795 + 9576 * 2 ^ 59
def prefixEnd_9576 : Nat := 4983230072969 + 3 ^ 40 * 9576 * 2
def baseEnd_9576 : Nat := 4917090747559767555967

theorem tailTrace_9576 : CollatzResearch.WordTrace tailWord_9576 prefixEnd_9576 4917090747559767555967 := by
  unfold tailWord_9576
  simp only [CollatzResearch.WordTrace]
  refine ⟨174632706657631147852291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 232843608876841530469721 174632706657631147852291)
  ·
    refine ⟨261949059986446721778437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174632706657631147852291 261949059986446721778437)
    ·
      refine ⟨49115448747458760333457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261949059986446721778437 49115448747458760333457)
      ·
        refine ⟨36836586560594070250093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49115448747458760333457 36836586560594070250093)
        ·
          refine ⟨13813719960222776343785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36836586560594070250093 13813719960222776343785)
          ·
            refine ⟨10360289970167082257839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13813719960222776343785 10360289970167082257839)
            ·
              refine ⟨15540434955250623386759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10360289970167082257839 15540434955250623386759)
              ·
                refine ⟨23310652432875935080139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15540434955250623386759 23310652432875935080139)
                ·
                  refine ⟨34965978649313902620209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23310652432875935080139 34965978649313902620209)
                  ·
                    refine ⟨26224483986985426965157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34965978649313902620209 26224483986985426965157)
                    ·
                      refine ⟨4917090747559767555967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 26224483986985426965157 4917090747559767555967)
                      ·
                        rfl

theorem cell23_9576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_9576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9576 prefixEnd_9576 := by exact prefixLift 9576
  have htrace : WordTrace (prefixWord ++ tailWord_9576) baseStart_9576 baseEnd_9576 := by
    simpa [prefixWord, tailWord_9576, baseEnd_9576] using wordTrace_append hprefix tailTrace_9576
  have hstable : (prefixWord ++ tailWord_9576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9576).length < 2 ^ (prefixWord ++ tailWord_9576).sum := by decide
  have hdescent : baseEnd_9576 < baseStart_9576 := by decide
  rcases family_descends (prefixWord ++ tailWord_9576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9630 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_9630 : Nat := 118140960795 + 9630 * 2 ^ 59
def prefixEnd_9630 : Nat := 4983230072969 + 3 ^ 40 * 9630 * 2
def baseEnd_9630 : Nat := 4944818702902556280719

theorem tailTrace_9630 : CollatzResearch.WordTrace tailWord_9630 prefixEnd_9630 4944818702902556280719 := by
  unfold tailWord_9630
  simp only [CollatzResearch.WordTrace]
  refine ⟨43904369389953689771293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 234156636746419678780229 43904369389953689771293)
  ·
    refine ⟨16464138521232633664235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43904369389953689771293 16464138521232633664235)
    ·
      refine ⟨24696207781848950496353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16464138521232633664235 24696207781848950496353)
      ·
        refine ⟨18522155836386712872265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24696207781848950496353 18522155836386712872265)
        ·
          refine ⟨13891616877290034654199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18522155836386712872265 13891616877290034654199)
          ·
            refine ⟨20837425315935051981299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13891616877290034654199 20837425315935051981299)
            ·
              refine ⟨31256137973902577971949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20837425315935051981299 31256137973902577971949)
              ·
                refine ⟨11721051740213466739481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31256137973902577971949 11721051740213466739481)
                ·
                  refine ⟨8790788805160100054611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11721051740213466739481 8790788805160100054611)
                  ·
                    refine ⟨13186183207740150081917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8790788805160100054611 13186183207740150081917)
                    ·
                      refine ⟨4944818702902556280719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 13186183207740150081917 4944818702902556280719)
                      ·
                        rfl

theorem cell23_9630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_9630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9630 prefixEnd_9630 := by exact prefixLift 9630
  have htrace : WordTrace (prefixWord ++ tailWord_9630) baseStart_9630 baseEnd_9630 := by
    simpa [prefixWord, tailWord_9630, baseEnd_9630] using wordTrace_append hprefix tailTrace_9630
  have hstable : (prefixWord ++ tailWord_9630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9630).length < 2 ^ (prefixWord ++ tailWord_9630).sum := by decide
  have hdescent : baseEnd_9630 < baseStart_9630 := by decide
  rcases family_descends (prefixWord ++ tailWord_9630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9632 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_9632 : Nat := 118140960795 + 9632 * 2 ^ 59
def prefixEnd_9632 : Nat := 4983230072969 + 3 ^ 40 * 9632 * 2
def baseEnd_9632 : Nat := 4945845664211548455709

theorem tailTrace_9632 : CollatzResearch.WordTrace tailWord_9632 prefixEnd_9632 4945845664211548455709 := by
  unfold tailWord_9632
  simp only [CollatzResearch.WordTrace]
  refine ⟨175653950556191929871575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 234205267408255906495433 175653950556191929871575)
  ·
    refine ⟨263480925834287894807363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175653950556191929871575 263480925834287894807363)
    ·
      refine ⟨395221388751431842211045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263480925834287894807363 395221388751431842211045)
      ·
        refine ⟨74104010390893470414571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 395221388751431842211045 74104010390893470414571)
        ·
          refine ⟨111156015586340205621857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74104010390893470414571 111156015586340205621857)
          ·
            refine ⟨83367011689755154216393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111156015586340205621857 83367011689755154216393)
            ·
              refine ⟨62525258767316365662295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83367011689755154216393 62525258767316365662295)
              ·
                refine ⟨93787888150974548493443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62525258767316365662295 93787888150974548493443)
                ·
                  refine ⟨140681832226461822740165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93787888150974548493443 140681832226461822740165)
                  ·
                    refine ⟨26377843542461591763781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140681832226461822740165 26377843542461591763781)
                    ·
                      refine ⟨4945845664211548455709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 26377843542461591763781 4945845664211548455709)
                      ·
                        rfl

theorem cell23_9632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_9632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9632 prefixEnd_9632 := by exact prefixLift 9632
  have htrace : WordTrace (prefixWord ++ tailWord_9632) baseStart_9632 baseEnd_9632 := by
    simpa [prefixWord, tailWord_9632, baseEnd_9632] using wordTrace_append hprefix tailTrace_9632
  have hstable : (prefixWord ++ tailWord_9632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9632).length < 2 ^ (prefixWord ++ tailWord_9632).sum := by decide
  have hdescent : baseEnd_9632 < baseStart_9632 := by decide
  rcases family_descends (prefixWord ++ tailWord_9632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9676 : List Nat := [2, 2, 1, 4, 2, 2, 1, 4, 5]
def baseStart_9676 : Nat := 118140960795 + 9676 * 2 ^ 59
def prefixEnd_9676 : Nat := 4983230072969 + 3 ^ 40 * 9676 * 2
def baseEnd_9676 : Nat := 552048757001041811723

theorem tailTrace_9676 : CollatzResearch.WordTrace tailWord_9676 prefixEnd_9676 552048757001041811723 := by
  unfold tailWord_9676
  simp only [CollatzResearch.WordTrace]
  refine ⟨176456356476489687172441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 235275141968652916229921 176456356476489687172441)
  ·
    refine ⟨132342267357367265379331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176456356476489687172441 132342267357367265379331)
    ·
      refine ⟨198513401036050898068997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132342267357367265379331 198513401036050898068997)
      ·
        refine ⟨37221262694259543387937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198513401036050898068997 37221262694259543387937)
        ·
          refine ⟨27915947020694657540953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37221262694259543387937 27915947020694657540953)
          ·
            refine ⟨20936960265520993155715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27915947020694657540953 20936960265520993155715)
            ·
              refine ⟨31405440398281489733573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20936960265520993155715 31405440398281489733573)
              ·
                refine ⟨5888520074677779325045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31405440398281489733573 5888520074677779325045)
                ·
                  refine ⟨552048757001041811723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5888520074677779325045 552048757001041811723)
                  ·
                    rfl

theorem cell23_9676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_9676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9676 prefixEnd_9676 := by exact prefixLift 9676
  have htrace : WordTrace (prefixWord ++ tailWord_9676) baseStart_9676 baseEnd_9676 := by
    simpa [prefixWord, tailWord_9676, baseEnd_9676] using wordTrace_append hprefix tailTrace_9676
  have hstable : (prefixWord ++ tailWord_9676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9676).length < 2 ^ (prefixWord ++ tailWord_9676).sum := by decide
  have hdescent : baseEnd_9676 < baseStart_9676 := by decide
  rcases family_descends (prefixWord ++ tailWord_9676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9679 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 2, 5, 2]
def baseStart_9679 : Nat := 118140960795 + 9679 * 2 ^ 59
def prefixEnd_9679 : Nat := 4983230072969 + 3 ^ 40 * 9679 * 2
def baseEnd_9679 : Nat := 4969979254972864567993

theorem tailTrace_9679 : CollatzResearch.WordTrace tailWord_9679 prefixEnd_9679 4969979254972864567993 := by
  unfold tailWord_9679
  simp only [CollatzResearch.WordTrace]
  refine ⟨353022131942110886704091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 235348087961407257802727 353022131942110886704091)
  ·
    refine ⟨529533197913166330056137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353022131942110886704091 529533197913166330056137)
    ·
      refine ⟨397149898434874747542103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 529533197913166330056137 397149898434874747542103)
      ·
        refine ⟨595724847652312121313155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397149898434874747542103 595724847652312121313155)
        ·
          refine ⟨893587271478468181969733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595724847652312121313155 893587271478468181969733)
          ·
            refine ⟨167547613402212784119325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 893587271478468181969733 167547613402212784119325)
            ·
              refine ⟨62830355025829794044747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167547613402212784119325 62830355025829794044747)
              ·
                refine ⟨94245532538744691067121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62830355025829794044747 94245532538744691067121)
                ·
                  refine ⟨70684149404058518300341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94245532538744691067121 70684149404058518300341)
                  ·
                    refine ⟨6626639006630486090657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70684149404058518300341 6626639006630486090657)
                    ·
                      refine ⟨4969979254972864567993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6626639006630486090657 4969979254972864567993)
                      ·
                        rfl

theorem cell23_9679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 5, 2].length) (baseStart_9679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9679 prefixEnd_9679 := by exact prefixLift 9679
  have htrace : WordTrace (prefixWord ++ tailWord_9679) baseStart_9679 baseEnd_9679 := by
    simpa [prefixWord, tailWord_9679, baseEnd_9679] using wordTrace_append hprefix tailTrace_9679
  have hstable : (prefixWord ++ tailWord_9679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9679).length < 2 ^ (prefixWord ++ tailWord_9679).sum := by decide
  have hdescent : baseEnd_9679 < baseStart_9679 := by decide
  rcases family_descends (prefixWord ++ tailWord_9679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9686 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_9686 : Nat := 118140960795 + 9686 * 2 ^ 59
def prefixEnd_9686 : Nat := 4983230072969 + 3 ^ 40 * 9686 * 2
def baseEnd_9686 : Nat := 4973573619554337180461

theorem tailTrace_9686 : CollatzResearch.WordTrace tailWord_9686 prefixEnd_9686 4973573619554337180461 := by
  unfold tailWord_9686
  simp only [CollatzResearch.WordTrace]
  refine ⟨22079840182296942638057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 235518295277834054805941 22079840182296942638057)
  ·
    refine ⟨16559880136722706978543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22079840182296942638057 16559880136722706978543)
    ·
      refine ⟨24839820205084060467815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16559880136722706978543 24839820205084060467815)
      ·
        refine ⟨37259730307626090701723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24839820205084060467815 37259730307626090701723)
        ·
          refine ⟨55889595461439136052585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37259730307626090701723 55889595461439136052585)
          ·
            refine ⟨41917196596079352039439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55889595461439136052585 41917196596079352039439)
            ·
              refine ⟨62875794894119028059159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41917196596079352039439 62875794894119028059159)
              ·
                refine ⟨94313692341178542088739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62875794894119028059159 94313692341178542088739)
                ·
                  refine ⟨141470538511767813133109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94313692341178542088739 141470538511767813133109)
                  ·
                    refine ⟨13262862985478232481229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 141470538511767813133109 13262862985478232481229)
                    ·
                      refine ⟨4973573619554337180461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 13262862985478232481229 4973573619554337180461)
                      ·
                        rfl

theorem cell23_9686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_9686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9686 prefixEnd_9686 := by exact prefixLift 9686
  have htrace : WordTrace (prefixWord ++ tailWord_9686) baseStart_9686 baseEnd_9686 := by
    simpa [prefixWord, tailWord_9686, baseEnd_9686] using wordTrace_append hprefix tailTrace_9686
  have hstable : (prefixWord ++ tailWord_9686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9686).length < 2 ^ (prefixWord ++ tailWord_9686).sum := by decide
  have hdescent : baseEnd_9686 < baseStart_9686 := by decide
  rcases family_descends (prefixWord ++ tailWord_9686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9722 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_9722 : Nat := 118140960795 + 9722 * 2 ^ 59
def prefixEnd_9722 : Nat := 4983230072969 + 3 ^ 40 * 9722 * 2
def baseEnd_9722 : Nat := 4992058923116196330295

theorem tailTrace_9722 : CollatzResearch.WordTrace tailWord_9722 prefixEnd_9722 4992058923116196330295 := by
  unfold tailWord_9722
  simp only [CollatzResearch.WordTrace]
  refine ⟨88647617696582307629855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 236393647190886153679613 88647617696582307629855)
  ·
    refine ⟨132971426544873461444783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88647617696582307629855 132971426544873461444783)
    ·
      refine ⟨199457139817310192167175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132971426544873461444783 199457139817310192167175)
      ·
        refine ⟨299185709725965288250763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199457139817310192167175 299185709725965288250763)
        ·
          refine ⟨448778564588947932376145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299185709725965288250763 448778564588947932376145)
          ·
            refine ⟨336583923441710949282109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448778564588947932376145 336583923441710949282109)
            ·
              refine ⟨126218971290641605980791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336583923441710949282109 126218971290641605980791)
              ·
                refine ⟨189328456935962408971187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126218971290641605980791 189328456935962408971187)
                ·
                  refine ⟨283992685403943613456781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189328456935962408971187 283992685403943613456781)
                  ·
                    refine ⟨106497257026478855046293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 283992685403943613456781 106497257026478855046293)
                    ·
                      refine ⟨4992058923116196330295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 106497257026478855046293 4992058923116196330295)
                      ·
                        rfl

theorem cell23_9722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_9722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9722 prefixEnd_9722 := by exact prefixLift 9722
  have htrace : WordTrace (prefixWord ++ tailWord_9722) baseStart_9722 baseEnd_9722 := by
    simpa [prefixWord, tailWord_9722, baseEnd_9722] using wordTrace_append hprefix tailTrace_9722
  have hstable : (prefixWord ++ tailWord_9722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9722).length < 2 ^ (prefixWord ++ tailWord_9722).sum := by decide
  have hdescent : baseEnd_9722 < baseStart_9722 := by decide
  rcases family_descends (prefixWord ++ tailWord_9722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9809 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 1, 6]
def baseStart_9809 : Nat := 118140960795 + 9809 * 2 ^ 59
def prefixEnd_9809 : Nat := 4983230072969 + 3 ^ 40 * 9809 * 2
def baseEnd_9809 : Nat := 1678910580019118647465

theorem tailTrace_9809 : CollatzResearch.WordTrace tailWord_9809 prefixEnd_9809 1678910580019118647465 := by
  unfold tailWord_9809
  simp only [CollatzResearch.WordTrace]
  refine ⟨357763621471143088936481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 238509080980762059290987 357763621471143088936481)
  ·
    refine ⟨268322716103357316702361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 357763621471143088936481 268322716103357316702361)
    ·
      refine ⟨201242037077517987526771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268322716103357316702361 201242037077517987526771)
      ·
        refine ⟨301863055616276981290157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201242037077517987526771 301863055616276981290157)
        ·
          refine ⟨113198645856103867983809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301863055616276981290157 113198645856103867983809)
          ·
            refine ⟨84898984392077900987857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113198645856103867983809 84898984392077900987857)
            ·
              refine ⟨63674238294058425740893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84898984392077900987857 63674238294058425740893)
              ·
                refine ⟨23877839360271909652835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63674238294058425740893 23877839360271909652835)
                ·
                  refine ⟨35816759040407864479253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23877839360271909652835 35816759040407864479253)
                  ·
                    refine ⟨1678910580019118647465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35816759040407864479253 1678910580019118647465)
                    ·
                      rfl

theorem cell23_9809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_9809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9809 prefixEnd_9809 := by exact prefixLift 9809
  have htrace : WordTrace (prefixWord ++ tailWord_9809) baseStart_9809 baseEnd_9809 := by
    simpa [prefixWord, tailWord_9809, baseEnd_9809] using wordTrace_append hprefix tailTrace_9809
  have hstable : (prefixWord ++ tailWord_9809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9809).length < 2 ^ (prefixWord ++ tailWord_9809).sum := by decide
  have hdescent : baseEnd_9809 < baseStart_9809 := by decide
  rcases family_descends (prefixWord ++ tailWord_9809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9820 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_9820 : Nat := 118140960795 + 9820 * 2 ^ 59
def prefixEnd_9820 : Nat := 4983230072969 + 3 ^ 40 * 9820 * 2
def baseEnd_9820 : Nat := 5042380027256812904845

theorem tailTrace_9820 : CollatzResearch.WordTrace tailWord_9820 prefixEnd_9820 5042380027256812904845 := by
  unfold tailWord_9820
  simp only [CollatzResearch.WordTrace]
  refine ⟨179082412215645983793457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 238776549620861311724609 179082412215645983793457)
  ·
    refine ⟨134311809161734487845093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179082412215645983793457 134311809161734487845093)
    ·
      refine ⟨25183464217825216470955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134311809161734487845093 25183464217825216470955)
      ·
        refine ⟨37775196326737824706433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25183464217825216470955 37775196326737824706433)
        ·
          refine ⟨28331397245053368529825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37775196326737824706433 28331397245053368529825)
          ·
            refine ⟨21248547933790026397369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28331397245053368529825 21248547933790026397369)
            ·
              refine ⟨15936410950342519798027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21248547933790026397369 15936410950342519798027)
              ·
                refine ⟨23904616425513779697041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15936410950342519798027 23904616425513779697041)
                ·
                  refine ⟨17928462319135334772781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23904616425513779697041 17928462319135334772781)
                  ·
                    refine ⟨6723173369675750539793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17928462319135334772781 6723173369675750539793)
                    ·
                      refine ⟨5042380027256812904845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6723173369675750539793 5042380027256812904845)
                      ·
                        rfl

theorem cell23_9820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_9820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9820 prefixEnd_9820 := by exact prefixLift 9820
  have htrace : WordTrace (prefixWord ++ tailWord_9820) baseStart_9820 baseEnd_9820 := by
    simpa [prefixWord, tailWord_9820, baseEnd_9820] using wordTrace_append hprefix tailTrace_9820
  have hstable : (prefixWord ++ tailWord_9820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9820).length < 2 ^ (prefixWord ++ tailWord_9820).sum := by decide
  have hdescent : baseEnd_9820 < baseStart_9820 := by decide
  rcases family_descends (prefixWord ++ tailWord_9820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9884 : List Nat := [2, 2, 3, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_9884 : Nat := 118140960795 + 9884 * 2 ^ 59
def prefixEnd_9884 : Nat := 4983230072969 + 3 ^ 40 * 9884 * 2
def baseEnd_9884 : Nat := 5075242789144562504551

theorem tailTrace_9884 : CollatzResearch.WordTrace tailWord_9884 prefixEnd_9884 5075242789144562504551 := by
  unfold tailWord_9884
  simp only [CollatzResearch.WordTrace]
  refine ⟨180249548099715448958353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 240332730799620598611137 180249548099715448958353)
  ·
    refine ⟨135187161074786586718765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180249548099715448958353 135187161074786586718765)
    ·
      refine ⟨50695185403044970019537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135187161074786586718765 50695185403044970019537)
      ·
        refine ⟨38021389052283727514653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50695185403044970019537 38021389052283727514653)
        ·
          refine ⟨14258020894606397817995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38021389052283727514653 14258020894606397817995)
          ·
            refine ⟨21387031341909596726993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14258020894606397817995 21387031341909596726993)
            ·
              refine ⟨16040273506432197545245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21387031341909596726993 16040273506432197545245)
              ·
                refine ⟨6015102564912074079467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16040273506432197545245 6015102564912074079467)
                ·
                  refine ⟨9022653847368111119201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6015102564912074079467 9022653847368111119201)
                  ·
                    refine ⟨6766990385526083339401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9022653847368111119201 6766990385526083339401)
                    ·
                      refine ⟨5075242789144562504551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6766990385526083339401 5075242789144562504551)
                      ·
                        rfl

theorem cell23_9884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_9884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9884 prefixEnd_9884 := by exact prefixLift 9884
  have htrace : WordTrace (prefixWord ++ tailWord_9884) baseStart_9884 baseEnd_9884 := by
    simpa [prefixWord, tailWord_9884, baseEnd_9884] using wordTrace_append hprefix tailTrace_9884
  have hstable : (prefixWord ++ tailWord_9884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9884).length < 2 ^ (prefixWord ++ tailWord_9884).sum := by decide
  have hdescent : baseEnd_9884 < baseStart_9884 := by decide
  rcases family_descends (prefixWord ++ tailWord_9884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9916 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_9916 : Nat := 118140960795 + 9916 * 2 ^ 59
def prefixEnd_9916 : Nat := 4983230072969 + 3 ^ 40 * 9916 * 2
def baseEnd_9916 : Nat := 1697224723362812434801

theorem tailTrace_9916 : CollatzResearch.WordTrace tailWord_9916 prefixEnd_9916 1697224723362812434801 := by
  unfold tailWord_9916
  simp only [CollatzResearch.WordTrace]
  refine ⟨180833116041750181540801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 241110821389000242054401 180833116041750181540801)
  ·
    refine ⟨135624837031312636155601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180833116041750181540801 135624837031312636155601)
    ·
      refine ⟨101718627773484477116701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135624837031312636155601 101718627773484477116701)
      ·
        refine ⟨38144485415056678918763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101718627773484477116701 38144485415056678918763)
        ·
          refine ⟨57216728122585018378145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38144485415056678918763 57216728122585018378145)
          ·
            refine ⟨42912546091938763783609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57216728122585018378145 42912546091938763783609)
            ·
              refine ⟨32184409568954072837707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42912546091938763783609 32184409568954072837707)
              ·
                refine ⟨48276614353431109256561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32184409568954072837707 48276614353431109256561)
                ·
                  refine ⟨36207460765073331942421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48276614353431109256561 36207460765073331942421)
                  ·
                    refine ⟨1697224723362812434801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36207460765073331942421 1697224723362812434801)
                    ·
                      rfl

theorem cell23_9916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_9916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9916 prefixEnd_9916 := by exact prefixLift 9916
  have htrace : WordTrace (prefixWord ++ tailWord_9916) baseStart_9916 baseEnd_9916 := by
    simpa [prefixWord, tailWord_9916, baseEnd_9916] using wordTrace_append hprefix tailTrace_9916
  have hstable : (prefixWord ++ tailWord_9916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9916).length < 2 ^ (prefixWord ++ tailWord_9916).sum := by decide
  have hdescent : baseEnd_9916 < baseStart_9916 := by decide
  rcases family_descends (prefixWord ++ tailWord_9916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9974 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_9974 : Nat := 118140960795 + 9974 * 2 ^ 59
def prefixEnd_9974 : Nat := 4983230072969 + 3 ^ 40 * 9974 * 2
def baseEnd_9974 : Nat := 5121456048049210379137

theorem tailTrace_9974 : CollatzResearch.WordTrace tailWord_9974 prefixEnd_9974 5121456048049210379137 := by
  unfold tailWord_9974
  simp only [CollatzResearch.WordTrace]
  refine ⟨22736354117086016793311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 242521110582250845795317 22736354117086016793311)
  ·
    refine ⟨34104531175629025189967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22736354117086016793311 34104531175629025189967)
    ·
      refine ⟨51156796763443537784951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34104531175629025189967 51156796763443537784951)
      ·
        refine ⟨76735195145165306677427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51156796763443537784951 76735195145165306677427)
        ·
          refine ⟨115102792717747960016141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76735195145165306677427 115102792717747960016141)
          ·
            refine ⟨43163547269155485006053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115102792717747960016141 43163547269155485006053)
            ·
              refine ⟨8093165112966653438635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43163547269155485006053 8093165112966653438635)
              ·
                refine ⟨12139747669449980157953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8093165112966653438635 12139747669449980157953)
                ·
                  refine ⟨9104810752087485118465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12139747669449980157953 9104810752087485118465)
                  ·
                    refine ⟨6828608064065613838849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9104810752087485118465 6828608064065613838849)
                    ·
                      refine ⟨5121456048049210379137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6828608064065613838849 5121456048049210379137)
                      ·
                        rfl

theorem cell23_9974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_9974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9974 prefixEnd_9974 := by exact prefixLift 9974
  have htrace : WordTrace (prefixWord ++ tailWord_9974) baseStart_9974 baseEnd_9974 := by
    simpa [prefixWord, tailWord_9974, baseEnd_9974] using wordTrace_append hprefix tailTrace_9974
  have hstable : (prefixWord ++ tailWord_9974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9974).length < 2 ^ (prefixWord ++ tailWord_9974).sum := by decide
  have hdescent : baseEnd_9974 < baseStart_9974 := by decide
  rcases family_descends (prefixWord ++ tailWord_9974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9996 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_9996 : Nat := 118140960795 + 9996 * 2 ^ 59
def prefixEnd_9996 : Nat := 4983230072969 + 3 ^ 40 * 9996 * 2
def baseEnd_9996 : Nat := 5132752622448124304035

theorem tailTrace_9996 : CollatzResearch.WordTrace tailWord_9996 prefixEnd_9996 5132752622448124304035 := by
  unfold tailWord_9996
  simp only [CollatzResearch.WordTrace]
  refine ⟨182292035896837012996921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 243056047862449350662561 182292035896837012996921)
  ·
    refine ⟨136719026922627759747691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182292035896837012996921 136719026922627759747691)
    ·
      refine ⟨205078540383941639621537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136719026922627759747691 205078540383941639621537)
      ·
        refine ⟨153808905287956229716153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205078540383941639621537 153808905287956229716153)
        ·
          refine ⟨115356678965967172287115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153808905287956229716153 115356678965967172287115)
          ·
            refine ⟨173035018448950758430673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115356678965967172287115 173035018448950758430673)
            ·
              refine ⟨129776263836713068823005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173035018448950758430673 129776263836713068823005)
              ·
                refine ⟨48666098938767400808627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129776263836713068823005 48666098938767400808627)
                ·
                  refine ⟨72999148408151101212941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48666098938767400808627 72999148408151101212941)
                  ·
                    refine ⟨27374680653056662954853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72999148408151101212941 27374680653056662954853)
                    ·
                      refine ⟨5132752622448124304035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 27374680653056662954853 5132752622448124304035)
                      ·
                        rfl

theorem cell23_9996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_9996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_9996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_9996 prefixEnd_9996 := by exact prefixLift 9996
  have htrace : WordTrace (prefixWord ++ tailWord_9996) baseStart_9996 baseEnd_9996 := by
    simpa [prefixWord, tailWord_9996, baseEnd_9996] using wordTrace_append hprefix tailTrace_9996
  have hstable : (prefixWord ++ tailWord_9996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9996).length < 2 ^ (prefixWord ++ tailWord_9996).sum := by decide
  have hdescent : baseEnd_9996 < baseStart_9996 := by decide
  rcases family_descends (prefixWord ++ tailWord_9996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10014 : List Nat := [4, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_10014 : Nat := 118140960795 + 10014 * 2 ^ 59
def prefixEnd_10014 : Nat := 4983230072969 + 3 ^ 40 * 10014 * 2
def baseEnd_10014 : Nat := 571332808247672653217

theorem tailTrace_10014 : CollatzResearch.WordTrace tailWord_10014 prefixEnd_10014 571332808247672653217 := by
  unfold tailWord_10014
  simp only [CollatzResearch.WordTrace]
  refine ⟨45655073216057887518637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 243493723818975400099397 45655073216057887518637)
  ·
    refine ⟨17120652456021707819489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45655073216057887518637 17120652456021707819489)
    ·
      refine ⟨12840489342016280864617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17120652456021707819489 12840489342016280864617)
      ·
        refine ⟨9630367006512210648463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12840489342016280864617 9630367006512210648463)
        ·
          refine ⟨14445550509768315972695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9630367006512210648463 14445550509768315972695)
          ·
            refine ⟨21668325764652473959043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14445550509768315972695 21668325764652473959043)
            ·
              refine ⟨32502488646978710938565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21668325764652473959043 32502488646978710938565)
              ·
                refine ⟨6094216621308508300981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32502488646978710938565 6094216621308508300981)
                ·
                  refine ⟨571332808247672653217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6094216621308508300981 571332808247672653217)
                  ·
                    rfl

theorem cell23_10014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_10014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10014 prefixEnd_10014 := by exact prefixLift 10014
  have htrace : WordTrace (prefixWord ++ tailWord_10014) baseStart_10014 baseEnd_10014 := by
    simpa [prefixWord, tailWord_10014, baseEnd_10014] using wordTrace_append hprefix tailTrace_10014
  have hstable : (prefixWord ++ tailWord_10014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10014).length < 2 ^ (prefixWord ++ tailWord_10014).sum := by decide
  have hdescent : baseEnd_10014 < baseStart_10014 := by decide
  rcases family_descends (prefixWord ++ tailWord_10014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10016 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_10016 : Nat := 118140960795 + 10016 * 2 ^ 59
def prefixEnd_10016 : Nat := 4983230072969 + 3 ^ 40 * 10016 * 2
def baseEnd_10016 : Nat := 5143022235538046053943

theorem tailTrace_10016 : CollatzResearch.WordTrace tailWord_10016 prefixEnd_10016 5143022235538046053943 := by
  unfold tailWord_10016
  simp only [CollatzResearch.WordTrace]
  refine ⟨182656765860608720860951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 243542354480811627814601 182656765860608720860951)
  ·
    refine ⟨273985148790913081291427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182656765860608720860951 273985148790913081291427)
    ·
      refine ⟨410977723186369621937141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273985148790913081291427 410977723186369621937141)
      ·
        refine ⟨38529161548722152056607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 410977723186369621937141 38529161548722152056607)
        ·
          refine ⟨57793742323083228084911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38529161548722152056607 57793742323083228084911)
          ·
            refine ⟨86690613484624842127367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57793742323083228084911 86690613484624842127367)
            ·
              refine ⟨130035920226937263191051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86690613484624842127367 130035920226937263191051)
              ·
                refine ⟨195053880340405894786577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130035920226937263191051 195053880340405894786577)
                ·
                  refine ⟨146290410255304421089933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195053880340405894786577 146290410255304421089933)
                  ·
                    refine ⟨54858903845739157908725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146290410255304421089933 54858903845739157908725)
                    ·
                      refine ⟨5143022235538046053943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 54858903845739157908725 5143022235538046053943)
                      ·
                        rfl

theorem cell23_10016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_10016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10016 prefixEnd_10016 := by exact prefixLift 10016
  have htrace : WordTrace (prefixWord ++ tailWord_10016) baseStart_10016 baseEnd_10016 := by
    simpa [prefixWord, tailWord_10016, baseEnd_10016] using wordTrace_append hprefix tailTrace_10016
  have hstable : (prefixWord ++ tailWord_10016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10016).length < 2 ^ (prefixWord ++ tailWord_10016).sum := by decide
  have hdescent : baseEnd_10016 < baseStart_10016 := by decide
  rcases family_descends (prefixWord ++ tailWord_10016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10047 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 2, 1, 4]
def baseStart_10047 : Nat := 118140960795 + 10047 * 2 ^ 59
def prefixEnd_10047 : Nat := 4983230072969 + 3 ^ 40 * 10047 * 2
def baseEnd_10047 : Nat := 5158940135827424766301

theorem tailTrace_10047 : CollatzResearch.WordTrace tailWord_10047 prefixEnd_10047 5158940135827424766301 := by
  unfold tailWord_10047
  simp only [CollatzResearch.WordTrace]
  refine ⟨366444194608909736100395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 244296129739273157400263 366444194608909736100395)
  ·
    refine ⟨549666291913364604150593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 366444194608909736100395 549666291913364604150593)
    ·
      refine ⟨412249718935023453112945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 549666291913364604150593 412249718935023453112945)
      ·
        refine ⟨309187289201267589834709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412249718935023453112945 309187289201267589834709)
        ·
          refine ⟨7246577090654709136751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 309187289201267589834709 7246577090654709136751)
          ·
            refine ⟨10869865635982063705127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7246577090654709136751 10869865635982063705127)
            ·
              refine ⟨16304798453973095557691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10869865635982063705127 16304798453973095557691)
              ·
                refine ⟨24457197680959643336537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16304798453973095557691 24457197680959643336537)
                ·
                  refine ⟨18342898260719732502403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24457197680959643336537 18342898260719732502403)
                  ·
                    refine ⟨27514347391079598753605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18342898260719732502403 27514347391079598753605)
                    ·
                      refine ⟨5158940135827424766301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 27514347391079598753605 5158940135827424766301)
                      ·
                        rfl

theorem cell23_10047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_10047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10047 prefixEnd_10047 := by exact prefixLift 10047
  have htrace : WordTrace (prefixWord ++ tailWord_10047) baseStart_10047 baseEnd_10047 := by
    simpa [prefixWord, tailWord_10047, baseEnd_10047] using wordTrace_append hprefix tailTrace_10047
  have hstable : (prefixWord ++ tailWord_10047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10047).length < 2 ^ (prefixWord ++ tailWord_10047).sum := by decide
  have hdescent : baseEnd_10047 < baseStart_10047 := by decide
  rcases family_descends (prefixWord ++ tailWord_10047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10080 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 3, 1, 3]
def baseStart_10080 : Nat := 118140960795 + 10080 * 2 ^ 59
def prefixEnd_10080 : Nat := 4983230072969 + 3 ^ 40 * 10080 * 2
def baseEnd_10080 : Nat := 5175884997425795653649

theorem tailTrace_10080 : CollatzResearch.WordTrace tailWord_10080 prefixEnd_10080 5175884997425795653649 := by
  unfold tailWord_10080
  simp only [CollatzResearch.WordTrace]
  refine ⟨183823901744678186025847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 245098535659570914701129 183823901744678186025847)
  ·
    refine ⟨275735852617017279038771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183823901744678186025847 275735852617017279038771)
    ·
      refine ⟨413603778925525918558157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275735852617017279038771 413603778925525918558157)
      ·
        refine ⟨155101417097072219459309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413603778925525918558157 155101417097072219459309)
        ·
          refine ⟨58163031411402082297241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155101417097072219459309 58163031411402082297241)
          ·
            refine ⟨43622273558551561722931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58163031411402082297241 43622273558551561722931)
            ·
              refine ⟨65433410337827342584397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43622273558551561722931 65433410337827342584397)
              ·
                refine ⟨24537528876685253469149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65433410337827342584397 24537528876685253469149)
                ·
                  refine ⟨9201573328756970050931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24537528876685253469149 9201573328756970050931)
                  ·
                    refine ⟨13802359993135455076397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9201573328756970050931 13802359993135455076397)
                    ·
                      refine ⟨5175884997425795653649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 13802359993135455076397 5175884997425795653649)
                      ·
                        rfl

theorem cell23_10080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_10080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10080 prefixEnd_10080 := by exact prefixLift 10080
  have htrace : WordTrace (prefixWord ++ tailWord_10080) baseStart_10080 baseEnd_10080 := by
    simpa [prefixWord, tailWord_10080, baseEnd_10080] using wordTrace_append hprefix tailTrace_10080
  have hstable : (prefixWord ++ tailWord_10080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10080).length < 2 ^ (prefixWord ++ tailWord_10080).sum := by decide
  have hdescent : baseEnd_10080 < baseStart_10080 := by decide
  rcases family_descends (prefixWord ++ tailWord_10080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10123 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 3]
def baseStart_10123 : Nat := 118140960795 + 10123 * 2 ^ 59
def prefixEnd_10123 : Nat := 4983230072969 + 3 ^ 40 * 10123 * 2
def baseEnd_10123 : Nat := 5197964665569127415951

theorem tailTrace_10123 : CollatzResearch.WordTrace tailWord_10123 prefixEnd_10123 5197964665569127415951 := by
  unfold tailWord_10123
  simp only [CollatzResearch.WordTrace]
  refine ⟨369216142333574715867023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 246144094889049810578015 369216142333574715867023)
  ·
    refine ⟨553824213500362073800535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 369216142333574715867023 553824213500362073800535)
    ·
      refine ⟨830736320250543110700803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 553824213500362073800535 830736320250543110700803)
      ·
        refine ⟨1246104480375814666051205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830736320250543110700803 1246104480375814666051205)
        ·
          refine ⟨233644590070465249884601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1246104480375814666051205 233644590070465249884601)
          ·
            refine ⟨175233442552848937413451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233644590070465249884601 175233442552848937413451)
            ·
              refine ⟨262850163829273406120177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175233442552848937413451 262850163829273406120177)
              ·
                refine ⟨197137622871955054590133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262850163829273406120177 197137622871955054590133)
                ·
                  refine ⟨18481652144245786367825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197137622871955054590133 18481652144245786367825)
                  ·
                    refine ⟨13861239108184339775869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18481652144245786367825 13861239108184339775869)
                    ·
                      refine ⟨5197964665569127415951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 13861239108184339775869 5197964665569127415951)
                      ·
                        rfl

theorem cell23_10123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 3].length) (baseStart_10123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10123 prefixEnd_10123 := by exact prefixLift 10123
  have htrace : WordTrace (prefixWord ++ tailWord_10123) baseStart_10123 baseEnd_10123 := by
    simpa [prefixWord, tailWord_10123, baseEnd_10123] using wordTrace_append hprefix tailTrace_10123
  have hstable : (prefixWord ++ tailWord_10123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10123).length < 2 ^ (prefixWord ++ tailWord_10123).sum := by decide
  have hdescent : baseEnd_10123 < baseStart_10123 := by decide
  rcases family_descends (prefixWord ++ tailWord_10123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10137 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 3, 2, 2]
def baseStart_10137 : Nat := 118140960795 + 10137 * 2 ^ 59
def prefixEnd_10137 : Nat := 4983230072969 + 3 ^ 40 * 10137 * 2
def baseEnd_10137 : Nat := 5205153394732072640887

theorem tailTrace_10137 : CollatzResearch.WordTrace tailWord_10137 prefixEnd_10137 5205153394732072640887 := by
  unfold tailWord_10137
  simp only [CollatzResearch.WordTrace]
  refine ⟨369726764282855106876665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 246484509521903404584443 369726764282855106876665)
  ·
    refine ⟨277295073212141330157499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 369726764282855106876665 277295073212141330157499)
    ·
      refine ⟨415942609818211995236249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277295073212141330157499 415942609818211995236249)
      ·
        refine ⟨311956957363658996427187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415942609818211995236249 311956957363658996427187)
        ·
          refine ⟨467935436045488494640781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311956957363658996427187 467935436045488494640781)
          ·
            refine ⟨175475788517058185490293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 467935436045488494640781 175475788517058185490293)
            ·
              refine ⟨16450855173474204889715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175475788517058185490293 16450855173474204889715)
              ·
                refine ⟨24676282760211307334573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16450855173474204889715 24676282760211307334573)
                ·
                  refine ⟨9253606035079240250465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24676282760211307334573 9253606035079240250465)
                  ·
                    refine ⟨6940204526309430187849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9253606035079240250465 6940204526309430187849)
                    ·
                      refine ⟨5205153394732072640887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6940204526309430187849 5205153394732072640887)
                      ·
                        rfl

theorem cell23_10137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_10137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10137 prefixEnd_10137 := by exact prefixLift 10137
  have htrace : WordTrace (prefixWord ++ tailWord_10137) baseStart_10137 baseEnd_10137 := by
    simpa [prefixWord, tailWord_10137, baseEnd_10137] using wordTrace_append hprefix tailTrace_10137
  have hstable : (prefixWord ++ tailWord_10137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10137).length < 2 ^ (prefixWord ++ tailWord_10137).sum := by decide
  have hdescent : baseEnd_10137 < baseStart_10137 := by decide
  rcases family_descends (prefixWord ++ tailWord_10137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10140 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_10140 : Nat := 118140960795 + 10140 * 2 ^ 59
def prefixEnd_10140 : Nat := 4983230072969 + 3 ^ 40 * 10140 * 2
def baseEnd_10140 : Nat := 5206693836695560903373

theorem tailTrace_10140 : CollatzResearch.WordTrace tailWord_10140 prefixEnd_10140 5206693836695560903373 := by
  unfold tailWord_10140
  simp only [CollatzResearch.WordTrace]
  refine ⟨184918091635993309617937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 246557455514657746157249 184918091635993309617937)
  ·
    refine ⟨138688568726994982213453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184918091635993309617937 138688568726994982213453)
    ·
      refine ⟨52008213272623118330045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138688568726994982213453 52008213272623118330045)
      ·
        refine ⟨19503079977233669373767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52008213272623118330045 19503079977233669373767)
        ·
          refine ⟨29254619965850504060651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19503079977233669373767 29254619965850504060651)
          ·
            refine ⟨43881929948775756090977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29254619965850504060651 43881929948775756090977)
            ·
              refine ⟨32911447461581817068233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43881929948775756090977 32911447461581817068233)
              ·
                refine ⟨24683585596186362801175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32911447461581817068233 24683585596186362801175)
                ·
                  refine ⟨37025378394279544201763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24683585596186362801175 37025378394279544201763)
                  ·
                    refine ⟨55538067591419316302645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37025378394279544201763 55538067591419316302645)
                    ·
                      refine ⟨5206693836695560903373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 55538067591419316302645 5206693836695560903373)
                      ·
                        rfl

theorem cell23_10140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_10140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10140 prefixEnd_10140 := by exact prefixLift 10140
  have htrace : WordTrace (prefixWord ++ tailWord_10140) baseStart_10140 baseEnd_10140 := by
    simpa [prefixWord, tailWord_10140, baseEnd_10140] using wordTrace_append hprefix tailTrace_10140
  have hstable : (prefixWord ++ tailWord_10140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10140).length < 2 ^ (prefixWord ++ tailWord_10140).sum := by decide
  have hdescent : baseEnd_10140 < baseStart_10140 := by decide
  rcases family_descends (prefixWord ++ tailWord_10140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10158 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_10158 : Nat := 118140960795 + 10158 * 2 ^ 59
def prefixEnd_10158 : Nat := 4983230072969 + 3 ^ 40 * 10158 * 2
def baseEnd_10158 : Nat := 5215936488476490478291

theorem tailTrace_10158 : CollatzResearch.WordTrace tailWord_10158 prefixEnd_10158 5215936488476490478291 := by
  unfold tailWord_10158
  simp only [CollatzResearch.WordTrace]
  refine ⟨46311587150846961673891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 246995131471183795594085 46311587150846961673891)
  ·
    refine ⟨69467380726270442510837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46311587150846961673891 69467380726270442510837)
    ·
      refine ⟨6512566943087853985391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69467380726270442510837 6512566943087853985391)
      ·
        refine ⟨9768850414631780978087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6512566943087853985391 9768850414631780978087)
        ·
          refine ⟨14653275621947671467131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9768850414631780978087 14653275621947671467131)
          ·
            refine ⟨21979913432921507200697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14653275621947671467131 21979913432921507200697)
            ·
              refine ⟨16484935074691130400523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21979913432921507200697 16484935074691130400523)
              ·
                refine ⟨24727402612036695600785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16484935074691130400523 24727402612036695600785)
                ·
                  refine ⟨18545551959027521700589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24727402612036695600785 18545551959027521700589)
                  ·
                    refine ⟨6954581984635320637721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18545551959027521700589 6954581984635320637721)
                    ·
                      refine ⟨5215936488476490478291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6954581984635320637721 5215936488476490478291)
                      ·
                        rfl

theorem cell23_10158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_10158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10158 prefixEnd_10158 := by exact prefixLift 10158
  have htrace : WordTrace (prefixWord ++ tailWord_10158) baseStart_10158 baseEnd_10158 := by
    simpa [prefixWord, tailWord_10158, baseEnd_10158] using wordTrace_append hprefix tailTrace_10158
  have hstable : (prefixWord ++ tailWord_10158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10158).length < 2 ^ (prefixWord ++ tailWord_10158).sum := by decide
  have hdescent : baseEnd_10158 < baseStart_10158 := by decide
  rcases family_descends (prefixWord ++ tailWord_10158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10170 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3]
def baseStart_10170 : Nat := 118140960795 + 10170 * 2 ^ 59
def prefixEnd_10170 : Nat := 4983230072969 + 3 ^ 40 * 10170 * 2
def baseEnd_10170 : Nat := 5222098256330443528235

theorem tailTrace_10170 : CollatzResearch.WordTrace tailWord_10170 prefixEnd_10170 5222098256330443528235 := by
  unfold tailWord_10170
  simp only [CollatzResearch.WordTrace]
  refine ⟨92732593290825435706991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 247286915442201161885309 92732593290825435706991)
  ·
    refine ⟨139098889936238153560487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92732593290825435706991 139098889936238153560487)
    ·
      refine ⟨208648334904357230340731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139098889936238153560487 208648334904357230340731)
      ·
        refine ⟨312972502356535845511097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208648334904357230340731 312972502356535845511097)
        ·
          refine ⟨234729376767401884133323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312972502356535845511097 234729376767401884133323)
          ·
            refine ⟨352094065151102826199985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234729376767401884133323 352094065151102826199985)
            ·
              refine ⟨264070548863327119649989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352094065151102826199985 264070548863327119649989)
              ·
                refine ⟨49513227911873834934373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264070548863327119649989 49513227911873834934373)
                ·
                  refine ⟨9283730233476344050195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49513227911873834934373 9283730233476344050195)
                  ·
                    refine ⟨13925595350214516075293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9283730233476344050195 13925595350214516075293)
                    ·
                      refine ⟨5222098256330443528235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 13925595350214516075293 5222098256330443528235)
                      ·
                        rfl

theorem cell23_10170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_10170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10170 prefixEnd_10170 := by exact prefixLift 10170
  have htrace : WordTrace (prefixWord ++ tailWord_10170) baseStart_10170 baseEnd_10170 := by
    simpa [prefixWord, tailWord_10170, baseEnd_10170] using wordTrace_append hprefix tailTrace_10170
  have hstable : (prefixWord ++ tailWord_10170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10170).length < 2 ^ (prefixWord ++ tailWord_10170).sum := by decide
  have hdescent : baseEnd_10170 < baseStart_10170 := by decide
  rcases family_descends (prefixWord ++ tailWord_10170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10174 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_10174 : Nat := 118140960795 + 10174 * 2 ^ 59
def prefixEnd_10174 : Nat := 4983230072969 + 3 ^ 40 * 10174 * 2
def baseEnd_10174 : Nat := 5224152178948427878217

theorem tailTrace_10174 : CollatzResearch.WordTrace tailWord_10174 prefixEnd_10174 5224152178948427878217 := by
  unfold tailWord_10174
  simp only [CollatzResearch.WordTrace]
  refine ⟨46384533143601303246697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 247384176765873617315717 46384533143601303246697)
  ·
    refine ⟨34788399857700977435023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46384533143601303246697 34788399857700977435023)
    ·
      refine ⟨52182599786551466152535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34788399857700977435023 52182599786551466152535)
      ·
        refine ⟨78273899679827199228803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52182599786551466152535 78273899679827199228803)
        ·
          refine ⟨117410849519740798843205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78273899679827199228803 117410849519740798843205)
          ·
            refine ⟨22014534284951399783101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117410849519740798843205 22014534284951399783101)
            ·
              refine ⟨8255450356856774918663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22014534284951399783101 8255450356856774918663)
              ·
                refine ⟨12383175535285162377995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8255450356856774918663 12383175535285162377995)
                ·
                  refine ⟨18574763302927743566993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12383175535285162377995 18574763302927743566993)
                  ·
                    refine ⟨13931072477195807675245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18574763302927743566993 13931072477195807675245)
                    ·
                      refine ⟨5224152178948427878217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 13931072477195807675245 5224152178948427878217)
                      ·
                        rfl

theorem cell23_10174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_10174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10174 prefixEnd_10174 := by exact prefixLift 10174
  have htrace : WordTrace (prefixWord ++ tailWord_10174) baseStart_10174 baseEnd_10174 := by
    simpa [prefixWord, tailWord_10174, baseEnd_10174] using wordTrace_append hprefix tailTrace_10174
  have hstable : (prefixWord ++ tailWord_10174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10174).length < 2 ^ (prefixWord ++ tailWord_10174).sum := by decide
  have hdescent : baseEnd_10174 < baseStart_10174 := by decide
  rcases family_descends (prefixWord ++ tailWord_10174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10187 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 3]
def baseStart_10187 : Nat := 118140960795 + 10187 * 2 ^ 59
def prefixEnd_10187 : Nat := 4983230072969 + 3 ^ 40 * 10187 * 2
def baseEnd_10187 : Nat := 5230827427456877015657

theorem tailTrace_10187 : CollatzResearch.WordTrace tailWord_10187 prefixEnd_10187 5230827427456877015657 := by
  unfold tailWord_10187
  simp only [CollatzResearch.WordTrace]
  refine ⟨371550414101713646196815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 247700276067809097464543 371550414101713646196815)
  ·
    refine ⟨557325621152570469295223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371550414101713646196815 557325621152570469295223)
    ·
      refine ⟨835988431728855703942835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557325621152570469295223 835988431728855703942835)
      ·
        refine ⟨1253982647593283555914253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835988431728855703942835 1253982647593283555914253)
        ·
          refine ⟨470243492847481333467845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1253982647593283555914253 470243492847481333467845)
          ·
            refine ⟨88170654908902750025221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 470243492847481333467845 88170654908902750025221)
            ·
              refine ⟨16531997795419265629729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88170654908902750025221 16531997795419265629729)
              ·
                refine ⟨12398998346564449222297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16531997795419265629729 12398998346564449222297)
                ·
                  refine ⟨9299248759923336916723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12398998346564449222297 9299248759923336916723)
                  ·
                    refine ⟨13948873139885005375085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9299248759923336916723 13948873139885005375085)
                    ·
                      refine ⟨5230827427456877015657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 13948873139885005375085 5230827427456877015657)
                      ·
                        rfl

theorem cell23_10187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 3].length) (baseStart_10187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10187 prefixEnd_10187 := by exact prefixLift 10187
  have htrace : WordTrace (prefixWord ++ tailWord_10187) baseStart_10187 baseEnd_10187 := by
    simpa [prefixWord, tailWord_10187, baseEnd_10187] using wordTrace_append hprefix tailTrace_10187
  have hstable : (prefixWord ++ tailWord_10187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10187).length < 2 ^ (prefixWord ++ tailWord_10187).sum := by decide
  have hdescent : baseEnd_10187 < baseStart_10187 := by decide
  rcases family_descends (prefixWord ++ tailWord_10187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10188 : List Nat := [2, 2, 1, 4, 1, 4, 2, 2, 1, 2, 2]
def baseStart_10188 : Nat := 118140960795 + 10188 * 2 ^ 59
def prefixEnd_10188 : Nat := 4983230072969 + 3 ^ 40 * 10188 * 2
def baseEnd_10188 : Nat := 5231340908111373103153

theorem tailTrace_10188 : CollatzResearch.WordTrace tailWord_10188 prefixEnd_10188 5231340908111373103153 := by
  unfold tailWord_10188
  simp only [CollatzResearch.WordTrace]
  refine ⟨185793443549045408491609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 247724591398727211322145 185793443549045408491609)
  ·
    refine ⟨139345082661784056368707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185793443549045408491609 139345082661784056368707)
    ·
      refine ⟨209017623992676084553061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139345082661784056368707 209017623992676084553061)
      ·
        refine ⟨39190804498626765853699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209017623992676084553061 39190804498626765853699)
        ·
          refine ⟨58786206747940148780549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39190804498626765853699 58786206747940148780549)
          ·
            refine ⟨11022413765238777896353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58786206747940148780549 11022413765238777896353)
            ·
              refine ⟨8266810323929083422265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11022413765238777896353 8266810323929083422265)
              ·
                refine ⟨6200107742946812566699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8266810323929083422265 6200107742946812566699)
                ·
                  refine ⟨9300161614420218850049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200107742946812566699 9300161614420218850049)
                  ·
                    refine ⟨6975121210815164137537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9300161614420218850049 6975121210815164137537)
                    ·
                      refine ⟨5231340908111373103153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6975121210815164137537 5231340908111373103153)
                      ·
                        rfl

theorem cell23_10188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_10188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10188 prefixEnd_10188 := by exact prefixLift 10188
  have htrace : WordTrace (prefixWord ++ tailWord_10188) baseStart_10188 baseEnd_10188 := by
    simpa [prefixWord, tailWord_10188, baseEnd_10188] using wordTrace_append hprefix tailTrace_10188
  have hstable : (prefixWord ++ tailWord_10188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10188).length < 2 ^ (prefixWord ++ tailWord_10188).sum := by decide
  have hdescent : baseEnd_10188 < baseStart_10188 := by decide
  rcases family_descends (prefixWord ++ tailWord_10188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10197 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_10197 : Nat := 118140960795 + 10197 * 2 ^ 59
def prefixEnd_10197 : Nat := 4983230072969 + 3 ^ 40 * 10197 * 2
def baseEnd_10197 : Nat := 5235962234001837890611

theorem tailTrace_10197 : CollatzResearch.WordTrace tailWord_10197 prefixEnd_10197 5235962234001837890611 := by
  unfold tailWord_10197
  simp only [CollatzResearch.WordTrace]
  refine ⟨371915144065485354060845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 247943429376990236040563 371915144065485354060845)
  ·
    refine ⟨139468179024557007772817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 371915144065485354060845 139468179024557007772817)
    ·
      refine ⟨104601134268417755829613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139468179024557007772817 104601134268417755829613)
      ·
        refine ⟨39225425350656658436105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104601134268417755829613 39225425350656658436105)
        ·
          refine ⟨29419069012992493827079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39225425350656658436105 29419069012992493827079)
          ·
            refine ⟨44128603519488740740619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29419069012992493827079 44128603519488740740619)
            ·
              refine ⟨66192905279233111110929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44128603519488740740619 66192905279233111110929)
              ·
                refine ⟨49644678959424833333197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66192905279233111110929 49644678959424833333197)
                ·
                  refine ⟨18616754609784312499949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49644678959424833333197 18616754609784312499949)
                  ·
                    refine ⟨6981282978669117187481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18616754609784312499949 6981282978669117187481)
                    ·
                      refine ⟨5235962234001837890611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 6981282978669117187481 5235962234001837890611)
                      ·
                        rfl

theorem cell23_10197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_10197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10197 prefixEnd_10197 := by exact prefixLift 10197
  have htrace : WordTrace (prefixWord ++ tailWord_10197) baseStart_10197 baseEnd_10197 := by
    simpa [prefixWord, tailWord_10197, baseEnd_10197] using wordTrace_append hprefix tailTrace_10197
  have hstable : (prefixWord ++ tailWord_10197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10197).length < 2 ^ (prefixWord ++ tailWord_10197).sum := by decide
  have hdescent : baseEnd_10197 < baseStart_10197 := by decide
  rcases family_descends (prefixWord ++ tailWord_10197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10223 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_10223 : Nat := 118140960795 + 10223 * 2 ^ 59
def prefixEnd_10223 : Nat := 4983230072969 + 3 ^ 40 * 10223 * 2
def baseEnd_10223 : Nat := 5249312731018736165491

theorem tailTrace_10223 : CollatzResearch.WordTrace tailWord_10223 prefixEnd_10223 5249312731018736165491 := by
  unfold tailWord_10223
  simp only [CollatzResearch.WordTrace]
  refine ⟨372863441971291794507323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 248575627980861196338215 372863441971291794507323)
  ·
    refine ⟨559295162956937691760985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 372863441971291794507323 559295162956937691760985)
    ·
      refine ⟨419471372217703268820739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 559295162956937691760985 419471372217703268820739)
      ·
        refine ⟨629207058326554903231109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419471372217703268820739 629207058326554903231109)
        ·
          refine ⟨117976323436229044355833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 629207058326554903231109 117976323436229044355833)
          ·
            refine ⟨88482242577171783266875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117976323436229044355833 88482242577171783266875)
            ·
              refine ⟨132723363865757674900313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88482242577171783266875 132723363865757674900313)
              ·
                refine ⟨99542522899318256175235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132723363865757674900313 99542522899318256175235)
                ·
                  refine ⟨149313784348977384262853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99542522899318256175235 149313784348977384262853)
                  ·
                    refine ⟨27996334565433259549285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149313784348977384262853 27996334565433259549285)
                    ·
                      refine ⟨5249312731018736165491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 27996334565433259549285 5249312731018736165491)
                      ·
                        rfl

theorem cell23_10223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_10223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10223 prefixEnd_10223 := by exact prefixLift 10223
  have htrace : WordTrace (prefixWord ++ tailWord_10223) baseStart_10223 baseEnd_10223 := by
    simpa [prefixWord, tailWord_10223, baseEnd_10223] using wordTrace_append hprefix tailTrace_10223
  have hstable : (prefixWord ++ tailWord_10223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10223).length < 2 ^ (prefixWord ++ tailWord_10223).sum := by decide
  have hdescent : baseEnd_10223 < baseStart_10223 := by decide
  rcases family_descends (prefixWord ++ tailWord_10223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10261 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_10261 : Nat := 118140960795 + 10261 * 2 ^ 59
def prefixEnd_10261 : Nat := 4983230072969 + 3 ^ 40 * 10261 * 2
def baseEnd_10261 : Nat := 5268824995889587490317

theorem tailTrace_10261 : CollatzResearch.WordTrace tailWord_10261 prefixEnd_10261 5268824995889587490317 := by
  unfold tailWord_10261
  simp only [CollatzResearch.WordTrace]
  refine ⟨374249415833624284390637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 249499610555749522927091 374249415833624284390637)
  ·
    refine ⟨140343530937609106646489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 374249415833624284390637 140343530937609106646489)
    ·
      refine ⟨105257648203206829984867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140343530937609106646489 105257648203206829984867)
      ·
        refine ⟨157886472304810244977301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105257648203206829984867 157886472304810244977301)
        ·
          refine ⟨7400928389287980233311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 157886472304810244977301 7400928389287980233311)
          ·
            refine ⟨11101392583931970349967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7400928389287980233311 11101392583931970349967)
            ·
              refine ⟨16652088875897955524951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11101392583931970349967 16652088875897955524951)
              ·
                refine ⟨24978133313846933287427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16652088875897955524951 24978133313846933287427)
                ·
                  refine ⟨37467199970770399931141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24978133313846933287427 37467199970770399931141)
                  ·
                    refine ⟨7025099994519449987089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37467199970770399931141 7025099994519449987089)
                    ·
                      refine ⟨5268824995889587490317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7025099994519449987089 5268824995889587490317)
                      ·
                        rfl

theorem cell23_10261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_10261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10261 prefixEnd_10261 := by exact prefixLift 10261
  have htrace : WordTrace (prefixWord ++ tailWord_10261) baseStart_10261 baseEnd_10261 := by
    simpa [prefixWord, tailWord_10261, baseEnd_10261] using wordTrace_append hprefix tailTrace_10261
  have hstable : (prefixWord ++ tailWord_10261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10261).length < 2 ^ (prefixWord ++ tailWord_10261).sum := by decide
  have hdescent : baseEnd_10261 < baseStart_10261 := by decide
  rcases family_descends (prefixWord ++ tailWord_10261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10297 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 2, 5]
def baseStart_10297 : Nat := 118140960795 + 10297 * 2 ^ 59
def prefixEnd_10297 : Nat := 4983230072969 + 3 ^ 40 * 10297 * 2
def baseEnd_10297 : Nat := 1762436766483815546717

theorem tailTrace_10297 : CollatzResearch.WordTrace tailWord_10297 prefixEnd_10297 1762436766483815546717 := by
  unfold tailWord_10297
  simp only [CollatzResearch.WordTrace]
  refine ⟨375562443703202432701145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 250374962468801621800763 375562443703202432701145)
  ·
    refine ⟨281671832777401824525859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 375562443703202432701145 281671832777401824525859)
    ·
      refine ⟨422507749166102736788789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281671832777401824525859 422507749166102736788789)
      ·
        refine ⟨39610101484322131573949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 422507749166102736788789 39610101484322131573949)
        ·
          refine ⟨14853788056620799340231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39610101484322131573949 14853788056620799340231)
          ·
            refine ⟨22280682084931199010347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14853788056620799340231 22280682084931199010347)
            ·
              refine ⟨33421023127396798515521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22280682084931199010347 33421023127396798515521)
              ·
                refine ⟨25065767345547598886641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33421023127396798515521 25065767345547598886641)
                ·
                  refine ⟨18799325509160699164981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25065767345547598886641 18799325509160699164981)
                  ·
                    refine ⟨1762436766483815546717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18799325509160699164981 1762436766483815546717)
                    ·
                      rfl

theorem cell23_10297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_10297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10297 prefixEnd_10297 := by exact prefixLift 10297
  have htrace : WordTrace (prefixWord ++ tailWord_10297) baseStart_10297 baseEnd_10297 := by
    simpa [prefixWord, tailWord_10297, baseEnd_10297] using wordTrace_append hprefix tailTrace_10297
  have hstable : (prefixWord ++ tailWord_10297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10297).length < 2 ^ (prefixWord ++ tailWord_10297).sum := by decide
  have hdescent : baseEnd_10297 < baseStart_10297 := by decide
  rcases family_descends (prefixWord ++ tailWord_10297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10317 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_10317 : Nat := 118140960795 + 10317 * 2 ^ 59
def prefixEnd_10317 : Nat := 4983230072969 + 3 ^ 40 * 10317 * 2
def baseEnd_10317 : Nat := 5297579912541368390059

theorem tailTrace_10317 : CollatzResearch.WordTrace tailWord_10317 prefixEnd_10317 5297579912541368390059 := by
  unfold tailWord_10317
  simp only [CollatzResearch.WordTrace]
  refine ⟨376291903630745848429205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 250861269087163898952803 376291903630745848429205)
  ·
    refine ⟨17638682982691211645119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 376291903630745848429205 17638682982691211645119)
    ·
      refine ⟨26458024474036817467679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17638682982691211645119 26458024474036817467679)
      ·
        refine ⟨39687036711055226201519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26458024474036817467679 39687036711055226201519)
        ·
          refine ⟨59530555066582839302279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39687036711055226201519 59530555066582839302279)
          ·
            refine ⟨89295832599874258953419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59530555066582839302279 89295832599874258953419)
            ·
              refine ⟨133943748899811388430129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89295832599874258953419 133943748899811388430129)
              ·
                refine ⟨100457811674858541322597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133943748899811388430129 100457811674858541322597)
                ·
                  refine ⟨18835839689035976497987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100457811674858541322597 18835839689035976497987)
                  ·
                    refine ⟨28253759533553964746981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18835839689035976497987 28253759533553964746981)
                    ·
                      refine ⟨5297579912541368390059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 28253759533553964746981 5297579912541368390059)
                      ·
                        rfl

theorem cell23_10317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_10317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10317 prefixEnd_10317 := by exact prefixLift 10317
  have htrace : WordTrace (prefixWord ++ tailWord_10317) baseStart_10317 baseEnd_10317 := by
    simpa [prefixWord, tailWord_10317, baseEnd_10317] using wordTrace_append hprefix tailTrace_10317
  have hstable : (prefixWord ++ tailWord_10317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10317).length < 2 ^ (prefixWord ++ tailWord_10317).sum := by decide
  have hdescent : baseEnd_10317 < baseStart_10317 := by decide
  rcases family_descends (prefixWord ++ tailWord_10317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10361 : List Nat := [1, 2, 1, 3, 4, 1, 4, 2, 1, 4]
def baseStart_10361 : Nat := 118140960795 + 10361 * 2 ^ 59
def prefixEnd_10361 : Nat := 4983230072969 + 3 ^ 40 * 10361 * 2
def baseEnd_10361 : Nat := 1773391020446398746619

theorem tailTrace_10361 : CollatzResearch.WordTrace tailWord_10361 prefixEnd_10361 1773391020446398746619 := by
  unfold tailWord_10361
  simp only [CollatzResearch.WordTrace]
  refine ⟨377896715471341363030937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 251931143647560908687291 377896715471341363030937)
  ·
    refine ⟨283422536603506022273203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 377896715471341363030937 283422536603506022273203)
    ·
      refine ⟨425133804905259033409805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283422536603506022273203 425133804905259033409805)
      ·
        refine ⟨159425176839472137528677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425133804905259033409805 159425176839472137528677)
        ·
          refine ⟨29892220657401025786627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159425176839472137528677 29892220657401025786627)
          ·
            refine ⟨44838330986101538679941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29892220657401025786627 44838330986101538679941)
            ·
              refine ⟨8407187059894038502489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44838330986101538679941 8407187059894038502489)
              ·
                refine ⟨6305390294920528876867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8407187059894038502489 6305390294920528876867)
                ·
                  refine ⟨9458085442380793315301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6305390294920528876867 9458085442380793315301)
                  ·
                    refine ⟨1773391020446398746619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9458085442380793315301 1773391020446398746619)
                    ·
                      rfl

theorem cell23_10361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 4].length) (baseStart_10361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10361 prefixEnd_10361 := by exact prefixLift 10361
  have htrace : WordTrace (prefixWord ++ tailWord_10361) baseStart_10361 baseEnd_10361 := by
    simpa [prefixWord, tailWord_10361, baseEnd_10361] using wordTrace_append hprefix tailTrace_10361
  have hstable : (prefixWord ++ tailWord_10361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10361).length < 2 ^ (prefixWord ++ tailWord_10361).sum := by decide
  have hdescent : baseEnd_10361 < baseStart_10361 := by decide
  rcases family_descends (prefixWord ++ tailWord_10361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10377 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 1, 5, 2]
def baseStart_10377 : Nat := 118140960795 + 10377 * 2 ^ 59
def prefixEnd_10377 : Nat := 4983230072969 + 3 ^ 40 * 10377 * 2
def baseEnd_10377 : Nat := 5328388751811133639783

theorem tailTrace_10377 : CollatzResearch.WordTrace tailWord_10377 prefixEnd_10377 5328388751811133639783 := by
  unfold tailWord_10377
  simp only [CollatzResearch.WordTrace]
  refine ⟨378480283413376095613385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 252320188942250730408923 378480283413376095613385)
  ·
    refine ⟨283860212560032071710039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 378480283413376095613385 283860212560032071710039)
    ·
      refine ⟨425790318840048107565059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283860212560032071710039 425790318840048107565059)
      ·
        refine ⟨638685478260072161347589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425790318840048107565059 638685478260072161347589)
        ·
          refine ⟨119753527173763530252673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 638685478260072161347589 119753527173763530252673)
          ·
            refine ⟨89815145380322647689505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119753527173763530252673 89815145380322647689505)
            ·
              refine ⟨67361359035241985767129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89815145380322647689505 67361359035241985767129)
              ·
                refine ⟨50521019276431489325347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67361359035241985767129 50521019276431489325347)
                ·
                  refine ⟨75781528914647233988021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50521019276431489325347 75781528914647233988021)
                  ·
                    refine ⟨7104518335748178186377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75781528914647233988021 7104518335748178186377)
                    ·
                      refine ⟨5328388751811133639783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7104518335748178186377 5328388751811133639783)
                      ·
                        rfl

theorem cell23_10377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 5, 2].length) (baseStart_10377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10377 prefixEnd_10377 := by exact prefixLift 10377
  have htrace : WordTrace (prefixWord ++ tailWord_10377) baseStart_10377 baseEnd_10377 := by
    simpa [prefixWord, tailWord_10377, baseEnd_10377] using wordTrace_append hprefix tailTrace_10377
  have hstable : (prefixWord ++ tailWord_10377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10377).length < 2 ^ (prefixWord ++ tailWord_10377).sum := by decide
  have hdescent : baseEnd_10377 < baseStart_10377 := by decide
  rcases family_descends (prefixWord ++ tailWord_10377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10388 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_10388 : Nat := 118140960795 + 10388 * 2 ^ 59
def prefixEnd_10388 : Nat := 4983230072969 + 3 ^ 40 * 10388 * 2
def baseEnd_10388 : Nat := 5334037039010590602233

theorem tailTrace_10388 : CollatzResearch.WordTrace tailWord_10388 prefixEnd_10388 5334037039010590602233 := by
  unfold tailWord_10388
  simp only [CollatzResearch.WordTrace]
  refine ⟨189440743186762487131909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 252587657582349982842545 189440743186762487131909)
  ·
    refine ⟨35520139347517966337233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189440743186762487131909 35520139347517966337233)
    ·
      refine ⟨26640104510638474752925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35520139347517966337233 26640104510638474752925)
      ·
        refine ⟨9990039191489428032347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26640104510638474752925 9990039191489428032347)
        ·
          refine ⟨14985058787234142048521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9990039191489428032347 14985058787234142048521)
          ·
            refine ⟨11238794090425606536391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14985058787234142048521 11238794090425606536391)
            ·
              refine ⟨16858191135638409804587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11238794090425606536391 16858191135638409804587)
              ·
                refine ⟨25287286703457614706881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16858191135638409804587 25287286703457614706881)
                ·
                  refine ⟨18965465027593211030161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25287286703457614706881 18965465027593211030161)
                  ·
                    refine ⟨14224098770694908272621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18965465027593211030161 14224098770694908272621)
                    ·
                      refine ⟨5334037039010590602233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 14224098770694908272621 5334037039010590602233)
                      ·
                        rfl

theorem cell23_10388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_10388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10388 prefixEnd_10388 := by exact prefixLift 10388
  have htrace : WordTrace (prefixWord ++ tailWord_10388) baseStart_10388 baseEnd_10388 := by
    simpa [prefixWord, tailWord_10388, baseEnd_10388] using wordTrace_append hprefix tailTrace_10388
  have hstable : (prefixWord ++ tailWord_10388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10388).length < 2 ^ (prefixWord ++ tailWord_10388).sum := by decide
  have hdescent : baseEnd_10388 < baseStart_10388 := by decide
  rcases family_descends (prefixWord ++ tailWord_10388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10401 : List Nat := [1, 2, 3, 3, 1, 2, 1, 5, 1, 1, 3]
def baseStart_10401 : Nat := 118140960795 + 10401 * 2 ^ 59
def prefixEnd_10401 : Nat := 4983230072969 + 3 ^ 40 * 10401 * 2
def baseEnd_10401 : Nat := 5340712287519039739673

theorem tailTrace_10401 : CollatzResearch.WordTrace tailWord_10401 prefixEnd_10401 5340712287519039739673 := by
  unfold tailWord_10401
  simp only [CollatzResearch.WordTrace]
  refine ⟨379355635326428194487057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 252903756884285462991371 379355635326428194487057)
  ·
    refine ⟨284516726494821145865293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 379355635326428194487057 284516726494821145865293)
    ·
      refine ⟨106693772435557929699485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284516726494821145865293 106693772435557929699485)
      ·
        refine ⟨40010164663334223637307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106693772435557929699485 40010164663334223637307)
        ·
          refine ⟨60015246995001335455961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40010164663334223637307 60015246995001335455961)
          ·
            refine ⟨45011435246251001591971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60015246995001335455961 45011435246251001591971)
            ·
              refine ⟨67517152869376502387957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45011435246251001591971 67517152869376502387957)
              ·
                refine ⟨6329733081504047098871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67517152869376502387957 6329733081504047098871)
                ·
                  refine ⟨9494599622256070648307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6329733081504047098871 9494599622256070648307)
                  ·
                    refine ⟨14241899433384105972461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9494599622256070648307 14241899433384105972461)
                    ·
                      refine ⟨5340712287519039739673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 14241899433384105972461 5340712287519039739673)
                      ·
                        rfl

theorem cell23_10401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_10401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10401 prefixEnd_10401 := by exact prefixLift 10401
  have htrace : WordTrace (prefixWord ++ tailWord_10401) baseStart_10401 baseEnd_10401 := by
    simpa [prefixWord, tailWord_10401, baseEnd_10401] using wordTrace_append hprefix tailTrace_10401
  have hstable : (prefixWord ++ tailWord_10401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10401).length < 2 ^ (prefixWord ++ tailWord_10401).sum := by decide
  have hdescent : baseEnd_10401 < baseStart_10401 := by decide
  rcases family_descends (prefixWord ++ tailWord_10401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10404 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_10404 : Nat := 118140960795 + 10404 * 2 ^ 59
def prefixEnd_10404 : Nat := 4983230072969 + 3 ^ 40 * 10404 * 2
def baseEnd_10404 : Nat := 1780750909827509334053

theorem tailTrace_10404 : CollatzResearch.WordTrace tailWord_10404 prefixEnd_10404 1780750909827509334053 := by
  unfold tailWord_10404
  simp only [CollatzResearch.WordTrace]
  refine ⟨189732527157779853423133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 252976702877039804564177 189732527157779853423133)
  ·
    refine ⟨71149697684167445033675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189732527157779853423133 71149697684167445033675)
    ·
      refine ⟨106724546526251167550513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71149697684167445033675 106724546526251167550513)
      ·
        refine ⟨80043409894688375662885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106724546526251167550513 80043409894688375662885)
        ·
          refine ⟨15008139355254070436791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80043409894688375662885 15008139355254070436791)
          ·
            refine ⟨22512209032881105655187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15008139355254070436791 22512209032881105655187)
            ·
              refine ⟨33768313549321658482781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22512209032881105655187 33768313549321658482781)
              ·
                refine ⟨12663117580995621931043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33768313549321658482781 12663117580995621931043)
                ·
                  refine ⟨18994676371493432896565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12663117580995621931043 18994676371493432896565)
                  ·
                    refine ⟨1780750909827509334053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18994676371493432896565 1780750909827509334053)
                    ·
                      rfl

theorem cell23_10404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_10404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10404 prefixEnd_10404 := by exact prefixLift 10404
  have htrace : WordTrace (prefixWord ++ tailWord_10404) baseStart_10404 baseEnd_10404 := by
    simpa [prefixWord, tailWord_10404, baseEnd_10404] using wordTrace_append hprefix tailTrace_10404
  have hstable : (prefixWord ++ tailWord_10404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10404).length < 2 ^ (prefixWord ++ tailWord_10404).sum := by decide
  have hdescent : baseEnd_10404 < baseStart_10404 := by decide
  rcases family_descends (prefixWord ++ tailWord_10404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10437 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_10437 : Nat := 118140960795 + 10437 * 2 ^ 59
def prefixEnd_10437 : Nat := 4983230072969 + 3 ^ 40 * 10437 * 2
def baseEnd_10437 : Nat := 5359197591080898889507

theorem tailTrace_10437 : CollatzResearch.WordTrace tailWord_10437 prefixEnd_10437 5359197591080898889507 := by
  unfold tailWord_10437
  simp only [CollatzResearch.WordTrace]
  refine ⟨380668663196006342797565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 253779108797337561865043 380668663196006342797565)
  ·
    refine ⟨142750748698502378549087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 380668663196006342797565 142750748698502378549087)
    ·
      refine ⟨214126123047753567823631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142750748698502378549087 214126123047753567823631)
      ·
        refine ⟨321189184571630351735447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214126123047753567823631 321189184571630351735447)
        ·
          refine ⟨481783776857445527603171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321189184571630351735447 481783776857445527603171)
          ·
            refine ⟨722675665286168291404757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481783776857445527603171 722675665286168291404757)
            ·
              refine ⟨16937710905144569329799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 722675665286168291404757 16937710905144569329799)
              ·
                refine ⟨25406566357716853994699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16937710905144569329799 25406566357716853994699)
                ·
                  refine ⟨38109849536575280992049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25406566357716853994699 38109849536575280992049)
                  ·
                    refine ⟨28582387152431460744037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38109849536575280992049 28582387152431460744037)
                    ·
                      refine ⟨5359197591080898889507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 28582387152431460744037 5359197591080898889507)
                      ·
                        rfl

theorem cell23_10437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_10437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10437 prefixEnd_10437 := by exact prefixLift 10437
  have htrace : WordTrace (prefixWord ++ tailWord_10437) baseStart_10437 baseEnd_10437 := by
    simpa [prefixWord, tailWord_10437, baseEnd_10437] using wordTrace_append hprefix tailTrace_10437
  have hstable : (prefixWord ++ tailWord_10437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10437).length < 2 ^ (prefixWord ++ tailWord_10437).sum := by decide
  have hdescent : baseEnd_10437 < baseStart_10437 := by decide
  rcases family_descends (prefixWord ++ tailWord_10437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10457 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 3]
def baseStart_10457 : Nat := 118140960795 + 10457 * 2 ^ 59
def prefixEnd_10457 : Nat := 4983230072969 + 3 ^ 40 * 10457 * 2
def baseEnd_10457 : Nat := 5369467204170820639415

theorem tailTrace_10457 : CollatzResearch.WordTrace tailWord_10457 prefixEnd_10457 5369467204170820639415 := by
  unfold tailWord_10457
  simp only [CollatzResearch.WordTrace]
  refine ⟨381398123123549758525625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 254265415415699839017083 381398123123549758525625)
  ·
    refine ⟨286048592342662318894219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 381398123123549758525625 286048592342662318894219)
    ·
      refine ⟨429072888513993478341329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286048592342662318894219 429072888513993478341329)
      ·
        refine ⟨321804666385495108755997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429072888513993478341329 321804666385495108755997)
        ·
          refine ⟨120676749894560665783499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321804666385495108755997 120676749894560665783499)
          ·
            refine ⟨181015124841840998675249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120676749894560665783499 181015124841840998675249)
            ·
              refine ⟨135761343631380749006437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181015124841840998675249 135761343631380749006437)
              ·
                refine ⟨25455251930883890438707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135761343631380749006437 25455251930883890438707)
                ·
                  refine ⟨38182877896325835658061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25455251930883890438707 38182877896325835658061)
                  ·
                    refine ⟨14318579211122188371773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38182877896325835658061 14318579211122188371773)
                    ·
                      refine ⟨5369467204170820639415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 14318579211122188371773 5369467204170820639415)
                      ·
                        rfl

theorem cell23_10457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_10457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10457 prefixEnd_10457 := by exact prefixLift 10457
  have htrace : WordTrace (prefixWord ++ tailWord_10457) baseStart_10457 baseEnd_10457 := by
    simpa [prefixWord, tailWord_10457, baseEnd_10457] using wordTrace_append hprefix tailTrace_10457
  have hstable : (prefixWord ++ tailWord_10457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10457).length < 2 ^ (prefixWord ++ tailWord_10457).sum := by decide
  have hdescent : baseEnd_10457 < baseStart_10457 := by decide
  rcases family_descends (prefixWord ++ tailWord_10457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10458 : List Nat := [3, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2]
def baseStart_10458 : Nat := 118140960795 + 10458 * 2 ^ 59
def prefixEnd_10458 : Nat := 4983230072969 + 3 ^ 40 * 10458 * 2
def baseEnd_10458 : Nat := 5369980684825316726911

theorem tailTrace_10458 : CollatzResearch.WordTrace tailWord_10458 prefixEnd_10458 5369980684825316726911 := by
  unfold tailWord_10458
  simp only [CollatzResearch.WordTrace]
  refine ⟨95358649029981732328007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 254289730746617952874685 95358649029981732328007)
  ·
    refine ⟨143037973544972598492011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95358649029981732328007 143037973544972598492011)
    ·
      refine ⟨214556960317458897738017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143037973544972598492011 214556960317458897738017)
      ·
        refine ⟨160917720238094173303513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214556960317458897738017 160917720238094173303513)
        ·
          refine ⟨120688290178570629977635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160917720238094173303513 120688290178570629977635)
          ·
            refine ⟨181032435267855944966453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120688290178570629977635 181032435267855944966453)
            ·
              refine ⟨16971790806361494840605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181032435267855944966453 16971790806361494840605)
              ·
                refine ⟨6364421552385560565227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16971790806361494840605 6364421552385560565227)
                ·
                  refine ⟨9546632328578340847841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6364421552385560565227 9546632328578340847841)
                  ·
                    refine ⟨7159974246433755635881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9546632328578340847841 7159974246433755635881)
                    ·
                      refine ⟨5369980684825316726911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7159974246433755635881 5369980684825316726911)
                      ·
                        rfl

theorem cell23_10458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_10458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10458 prefixEnd_10458 := by exact prefixLift 10458
  have htrace : WordTrace (prefixWord ++ tailWord_10458) baseStart_10458 baseEnd_10458 := by
    simpa [prefixWord, tailWord_10458, baseEnd_10458] using wordTrace_append hprefix tailTrace_10458
  have hstable : (prefixWord ++ tailWord_10458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10458).length < 2 ^ (prefixWord ++ tailWord_10458).sum := by decide
  have hdescent : baseEnd_10458 < baseStart_10458 := by decide
  rcases family_descends (prefixWord ++ tailWord_10458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10461 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_10461 : Nat := 118140960795 + 10461 * 2 ^ 59
def prefixEnd_10461 : Nat := 4983230072969 + 3 ^ 40 * 10461 * 2
def baseEnd_10461 : Nat := 5371521126788804989397

theorem tailTrace_10461 : CollatzResearch.WordTrace tailWord_10461 prefixEnd_10461 5371521126788804989397 := by
  unfold tailWord_10461
  simp only [CollatzResearch.WordTrace]
  refine ⟨381544015109058441671237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 254362676739372294447491 381544015109058441671237)
  ·
    refine ⟨71539502832948457813357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 381544015109058441671237 71539502832948457813357)
    ·
      refine ⟨26827313562355671680009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71539502832948457813357 26827313562355671680009)
      ·
        refine ⟨20120485171766753760007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26827313562355671680009 20120485171766753760007)
        ·
          refine ⟨30180727757650130640011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20120485171766753760007 30180727757650130640011)
          ·
            refine ⟨45271091636475195960017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30180727757650130640011 45271091636475195960017)
            ·
              refine ⟨33953318727356396970013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45271091636475195960017 33953318727356396970013)
              ·
                refine ⟨12732494522758648863755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33953318727356396970013 12732494522758648863755)
                ·
                  refine ⟨19098741784137973295633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12732494522758648863755 19098741784137973295633)
                  ·
                    refine ⟨14324056338103479971725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19098741784137973295633 14324056338103479971725)
                    ·
                      refine ⟨5371521126788804989397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 14324056338103479971725 5371521126788804989397)
                      ·
                        rfl

theorem cell23_10461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_10461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10461 prefixEnd_10461 := by exact prefixLift 10461
  have htrace : WordTrace (prefixWord ++ tailWord_10461) baseStart_10461 baseEnd_10461 := by
    simpa [prefixWord, tailWord_10461, baseEnd_10461] using wordTrace_append hprefix tailTrace_10461
  have hstable : (prefixWord ++ tailWord_10461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10461).length < 2 ^ (prefixWord ++ tailWord_10461).sum := by decide
  have hdescent : baseEnd_10461 < baseStart_10461 := by decide
  rcases family_descends (prefixWord ++ tailWord_10461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10474 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_10474 : Nat := 118140960795 + 10474 * 2 ^ 59
def prefixEnd_10474 : Nat := 4983230072969 + 3 ^ 40 * 10474 * 2
def baseEnd_10474 : Nat := 5378196375297254126837

theorem tailTrace_10474 : CollatzResearch.WordTrace tailWord_10474 prefixEnd_10474 5378196375297254126837 := by
  unfold tailWord_10474
  simp only [CollatzResearch.WordTrace]
  refine ⟨95504541015490415473619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 254678776041307774596317 95504541015490415473619)
  ·
    refine ⟨143256811523235623210429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95504541015490415473619 143256811523235623210429)
    ·
      refine ⟨53721304321213358703911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143256811523235623210429 53721304321213358703911)
      ·
        refine ⟨80581956481820038055867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53721304321213358703911 80581956481820038055867)
        ·
          refine ⟨120872934722730057083801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80581956481820038055867 120872934722730057083801)
          ·
            refine ⟨90654701042047542812851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120872934722730057083801 90654701042047542812851)
            ·
              refine ⟨135982051563071314219277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90654701042047542812851 135982051563071314219277)
              ·
                refine ⟨50993269336151742832229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135982051563071314219277 50993269336151742832229)
                ·
                  refine ⟨9561238000528451781043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50993269336151742832229 9561238000528451781043)
                  ·
                    refine ⟨14341857000792677671565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9561238000528451781043 14341857000792677671565)
                    ·
                      refine ⟨5378196375297254126837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 14341857000792677671565 5378196375297254126837)
                      ·
                        rfl

theorem cell23_10474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_10474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10474 prefixEnd_10474 := by exact prefixLift 10474
  have htrace : WordTrace (prefixWord ++ tailWord_10474) baseStart_10474 baseEnd_10474 := by
    simpa [prefixWord, tailWord_10474, baseEnd_10474] using wordTrace_append hprefix tailTrace_10474
  have hstable : (prefixWord ++ tailWord_10474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10474).length < 2 ^ (prefixWord ++ tailWord_10474).sum := by decide
  have hdescent : baseEnd_10474 < baseStart_10474 := by decide
  rcases family_descends (prefixWord ++ tailWord_10474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10517 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_10517 : Nat := 118140960795 + 10517 * 2 ^ 59
def prefixEnd_10517 : Nat := 4983230072969 + 3 ^ 40 * 10517 * 2
def baseEnd_10517 : Nat := 5400276043440585889139

theorem tailTrace_10517 : CollatzResearch.WordTrace tailWord_10517 prefixEnd_10517 5400276043440585889139 := by
  unfold tailWord_10517
  simp only [CollatzResearch.WordTrace]
  refine ⟨383586502906180005709805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 255724335270786670473203 383586502906180005709805)
  ·
    refine ⟨143844938589817502141177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 383586502906180005709805 143844938589817502141177)
    ·
      refine ⟨107883703942363126605883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143844938589817502141177 107883703942363126605883)
      ·
        refine ⟨161825555913544689908825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107883703942363126605883 161825555913544689908825)
        ·
          refine ⟨121369166935158517431619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161825555913544689908825 121369166935158517431619)
          ·
            refine ⟨182053750402737776147429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121369166935158517431619 182053750402737776147429)
            ·
              refine ⟨34135078200513333027643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182053750402737776147429 34135078200513333027643)
              ·
                refine ⟨51202617300769999541465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34135078200513333027643 51202617300769999541465)
                ·
                  refine ⟨38401962975577499656099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51202617300769999541465 38401962975577499656099)
                  ·
                    refine ⟨57602944463366249484149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38401962975577499656099 57602944463366249484149)
                    ·
                      refine ⟨5400276043440585889139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 57602944463366249484149 5400276043440585889139)
                      ·
                        rfl

theorem cell23_10517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_10517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10517 prefixEnd_10517 := by exact prefixLift 10517
  have htrace : WordTrace (prefixWord ++ tailWord_10517) baseStart_10517 baseEnd_10517 := by
    simpa [prefixWord, tailWord_10517, baseEnd_10517] using wordTrace_append hprefix tailTrace_10517
  have hstable : (prefixWord ++ tailWord_10517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10517).length < 2 ^ (prefixWord ++ tailWord_10517).sum := by decide
  have hdescent : baseEnd_10517 < baseStart_10517 := by decide
  rcases family_descends (prefixWord ++ tailWord_10517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10541 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_10541 : Nat := 118140960795 + 10541 * 2 ^ 59
def prefixEnd_10541 : Nat := 4983230072969 + 3 ^ 40 * 10541 * 2
def baseEnd_10541 : Nat := 1804199859716163996343

theorem tailTrace_10541 : CollatzResearch.WordTrace tailWord_10541 prefixEnd_10541 1804199859716163996343 := by
  unfold tailWord_10541
  simp only [CollatzResearch.WordTrace]
  refine ⟨384461854819232104583477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 256307903212821403055651 384461854819232104583477)
  ·
    refine ⟨36043298889303009804701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 384461854819232104583477 36043298889303009804701)
    ·
      refine ⟨13516237083488628676763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36043298889303009804701 13516237083488628676763)
      ·
        refine ⟨20274355625232943015145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13516237083488628676763 20274355625232943015145)
        ·
          refine ⟨15205766718924707261359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20274355625232943015145 15205766718924707261359)
          ·
            refine ⟨22808650078387060892039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15205766718924707261359 22808650078387060892039)
            ·
              refine ⟨34212975117580591338059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22808650078387060892039 34212975117580591338059)
              ·
                refine ⟨51319462676370887007089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34212975117580591338059 51319462676370887007089)
                ·
                  refine ⟨38489597007278165255317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51319462676370887007089 38489597007278165255317)
                  ·
                    refine ⟨1804199859716163996343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38489597007278165255317 1804199859716163996343)
                    ·
                      rfl

theorem cell23_10541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_10541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10541 prefixEnd_10541 := by exact prefixLift 10541
  have htrace : WordTrace (prefixWord ++ tailWord_10541) baseStart_10541 baseEnd_10541 := by
    simpa [prefixWord, tailWord_10541, baseEnd_10541] using wordTrace_append hprefix tailTrace_10541
  have hstable : (prefixWord ++ tailWord_10541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10541).length < 2 ^ (prefixWord ++ tailWord_10541).sum := by decide
  have hdescent : baseEnd_10541 < baseStart_10541 := by decide
  rcases family_descends (prefixWord ++ tailWord_10541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10548 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_10548 : Nat := 118140960795 + 10548 * 2 ^ 59
def prefixEnd_10548 : Nat := 4983230072969 + 3 ^ 40 * 10548 * 2
def baseEnd_10548 : Nat := 5416193943729964601497

theorem tailTrace_10548 : CollatzResearch.WordTrace tailWord_10548 prefixEnd_10548 5416193943729964601497 := by
  unfold tailWord_10548
  simp only [CollatzResearch.WordTrace]
  refine ⟨192358582896936150044149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 256478110529248200058865 192358582896936150044149)
  ·
    refine ⟨18033617146587764066639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192358582896936150044149 18033617146587764066639)
    ·
      refine ⟨27050425719881646099959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18033617146587764066639 27050425719881646099959)
      ·
        refine ⟨40575638579822469149939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27050425719881646099959 40575638579822469149939)
        ·
          refine ⟨60863457869733703724909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40575638579822469149939 60863457869733703724909)
          ·
            refine ⟨22823796701150138896841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60863457869733703724909 22823796701150138896841)
            ·
              refine ⟨17117847525862604172631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22823796701150138896841 17117847525862604172631)
              ·
                refine ⟨25676771288793906258947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17117847525862604172631 25676771288793906258947)
                ·
                  refine ⟨38515156933190859388421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25676771288793906258947 38515156933190859388421)
                  ·
                    refine ⟨7221591924973286135329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38515156933190859388421 7221591924973286135329)
                    ·
                      refine ⟨5416193943729964601497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7221591924973286135329 5416193943729964601497)
                      ·
                        rfl

theorem cell23_10548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_10548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10548 prefixEnd_10548 := by exact prefixLift 10548
  have htrace : WordTrace (prefixWord ++ tailWord_10548) baseStart_10548 baseEnd_10548 := by
    simpa [prefixWord, tailWord_10548, baseEnd_10548] using wordTrace_append hprefix tailTrace_10548
  have hstable : (prefixWord ++ tailWord_10548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10548).length < 2 ^ (prefixWord ++ tailWord_10548).sum := by decide
  have hdescent : baseEnd_10548 < baseStart_10548 := by decide
  rcases family_descends (prefixWord ++ tailWord_10548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10567 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 1, 7]
def baseStart_10567 : Nat := 118140960795 + 10567 * 2 ^ 59
def prefixEnd_10567 : Nat := 4983230072969 + 3 ^ 40 * 10567 * 2
def baseEnd_10567 : Nat := 1808650025388463421303

theorem tailTrace_10567 : CollatzResearch.WordTrace tailWord_10567 prefixEnd_10567 1808650025388463421303 := by
  unfold tailWord_10567
  simp only [CollatzResearch.WordTrace]
  refine ⟨385410152725038545029955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 256940101816692363353303 385410152725038545029955)
  ·
    refine ⟨578115229087557817544933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 385410152725038545029955 578115229087557817544933)
    ·
      refine ⟨108396605453917090789675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 578115229087557817544933 108396605453917090789675)
      ·
        refine ⟨162594908180875636184513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108396605453917090789675 162594908180875636184513)
        ·
          refine ⟨121946181135656727138385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162594908180875636184513 121946181135656727138385)
          ·
            refine ⟨91459635851742545353789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121946181135656727138385 91459635851742545353789)
            ·
              refine ⟨34297363444403454507671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91459635851742545353789 34297363444403454507671)
              ·
                refine ⟨51446045166605181761507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34297363444403454507671 51446045166605181761507)
                ·
                  refine ⟨77169067749907772642261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51446045166605181761507 77169067749907772642261)
                  ·
                    refine ⟨1808650025388463421303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 77169067749907772642261 1808650025388463421303)
                    ·
                      rfl

theorem cell23_10567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_10567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10567 prefixEnd_10567 := by exact prefixLift 10567
  have htrace : WordTrace (prefixWord ++ tailWord_10567) baseStart_10567 baseEnd_10567 := by
    simpa [prefixWord, tailWord_10567, baseEnd_10567] using wordTrace_append hprefix tailTrace_10567
  have hstable : (prefixWord ++ tailWord_10567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10567).length < 2 ^ (prefixWord ++ tailWord_10567).sum := by decide
  have hdescent : baseEnd_10567 < baseStart_10567 := by decide
  rcases family_descends (prefixWord ++ tailWord_10567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10574 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_10574 : Nat := 118140960795 + 10574 * 2 ^ 59
def prefixEnd_10574 : Nat := 4983230072969 + 3 ^ 40 * 10574 * 2
def baseEnd_10574 : Nat := 5429544440746862876377

theorem tailTrace_10574 : CollatzResearch.WordTrace tailWord_10574 prefixEnd_10574 5429544440746862876377 := by
  unfold tailWord_10574
  simp only [CollatzResearch.WordTrace]
  refine ⟨48208182962459842566847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 257110309133119160356517 48208182962459842566847)
  ·
    refine ⟨72312274443689763850271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48208182962459842566847 72312274443689763850271)
    ·
      refine ⟨108468411665534645775407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72312274443689763850271 108468411665534645775407)
      ·
        refine ⟨162702617498301968663111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108468411665534645775407 162702617498301968663111)
        ·
          refine ⟨244053926247452952994667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162702617498301968663111 244053926247452952994667)
          ·
            refine ⟨366080889371179429492001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244053926247452952994667 366080889371179429492001)
            ·
              refine ⟨274560667028384572119001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366080889371179429492001 274560667028384572119001)
              ·
                refine ⟨205920500271288429089251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274560667028384572119001 205920500271288429089251)
                ·
                  refine ⟨308880750406932643633877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205920500271288429089251 308880750406932643633877)
                  ·
                    refine ⟨7239392587662483835169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 308880750406932643633877 7239392587662483835169)
                    ·
                      refine ⟨5429544440746862876377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7239392587662483835169 5429544440746862876377)
                      ·
                        rfl

theorem cell23_10574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_10574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10574 prefixEnd_10574 := by exact prefixLift 10574
  have htrace : WordTrace (prefixWord ++ tailWord_10574) baseStart_10574 baseEnd_10574 := by
    simpa [prefixWord, tailWord_10574, baseEnd_10574] using wordTrace_append hprefix tailTrace_10574
  have hstable : (prefixWord ++ tailWord_10574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10574).length < 2 ^ (prefixWord ++ tailWord_10574).sum := by decide
  have hdescent : baseEnd_10574 < baseStart_10574 := by decide
  rcases family_descends (prefixWord ++ tailWord_10574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10617 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_10617 : Nat := 118140960795 + 10617 * 2 ^ 59
def prefixEnd_10617 : Nat := 4983230072969 + 3 ^ 40 * 10617 * 2
def baseEnd_10617 : Nat := 5451624108890194638679

theorem tailTrace_10617 : CollatzResearch.WordTrace tailWord_10617 prefixEnd_10617 5451624108890194638679 := by
  unfold tailWord_10617
  simp only [CollatzResearch.WordTrace]
  refine ⟨387233802543897084350105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 258155868362598056233403 387233802543897084350105)
  ·
    refine ⟨290425351907922813262579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 387233802543897084350105 290425351907922813262579)
    ·
      refine ⟨435638027861884219893869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290425351907922813262579 435638027861884219893869)
      ·
        refine ⟨163364260448206582460201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435638027861884219893869 163364260448206582460201)
        ·
          refine ⟨122523195336154936845151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163364260448206582460201 122523195336154936845151)
          ·
            refine ⟨183784793004232405267727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122523195336154936845151 183784793004232405267727)
            ·
              refine ⟨275677189506348607901591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183784793004232405267727 275677189506348607901591)
              ·
                refine ⟨413515784259522911852387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275677189506348607901591 413515784259522911852387)
                ·
                  refine ⟨620273676389284367778581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413515784259522911852387 620273676389284367778581)
                  ·
                    refine ⟨29075328580747704739621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 620273676389284367778581 29075328580747704739621)
                    ·
                      refine ⟨5451624108890194638679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 29075328580747704739621 5451624108890194638679)
                      ·
                        rfl

theorem cell23_10617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_10617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10617 prefixEnd_10617 := by exact prefixLift 10617
  have htrace : WordTrace (prefixWord ++ tailWord_10617) baseStart_10617 baseEnd_10617 := by
    simpa [prefixWord, tailWord_10617, baseEnd_10617] using wordTrace_append hprefix tailTrace_10617
  have hstable : (prefixWord ++ tailWord_10617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10617).length < 2 ^ (prefixWord ++ tailWord_10617).sum := by decide
  have hdescent : baseEnd_10617 < baseStart_10617 := by decide
  rcases family_descends (prefixWord ++ tailWord_10617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10647 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_10647 : Nat := 118140960795 + 10647 * 2 ^ 59
def prefixEnd_10647 : Nat := 4983230072969 + 3 ^ 40 * 10647 * 2
def baseEnd_10647 : Nat := 5467028528525077263541

theorem tailTrace_10647 : CollatzResearch.WordTrace tailWord_10647 prefixEnd_10647 5467028528525077263541 := by
  unfold tailWord_10647
  simp only [CollatzResearch.WordTrace]
  refine ⟨388327992435212207942195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 258885328290141471961463 388327992435212207942195)
  ·
    refine ⟨582491988652818311913293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 388327992435212207942195 582491988652818311913293)
    ·
      refine ⟨218434495744806866967485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 582491988652818311913293 218434495744806866967485)
      ·
        refine ⟨81912935904302575112807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218434495744806866967485 81912935904302575112807)
        ·
          refine ⟨122869403856453862669211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81912935904302575112807 122869403856453862669211)
          ·
            refine ⟨184304105784680794003817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122869403856453862669211 184304105784680794003817)
            ·
              refine ⟨138228079338510595502863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184304105784680794003817 138228079338510595502863)
              ·
                refine ⟨207342119007765893254295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138228079338510595502863 207342119007765893254295)
                ·
                  refine ⟨311013178511648839881443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207342119007765893254295 311013178511648839881443)
                  ·
                    refine ⟨466519767767473259822165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 311013178511648839881443 466519767767473259822165)
                    ·
                      refine ⟨5467028528525077263541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 466519767767473259822165 5467028528525077263541)
                      ·
                        rfl

theorem cell23_10647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_10647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10647 prefixEnd_10647 := by exact prefixLift 10647
  have htrace : WordTrace (prefixWord ++ tailWord_10647) baseStart_10647 baseEnd_10647 := by
    simpa [prefixWord, tailWord_10647, baseEnd_10647] using wordTrace_append hprefix tailTrace_10647
  have hstable : (prefixWord ++ tailWord_10647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10647).length < 2 ^ (prefixWord ++ tailWord_10647).sum := by decide
  have hdescent : baseEnd_10647 < baseStart_10647 := by decide
  rcases family_descends (prefixWord ++ tailWord_10647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10648 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 3, 4]
def baseStart_10648 : Nat := 118140960795 + 10648 * 2 ^ 59
def prefixEnd_10648 : Nat := 4983230072969 + 3 ^ 40 * 10648 * 2
def baseEnd_10648 : Nat := 1822514003059857783679

theorem tailTrace_10648 : CollatzResearch.WordTrace tailWord_10648 prefixEnd_10648 1822514003059857783679 := by
  unfold tailWord_10648
  simp only [CollatzResearch.WordTrace]
  refine ⟨194182232715794689364299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 258909643621059585819065 194182232715794689364299)
  ·
    refine ⟨291273349073692034046449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194182232715794689364299 291273349073692034046449)
    ·
      refine ⟨218455011805269025534837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291273349073692034046449 218455011805269025534837)
      ·
        refine ⟨20480157356743971143891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218455011805269025534837 20480157356743971143891)
        ·
          refine ⟨30720236035115956715837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20480157356743971143891 30720236035115956715837)
          ·
            refine ⟨11520088513168483768439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30720236035115956715837 11520088513168483768439)
            ·
              refine ⟨17280132769752725652659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11520088513168483768439 17280132769752725652659)
              ·
                refine ⟨25920199154629088478989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17280132769752725652659 25920199154629088478989)
                ·
                  refine ⟨9720074682985908179621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25920199154629088478989 9720074682985908179621)
                  ·
                    refine ⟨1822514003059857783679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9720074682985908179621 1822514003059857783679)
                    ·
                      rfl

theorem cell23_10648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_10648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10648 prefixEnd_10648 := by exact prefixLift 10648
  have htrace : WordTrace (prefixWord ++ tailWord_10648) baseStart_10648 baseEnd_10648 := by
    simpa [prefixWord, tailWord_10648, baseEnd_10648] using wordTrace_append hprefix tailTrace_10648
  have hstable : (prefixWord ++ tailWord_10648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10648).length < 2 ^ (prefixWord ++ tailWord_10648).sum := by decide
  have hdescent : baseEnd_10648 < baseStart_10648 := by decide
  rcases family_descends (prefixWord ++ tailWord_10648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10674 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_10674 : Nat := 118140960795 + 10674 * 2 ^ 59
def prefixEnd_10674 : Nat := 4983230072969 + 3 ^ 40 * 10674 * 2
def baseEnd_10674 : Nat := 1826964168732157208639

theorem tailTrace_10674 : CollatzResearch.WordTrace tailWord_10674 prefixEnd_10674 1826964168732157208639 := by
  unfold tailWord_10674
  simp only [CollatzResearch.WordTrace]
  refine ⟨97328190834348954793769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 259541842224930546116717 97328190834348954793769)
  ·
    refine ⟨72996143125761716095327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97328190834348954793769 72996143125761716095327)
    ·
      refine ⟨109494214688642574142991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72996143125761716095327 109494214688642574142991)
      ·
        refine ⟨164241322032963861214487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109494214688642574142991 164241322032963861214487)
        ·
          refine ⟨246361983049445791821731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164241322032963861214487 246361983049445791821731)
          ·
            refine ⟨369542974574168687732597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246361983049445791821731 369542974574168687732597)
            ·
              refine ⟨34644653866328314474931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 369542974574168687732597 34644653866328314474931)
              ·
                refine ⟨51966980799492471712397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34644653866328314474931 51966980799492471712397)
                ·
                  refine ⟨19487617799809676892149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51966980799492471712397 19487617799809676892149)
                  ·
                    refine ⟨1826964168732157208639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19487617799809676892149 1826964168732157208639)
                    ·
                      rfl

theorem cell23_10674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_10674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10674 prefixEnd_10674 := by exact prefixLift 10674
  have htrace : WordTrace (prefixWord ++ tailWord_10674) baseStart_10674 baseEnd_10674 := by
    simpa [prefixWord, tailWord_10674, baseEnd_10674] using wordTrace_append hprefix tailTrace_10674
  have hstable : (prefixWord ++ tailWord_10674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10674).length < 2 ^ (prefixWord ++ tailWord_10674).sum := by decide
  have hdescent : baseEnd_10674 < baseStart_10674 := by decide
  rcases family_descends (prefixWord ++ tailWord_10674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10688 : List Nat := [2, 1, 1, 2, 3, 1, 1, 7, 1, 1, 3]
def baseStart_10688 : Nat := 118140960795 + 10688 * 2 ^ 59
def prefixEnd_10688 : Nat := 4983230072969 + 3 ^ 40 * 10688 * 2
def baseEnd_10688 : Nat := 5488081235359416850853

theorem tailTrace_10688 : CollatzResearch.WordTrace tailWord_10688 prefixEnd_10688 5488081235359416850853 := by
  unfold tailWord_10688
  simp only [CollatzResearch.WordTrace]
  refine ⟨194911692643338105092359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 259882256857784140123145 194911692643338105092359)
  ·
    refine ⟨292367538965007157638539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194911692643338105092359 292367538965007157638539)
    ·
      refine ⟨438551308447510736457809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292367538965007157638539 438551308447510736457809)
      ·
        refine ⟨328913481335633052343357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438551308447510736457809 328913481335633052343357)
        ·
          refine ⟨123342555500862394628759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 328913481335633052343357 123342555500862394628759)
          ·
            refine ⟨185013833251293591943139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123342555500862394628759 185013833251293591943139)
            ·
              refine ⟨277520749876940387914709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185013833251293591943139 277520749876940387914709)
              ·
                refine ⟨6504392575240790341751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 277520749876940387914709 6504392575240790341751)
                ·
                  refine ⟨9756588862861185512627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6504392575240790341751 9756588862861185512627)
                  ·
                    refine ⟨14634883294291778268941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9756588862861185512627 14634883294291778268941)
                    ·
                      refine ⟨5488081235359416850853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 14634883294291778268941 5488081235359416850853)
                      ·
                        rfl

theorem cell23_10688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 1, 3].length) (baseStart_10688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10688 prefixEnd_10688 := by exact prefixLift 10688
  have htrace : WordTrace (prefixWord ++ tailWord_10688) baseStart_10688 baseEnd_10688 := by
    simpa [prefixWord, tailWord_10688, baseEnd_10688] using wordTrace_append hprefix tailTrace_10688
  have hstable : (prefixWord ++ tailWord_10688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10688).length < 2 ^ (prefixWord ++ tailWord_10688).sum := by decide
  have hdescent : baseEnd_10688 < baseStart_10688 := by decide
  rcases family_descends (prefixWord ++ tailWord_10688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10714 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_10714 : Nat := 118140960795 + 10714 * 2 ^ 59
def prefixEnd_10714 : Nat := 4983230072969 + 3 ^ 40 * 10714 * 2
def baseEnd_10714 : Nat := 5501431732376315125733

theorem tailTrace_10714 : CollatzResearch.WordTrace tailWord_10714 prefixEnd_10714 5501431732376315125733 := by
  unfold tailWord_10714
  simp only [CollatzResearch.WordTrace]
  refine ⟨97692920798120662657799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 260514455461655100420797 97692920798120662657799)
  ·
    refine ⟨146539381197180993986699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97692920798120662657799 146539381197180993986699)
    ·
      refine ⟨219809071795771490980049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146539381197180993986699 219809071795771490980049)
      ·
        refine ⟨164856803846828618235037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219809071795771490980049 164856803846828618235037)
        ·
          refine ⟨61821301442560731838139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164856803846828618235037 61821301442560731838139)
          ·
            refine ⟨92731952163841097757209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61821301442560731838139 92731952163841097757209)
            ·
              refine ⟨69548964122880823317907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92731952163841097757209 69548964122880823317907)
              ·
                refine ⟨104323446184321234976861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69548964122880823317907 104323446184321234976861)
                ·
                  refine ⟨39121292319120463116323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104323446184321234976861 39121292319120463116323)
                  ·
                    refine ⟨58681938478680694674485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39121292319120463116323 58681938478680694674485)
                    ·
                      refine ⟨5501431732376315125733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 58681938478680694674485 5501431732376315125733)
                      ·
                        rfl

theorem cell23_10714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_10714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10714 prefixEnd_10714 := by exact prefixLift 10714
  have htrace : WordTrace (prefixWord ++ tailWord_10714) baseStart_10714 baseEnd_10714 := by
    simpa [prefixWord, tailWord_10714, baseEnd_10714] using wordTrace_append hprefix tailTrace_10714
  have hstable : (prefixWord ++ tailWord_10714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10714).length < 2 ^ (prefixWord ++ tailWord_10714).sum := by decide
  have hdescent : baseEnd_10714 < baseStart_10714 := by decide
  rcases family_descends (prefixWord ++ tailWord_10714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10721 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 2, 4]
def baseStart_10721 : Nat := 118140960795 + 10721 * 2 ^ 59
def prefixEnd_10721 : Nat := 4983230072969 + 3 ^ 40 * 10721 * 2
def baseEnd_10721 : Nat := 1835008698985929246067

theorem tailTrace_10721 : CollatzResearch.WordTrace tailWord_10721 prefixEnd_10721 1835008698985929246067 := by
  unfold tailWord_10721
  simp only [CollatzResearch.WordTrace]
  refine ⟨391026994167122846136017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 260684662778081897424011 391026994167122846136017)
  ·
    refine ⟨293270245625342134602013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 391026994167122846136017 293270245625342134602013)
    ·
      refine ⟨109976342109503300475755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293270245625342134602013 109976342109503300475755)
      ·
        refine ⟨164964513164254950713633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109976342109503300475755 164964513164254950713633)
        ·
          refine ⟨123723384873191213035225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164964513164254950713633 123723384873191213035225)
          ·
            refine ⟨92792538654893409776419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123723384873191213035225 92792538654893409776419)
            ·
              refine ⟨139188807982340114664629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92792538654893409776419 139188807982340114664629)
              ·
                refine ⟨13048950748344385749809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139188807982340114664629 13048950748344385749809)
                ·
                  refine ⟨9786713061258289312357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13048950748344385749809 9786713061258289312357)
                  ·
                    refine ⟨1835008698985929246067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9786713061258289312357 1835008698985929246067)
                    ·
                      rfl

theorem cell23_10721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_10721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10721 prefixEnd_10721 := by exact prefixLift 10721
  have htrace : WordTrace (prefixWord ++ tailWord_10721) baseStart_10721 baseEnd_10721 := by
    simpa [prefixWord, tailWord_10721, baseEnd_10721] using wordTrace_append hprefix tailTrace_10721
  have hstable : (prefixWord ++ tailWord_10721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10721).length < 2 ^ (prefixWord ++ tailWord_10721).sum := by decide
  have hdescent : baseEnd_10721 < baseStart_10721 := by decide
  rcases family_descends (prefixWord ++ tailWord_10721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10722 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_10722 : Nat := 118140960795 + 10722 * 2 ^ 59
def prefixEnd_10722 : Nat := 4983230072969 + 3 ^ 40 * 10722 * 2
def baseEnd_10722 : Nat := 5505539577612283825697

theorem tailTrace_10722 : CollatzResearch.WordTrace tailWord_10722 prefixEnd_10722 5505539577612283825697 := by
  unfold tailWord_10722
  simp only [CollatzResearch.WordTrace]
  refine ⟨97765866790875004230605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 260708978109000011281613 97765866790875004230605)
  ·
    refine ⟨36662200046578126586477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97765866790875004230605 36662200046578126586477)
    ·
      refine ⟨13748325017466797469929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36662200046578126586477 13748325017466797469929)
      ·
        refine ⟨10311243763100098102447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13748325017466797469929 10311243763100098102447)
        ·
          refine ⟨15466865644650147153671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10311243763100098102447 15466865644650147153671)
          ·
            refine ⟨23200298466975220730507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15466865644650147153671 23200298466975220730507)
            ·
              refine ⟨34800447700462831095761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23200298466975220730507 34800447700462831095761)
              ·
                refine ⟨26100335775347123321821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34800447700462831095761 26100335775347123321821)
                ·
                  refine ⟨9787625915755171245683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26100335775347123321821 9787625915755171245683)
                  ·
                    refine ⟨14681438873632756868525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9787625915755171245683 14681438873632756868525)
                    ·
                      refine ⟨5505539577612283825697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 14681438873632756868525 5505539577612283825697)
                      ·
                        rfl

theorem cell23_10722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_10722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10722 prefixEnd_10722 := by exact prefixLift 10722
  have htrace : WordTrace (prefixWord ++ tailWord_10722) baseStart_10722 baseEnd_10722 := by
    simpa [prefixWord, tailWord_10722, baseEnd_10722] using wordTrace_append hprefix tailTrace_10722
  have hstable : (prefixWord ++ tailWord_10722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10722).length < 2 ^ (prefixWord ++ tailWord_10722).sum := by decide
  have hdescent : baseEnd_10722 < baseStart_10722 := by decide
  rcases family_descends (prefixWord ++ tailWord_10722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10728 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_10728 : Nat := 118140960795 + 10728 * 2 ^ 59
def prefixEnd_10728 : Nat := 4983230072969 + 3 ^ 40 * 10728 * 2
def baseEnd_10728 : Nat := 5508620461539260350669

theorem tailTrace_10728 : CollatzResearch.WordTrace tailWord_10728 prefixEnd_10728 5508620461539260350669 := by
  unfold tailWord_10728
  simp only [CollatzResearch.WordTrace]
  refine ⟨195641152570881520820419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 260854870094508694427225 195641152570881520820419)
  ·
    refine ⟨293461728856322281230629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195641152570881520820419 293461728856322281230629)
    ·
      refine ⟨55024074160560427730743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293461728856322281230629 55024074160560427730743)
      ·
        refine ⟨82536111240840641596115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55024074160560427730743 82536111240840641596115)
        ·
          refine ⟨123804166861260962394173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82536111240840641596115 123804166861260962394173)
          ·
            refine ⟨46426562572972860897815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123804166861260962394173 46426562572972860897815)
            ·
              refine ⟨69639843859459291346723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46426562572972860897815 69639843859459291346723)
              ·
                refine ⟨104459765789188937020085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69639843859459291346723 104459765789188937020085)
                ·
                  refine ⟨9793103042736462845633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104459765789188937020085 9793103042736462845633)
                  ·
                    refine ⟨7344827282052347134225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9793103042736462845633 7344827282052347134225)
                    ·
                      refine ⟨5508620461539260350669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7344827282052347134225 5508620461539260350669)
                      ·
                        rfl

theorem cell23_10728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_10728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10728 prefixEnd_10728 := by exact prefixLift 10728
  have htrace : WordTrace (prefixWord ++ tailWord_10728) baseStart_10728 baseEnd_10728 := by
    simpa [prefixWord, tailWord_10728, baseEnd_10728] using wordTrace_append hprefix tailTrace_10728
  have hstable : (prefixWord ++ tailWord_10728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10728).length < 2 ^ (prefixWord ++ tailWord_10728).sum := by decide
  have hdescent : baseEnd_10728 < baseStart_10728 := by decide
  rcases family_descends (prefixWord ++ tailWord_10728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10731 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 3]
def baseStart_10731 : Nat := 118140960795 + 10731 * 2 ^ 59
def prefixEnd_10731 : Nat := 4983230072969 + 3 ^ 40 * 10731 * 2
def baseEnd_10731 : Nat := 5510160903502748613155

theorem tailTrace_10731 : CollatzResearch.WordTrace tailWord_10731 prefixEnd_10731 5510160903502748613155 := by
  unfold tailWord_10731
  simp only [CollatzResearch.WordTrace]
  refine ⟨391391724130894554000047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 260927816087263036000031 391391724130894554000047)
  ·
    refine ⟨587087586196341831000071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391391724130894554000047 587087586196341831000071)
    ·
      refine ⟨880631379294512746500107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 587087586196341831000071 880631379294512746500107)
      ·
        refine ⟨1320947068941769119750161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880631379294512746500107 1320947068941769119750161)
        ·
          refine ⟨990710301706326839812621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320947068941769119750161 990710301706326839812621)
          ·
            refine ⟨371516363139872564929733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 990710301706326839812621 371516363139872564929733)
            ·
              refine ⟨69659318088726105924325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 371516363139872564929733 69659318088726105924325)
              ·
                refine ⟨13061122141636144860811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69659318088726105924325 13061122141636144860811)
                ·
                  refine ⟨19591683212454217291217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13061122141636144860811 19591683212454217291217)
                  ·
                    refine ⟨14693762409340662968413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19591683212454217291217 14693762409340662968413)
                    ·
                      refine ⟨5510160903502748613155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 14693762409340662968413 5510160903502748613155)
                      ·
                        rfl

theorem cell23_10731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 3].length) (baseStart_10731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10731 prefixEnd_10731 := by exact prefixLift 10731
  have htrace : WordTrace (prefixWord ++ tailWord_10731) baseStart_10731 baseEnd_10731 := by
    simpa [prefixWord, tailWord_10731, baseEnd_10731] using wordTrace_append hprefix tailTrace_10731
  have hstable : (prefixWord ++ tailWord_10731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10731).length < 2 ^ (prefixWord ++ tailWord_10731).sum := by decide
  have hdescent : baseEnd_10731 < baseStart_10731 := by decide
  rcases family_descends (prefixWord ++ tailWord_10731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10745 : List Nat := [1, 2, 1, 3, 1, 2, 3, 5, 1, 2, 2]
def baseStart_10745 : Nat := 118140960795 + 10745 * 2 ^ 59
def prefixEnd_10745 : Nat := 4983230072969 + 3 ^ 40 * 10745 * 2
def baseEnd_10745 : Nat := 5517349632665693838091

theorem tailTrace_10745 : CollatzResearch.WordTrace tailWord_10745 prefixEnd_10745 5517349632665693838091 := by
  unfold tailWord_10745
  simp only [CollatzResearch.WordTrace]
  refine ⟨391902346080174945009689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 261268230720116630006459 391902346080174945009689)
  ·
    refine ⟨293926759560131208757267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 391902346080174945009689 293926759560131208757267)
    ·
      refine ⟨440890139340196813135901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293926759560131208757267 440890139340196813135901)
      ·
        refine ⟨165333802252573804925963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 440890139340196813135901 165333802252573804925963)
        ·
          refine ⟨248000703378860707388945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165333802252573804925963 248000703378860707388945)
          ·
            refine ⟨186000527534145530541709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248000703378860707388945 186000527534145530541709)
            ·
              refine ⟨69750197825304573953141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186000527534145530541709 69750197825304573953141)
              ·
                refine ⟨6539081046122303808107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69750197825304573953141 6539081046122303808107)
                ·
                  refine ⟨9808621569183455712161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6539081046122303808107 9808621569183455712161)
                  ·
                    refine ⟨7356466176887591784121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9808621569183455712161 7356466176887591784121)
                    ·
                      refine ⟨5517349632665693838091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7356466176887591784121 5517349632665693838091)
                      ·
                        rfl

theorem cell23_10745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_10745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10745 prefixEnd_10745 := by exact prefixLift 10745
  have htrace : WordTrace (prefixWord ++ tailWord_10745) baseStart_10745 baseEnd_10745 := by
    simpa [prefixWord, tailWord_10745, baseEnd_10745] using wordTrace_append hprefix tailTrace_10745
  have hstable : (prefixWord ++ tailWord_10745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10745).length < 2 ^ (prefixWord ++ tailWord_10745).sum := by decide
  have hdescent : baseEnd_10745 < baseStart_10745 := by decide
  rcases family_descends (prefixWord ++ tailWord_10745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10765 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_10765 : Nat := 118140960795 + 10765 * 2 ^ 59
def prefixEnd_10765 : Nat := 4983230072969 + 3 ^ 40 * 10765 * 2
def baseEnd_10765 : Nat := 5527619245755615587999

theorem tailTrace_10765 : CollatzResearch.WordTrace tailWord_10765 prefixEnd_10765 5527619245755615587999 := by
  unfold tailWord_10765
  simp only [CollatzResearch.WordTrace]
  refine ⟨392631806007718360737749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 261754537338478907158499 392631806007718360737749)
  ·
    refine ⟨9202307953305899079791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 392631806007718360737749 9202307953305899079791)
    ·
      refine ⟨13803461929958848619687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9202307953305899079791 13803461929958848619687)
      ·
        refine ⟨20705192894938272929531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13803461929958848619687 20705192894938272929531)
        ·
          refine ⟨31057789342407409394297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20705192894938272929531 31057789342407409394297)
          ·
            refine ⟨23293342006805557045723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31057789342407409394297 23293342006805557045723)
            ·
              refine ⟨34940013010208335568585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23293342006805557045723 34940013010208335568585)
              ·
                refine ⟨26205009757656251676439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34940013010208335568585 26205009757656251676439)
                ·
                  refine ⟨39307514636484377514659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26205009757656251676439 39307514636484377514659)
                  ·
                    refine ⟨58961271954726566271989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39307514636484377514659 58961271954726566271989)
                    ·
                      refine ⟨5527619245755615587999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 58961271954726566271989 5527619245755615587999)
                      ·
                        rfl

theorem cell23_10765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_10765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10765 prefixEnd_10765 := by exact prefixLift 10765
  have htrace : WordTrace (prefixWord ++ tailWord_10765) baseStart_10765 baseEnd_10765 := by
    simpa [prefixWord, tailWord_10765, baseEnd_10765] using wordTrace_append hprefix tailTrace_10765
  have hstable : (prefixWord ++ tailWord_10765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10765).length < 2 ^ (prefixWord ++ tailWord_10765).sum := by decide
  have hdescent : baseEnd_10765 < baseStart_10765 := by decide
  rcases family_descends (prefixWord ++ tailWord_10765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10772 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_10772 : Nat := 118140960795 + 10772 * 2 ^ 59
def prefixEnd_10772 : Nat := 4983230072969 + 3 ^ 40 * 10772 * 2
def baseEnd_10772 : Nat := 1843737870112362733489

theorem tailTrace_10772 : CollatzResearch.WordTrace tailWord_10772 prefixEnd_10772 1843737870112362733489 := by
  unfold tailWord_10772
  simp only [CollatzResearch.WordTrace]
  refine ⟨196443558491179278121285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 261924744654905704161713 196443558491179278121285)
  ·
    refine ⟨36833167217096114647741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196443558491179278121285 36833167217096114647741)
    ·
      refine ⟨13812437706411042992903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36833167217096114647741 13812437706411042992903)
      ·
        refine ⟨20718656559616564489355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13812437706411042992903 20718656559616564489355)
        ·
          refine ⟨31077984839424846734033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20718656559616564489355 31077984839424846734033)
          ·
            refine ⟨23308488629568635050525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31077984839424846734033 23308488629568635050525)
            ·
              refine ⟨8740683236088238143947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23308488629568635050525 8740683236088238143947)
              ·
                refine ⟨13111024854132357215921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8740683236088238143947 13111024854132357215921)
                ·
                  refine ⟨9833268640599267911941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13111024854132357215921 9833268640599267911941)
                  ·
                    refine ⟨1843737870112362733489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9833268640599267911941 1843737870112362733489)
                    ·
                      rfl

theorem cell23_10772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_10772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10772 prefixEnd_10772 := by exact prefixLift 10772
  have htrace : WordTrace (prefixWord ++ tailWord_10772) baseStart_10772 baseEnd_10772 := by
    simpa [prefixWord, tailWord_10772, baseEnd_10772] using wordTrace_append hprefix tailTrace_10772
  have hstable : (prefixWord ++ tailWord_10772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10772).length < 2 ^ (prefixWord ++ tailWord_10772).sum := by decide
  have hdescent : baseEnd_10772 < baseStart_10772 := by decide
  rcases family_descends (prefixWord ++ tailWord_10772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10775 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 4]
def baseStart_10775 : Nat := 118140960795 + 10775 * 2 ^ 59
def prefixEnd_10775 : Nat := 4983230072969 + 3 ^ 40 * 10775 * 2
def baseEnd_10775 : Nat := 5532754052300576462953

theorem tailTrace_10775 : CollatzResearch.WordTrace tailWord_10775 prefixEnd_10775 5532754052300576462953 := by
  unfold tailWord_10775
  simp only [CollatzResearch.WordTrace]
  refine ⟨392996535971490068601779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 261997690647660045734519 392996535971490068601779)
  ·
    refine ⟨589494803957235102902669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 392996535971490068601779 589494803957235102902669)
    ·
      refine ⟨221060551483963163588501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 589494803957235102902669 221060551483963163588501)
      ·
        refine ⟨10362213350810773293211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 221060551483963163588501 10362213350810773293211)
        ·
          refine ⟨15543320026216159939817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10362213350810773293211 15543320026216159939817)
          ·
            refine ⟨11657490019662119954863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15543320026216159939817 11657490019662119954863)
            ·
              refine ⟨17486235029493179932295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11657490019662119954863 17486235029493179932295)
              ·
                refine ⟨26229352544239769898443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17486235029493179932295 26229352544239769898443)
                ·
                  refine ⟨39344028816359654847665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26229352544239769898443 39344028816359654847665)
                  ·
                    refine ⟨29508021612269741135749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39344028816359654847665 29508021612269741135749)
                    ·
                      refine ⟨5532754052300576462953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 29508021612269741135749 5532754052300576462953)
                      ·
                        rfl

theorem cell23_10775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_10775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10775 prefixEnd_10775 := by exact prefixLift 10775
  have htrace : WordTrace (prefixWord ++ tailWord_10775) baseStart_10775 baseEnd_10775 := by
    simpa [prefixWord, tailWord_10775, baseEnd_10775] using wordTrace_append hprefix tailTrace_10775
  have hstable : (prefixWord ++ tailWord_10775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10775).length < 2 ^ (prefixWord ++ tailWord_10775).sum := by decide
  have hdescent : baseEnd_10775 < baseStart_10775 := by decide
  rcases family_descends (prefixWord ++ tailWord_10775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10778 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3]
def baseStart_10778 : Nat := 118140960795 + 10778 * 2 ^ 59
def prefixEnd_10778 : Nat := 4983230072969 + 3 ^ 40 * 10778 * 2
def baseEnd_10778 : Nat := 5534294494264064725439

theorem tailTrace_10778 : CollatzResearch.WordTrace tailWord_10778 prefixEnd_10778 5534294494264064725439 := by
  unfold tailWord_10778
  simp only [CollatzResearch.WordTrace]
  refine ⟨98276488740155395240247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 262070636640414387307325 98276488740155395240247)
  ·
    refine ⟨147414733110233092860371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98276488740155395240247 147414733110233092860371)
    ·
      refine ⟨221122099665349639290557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147414733110233092860371 221122099665349639290557)
      ·
        refine ⟨82920787374506114733959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221122099665349639290557 82920787374506114733959)
        ·
          refine ⟨124381181061759172100939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82920787374506114733959 124381181061759172100939)
          ·
            refine ⟨186571771592638758151409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124381181061759172100939 186571771592638758151409)
            ·
              refine ⟨139928828694479068613557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186571771592638758151409 139928828694479068613557)
              ·
                refine ⟨13118327690107412682521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139928828694479068613557 13118327690107412682521)
                ·
                  refine ⟨9838745767580559511891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13118327690107412682521 9838745767580559511891)
                  ·
                    refine ⟨14758118651370839267837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9838745767580559511891 14758118651370839267837)
                    ·
                      refine ⟨5534294494264064725439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 14758118651370839267837 5534294494264064725439)
                      ·
                        rfl

theorem cell23_10778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_10778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10778 prefixEnd_10778 := by exact prefixLift 10778
  have htrace : WordTrace (prefixWord ++ tailWord_10778) baseStart_10778 baseEnd_10778 := by
    simpa [prefixWord, tailWord_10778, baseEnd_10778] using wordTrace_append hprefix tailTrace_10778
  have hstable : (prefixWord ++ tailWord_10778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10778).length < 2 ^ (prefixWord ++ tailWord_10778).sum := by decide
  have hdescent : baseEnd_10778 < baseStart_10778 := by decide
  rcases family_descends (prefixWord ++ tailWord_10778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10829 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_10829 : Nat := 118140960795 + 10829 * 2 ^ 59
def prefixEnd_10829 : Nat := 4983230072969 + 3 ^ 40 * 10829 * 2
def baseEnd_10829 : Nat := 5560482007643365187705

theorem tailTrace_10829 : CollatzResearch.WordTrace tailWord_10829 prefixEnd_10829 5560482007643365187705 := by
  unfold tailWord_10829
  simp only [CollatzResearch.WordTrace]
  refine ⟨394966077775857291067541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 263310718517238194045027 394966077775857291067541)
  ·
    refine ⟨18514034895743310518791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 394966077775857291067541 18514034895743310518791)
    ·
      refine ⟨27771052343614965778187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18514034895743310518791 27771052343614965778187)
      ·
        refine ⟨41656578515422448667281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27771052343614965778187 41656578515422448667281)
        ·
          refine ⟨31242433886566836500461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41656578515422448667281 31242433886566836500461)
          ·
            refine ⟨11715912707462563687673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31242433886566836500461 11715912707462563687673)
            ·
              refine ⟨8786934530596922765755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11715912707462563687673 8786934530596922765755)
              ·
                refine ⟨13180401795895384148633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8786934530596922765755 13180401795895384148633)
                ·
                  refine ⟨9885301346921538111475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13180401795895384148633 9885301346921538111475)
                  ·
                    refine ⟨14827952020382307167213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9885301346921538111475 14827952020382307167213)
                    ·
                      refine ⟨5560482007643365187705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 14827952020382307167213 5560482007643365187705)
                      ·
                        rfl

theorem cell23_10829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_10829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10829 prefixEnd_10829 := by exact prefixLift 10829
  have htrace : WordTrace (prefixWord ++ tailWord_10829) baseStart_10829 baseEnd_10829 := by
    simpa [prefixWord, tailWord_10829, baseEnd_10829] using wordTrace_append hprefix tailTrace_10829
  have hstable : (prefixWord ++ tailWord_10829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10829).length < 2 ^ (prefixWord ++ tailWord_10829).sum := by decide
  have hdescent : baseEnd_10829 < baseStart_10829 := by decide
  rcases family_descends (prefixWord ++ tailWord_10829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10858 : List Nat := [3, 1, 3, 2, 1, 1, 2, 5, 5]
def baseStart_10858 : Nat := 118140960795 + 10858 * 2 ^ 59
def prefixEnd_10858 : Nat := 4983230072969 + 3 ^ 40 * 10858 * 2
def baseEnd_10858 : Nat := 619485882958194636119

theorem tailTrace_10858 : CollatzResearch.WordTrace tailWord_10858 prefixEnd_10858 619485882958194636119 := by
  unfold tailWord_10858
  simp only [CollatzResearch.WordTrace]
  refine ⟨99005948667698810968307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 264015863113863495915485 99005948667698810968307)
  ·
    refine ⟨148508923001548216452461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99005948667698810968307 148508923001548216452461)
    ·
      refine ⟨55690846125580581169673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148508923001548216452461 55690846125580581169673)
      ·
        refine ⟨41768134594185435877255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55690846125580581169673 41768134594185435877255)
        ·
          refine ⟨62652201891278153815883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41768134594185435877255 62652201891278153815883)
          ·
            refine ⟨93978302836917230723825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62652201891278153815883 93978302836917230723825)
            ·
              refine ⟨70483727127687923042869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93978302836917230723825 70483727127687923042869)
              ·
                refine ⟨6607849418220742785269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70483727127687923042869 6607849418220742785269)
                ·
                  refine ⟨619485882958194636119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6607849418220742785269 619485882958194636119)
                  ·
                    rfl

theorem cell23_10858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_10858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10858 prefixEnd_10858 := by exact prefixLift 10858
  have htrace : WordTrace (prefixWord ++ tailWord_10858) baseStart_10858 baseEnd_10858 := by
    simpa [prefixWord, tailWord_10858, baseEnd_10858] using wordTrace_append hprefix tailTrace_10858
  have hstable : (prefixWord ++ tailWord_10858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10858).length < 2 ^ (prefixWord ++ tailWord_10858).sum := by decide
  have hdescent : baseEnd_10858 < baseStart_10858 := by decide
  rcases family_descends (prefixWord ++ tailWord_10858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10869 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_10869 : Nat := 118140960795 + 10869 * 2 ^ 59
def prefixEnd_10869 : Nat := 4983230072969 + 3 ^ 40 * 10869 * 2
def baseEnd_10869 : Nat := 5581021233823208687521

theorem tailTrace_10869 : CollatzResearch.WordTrace tailWord_10869 prefixEnd_10869 5581021233823208687521 := by
  unfold tailWord_10869
  simp only [CollatzResearch.WordTrace]
  refine ⟨396424997630944122523661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 264283331753962748349107 396424997630944122523661)
  ·
    refine ⟨148659374111604045946373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 396424997630944122523661 148659374111604045946373)
    ·
      refine ⟨27873632645925758614945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148659374111604045946373 27873632645925758614945)
      ·
        refine ⟨20905224484444318961209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27873632645925758614945 20905224484444318961209)
        ·
          refine ⟨15678918363333239220907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20905224484444318961209 15678918363333239220907)
          ·
            refine ⟨23518377544999858831361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15678918363333239220907 23518377544999858831361)
            ·
              refine ⟨17638783158749894123521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23518377544999858831361 17638783158749894123521)
              ·
                refine ⟨13229087369062420592641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17638783158749894123521 13229087369062420592641)
                ·
                  refine ⟨9921815526796815444481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13229087369062420592641 9921815526796815444481)
                  ·
                    refine ⟨7441361645097611583361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9921815526796815444481 7441361645097611583361)
                    ·
                      refine ⟨5581021233823208687521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7441361645097611583361 5581021233823208687521)
                      ·
                        rfl

theorem cell23_10869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_10869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10869 prefixEnd_10869 := by exact prefixLift 10869
  have htrace : WordTrace (prefixWord ++ tailWord_10869) baseStart_10869 baseEnd_10869 := by
    simpa [prefixWord, tailWord_10869, baseEnd_10869] using wordTrace_append hprefix tailTrace_10869
  have hstable : (prefixWord ++ tailWord_10869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10869).length < 2 ^ (prefixWord ++ tailWord_10869).sum := by decide
  have hdescent : baseEnd_10869 < baseStart_10869 := by decide
  rcases family_descends (prefixWord ++ tailWord_10869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10871 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 2, 5]
def baseStart_10871 : Nat := 118140960795 + 10871 * 2 ^ 59
def prefixEnd_10871 : Nat := 4983230072969 + 3 ^ 40 * 10871 * 2
def baseEnd_10871 : Nat := 1860682731710733620837

theorem tailTrace_10871 : CollatzResearch.WordTrace tailWord_10871 prefixEnd_10871 1860682731710733620837 := by
  unfold tailWord_10871
  simp only [CollatzResearch.WordTrace]
  refine ⟨396497943623698464096467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 264331962415798976064311 396497943623698464096467)
  ·
    refine ⟨594746915435547696144701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 396497943623698464096467 594746915435547696144701)
    ·
      refine ⟨223030093288330386054263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 594746915435547696144701 223030093288330386054263)
      ·
        refine ⟨334545139932495579081395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223030093288330386054263 334545139932495579081395)
        ·
          refine ⟨501817709898743368622093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334545139932495579081395 501817709898743368622093)
          ·
            refine ⟨188181641212028763233285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 501817709898743368622093 188181641212028763233285)
            ·
              refine ⟨35284057727255393106241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188181641212028763233285 35284057727255393106241)
              ·
                refine ⟨26463043295441544829681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35284057727255393106241 26463043295441544829681)
                ·
                  refine ⟨19847282471581158622261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26463043295441544829681 19847282471581158622261)
                  ·
                    refine ⟨1860682731710733620837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19847282471581158622261 1860682731710733620837)
                    ·
                      rfl

theorem cell23_10871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_10871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10871 prefixEnd_10871 := by exact prefixLift 10871
  have htrace : WordTrace (prefixWord ++ tailWord_10871) baseStart_10871 baseEnd_10871 := by
    simpa [prefixWord, tailWord_10871, baseEnd_10871] using wordTrace_append hprefix tailTrace_10871
  have hstable : (prefixWord ++ tailWord_10871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10871).length < 2 ^ (prefixWord ++ tailWord_10871).sum := by decide
  have hdescent : baseEnd_10871 < baseStart_10871 := by decide
  rcases family_descends (prefixWord ++ tailWord_10871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10881 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_10881 : Nat := 118140960795 + 10881 * 2 ^ 59
def prefixEnd_10881 : Nat := 4983230072969 + 3 ^ 40 * 10881 * 2
def baseEnd_10881 : Nat := 5587183001677161737465

theorem tailTrace_10881 : CollatzResearch.WordTrace tailWord_10881 prefixEnd_10881 5587183001677161737465 := by
  unfold tailWord_10881
  simp only [CollatzResearch.WordTrace]
  refine ⟨396862673587470171960497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 264575115724980114640331 396862673587470171960497)
  ·
    refine ⟨297647005190602628970373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 396862673587470171960497 297647005190602628970373)
    ·
      refine ⟨55808813473237992931945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297647005190602628970373 55808813473237992931945)
      ·
        refine ⟨41856610104928494698959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55808813473237992931945 41856610104928494698959)
        ·
          refine ⟨62784915157392742048439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41856610104928494698959 62784915157392742048439)
          ·
            refine ⟨94177372736089113072659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62784915157392742048439 94177372736089113072659)
            ·
              refine ⟨141266059104133669608989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94177372736089113072659 141266059104133669608989)
              ·
                refine ⟨52974772164050126103371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141266059104133669608989 52974772164050126103371)
                ·
                  refine ⟨79462158246075189155057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52974772164050126103371 79462158246075189155057)
                  ·
                    refine ⟨59596618684556391866293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79462158246075189155057 59596618684556391866293)
                    ·
                      refine ⟨5587183001677161737465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 59596618684556391866293 5587183001677161737465)
                      ·
                        rfl

theorem cell23_10881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_10881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10881 prefixEnd_10881 := by exact prefixLift 10881
  have htrace : WordTrace (prefixWord ++ tailWord_10881) baseStart_10881 baseEnd_10881 := by
    simpa [prefixWord, tailWord_10881, baseEnd_10881] using wordTrace_append hprefix tailTrace_10881
  have hstable : (prefixWord ++ tailWord_10881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10881).length < 2 ^ (prefixWord ++ tailWord_10881).sum := by decide
  have hdescent : baseEnd_10881 < baseStart_10881 := by decide
  rcases family_descends (prefixWord ++ tailWord_10881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10908 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_10908 : Nat := 118140960795 + 10908 * 2 ^ 59
def prefixEnd_10908 : Nat := 4983230072969 + 3 ^ 40 * 10908 * 2
def baseEnd_10908 : Nat := 5601046979348556099841

theorem tailTrace_10908 : CollatzResearch.WordTrace tailWord_10908 prefixEnd_10908 5601046979348556099841 := by
  unfold tailWord_10908
  simp only [CollatzResearch.WordTrace]
  refine ⟨198923722244826891596689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 265231629659769188795585 198923722244826891596689)
  ·
    refine ⟨149192791683620168697517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198923722244826891596689 149192791683620168697517)
    ·
      refine ⟨55947296881357563261569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149192791683620168697517 55947296881357563261569)
      ·
        refine ⟨41960472661018172446177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55947296881357563261569 41960472661018172446177)
        ·
          refine ⟨31470354495763629334633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41960472661018172446177 31470354495763629334633)
          ·
            refine ⟨23602765871822722000975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31470354495763629334633 23602765871822722000975)
            ·
              refine ⟨35404148807734083001463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23602765871822722000975 35404148807734083001463)
              ·
                refine ⟨53106223211601124502195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35404148807734083001463 53106223211601124502195)
                ·
                  refine ⟨79659334817401686753293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53106223211601124502195 79659334817401686753293)
                  ·
                    refine ⟨29872250556525632532485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79659334817401686753293 29872250556525632532485)
                    ·
                      refine ⟨5601046979348556099841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 29872250556525632532485 5601046979348556099841)
                      ·
                        rfl

theorem cell23_10908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_10908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10908 prefixEnd_10908 := by exact prefixLift 10908
  have htrace : WordTrace (prefixWord ++ tailWord_10908) baseStart_10908 baseEnd_10908 := by
    simpa [prefixWord, tailWord_10908, baseEnd_10908] using wordTrace_append hprefix tailTrace_10908
  have hstable : (prefixWord ++ tailWord_10908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10908).length < 2 ^ (prefixWord ++ tailWord_10908).sum := by decide
  have hdescent : baseEnd_10908 < baseStart_10908 := by decide
  rcases family_descends (prefixWord ++ tailWord_10908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10925 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_10925 : Nat := 118140960795 + 10925 * 2 ^ 59
def prefixEnd_10925 : Nat := 4983230072969 + 3 ^ 40 * 10925 * 2
def baseEnd_10925 : Nat := 5609776150474989587263

theorem tailTrace_10925 : CollatzResearch.WordTrace tailWord_10925 prefixEnd_10925 5609776150474989587263 := by
  unfold tailWord_10925
  simp only [CollatzResearch.WordTrace]
  refine ⟨398467485428065686562229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 265644990285377124374819 398467485428065686562229)
  ·
    refine ⟨37356326758881158115209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 398467485428065686562229 37356326758881158115209)
    ·
      refine ⟨28017245069160868586407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37356326758881158115209 28017245069160868586407)
      ·
        refine ⟨42025867603741302879611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28017245069160868586407 42025867603741302879611)
        ·
          refine ⟨63038801405611954319417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42025867603741302879611 63038801405611954319417)
          ·
            refine ⟨47279101054208965739563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63038801405611954319417 47279101054208965739563)
            ·
              refine ⟨70918651581313448609345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47279101054208965739563 70918651581313448609345)
              ·
                refine ⟨53188988685985086457009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70918651581313448609345 53188988685985086457009)
                ·
                  refine ⟨39891741514488814842757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53188988685985086457009 39891741514488814842757)
                  ·
                    refine ⟨7479701533966652783017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39891741514488814842757 7479701533966652783017)
                    ·
                      refine ⟨5609776150474989587263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7479701533966652783017 5609776150474989587263)
                      ·
                        rfl

theorem cell23_10925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_10925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10925 prefixEnd_10925 := by exact prefixLift 10925
  have htrace : WordTrace (prefixWord ++ tailWord_10925) baseStart_10925 baseEnd_10925 := by
    simpa [prefixWord, tailWord_10925, baseEnd_10925] using wordTrace_append hprefix tailTrace_10925
  have hstable : (prefixWord ++ tailWord_10925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10925).length < 2 ^ (prefixWord ++ tailWord_10925).sum := by decide
  have hdescent : baseEnd_10925 < baseStart_10925 := by decide
  rcases family_descends (prefixWord ++ tailWord_10925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10931 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 8]
def baseStart_10931 : Nat := 118140960795 + 10931 * 2 ^ 59
def prefixEnd_10931 : Nat := 4983230072969 + 3 ^ 40 * 10931 * 2
def baseEnd_10931 : Nat := 623650781600218456915

theorem tailTrace_10931 : CollatzResearch.WordTrace tailWord_10931 prefixEnd_10931 623650781600218456915 := by
  unfold tailWord_10931
  simp only [CollatzResearch.WordTrace]
  refine ⟨398686323406328711280647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 265790882270885807520431 398686323406328711280647)
  ·
    refine ⟨598029485109493066920971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 398686323406328711280647 598029485109493066920971)
    ·
      refine ⟨897044227664239600381457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598029485109493066920971 897044227664239600381457)
      ·
        refine ⟨672783170748179700286093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 897044227664239600381457 672783170748179700286093)
        ·
          refine ⟨252293689030567387607285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672783170748179700286093 252293689030567387607285)
          ·
            refine ⟨23652533346615692588183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252293689030567387607285 23652533346615692588183)
            ·
              refine ⟨35478800019923538882275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23652533346615692588183 35478800019923538882275)
              ·
                refine ⟨53218200029885308323413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35478800019923538882275 53218200029885308323413)
                ·
                  refine ⟨623650781600218456915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 53218200029885308323413 623650781600218456915)
                  ·
                    rfl

theorem cell23_10931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 8].length) (baseStart_10931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10931 prefixEnd_10931 := by exact prefixLift 10931
  have htrace : WordTrace (prefixWord ++ tailWord_10931) baseStart_10931 baseEnd_10931 := by
    simpa [prefixWord, tailWord_10931, baseEnd_10931] using wordTrace_append hprefix tailTrace_10931
  have hstable : (prefixWord ++ tailWord_10931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10931).length < 2 ^ (prefixWord ++ tailWord_10931).sum := by decide
  have hdescent : baseEnd_10931 < baseStart_10931 := by decide
  rcases family_descends (prefixWord ++ tailWord_10931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10935 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 3, 4]
def baseStart_10935 : Nat := 118140960795 + 10935 * 2 ^ 59
def prefixEnd_10935 : Nat := 4983230072969 + 3 ^ 40 * 10935 * 2
def baseEnd_10935 : Nat := 1871636985673316820739

theorem tailTrace_10935 : CollatzResearch.WordTrace tailWord_10935 prefixEnd_10935 1871636985673316820739 := by
  unfold tailWord_10935
  simp only [CollatzResearch.WordTrace]
  refine ⟨398832215391837394426259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 265888143594558262950839 398832215391837394426259)
  ·
    refine ⟨598248323087756091639389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 398832215391837394426259 598248323087756091639389)
    ·
      refine ⟨224343121157908534364771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 598248323087756091639389 224343121157908534364771)
      ·
        refine ⟨336514681736862801547157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224343121157908534364771 336514681736862801547157)
        ·
          refine ⟨15774125706415443822523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 336514681736862801547157 15774125706415443822523)
          ·
            refine ⟨23661188559623165733785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15774125706415443822523 23661188559623165733785)
            ·
              refine ⟨17745891419717374300339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23661188559623165733785 17745891419717374300339)
              ·
                refine ⟨26618837129576061450509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17745891419717374300339 26618837129576061450509)
                ·
                  refine ⟨9982063923591023043941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26618837129576061450509 9982063923591023043941)
                  ·
                    refine ⟨1871636985673316820739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9982063923591023043941 1871636985673316820739)
                    ·
                      rfl

theorem cell23_10935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_10935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_10935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_10935 prefixEnd_10935 := by exact prefixLift 10935
  have htrace : WordTrace (prefixWord ++ tailWord_10935) baseStart_10935 baseEnd_10935 := by
    simpa [prefixWord, tailWord_10935, baseEnd_10935] using wordTrace_append hprefix tailTrace_10935
  have hstable : (prefixWord ++ tailWord_10935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10935).length < 2 ^ (prefixWord ++ tailWord_10935).sum := by decide
  have hdescent : baseEnd_10935 < baseStart_10935 := by decide
  rcases family_descends (prefixWord ++ tailWord_10935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11015 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_11015 : Nat := 118140960795 + 11015 * 2 ^ 59
def prefixEnd_11015 : Nat := 4983230072969 + 3 ^ 40 * 11015 * 2
def baseEnd_11015 : Nat := 5655989409379637461849

theorem tailTrace_11015 : CollatzResearch.WordTrace tailWord_11015 prefixEnd_11015 5655989409379637461849 := by
  unfold tailWord_11015
  simp only [CollatzResearch.WordTrace]
  refine ⟨401750055102011057338499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 267833370068007371558999 401750055102011057338499)
  ·
    refine ⟨602625082653016586007749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 401750055102011057338499 602625082653016586007749)
    ·
      refine ⟨112992202997440609876453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 602625082653016586007749 112992202997440609876453)
      ·
        refine ⟨21186038062020114351835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112992202997440609876453 21186038062020114351835)
        ·
          refine ⟨31779057093030171527753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21186038062020114351835 31779057093030171527753)
          ·
            refine ⟨23834292819772628645815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31779057093030171527753 23834292819772628645815)
            ·
              refine ⟨35751439229658942968723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23834292819772628645815 35751439229658942968723)
              ·
                refine ⟨53627158844488414453085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35751439229658942968723 53627158844488414453085)
                ·
                  refine ⟨20110184566683155419907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53627158844488414453085 20110184566683155419907)
                  ·
                    refine ⟨30165276850024733129861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20110184566683155419907 30165276850024733129861)
                    ·
                      refine ⟨5655989409379637461849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 30165276850024733129861 5655989409379637461849)
                      ·
                        rfl

theorem cell23_11015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_11015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11015 prefixEnd_11015 := by exact prefixLift 11015
  have htrace : WordTrace (prefixWord ++ tailWord_11015) baseStart_11015 baseEnd_11015 := by
    simpa [prefixWord, tailWord_11015, baseEnd_11015] using wordTrace_append hprefix tailTrace_11015
  have hstable : (prefixWord ++ tailWord_11015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11015).length < 2 ^ (prefixWord ++ tailWord_11015).sum := by decide
  have hdescent : baseEnd_11015 < baseStart_11015 := by decide
  rcases family_descends (prefixWord ++ tailWord_11015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11038 : List Nat := [4, 3, 2, 14]
def baseStart_11038 : Nat := 118140960795 + 11038 * 2 ^ 59
def prefixEnd_11038 : Nat := 4983230072969 + 3 ^ 40 * 11038 * 2
def baseEnd_11038 : Nat := 2591586403490190889

theorem tailTrace_11038 : CollatzResearch.WordTrace tailWord_11038 prefixEnd_11038 2591586403490190889 := by
  unfold tailWord_11038
  simp only [CollatzResearch.WordTrace]
  refine ⟨50323616752335748178221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 268392622679123990283845 50323616752335748178221)
  ·
    refine ⟨18871356282125905566833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50323616752335748178221 18871356282125905566833)
    ·
      refine ⟨14153517211594429175125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18871356282125905566833 14153517211594429175125)
      ·
        refine ⟨2591586403490190889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 14153517211594429175125 2591586403490190889)
        ·
          rfl

theorem cell23_11038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 14].length) (baseStart_11038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11038 prefixEnd_11038 := by exact prefixLift 11038
  have htrace : WordTrace (prefixWord ++ tailWord_11038) baseStart_11038 baseEnd_11038 := by
    simpa [prefixWord, tailWord_11038, baseEnd_11038] using wordTrace_append hprefix tailTrace_11038
  have hstable : (prefixWord ++ tailWord_11038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11038).length < 2 ^ (prefixWord ++ tailWord_11038).sum := by decide
  have hdescent : baseEnd_11038 < baseStart_11038 := by decide
  rcases family_descends (prefixWord ++ tailWord_11038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11042 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_11042 : Nat := 118140960795 + 11042 * 2 ^ 59
def prefixEnd_11042 : Nat := 4983230072969 + 3 ^ 40 * 11042 * 2
def baseEnd_11042 : Nat := 1889951129017010608075

theorem tailTrace_11042 : CollatzResearch.WordTrace tailWord_11042 prefixEnd_11042 1889951129017010608075 := by
  unfold tailWord_11042
  simp only [CollatzResearch.WordTrace]
  refine ⟨100683706501048667142845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 268489884002796445714253 100683706501048667142845)
  ·
    refine ⟨37756389937893250178567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100683706501048667142845 37756389937893250178567)
    ·
      refine ⟨56634584906839875267851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37756389937893250178567 56634584906839875267851)
      ·
        refine ⟨84951877360259812901777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56634584906839875267851 84951877360259812901777)
        ·
          refine ⟨63713908020194859676333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84951877360259812901777 63713908020194859676333)
          ·
            refine ⟨23892715507573072378625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63713908020194859676333 23892715507573072378625)
            ·
              refine ⟨17919536630679804283969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23892715507573072378625 17919536630679804283969)
              ·
                refine ⟨13439652473009853212977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17919536630679804283969 13439652473009853212977)
                ·
                  refine ⟨10079739354757389909733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13439652473009853212977 10079739354757389909733)
                  ·
                    refine ⟨1889951129017010608075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10079739354757389909733 1889951129017010608075)
                    ·
                      rfl

theorem cell23_11042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_11042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11042 prefixEnd_11042 := by exact prefixLift 11042
  have htrace : WordTrace (prefixWord ++ tailWord_11042) baseStart_11042 baseEnd_11042 := by
    simpa [prefixWord, tailWord_11042, baseEnd_11042] using wordTrace_append hprefix tailTrace_11042
  have hstable : (prefixWord ++ tailWord_11042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11042).length < 2 ^ (prefixWord ++ tailWord_11042).sum := by decide
  have hdescent : baseEnd_11042 < baseStart_11042 := by decide
  rcases family_descends (prefixWord ++ tailWord_11042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11051 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 2, 7]
def baseStart_11051 : Nat := 118140960795 + 11051 * 2 ^ 59
def prefixEnd_11051 : Nat := 4983230072969 + 3 ^ 40 * 11051 * 2
def baseEnd_11051 : Nat := 1891491570980498870561

theorem tailTrace_11051 : CollatzResearch.WordTrace tailWord_11051 prefixEnd_11051 1891491570980498870561 := by
  unfold tailWord_11051
  simp only [CollatzResearch.WordTrace]
  refine ⟨403063082971589205649007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 268708721981059470432671 403063082971589205649007)
  ·
    refine ⟨604594624457383808473511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403063082971589205649007 604594624457383808473511)
    ·
      refine ⟨906891936686075712710267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604594624457383808473511 906891936686075712710267)
      ·
        refine ⟨1360337905029113569065401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906891936686075712710267 1360337905029113569065401)
        ·
          refine ⟨1020253428771835176799051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1360337905029113569065401 1020253428771835176799051)
          ·
            refine ⟨1530380143157752765198577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020253428771835176799051 1530380143157752765198577)
            ·
              refine ⟨1147785107368314573898933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530380143157752765198577 1147785107368314573898933)
              ·
                refine ⟨107604853815779491303025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1147785107368314573898933 107604853815779491303025)
                ·
                  refine ⟨80703640361834618477269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107604853815779491303025 80703640361834618477269)
                  ·
                    refine ⟨1891491570980498870561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 80703640361834618477269 1891491570980498870561)
                    ·
                      rfl

theorem cell23_11051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 7].length) (baseStart_11051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11051 prefixEnd_11051 := by exact prefixLift 11051
  have htrace : WordTrace (prefixWord ++ tailWord_11051) baseStart_11051 baseEnd_11051 := by
    simpa [prefixWord, tailWord_11051, baseEnd_11051] using wordTrace_append hprefix tailTrace_11051
  have hstable : (prefixWord ++ tailWord_11051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11051).length < 2 ^ (prefixWord ++ tailWord_11051).sum := by decide
  have hdescent : baseEnd_11051 < baseStart_11051 := by decide
  rcases family_descends (prefixWord ++ tailWord_11051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11075 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 3, 3, 2]
def baseStart_11075 : Nat := 118140960795 + 11075 * 2 ^ 59
def prefixEnd_11075 : Nat := 4983230072969 + 3 ^ 40 * 11075 * 2
def baseEnd_11075 : Nat := 5686798248649402711573

theorem tailTrace_11075 : CollatzResearch.WordTrace tailWord_11075 prefixEnd_11075 5686798248649402711573 := by
  unfold tailWord_11075
  simp only [CollatzResearch.WordTrace]
  refine ⟨403938434884641304522679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 269292289923094203015119 403938434884641304522679)
  ·
    refine ⟨605907652326961956784019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403938434884641304522679 605907652326961956784019)
    ·
      refine ⟨908861478490442935176029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605907652326961956784019 908861478490442935176029)
      ·
        refine ⟨340823054433916100691011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 908861478490442935176029 340823054433916100691011)
        ·
          refine ⟨511234581650874151036517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340823054433916100691011 511234581650874151036517)
          ·
            refine ⟨95856484059538903319347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 511234581650874151036517 95856484059538903319347)
            ·
              refine ⟨143784726089308354979021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95856484059538903319347 143784726089308354979021)
              ·
                refine ⟨53919272283490633117133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143784726089308354979021 53919272283490633117133)
                ·
                  refine ⟨20219727106308987418925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53919272283490633117133 20219727106308987418925)
                  ·
                    refine ⟨7582397664865870282097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20219727106308987418925 7582397664865870282097)
                    ·
                      refine ⟨5686798248649402711573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7582397664865870282097 5686798248649402711573)
                      ·
                        rfl

theorem cell23_11075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_11075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11075 prefixEnd_11075 := by exact prefixLift 11075
  have htrace : WordTrace (prefixWord ++ tailWord_11075) baseStart_11075 baseEnd_11075 := by
    simpa [prefixWord, tailWord_11075, baseEnd_11075] using wordTrace_append hprefix tailTrace_11075
  have hstable : (prefixWord ++ tailWord_11075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11075).length < 2 ^ (prefixWord ++ tailWord_11075).sum := by decide
  have hdescent : baseEnd_11075 < baseStart_11075 := by decide
  rcases family_descends (prefixWord ++ tailWord_11075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11098 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_11098 : Nat := 118140960795 + 11098 * 2 ^ 59
def prefixEnd_11098 : Nat := 4983230072969 + 3 ^ 40 * 11098 * 2
def baseEnd_11098 : Nat := 1899536101234270907989

theorem tailTrace_11098 : CollatzResearch.WordTrace tailWord_11098 prefixEnd_11098 1899536101234270907989 := by
  unfold tailWord_11098
  simp only [CollatzResearch.WordTrace]
  refine ⟨101194328450329058152487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 269851542534210821739965 101194328450329058152487)
  ·
    refine ⟨151791492675493587228731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101194328450329058152487 151791492675493587228731)
    ·
      refine ⟨227687239013240380843097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151791492675493587228731 227687239013240380843097)
      ·
        refine ⟨170765429259930285632323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227687239013240380843097 170765429259930285632323)
        ·
          refine ⟨256148143889895428448485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170765429259930285632323 256148143889895428448485)
          ·
            refine ⟨48027776979355392834091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256148143889895428448485 48027776979355392834091)
            ·
              refine ⟨72041665469033089251137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48027776979355392834091 72041665469033089251137)
              ·
                refine ⟨54031249101774816938353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72041665469033089251137 54031249101774816938353)
                ·
                  refine ⟨40523436826331112703765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54031249101774816938353 40523436826331112703765)
                  ·
                    refine ⟨1899536101234270907989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40523436826331112703765 1899536101234270907989)
                    ·
                      rfl

theorem cell23_11098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_11098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11098 prefixEnd_11098 := by exact prefixLift 11098
  have htrace : WordTrace (prefixWord ++ tailWord_11098) baseStart_11098 baseEnd_11098 := by
    simpa [prefixWord, tailWord_11098, baseEnd_11098] using wordTrace_append hprefix tailTrace_11098
  have hstable : (prefixWord ++ tailWord_11098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11098).length < 2 ^ (prefixWord ++ tailWord_11098).sum := by decide
  have hdescent : baseEnd_11098 < baseStart_11098 := by decide
  rcases family_descends (prefixWord ++ tailWord_11098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11122 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_11122 : Nat := 118140960795 + 11122 * 2 ^ 59
def prefixEnd_11122 : Nat := 4983230072969 + 3 ^ 40 * 11122 * 2
def baseEnd_11122 : Nat := 5710931839410718823857

theorem tailTrace_11122 : CollatzResearch.WordTrace tailWord_11122 prefixEnd_11122 5710931839410718823857 := by
  unfold tailWord_11122
  simp only [CollatzResearch.WordTrace]
  refine ⟨101413166428592082870905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 270435110476245554322413 101413166428592082870905)
  ·
    refine ⟨76059874821444062153179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101413166428592082870905 76059874821444062153179)
    ·
      refine ⟨114089812232166093229769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76059874821444062153179 114089812232166093229769)
      ·
        refine ⟨85567359174124569922327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114089812232166093229769 85567359174124569922327)
        ·
          refine ⟨128351038761186854883491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85567359174124569922327 128351038761186854883491)
          ·
            refine ⟨192526558141780282325237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128351038761186854883491 192526558141780282325237)
            ·
              refine ⟨18049364825791901467991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192526558141780282325237 18049364825791901467991)
              ·
                refine ⟨27074047238687852201987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18049364825791901467991 27074047238687852201987)
                ·
                  refine ⟨40611070858031778302981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27074047238687852201987 40611070858031778302981)
                  ·
                    refine ⟨7614575785880958431809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40611070858031778302981 7614575785880958431809)
                    ·
                      refine ⟨5710931839410718823857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7614575785880958431809 5710931839410718823857)
                      ·
                        rfl

theorem cell23_11122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_11122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11122 prefixEnd_11122 := by exact prefixLift 11122
  have htrace : WordTrace (prefixWord ++ tailWord_11122) baseStart_11122 baseEnd_11122 := by
    simpa [prefixWord, tailWord_11122, baseEnd_11122] using wordTrace_append hprefix tailTrace_11122
  have hstable : (prefixWord ++ tailWord_11122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11122).length < 2 ^ (prefixWord ++ tailWord_11122).sum := by decide
  have hdescent : baseEnd_11122 < baseStart_11122 := by decide
  rcases family_descends (prefixWord ++ tailWord_11122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11126 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_11126 : Nat := 118140960795 + 11126 * 2 ^ 59
def prefixEnd_11126 : Nat := 4983230072969 + 3 ^ 40 * 11126 * 2
def baseEnd_11126 : Nat := 5712985762028703173839

theorem tailTrace_11126 : CollatzResearch.WordTrace tailWord_11126 prefixEnd_11126 5712985762028703173839 := by
  unfold tailWord_11126
  simp only [CollatzResearch.WordTrace]
  refine ⟨25362409856242313414327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 270532371799918009752821 25362409856242313414327)
  ·
    refine ⟨38043614784363470121491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25362409856242313414327 38043614784363470121491)
    ·
      refine ⟨57065422176545205182237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38043614784363470121491 57065422176545205182237)
      ·
        refine ⟨21399533316204451943339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57065422176545205182237 21399533316204451943339)
        ·
          refine ⟨32099299974306677915009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21399533316204451943339 32099299974306677915009)
          ·
            refine ⟨24074474980730008436257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32099299974306677915009 24074474980730008436257)
            ·
              refine ⟨18055856235547506327193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24074474980730008436257 18055856235547506327193)
              ·
                refine ⟨13541892176660629745395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18055856235547506327193 13541892176660629745395)
                ·
                  refine ⟨20312838264990944618093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13541892176660629745395 20312838264990944618093)
                  ·
                    refine ⟨7617314349371604231785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20312838264990944618093 7617314349371604231785)
                    ·
                      refine ⟨5712985762028703173839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7617314349371604231785 5712985762028703173839)
                      ·
                        rfl

theorem cell23_11126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_11126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11126 prefixEnd_11126 := by exact prefixLift 11126
  have htrace : WordTrace (prefixWord ++ tailWord_11126) baseStart_11126 baseEnd_11126 := by
    simpa [prefixWord, tailWord_11126, baseEnd_11126] using wordTrace_append hprefix tailTrace_11126
  have hstable : (prefixWord ++ tailWord_11126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11126).length < 2 ^ (prefixWord ++ tailWord_11126).sum := by decide
  have hdescent : baseEnd_11126 < baseStart_11126 := by decide
  rcases family_descends (prefixWord ++ tailWord_11126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11162 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 7]
def baseStart_11162 : Nat := 118140960795 + 11162 * 2 ^ 59
def prefixEnd_11162 : Nat := 4983230072969 + 3 ^ 40 * 11162 * 2
def baseEnd_11162 : Nat := 636830118398951369297

theorem tailTrace_11162 : CollatzResearch.WordTrace tailWord_11162 prefixEnd_11162 636830118398951369297 := by
  unfold tailWord_11162
  simp only [CollatzResearch.WordTrace]
  refine ⟨101777896392363790734935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 271407723712970108626493 101777896392363790734935)
  ·
    refine ⟨152666844588545686102403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101777896392363790734935 152666844588545686102403)
    ·
      refine ⟨229000266882818529153605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152666844588545686102403 229000266882818529153605)
      ·
        refine ⟨42937550040528474216301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229000266882818529153605 42937550040528474216301)
        ·
          refine ⟨16101581265198177831113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42937550040528474216301 16101581265198177831113)
          ·
            refine ⟨12076185948898633373335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16101581265198177831113 12076185948898633373335)
            ·
              refine ⟨18114278923347950060003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12076185948898633373335 18114278923347950060003)
              ·
                refine ⟨27171418385021925090005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18114278923347950060003 27171418385021925090005)
                ·
                  refine ⟨636830118398951369297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 27171418385021925090005 636830118398951369297)
                  ·
                    rfl

theorem cell23_11162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_11162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11162 prefixEnd_11162 := by exact prefixLift 11162
  have htrace : WordTrace (prefixWord ++ tailWord_11162) baseStart_11162 baseEnd_11162 := by
    simpa [prefixWord, tailWord_11162, baseEnd_11162] using wordTrace_append hprefix tailTrace_11162
  have hstable : (prefixWord ++ tailWord_11162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11162).length < 2 ^ (prefixWord ++ tailWord_11162).sum := by decide
  have hdescent : baseEnd_11162 < baseStart_11162 := by decide
  rcases family_descends (prefixWord ++ tailWord_11162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11168 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_11168 : Nat := 118140960795 + 11168 * 2 ^ 59
def prefixEnd_11168 : Nat := 4983230072969 + 3 ^ 40 * 11168 * 2
def baseEnd_11168 : Nat := 5734551949517538848645

theorem tailTrace_11168 : CollatzResearch.WordTrace tailWord_11168 prefixEnd_11168 5734551949517538848645 := by
  unfold tailWord_11168
  simp only [CollatzResearch.WordTrace]
  refine ⟨203665211773859093829079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 271553615698478791772105 203665211773859093829079)
  ·
    refine ⟨305497817660788640743619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203665211773859093829079 305497817660788640743619)
    ·
      refine ⟨458246726491182961115429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305497817660788640743619 458246726491182961115429)
      ·
        refine ⟨85921261217096805209143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 458246726491182961115429 85921261217096805209143)
        ·
          refine ⟨128881891825645207813715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85921261217096805209143 128881891825645207813715)
          ·
            refine ⟨193322837738467811720573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128881891825645207813715 193322837738467811720573)
            ·
              refine ⟨72496064151925429395215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193322837738467811720573 72496064151925429395215)
              ·
                refine ⟨108744096227888144092823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72496064151925429395215 108744096227888144092823)
                ·
                  refine ⟨163116144341832216139235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108744096227888144092823 163116144341832216139235)
                  ·
                    refine ⟨244674216512748324208853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163116144341832216139235 244674216512748324208853)
                    ·
                      refine ⟨5734551949517538848645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 244674216512748324208853 5734551949517538848645)
                      ·
                        rfl

theorem cell23_11168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_11168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11168 prefixEnd_11168 := by exact prefixLift 11168
  have htrace : WordTrace (prefixWord ++ tailWord_11168) baseStart_11168 baseEnd_11168 := by
    simpa [prefixWord, tailWord_11168, baseEnd_11168] using wordTrace_append hprefix tailTrace_11168
  have hstable : (prefixWord ++ tailWord_11168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11168).length < 2 ^ (prefixWord ++ tailWord_11168).sum := by decide
  have hdescent : baseEnd_11168 < baseStart_11168 := by decide
  rcases family_descends (prefixWord ++ tailWord_11168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11212 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 2, 4, 2]
def baseStart_11212 : Nat := 118140960795 + 11212 * 2 ^ 59
def prefixEnd_11212 : Nat := 4983230072969 + 3 ^ 40 * 11212 * 2
def baseEnd_11212 : Nat := 5757145098315366698443

theorem tailTrace_11212 : CollatzResearch.WordTrace tailWord_11212 prefixEnd_11212 5757145098315366698443 := by
  unfold tailWord_11212
  simp only [CollatzResearch.WordTrace]
  refine ⟨204467617694156851129945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 272623490258875801506593 204467617694156851129945)
  ·
    refine ⟨153350713270617638347459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204467617694156851129945 153350713270617638347459)
    ·
      refine ⟨230026069905926457521189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153350713270617638347459 230026069905926457521189)
      ·
        refine ⟨43129888107361210785223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230026069905926457521189 43129888107361210785223)
        ·
          refine ⟨64694832161041816177835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43129888107361210785223 64694832161041816177835)
          ·
            refine ⟨97042248241562724266753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64694832161041816177835 97042248241562724266753)
            ·
              refine ⟨72781686181172043200065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97042248241562724266753 72781686181172043200065)
              ·
                refine ⟨54586264635879032400049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72781686181172043200065 54586264635879032400049)
                ·
                  refine ⟨40939698476909274300037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54586264635879032400049 40939698476909274300037)
                  ·
                    refine ⟨7676193464420488931257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40939698476909274300037 7676193464420488931257)
                    ·
                      refine ⟨5757145098315366698443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7676193464420488931257 5757145098315366698443)
                      ·
                        rfl

theorem cell23_11212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_11212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11212 prefixEnd_11212 := by exact prefixLift 11212
  have htrace : WordTrace (prefixWord ++ tailWord_11212) baseStart_11212 baseEnd_11212 := by
    simpa [prefixWord, tailWord_11212, baseEnd_11212] using wordTrace_append hprefix tailTrace_11212
  have hstable : (prefixWord ++ tailWord_11212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11212).length < 2 ^ (prefixWord ++ tailWord_11212).sum := by decide
  have hdescent : baseEnd_11212 < baseStart_11212 := by decide
  rcases family_descends (prefixWord ++ tailWord_11212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11213 : List Nat := [1, 6, 3, 1, 1, 1, 1, 4, 5]
def baseStart_11213 : Nat := 118140960795 + 11213 * 2 ^ 59
def prefixEnd_11213 : Nat := 4983230072969 + 3 ^ 40 * 11213 * 2
def baseEnd_11213 : Nat := 639739842107762531771

theorem tailTrace_11213 : CollatzResearch.WordTrace tailWord_11213 prefixEnd_11213 639739842107762531771 := by
  unfold tailWord_11213
  simp only [CollatzResearch.WordTrace]
  refine ⟨408971708384690873046293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 272647805589793915364195 408971708384690873046293)
  ·
    refine ⟨19170548830532384674045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 408971708384690873046293 19170548830532384674045)
    ·
      refine ⟨7188955811449644252767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19170548830532384674045 7188955811449644252767)
      ·
        refine ⟨10783433717174466379151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7188955811449644252767 10783433717174466379151)
        ·
          refine ⟨16175150575761699568727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10783433717174466379151 16175150575761699568727)
          ·
            refine ⟨24262725863642549353091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16175150575761699568727 24262725863642549353091)
            ·
              refine ⟨36394088795463824029637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24262725863642549353091 36394088795463824029637)
              ·
                refine ⟨6823891649149467005557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36394088795463824029637 6823891649149467005557)
                ·
                  refine ⟨639739842107762531771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6823891649149467005557 639739842107762531771)
                  ·
                    rfl

theorem cell23_11213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_11213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11213 prefixEnd_11213 := by exact prefixLift 11213
  have htrace : WordTrace (prefixWord ++ tailWord_11213) baseStart_11213 baseEnd_11213 := by
    simpa [prefixWord, tailWord_11213, baseEnd_11213] using wordTrace_append hprefix tailTrace_11213
  have hstable : (prefixWord ++ tailWord_11213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11213).length < 2 ^ (prefixWord ++ tailWord_11213).sum := by decide
  have hdescent : baseEnd_11213 < baseStart_11213 := by decide
  rcases family_descends (prefixWord ++ tailWord_11213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11229 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_11229 : Nat := 118140960795 + 11229 * 2 ^ 59
def prefixEnd_11229 : Nat := 4983230072969 + 3 ^ 40 * 11229 * 2
def baseEnd_11229 : Nat := 5765874269441800185865

theorem tailTrace_11229 : CollatzResearch.WordTrace tailWord_11229 prefixEnd_11229 5765874269441800185865 := by
  unfold tailWord_11229
  simp only [CollatzResearch.WordTrace]
  refine ⟨409555276326725605628741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 273036850884483737085827 409555276326725605628741)
  ·
    refine ⟨76791614311261051055389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 409555276326725605628741 76791614311261051055389)
    ·
      refine ⟨28796855366722894145771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76791614311261051055389 28796855366722894145771)
      ·
        refine ⟨43195283050084341218657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28796855366722894145771 43195283050084341218657)
        ·
          refine ⟨32396462287563255913993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43195283050084341218657 32396462287563255913993)
          ·
            refine ⟨24297346715672441935495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32396462287563255913993 24297346715672441935495)
            ·
              refine ⟨36446020073508662903243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24297346715672441935495 36446020073508662903243)
              ·
                refine ⟨54669030110262994354865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36446020073508662903243 54669030110262994354865)
                ·
                  refine ⟨41001772582697245766149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54669030110262994354865 41001772582697245766149)
                  ·
                    refine ⟨7687832359255733581153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41001772582697245766149 7687832359255733581153)
                    ·
                      refine ⟨5765874269441800185865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7687832359255733581153 5765874269441800185865)
                      ·
                        rfl

theorem cell23_11229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_11229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11229 prefixEnd_11229 := by exact prefixLift 11229
  have htrace : WordTrace (prefixWord ++ tailWord_11229) baseStart_11229 baseEnd_11229 := by
    simpa [prefixWord, tailWord_11229, baseEnd_11229] using wordTrace_append hprefix tailTrace_11229
  have hstable : (prefixWord ++ tailWord_11229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11229).length < 2 ^ (prefixWord ++ tailWord_11229).sum := by decide
  have hdescent : baseEnd_11229 < baseStart_11229 := by decide
  rcases family_descends (prefixWord ++ tailWord_11229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11235 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 6]
def baseStart_11235 : Nat := 118140960795 + 11235 * 2 ^ 59
def prefixEnd_11235 : Nat := 4983230072969 + 3 ^ 40 * 11235 * 2
def baseEnd_11235 : Nat := 640995017040975190093

theorem tailTrace_11235 : CollatzResearch.WordTrace tailWord_11235 prefixEnd_11235 640995017040975190093 := by
  unfold tailWord_11235
  simp only [CollatzResearch.WordTrace]
  refine ⟨409774114304988630347159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 273182742869992420231439 409774114304988630347159)
  ·
    refine ⟨614661171457482945520739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409774114304988630347159 614661171457482945520739)
    ·
      refine ⟨921991757186224418281109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614661171457482945520739 921991757186224418281109)
      ·
        refine ⟨43218363618104269606927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 921991757186224418281109 43218363618104269606927)
        ·
          refine ⟨64827545427156404410391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43218363618104269606927 64827545427156404410391)
          ·
            refine ⟨97241318140734606615587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64827545427156404410391 97241318140734606615587)
            ·
              refine ⟨145861977211101909923381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97241318140734606615587 145861977211101909923381)
              ·
                refine ⟨13674560363540804055317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145861977211101909923381 13674560363540804055317)
                ·
                  refine ⟨640995017040975190093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13674560363540804055317 640995017040975190093)
                  ·
                    rfl

theorem cell23_11235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 6].length) (baseStart_11235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11235 prefixEnd_11235 := by exact prefixLift 11235
  have htrace : WordTrace (prefixWord ++ tailWord_11235) baseStart_11235 baseEnd_11235 := by
    simpa [prefixWord, tailWord_11235, baseEnd_11235] using wordTrace_append hprefix tailTrace_11235
  have hstable : (prefixWord ++ tailWord_11235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11235).length < 2 ^ (prefixWord ++ tailWord_11235).sum := by decide
  have hdescent : baseEnd_11235 < baseStart_11235 := by decide
  rcases family_descends (prefixWord ++ tailWord_11235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11246 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_11246 : Nat := 118140960795 + 11246 * 2 ^ 59
def prefixEnd_11246 : Nat := 4983230072969 + 3 ^ 40 * 11246 * 2
def baseEnd_11246 : Nat := 5774603440568233673287

theorem tailTrace_11246 : CollatzResearch.WordTrace tailWord_11246 prefixEnd_11246 5774603440568233673287 := by
  unfold tailWord_11246
  simp only [CollatzResearch.WordTrace]
  refine ⟨51271914658142188624699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 273450211510091672665061 51271914658142188624699)
  ·
    refine ⟨76907871987213282937049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51271914658142188624699 76907871987213282937049)
    ·
      refine ⟨57680903990409962202787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76907871987213282937049 57680903990409962202787)
      ·
        refine ⟨86521355985614943304181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57680903990409962202787 86521355985614943304181)
        ·
          refine ⟨8111377123651400934767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86521355985614943304181 8111377123651400934767)
          ·
            refine ⟨12167065685477101402151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8111377123651400934767 12167065685477101402151)
            ·
              refine ⟨18250598528215652103227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12167065685477101402151 18250598528215652103227)
              ·
                refine ⟨27375897792323478154841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18250598528215652103227 27375897792323478154841)
                ·
                  refine ⟨20531923344242608616131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27375897792323478154841 20531923344242608616131)
                  ·
                    refine ⟨30797885016363912924197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20531923344242608616131 30797885016363912924197)
                    ·
                      refine ⟨5774603440568233673287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 30797885016363912924197 5774603440568233673287)
                      ·
                        rfl

theorem cell23_11246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_11246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11246 prefixEnd_11246 := by exact prefixLift 11246
  have htrace : WordTrace (prefixWord ++ tailWord_11246) baseStart_11246 baseEnd_11246 := by
    simpa [prefixWord, tailWord_11246, baseEnd_11246] using wordTrace_append hprefix tailTrace_11246
  have hstable : (prefixWord ++ tailWord_11246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11246).length < 2 ^ (prefixWord ++ tailWord_11246).sum := by decide
  have hdescent : baseEnd_11246 < baseStart_11246 := by decide
  rcases family_descends (prefixWord ++ tailWord_11246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11249 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 3]
def baseStart_11249 : Nat := 118140960795 + 11249 * 2 ^ 59
def prefixEnd_11249 : Nat := 4983230072969 + 3 ^ 40 * 11249 * 2
def baseEnd_11249 : Nat := 5776143882531721935773

theorem tailTrace_11249 : CollatzResearch.WordTrace tailWord_11249 prefixEnd_11249 5776143882531721935773 := by
  unfold tailWord_11249
  simp only [CollatzResearch.WordTrace]
  refine ⟨410284736254269021356801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 273523157502846014237867 410284736254269021356801)
  ·
    refine ⟨307713552190701766017601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 410284736254269021356801 307713552190701766017601)
    ·
      refine ⟨230785164143026324513201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307713552190701766017601 230785164143026324513201)
      ·
        refine ⟨173088873107269743384901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230785164143026324513201 173088873107269743384901)
        ·
          refine ⟨32454163707613076884669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173088873107269743384901 32454163707613076884669)
          ·
            refine ⟨12170311390354903831751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32454163707613076884669 12170311390354903831751)
            ·
              refine ⟨18255467085532355747627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12170311390354903831751 18255467085532355747627)
              ·
                refine ⟨27383200628298533621441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18255467085532355747627 27383200628298533621441)
                ·
                  refine ⟨20537400471223900216081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27383200628298533621441 20537400471223900216081)
                  ·
                    refine ⟨15403050353417925162061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20537400471223900216081 15403050353417925162061)
                    ·
                      refine ⟨5776143882531721935773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 15403050353417925162061 5776143882531721935773)
                      ·
                        rfl

theorem cell23_11249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_11249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11249 prefixEnd_11249 := by exact prefixLift 11249
  have htrace : WordTrace (prefixWord ++ tailWord_11249) baseStart_11249 baseEnd_11249 := by
    simpa [prefixWord, tailWord_11249, baseEnd_11249] using wordTrace_append hprefix tailTrace_11249
  have hstable : (prefixWord ++ tailWord_11249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11249).length < 2 ^ (prefixWord ++ tailWord_11249).sum := by decide
  have hdescent : baseEnd_11249 < baseStart_11249 := by decide
  rcases family_descends (prefixWord ++ tailWord_11249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11315 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 4]
def baseStart_11315 : Nat := 118140960795 + 11315 * 2 ^ 59
def prefixEnd_11315 : Nat := 4983230072969 + 3 ^ 40 * 11315 * 2
def baseEnd_11315 : Nat := 5810033605728463710469

theorem tailTrace_11315 : CollatzResearch.WordTrace tailWord_11315 prefixEnd_11315 5810033605728463710469 := by
  unfold tailWord_11315
  simp only [CollatzResearch.WordTrace]
  refine ⟨412691954015162293259399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 275127969343441528839599 412691954015162293259399)
  ·
    refine ⟨619037931022743439889099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 412691954015162293259399 619037931022743439889099)
    ·
      refine ⟨928556896534115159833649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619037931022743439889099 928556896534115159833649)
      ·
        refine ⟨696417672400586369875237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 928556896534115159833649 696417672400586369875237)
        ·
          refine ⟨130578313575109944351607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 696417672400586369875237 130578313575109944351607)
          ·
            refine ⟨195867470362664916527411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130578313575109944351607 195867470362664916527411)
            ·
              refine ⟨293801205543997374791117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195867470362664916527411 293801205543997374791117)
              ·
                refine ⟨110175452078999015546669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293801205543997374791117 110175452078999015546669)
                ·
                  refine ⟨41315794529624630830001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110175452078999015546669 41315794529624630830001)
                  ·
                    refine ⟨30986845897218473122501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41315794529624630830001 30986845897218473122501)
                    ·
                      refine ⟨5810033605728463710469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 30986845897218473122501 5810033605728463710469)
                      ·
                        rfl

theorem cell23_11315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_11315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11315 prefixEnd_11315 := by exact prefixLift 11315
  have htrace : WordTrace (prefixWord ++ tailWord_11315) baseStart_11315 baseEnd_11315 := by
    simpa [prefixWord, tailWord_11315, baseEnd_11315] using wordTrace_append hprefix tailTrace_11315
  have hstable : (prefixWord ++ tailWord_11315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11315).length < 2 ^ (prefixWord ++ tailWord_11315).sum := by decide
  have hdescent : baseEnd_11315 < baseStart_11315 := by decide
  rcases family_descends (prefixWord ++ tailWord_11315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11325 : List Nat := [1, 4, 1, 3, 1, 2, 11]
def baseStart_11325 : Nat := 118140960795 + 11325 * 2 ^ 59
def prefixEnd_11325 : Nat := 4983230072969 + 3 ^ 40 * 11325 * 2
def baseEnd_11325 : Nat := 71792202620659562783

theorem tailTrace_11325 : CollatzResearch.WordTrace tailWord_11325 prefixEnd_11325 71792202620659562783 := by
  unfold tailWord_11325
  simp only [CollatzResearch.WordTrace]
  refine ⟨413056683978934001123429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 275371122652622667415619 413056683978934001123429)
  ·
    refine ⟨77448128246050125210643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 413056683978934001123429 77448128246050125210643)
    ·
      refine ⟨116172192369075187815965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77448128246050125210643 116172192369075187815965)
      ·
        refine ⟨43564572138403195430987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116172192369075187815965 43564572138403195430987)
        ·
          refine ⟨65346858207604793146481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43564572138403195430987 65346858207604793146481)
          ·
            refine ⟨49010143655703594859861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65346858207604793146481 49010143655703594859861)
            ·
              refine ⟨71792202620659562783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 49010143655703594859861 71792202620659562783)
              ·
                rfl

theorem cell23_11325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 11].length) (baseStart_11325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11325 prefixEnd_11325 := by exact prefixLift 11325
  have htrace : WordTrace (prefixWord ++ tailWord_11325) baseStart_11325 baseEnd_11325 := by
    simpa [prefixWord, tailWord_11325, baseEnd_11325] using wordTrace_append hprefix tailTrace_11325
  have hstable : (prefixWord ++ tailWord_11325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11325).length < 2 ^ (prefixWord ++ tailWord_11325).sum := by decide
  have hdescent : baseEnd_11325 < baseStart_11325 := by decide
  rcases family_descends (prefixWord ++ tailWord_11325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11346 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_11346 : Nat := 118140960795 + 11346 * 2 ^ 59
def prefixEnd_11346 : Nat := 4983230072969 + 3 ^ 40 * 11346 * 2
def baseEnd_11346 : Nat := 1941983835339280807609

theorem tailTrace_11346 : CollatzResearch.WordTrace tailWord_11346 prefixEnd_11346 1941983835339280807609 := by
  unfold tailWord_11346
  simp only [CollatzResearch.WordTrace]
  refine ⟨103455654225713646909473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 275881744601903058425261 103455654225713646909473)
  ·
    refine ⟨77591740669285235182105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103455654225713646909473 77591740669285235182105)
    ·
      refine ⟨58193805501963926386579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77591740669285235182105 58193805501963926386579)
      ·
        refine ⟨87290708252945889579869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58193805501963926386579 87290708252945889579869)
        ·
          refine ⟨32734015594854708592451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87290708252945889579869 32734015594854708592451)
          ·
            refine ⟨49101023392282062888677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32734015594854708592451 49101023392282062888677)
            ·
              refine ⟨9206441886052886791627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49101023392282062888677 9206441886052886791627)
              ·
                refine ⟨13809662829079330187441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9206441886052886791627 13809662829079330187441)
                ·
                  refine ⟨10357247121809497640581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13809662829079330187441 10357247121809497640581)
                  ·
                    refine ⟨1941983835339280807609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10357247121809497640581 1941983835339280807609)
                    ·
                      rfl

theorem cell23_11346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_11346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11346 prefixEnd_11346 := by exact prefixLift 11346
  have htrace : WordTrace (prefixWord ++ tailWord_11346) baseStart_11346 baseEnd_11346 := by
    simpa [prefixWord, tailWord_11346, baseEnd_11346] using wordTrace_append hprefix tailTrace_11346
  have hstable : (prefixWord ++ tailWord_11346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11346).length < 2 ^ (prefixWord ++ tailWord_11346).sum := by decide
  have hdescent : baseEnd_11346 < baseStart_11346 := by decide
  rcases family_descends (prefixWord ++ tailWord_11346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11350 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_11350 : Nat := 118140960795 + 11350 * 2 ^ 59
def prefixEnd_11350 : Nat := 4983230072969 + 3 ^ 40 * 11350 * 2
def baseEnd_11350 : Nat := 1942668476211942257603

theorem tailTrace_11350 : CollatzResearch.WordTrace tailWord_11350 prefixEnd_11350 1942668476211942257603 := by
  unfold tailWord_11350
  simp only [CollatzResearch.WordTrace]
  refine ⟨25873031805522704423969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 275979005925575513855669 25873031805522704423969)
  ·
    refine ⟨19404773854142028317977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25873031805522704423969 19404773854142028317977)
    ·
      refine ⟨14553580390606521238483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19404773854142028317977 14553580390606521238483)
      ·
        refine ⟨21830370585909781857725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553580390606521238483 21830370585909781857725)
        ·
          refine ⟨8186388969716168196647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21830370585909781857725 8186388969716168196647)
          ·
            refine ⟨12279583454574252294971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186388969716168196647 12279583454574252294971)
            ·
              refine ⟨18419375181861378442457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12279583454574252294971 18419375181861378442457)
              ·
                refine ⟨13814531386396033831843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18419375181861378442457 13814531386396033831843)
                ·
                  refine ⟨20721797079594050747765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13814531386396033831843 20721797079594050747765)
                  ·
                    refine ⟨1942668476211942257603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20721797079594050747765 1942668476211942257603)
                    ·
                      rfl

theorem cell23_11350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_11350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11350 prefixEnd_11350 := by exact prefixLift 11350
  have htrace : WordTrace (prefixWord ++ tailWord_11350) baseStart_11350 baseEnd_11350 := by
    simpa [prefixWord, tailWord_11350, baseEnd_11350] using wordTrace_append hprefix tailTrace_11350
  have hstable : (prefixWord ++ tailWord_11350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11350).length < 2 ^ (prefixWord ++ tailWord_11350).sum := by decide
  have hdescent : baseEnd_11350 < baseStart_11350 := by decide
  rcases family_descends (prefixWord ++ tailWord_11350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11352 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_11352 : Nat := 118140960795 + 11352 * 2 ^ 59
def prefixEnd_11352 : Nat := 4983230072969 + 3 ^ 40 * 11352 * 2
def baseEnd_11352 : Nat := 5829032389944818947799

theorem tailTrace_11352 : CollatzResearch.WordTrace tailWord_11352 prefixEnd_11352 5829032389944818947799 := by
  unfold tailWord_11352
  simp only [CollatzResearch.WordTrace]
  refine ⟨207020727440558806178155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 276027636587411741570873 207020727440558806178155)
  ·
    refine ⟨310531091160838209267233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207020727440558806178155 310531091160838209267233)
    ·
      refine ⟨232898318370628656950425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310531091160838209267233 232898318370628656950425)
      ·
        refine ⟨174673738777971492712819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232898318370628656950425 174673738777971492712819)
        ·
          refine ⟨262010608166957239069229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174673738777971492712819 262010608166957239069229)
          ·
            refine ⟨98253978062608964650961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262010608166957239069229 98253978062608964650961)
            ·
              refine ⟨73690483546956723488221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98253978062608964650961 73690483546956723488221)
              ·
                refine ⟨27633931330108771308083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73690483546956723488221 27633931330108771308083)
                ·
                  refine ⟨41450896995163156962125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27633931330108771308083 41450896995163156962125)
                  ·
                    refine ⟨15544086373186183860797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41450896995163156962125 15544086373186183860797)
                    ·
                      refine ⟨5829032389944818947799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 15544086373186183860797 5829032389944818947799)
                      ·
                        rfl

theorem cell23_11352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_11352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11352 prefixEnd_11352 := by exact prefixLift 11352
  have htrace : WordTrace (prefixWord ++ tailWord_11352) baseStart_11352 baseEnd_11352 := by
    simpa [prefixWord, tailWord_11352, baseEnd_11352] using wordTrace_append hprefix tailTrace_11352
  have hstable : (prefixWord ++ tailWord_11352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11352).length < 2 ^ (prefixWord ++ tailWord_11352).sum := by decide
  have hdescent : baseEnd_11352 < baseStart_11352 := by decide
  rcases family_descends (prefixWord ++ tailWord_11352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11402 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_11402 : Nat := 118140960795 + 11402 * 2 ^ 59
def prefixEnd_11402 : Nat := 4983230072969 + 3 ^ 40 * 11402 * 2
def baseEnd_11402 : Nat := 1951568807556541107523

theorem tailTrace_11402 : CollatzResearch.WordTrace tailWord_11402 prefixEnd_11402 1951568807556541107523 := by
  unfold tailWord_11402
  simp only [CollatzResearch.WordTrace]
  refine ⟨103966276174994037919115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 277243403133317434450973 103966276174994037919115)
  ·
    refine ⟨155949414262491056878673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103966276174994037919115 155949414262491056878673)
    ·
      refine ⟨116962060696868292659005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155949414262491056878673 116962060696868292659005)
      ·
        refine ⟨43860772761325609747127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116962060696868292659005 43860772761325609747127)
        ·
          refine ⟨65791159141988414620691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43860772761325609747127 65791159141988414620691)
          ·
            refine ⟨98686738712982621931037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65791159141988414620691 98686738712982621931037)
            ·
              refine ⟨37007527017368483224139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98686738712982621931037 37007527017368483224139)
              ·
                refine ⟨55511290526052724836209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37007527017368483224139 55511290526052724836209)
                ·
                  refine ⟨41633467894539543627157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55511290526052724836209 41633467894539543627157)
                  ·
                    refine ⟨1951568807556541107523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41633467894539543627157 1951568807556541107523)
                    ·
                      rfl

theorem cell23_11402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_11402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11402 prefixEnd_11402 := by exact prefixLift 11402
  have htrace : WordTrace (prefixWord ++ tailWord_11402) baseStart_11402 baseEnd_11402 := by
    simpa [prefixWord, tailWord_11402, baseEnd_11402] using wordTrace_append hprefix tailTrace_11402
  have hstable : (prefixWord ++ tailWord_11402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11402).length < 2 ^ (prefixWord ++ tailWord_11402).sum := by decide
  have hdescent : baseEnd_11402 < baseStart_11402 := by decide
  rcases family_descends (prefixWord ++ tailWord_11402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11449 : List Nat := [1, 2, 1, 4, 1, 3, 2, 4, 5]
def baseStart_11449 : Nat := 118140960795 + 11449 * 2 ^ 59
def prefixEnd_11449 : Nat := 4983230072969 + 3 ^ 40 * 11449 * 2
def baseEnd_11449 : Nat := 653204445936771048317

theorem tailTrace_11449 : CollatzResearch.WordTrace tailWord_11449 prefixEnd_11449 653204445936771048317 := by
  unfold tailWord_11449
  simp only [CollatzResearch.WordTrace]
  refine ⟨417579335529703178637401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 278386223686468785758267 417579335529703178637401)
  ·
    refine ⟨313184501647277383978051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 417579335529703178637401 313184501647277383978051)
    ·
      refine ⟨469776752470916075967077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313184501647277383978051 469776752470916075967077)
      ·
        refine ⟨88083141088296764243827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 469776752470916075967077 88083141088296764243827)
        ·
          refine ⟨132124711632445146365741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88083141088296764243827 132124711632445146365741)
          ·
            refine ⟨49546766862166929887153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132124711632445146365741 49546766862166929887153)
            ·
              refine ⟨37160075146625197415365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49546766862166929887153 37160075146625197415365)
              ·
                refine ⟨6967514089992224515381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37160075146625197415365 6967514089992224515381)
                ·
                  refine ⟨653204445936771048317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6967514089992224515381 653204445936771048317)
                  ·
                    rfl

theorem cell23_11449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 5].length) (baseStart_11449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11449 prefixEnd_11449 := by exact prefixLift 11449
  have htrace : WordTrace (prefixWord ++ tailWord_11449) baseStart_11449 baseEnd_11449 := by
    simpa [prefixWord, tailWord_11449, baseEnd_11449] using wordTrace_append hprefix tailTrace_11449
  have hstable : (prefixWord ++ tailWord_11449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11449).length < 2 ^ (prefixWord ++ tailWord_11449).sum := by decide
  have hdescent : baseEnd_11449 < baseStart_11449 := by decide
  rcases family_descends (prefixWord ++ tailWord_11449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11460 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_11460 : Nat := 118140960795 + 11460 * 2 ^ 59
def prefixEnd_11460 : Nat := 4983230072969 + 3 ^ 40 * 11460 * 2
def baseEnd_11460 : Nat := 5884488300630396397303

theorem tailTrace_11460 : CollatzResearch.WordTrace tailWord_11460 prefixEnd_11460 5884488300630396397303 := by
  unfold tailWord_11460
  simp only [CollatzResearch.WordTrace]
  refine ⟨208990269244926028643917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 278653692326568038191889 208990269244926028643917)
  ·
    refine ⟨78371350966847260741469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 208990269244926028643917 78371350966847260741469)
    ·
      refine ⟨29389256612567722778051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78371350966847260741469 29389256612567722778051)
      ·
        refine ⟨44083884918851584167077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29389256612567722778051 44083884918851584167077)
        ·
          refine ⟨8265728422284672031327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44083884918851584167077 8265728422284672031327)
          ·
            refine ⟨12398592633427008046991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8265728422284672031327 12398592633427008046991)
            ·
              refine ⟨18597888950140512070487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12398592633427008046991 18597888950140512070487)
              ·
                refine ⟨27896833425210768105731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18597888950140512070487 27896833425210768105731)
                ·
                  refine ⟨41845250137816152158597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27896833425210768105731 41845250137816152158597)
                  ·
                    refine ⟨7845984400840528529737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41845250137816152158597 7845984400840528529737)
                    ·
                      refine ⟨5884488300630396397303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 7845984400840528529737 5884488300630396397303)
                      ·
                        rfl

theorem cell23_11460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_11460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11460 prefixEnd_11460 := by exact prefixLift 11460
  have htrace : WordTrace (prefixWord ++ tailWord_11460) baseStart_11460 baseEnd_11460 := by
    simpa [prefixWord, tailWord_11460, baseEnd_11460] using wordTrace_append hprefix tailTrace_11460
  have hstable : (prefixWord ++ tailWord_11460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11460).length < 2 ^ (prefixWord ++ tailWord_11460).sum := by decide
  have hdescent : baseEnd_11460 < baseStart_11460 := by decide
  rcases family_descends (prefixWord ++ tailWord_11460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11499 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 4]
def baseStart_11499 : Nat := 118140960795 + 11499 * 2 ^ 59
def prefixEnd_11499 : Nat := 4983230072969 + 3 ^ 40 * 11499 * 2
def baseEnd_11499 : Nat := 5904514046155743809623

theorem tailTrace_11499 : CollatzResearch.WordTrace tailWord_11499 prefixEnd_11499 5904514046155743809623 := by
  unfold tailWord_11499
  simp only [CollatzResearch.WordTrace]
  refine ⟨419402985348561717957551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 279601990232374478638367 419402985348561717957551)
  ·
    refine ⟨629104478022842576936327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 419402985348561717957551 629104478022842576936327)
    ·
      refine ⟨943656717034263865404491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 629104478022842576936327 943656717034263865404491)
      ·
        refine ⟨1415485075551395798106737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943656717034263865404491 1415485075551395798106737)
        ·
          refine ⟨1061613806663546848580053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1415485075551395798106737 1061613806663546848580053)
          ·
            refine ⟨24881573593676879263595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1061613806663546848580053 24881573593676879263595)
            ·
              refine ⟨37322360390515318895393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24881573593676879263595 37322360390515318895393)
              ·
                refine ⟨27991770292886489171545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37322360390515318895393 27991770292886489171545)
                ·
                  refine ⟨20993827719664866878659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27991770292886489171545 20993827719664866878659)
                  ·
                    refine ⟨31490741579497300317989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20993827719664866878659 31490741579497300317989)
                    ·
                      refine ⟨5904514046155743809623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 31490741579497300317989 5904514046155743809623)
                      ·
                        rfl

theorem cell23_11499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 4].length) (baseStart_11499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11499 prefixEnd_11499 := by exact prefixLift 11499
  have htrace : WordTrace (prefixWord ++ tailWord_11499) baseStart_11499 baseEnd_11499 := by
    simpa [prefixWord, tailWord_11499, baseEnd_11499] using wordTrace_append hprefix tailTrace_11499
  have hstable : (prefixWord ++ tailWord_11499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11499).length < 2 ^ (prefixWord ++ tailWord_11499).sum := by decide
  have hdescent : baseEnd_11499 < baseStart_11499 := by decide
  rcases family_descends (prefixWord ++ tailWord_11499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11560 : List Nat := [2, 1, 5, 1, 2, 1, 4, 2, 1, 4]
def baseStart_11560 : Nat := 118140960795 + 11560 * 2 ^ 59
def prefixEnd_11560 : Nat := 4983230072969 + 3 ^ 40 * 11560 * 2
def baseEnd_11560 : Nat := 1978612122026668382281

theorem tailTrace_11560 : CollatzResearch.WordTrace tailWord_11560 prefixEnd_11560 1978612122026668382281 := by
  unfold tailWord_11560
  simp only [CollatzResearch.WordTrace]
  refine ⟨210813919063784567964067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 281085225418379423952089 210813919063784567964067)
  ·
    refine ⟨316220878595676851946101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210813919063784567964067 316220878595676851946101)
    ·
      refine ⟨29645707368344704869947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316220878595676851946101 29645707368344704869947)
      ·
        refine ⟨44468561052517057304921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29645707368344704869947 44468561052517057304921)
        ·
          refine ⟨33351420789387792978691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44468561052517057304921 33351420789387792978691)
          ·
            refine ⟨50027131184081689468037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33351420789387792978691 50027131184081689468037)
            ·
              refine ⟨9380087097015316775257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50027131184081689468037 9380087097015316775257)
              ·
                refine ⟨7035065322761487581443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9380087097015316775257 7035065322761487581443)
                ·
                  refine ⟨10552597984142231372165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7035065322761487581443 10552597984142231372165)
                  ·
                    refine ⟨1978612122026668382281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10552597984142231372165 1978612122026668382281)
                    ·
                      rfl

theorem cell23_11560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_11560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11560 prefixEnd_11560 := by exact prefixLift 11560
  have htrace : WordTrace (prefixWord ++ tailWord_11560) baseStart_11560 baseEnd_11560 := by
    simpa [prefixWord, tailWord_11560, baseEnd_11560] using wordTrace_append hprefix tailTrace_11560
  have hstable : (prefixWord ++ tailWord_11560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11560).length < 2 ^ (prefixWord ++ tailWord_11560).sum := by decide
  have hdescent : baseEnd_11560 < baseStart_11560 := by decide
  rcases family_descends (prefixWord ++ tailWord_11560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11569 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 3, 5]
def baseStart_11569 : Nat := 118140960795 + 11569 * 2 ^ 59
def prefixEnd_11569 : Nat := 4983230072969 + 3 ^ 40 * 11569 * 2
def baseEnd_11569 : Nat := 1980152563990156644767

theorem tailTrace_11569 : CollatzResearch.WordTrace tailWord_11569 prefixEnd_11569 1980152563990156644767 := by
  unfold tailWord_11569
  simp only [CollatzResearch.WordTrace]
  refine ⟨421956095094963673005761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 281304063396642448670507 421956095094963673005761)
  ·
    refine ⟨316467071321222754754321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 421956095094963673005761 316467071321222754754321)
    ·
      refine ⟨237350303490917066065741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316467071321222754754321 237350303490917066065741)
      ·
        refine ⟨89006363809093899774653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237350303490917066065741 89006363809093899774653)
        ·
          refine ⟨33377386428410212415495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89006363809093899774653 33377386428410212415495)
          ·
            refine ⟨50066079642615318623243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33377386428410212415495 50066079642615318623243)
            ·
              refine ⟨75099119463922977934865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50066079642615318623243 75099119463922977934865)
              ·
                refine ⟨56324339597942233451149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75099119463922977934865 56324339597942233451149)
                ·
                  refine ⟨21121627349228337544181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56324339597942233451149 21121627349228337544181)
                  ·
                    refine ⟨1980152563990156644767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21121627349228337544181 1980152563990156644767)
                    ·
                      rfl

theorem cell23_11569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_11569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11569 prefixEnd_11569 := by exact prefixLift 11569
  have htrace : WordTrace (prefixWord ++ tailWord_11569) baseStart_11569 baseEnd_11569 := by
    simpa [prefixWord, tailWord_11569, baseEnd_11569] using wordTrace_append hprefix tailTrace_11569
  have hstable : (prefixWord ++ tailWord_11569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11569).length < 2 ^ (prefixWord ++ tailWord_11569).sum := by decide
  have hdescent : baseEnd_11569 < baseStart_11569 := by decide
  rcases family_descends (prefixWord ++ tailWord_11569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11616 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 4, 4]
def baseStart_11616 : Nat := 118140960795 + 11616 * 2 ^ 59
def prefixEnd_11616 : Nat := 4983230072969 + 3 ^ 40 * 11616 * 2
def baseEnd_11616 : Nat := 1988197094243928682195

theorem tailTrace_11616 : CollatzResearch.WordTrace tailWord_11616 prefixEnd_11616 1988197094243928682195 := by
  unfold tailWord_11616
  simp only [CollatzResearch.WordTrace]
  refine ⟨211835162962345349983351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 282446883949793799977801 211835162962345349983351)
  ·
    refine ⟨317752744443518024975027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211835162962345349983351 317752744443518024975027)
    ·
      refine ⟨476629116665277037462541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317752744443518024975027 476629116665277037462541)
      ·
        refine ⟨178735918749478889048453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476629116665277037462541 178735918749478889048453)
        ·
          refine ⟨33512984765527291696585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178735918749478889048453 33512984765527291696585)
          ·
            refine ⟨25134738574145468772439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33512984765527291696585 25134738574145468772439)
            ·
              refine ⟨37702107861218203158659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25134738574145468772439 37702107861218203158659)
              ·
                refine ⟨56553161791827304737989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37702107861218203158659 56553161791827304737989)
                ·
                  refine ⟨10603717835967619638373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56553161791827304737989 10603717835967619638373)
                  ·
                    refine ⟨1988197094243928682195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10603717835967619638373 1988197094243928682195)
                    ·
                      rfl

theorem cell23_11616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 4].length) (baseStart_11616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11616 prefixEnd_11616 := by exact prefixLift 11616
  have htrace : WordTrace (prefixWord ++ tailWord_11616) baseStart_11616 baseEnd_11616 := by
    simpa [prefixWord, tailWord_11616, baseEnd_11616] using wordTrace_append hprefix tailTrace_11616
  have hstable : (prefixWord ++ tailWord_11616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11616).length < 2 ^ (prefixWord ++ tailWord_11616).sum := by decide
  have hdescent : baseEnd_11616 < baseStart_11616 := by decide
  rcases family_descends (prefixWord ++ tailWord_11616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11759 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_11759 : Nat := 118140960795 + 11759 * 2 ^ 59
def prefixEnd_11759 : Nat := 4983230072969 + 3 ^ 40 * 11759 * 2
def baseEnd_11759 : Nat := 6038019016324726558427

theorem tailTrace_11759 : CollatzResearch.WordTrace tailWord_11759 prefixEnd_11759 6038019016324726558427 := by
  unfold tailWord_11759
  simp only [CollatzResearch.WordTrace]
  refine ⟨428885964406626122422331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 285923976271084081614887 428885964406626122422331)
  ·
    refine ⟨643328946609939183633497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 428885964406626122422331 643328946609939183633497)
    ·
      refine ⟨482496709957454387725123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 643328946609939183633497 482496709957454387725123)
      ·
        refine ⟨723745064936181581587685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482496709957454387725123 723745064936181581587685)
        ·
          refine ⟨135702199675534046547691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 723745064936181581587685 135702199675534046547691)
          ·
            refine ⟨203553299513301069821537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135702199675534046547691 203553299513301069821537)
            ·
              refine ⟨152664974634975802366153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203553299513301069821537 152664974634975802366153)
              ·
                refine ⟨114498730976231851774615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152664974634975802366153 114498730976231851774615)
                ·
                  refine ⟨171748096464347777661923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114498730976231851774615 171748096464347777661923)
                  ·
                    refine ⟨257622144696521666492885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171748096464347777661923 257622144696521666492885)
                    ·
                      refine ⟨6038019016324726558427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 257622144696521666492885 6038019016324726558427)
                      ·
                        rfl

theorem cell23_11759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_11759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11759 prefixEnd_11759 := by exact prefixLift 11759
  have htrace : WordTrace (prefixWord ++ tailWord_11759) baseStart_11759 baseEnd_11759 := by
    simpa [prefixWord, tailWord_11759, baseEnd_11759] using wordTrace_append hprefix tailTrace_11759
  have hstable : (prefixWord ++ tailWord_11759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11759).length < 2 ^ (prefixWord ++ tailWord_11759).sum := by decide
  have hdescent : baseEnd_11759 < baseStart_11759 := by decide
  rcases family_descends (prefixWord ++ tailWord_11759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11819 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 9]
def baseStart_11819 : Nat := 118140960795 + 11819 * 2 ^ 59
def prefixEnd_11819 : Nat := 4983230072969 + 3 ^ 40 * 11819 * 2
def baseEnd_11819 : Nat := 6068827855594491808151

theorem tailTrace_11819 : CollatzResearch.WordTrace tailWord_11819 prefixEnd_11819 6068827855594491808151 := by
  unfold tailWord_11819
  simp only [CollatzResearch.WordTrace]
  refine ⟨431074344189256369606511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 287382896126170913071007 431074344189256369606511)
  ·
    refine ⟨646611516283884554409767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 431074344189256369606511 646611516283884554409767)
    ·
      refine ⟨969917274425826831614651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646611516283884554409767 969917274425826831614651)
      ·
        refine ⟨1454875911638740247421977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969917274425826831614651 1454875911638740247421977)
        ·
          refine ⟨1091156933729055185566483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1454875911638740247421977 1091156933729055185566483)
          ·
            refine ⟨1636735400593582778349725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091156933729055185566483 1636735400593582778349725)
            ·
              refine ⟨613775775222593541881147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1636735400593582778349725 613775775222593541881147)
              ·
                refine ⟨920663662833890312821721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613775775222593541881147 920663662833890312821721)
                ·
                  refine ⟨690497747125417734616291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920663662833890312821721 690497747125417734616291)
                  ·
                    refine ⟨1035746620688126601924437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 690497747125417734616291 1035746620688126601924437)
                    ·
                      refine ⟨6068827855594491808151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 1035746620688126601924437 6068827855594491808151)
                      ·
                        rfl

theorem cell23_11819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_11819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11819 prefixEnd_11819 := by exact prefixLift 11819
  have htrace : WordTrace (prefixWord ++ tailWord_11819) baseStart_11819 baseEnd_11819 := by
    simpa [prefixWord, tailWord_11819, baseEnd_11819] using wordTrace_append hprefix tailTrace_11819
  have hstable : (prefixWord ++ tailWord_11819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11819).length < 2 ^ (prefixWord ++ tailWord_11819).sum := by decide
  have hdescent : baseEnd_11819 < baseStart_11819 := by decide
  rcases family_descends (prefixWord ++ tailWord_11819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11847 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 3, 4]
def baseStart_11847 : Nat := 118140960795 + 11847 * 2 ^ 59
def prefixEnd_11847 : Nat := 4983230072969 + 3 ^ 40 * 11847 * 2
def baseEnd_11847 : Nat := 2027735104640127419341

theorem tailTrace_11847 : CollatzResearch.WordTrace tailWord_11847 prefixEnd_11847 2027735104640127419341 := by
  unfold tailWord_11847
  simp only [CollatzResearch.WordTrace]
  refine ⟨432095588087817151625795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 288063725391878101083863 432095588087817151625795)
  ·
    refine ⟨648143382131725727438693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 432095588087817151625795 648143382131725727438693)
    ·
      refine ⟨121526884149698573894755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 648143382131725727438693 121526884149698573894755)
      ·
        refine ⟨182290326224547860842133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121526884149698573894755 182290326224547860842133)
        ·
          refine ⟨8544859041775680976975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 182290326224547860842133 8544859041775680976975)
          ·
            refine ⟨12817288562663521465463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544859041775680976975 12817288562663521465463)
            ·
              refine ⟨19225932843995282198195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12817288562663521465463 19225932843995282198195)
              ·
                refine ⟨28838899265992923297293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19225932843995282198195 28838899265992923297293)
                ·
                  refine ⟨10814587224747346236485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28838899265992923297293 10814587224747346236485)
                  ·
                    refine ⟨2027735104640127419341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10814587224747346236485 2027735104640127419341)
                    ·
                      rfl

theorem cell23_11847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_11847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11847 prefixEnd_11847 := by exact prefixLift 11847
  have htrace : WordTrace (prefixWord ++ tailWord_11847) baseStart_11847 baseEnd_11847 := by
    simpa [prefixWord, tailWord_11847, baseEnd_11847] using wordTrace_append hprefix tailTrace_11847
  have hstable : (prefixWord ++ tailWord_11847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11847).length < 2 ^ (prefixWord ++ tailWord_11847).sum := by decide
  have hdescent : baseEnd_11847 < baseStart_11847 := by decide
  rcases family_descends (prefixWord ++ tailWord_11847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
