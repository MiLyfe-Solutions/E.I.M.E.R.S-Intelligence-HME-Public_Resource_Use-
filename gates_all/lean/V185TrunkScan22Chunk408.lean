import V185TrunkScan22Chunk407

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3639075 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 5]
def baseStart_3639075 : Nat := 118140960795 + 3639075 * 2 ^ 59
def prefixEnd_3639075 : Nat := 4983230072969 + 3 ^ 40 * 3639075 * 2
def baseEnd_3639075 : Nat := 415243247280101074672601

theorem tailTrace_3639075 : CollatzResearch.WordTrace tailWord_3639075 prefixEnd_3639075 415243247280101074672601 := by
  unfold tailWord_3639075
  simp only [CollatzResearch.WordTrace]
  refine ⟨132727969291260254374606679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88485312860840169583071119 132727969291260254374606679)
  ·
    refine ⟨199091953936890381561910019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132727969291260254374606679 199091953936890381561910019)
    ·
      refine ⟨298637930905335572342865029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199091953936890381561910019 298637930905335572342865029)
      ·
        refine ⟨55994612044750419814287193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298637930905335572342865029 55994612044750419814287193)
        ·
          refine ⟨41995959033562814860715395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55994612044750419814287193 41995959033562814860715395)
          ·
            refine ⟨62993938550344222291073093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41995959033562814860715395 62993938550344222291073093)
            ·
              refine ⟨11811363478189541679576205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62993938550344222291073093 11811363478189541679576205)
              ·
                refine ⟨4429261304321078129841077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11811363478189541679576205 4429261304321078129841077)
                ·
                  refine ⟨415243247280101074672601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4429261304321078129841077 415243247280101074672601)
                  ·
                    rfl

theorem cell22_3639075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 5].length) (baseStart_3639075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639075 prefixEnd_3639075 := by exact prefixLift 3639075
  have htrace : WordTrace (prefixWord ++ tailWord_3639075) baseStart_3639075 baseEnd_3639075 := by
    simpa [prefixWord, tailWord_3639075, baseEnd_3639075] using wordTrace_append hprefix tailTrace_3639075
  have hstable : (prefixWord ++ tailWord_3639075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639075).length < 2 ^ (prefixWord ++ tailWord_3639075).sum := by decide
  have hdescent : baseEnd_3639075 < baseStart_3639075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639139 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 1, 4]
def baseStart_3639139 : Nat := 118140960795 + 3639139 * 2 ^ 59
def prefixEnd_3639139 : Nat := 4983230072969 + 3 ^ 40 * 3639139 * 2
def baseEnd_3639139 : Nat := 1245751650348228390417607

theorem tailTrace_3639139 : CollatzResearch.WordTrace tailWord_3639139 prefixEnd_3639139 1245751650348228390417607 := by
  unfold tailWord_3639139
  simp only [CollatzResearch.WordTrace]
  refine ⟨132730303563028393304936471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88486869042018928869957647 132730303563028393304936471)
  ·
    refine ⟨199095455344542589957404707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132730303563028393304936471 199095455344542589957404707)
    ·
      refine ⟨298643183016813884936107061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199095455344542589957404707 298643183016813884936107061)
      ·
        refine ⟨27997798407826301712760037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298643183016813884936107061 27997798407826301712760037)
        ·
          refine ⟨5249587201467431571142507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27997798407826301712760037 5249587201467431571142507)
          ·
            refine ⟨7874380802201147356713761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249587201467431571142507 7874380802201147356713761)
            ·
              refine ⟨5905785601650860517535321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7874380802201147356713761 5905785601650860517535321)
              ·
                refine ⟨4429339201238145388151491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5905785601650860517535321 4429339201238145388151491)
                ·
                  refine ⟨6644008801857218082227237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429339201238145388151491 6644008801857218082227237)
                  ·
                    refine ⟨1245751650348228390417607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6644008801857218082227237 1245751650348228390417607)
                    ·
                      rfl

theorem cell22_3639139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 4].length) (baseStart_3639139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639139 prefixEnd_3639139 := by exact prefixLift 3639139
  have htrace : WordTrace (prefixWord ++ tailWord_3639139) baseStart_3639139 baseEnd_3639139 := by
    simpa [prefixWord, tailWord_3639139, baseEnd_3639139] using wordTrace_append hprefix tailTrace_3639139
  have hstable : (prefixWord ++ tailWord_3639139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639139).length < 2 ^ (prefixWord ++ tailWord_3639139).sum := by decide
  have hdescent : baseEnd_3639139 < baseStart_3639139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639186 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_3639186 : Nat := 118140960795 + 3639186 * 2 ^ 59
def prefixEnd_3639186 : Nat := 4983230072969 + 3 ^ 40 * 3639186 * 2
def baseEnd_3639186 : Nat := 1245767739408735934492463

theorem tailTrace_3639186 : CollatzResearch.WordTrace tailWord_3639186 prefixEnd_3639186 1245767739408735934492463 := by
  unfold tailWord_3639186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33183004448464530082974353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88488011862572080221264941 33183004448464530082974353)
  ·
    refine ⟨24887253336348397562230765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33183004448464530082974353 24887253336348397562230765)
    ·
      refine ⟨9332720001130649085836537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24887253336348397562230765 9332720001130649085836537)
      ·
        refine ⟨6999540000847986814377403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9332720001130649085836537 6999540000847986814377403)
        ·
          refine ⟨10499310001271980221566105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6999540000847986814377403 10499310001271980221566105)
          ·
            refine ⟨7874482500953985166174579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10499310001271980221566105 7874482500953985166174579)
            ·
              refine ⟨11811723751430977749261869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7874482500953985166174579 11811723751430977749261869)
              ·
                refine ⟨4429396406786616655973201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11811723751430977749261869 4429396406786616655973201)
                ·
                  refine ⟨3322047305089962491979901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4429396406786616655973201 3322047305089962491979901)
                  ·
                    refine ⟨1245767739408735934492463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3322047305089962491979901 1245767739408735934492463)
                    ·
                      rfl

theorem cell22_3639186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_3639186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639186 prefixEnd_3639186 := by exact prefixLift 3639186
  have htrace : WordTrace (prefixWord ++ tailWord_3639186) baseStart_3639186 baseEnd_3639186 := by
    simpa [prefixWord, tailWord_3639186, baseEnd_3639186] using wordTrace_append hprefix tailTrace_3639186
  have hstable : (prefixWord ++ tailWord_3639186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639186).length < 2 ^ (prefixWord ++ tailWord_3639186).sum := by decide
  have hdescent : baseEnd_3639186 < baseStart_3639186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639190 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3639190 : Nat := 118140960795 + 3639190 * 2 ^ 59
def prefixEnd_3639190 : Nat := 4983230072969 + 3 ^ 40 * 3639190 * 2
def baseEnd_3639190 : Nat := 1245769108690481257392451

theorem tailTrace_3639190 : CollatzResearch.WordTrace tailWord_3639190 prefixEnd_3639190 1245769108690481257392451 := by
  unfold tailWord_3639190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295760230365226813440189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88488109123895752676695349 8295760230365226813440189)
  ·
    refine ⟨3110910086386960055040071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8295760230365226813440189 3110910086386960055040071)
    ·
      refine ⟨4666365129580440082560107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3110910086386960055040071 4666365129580440082560107)
      ·
        refine ⟨6999547694370660123840161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4666365129580440082560107 6999547694370660123840161)
        ·
          refine ⟨5249660770777995092880121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6999547694370660123840161 5249660770777995092880121)
          ·
            refine ⟨3937245578083496319660091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5249660770777995092880121 3937245578083496319660091)
            ·
              refine ⟨5905868367125244479490137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937245578083496319660091 5905868367125244479490137)
              ·
                refine ⟨4429401275343933359617603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5905868367125244479490137 4429401275343933359617603)
                ·
                  refine ⟨6644101913015900039426405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429401275343933359617603 6644101913015900039426405)
                  ·
                    refine ⟨1245769108690481257392451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6644101913015900039426405 1245769108690481257392451)
                    ·
                      rfl

theorem cell22_3639190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3639190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639190 prefixEnd_3639190 := by exact prefixLift 3639190
  have htrace : WordTrace (prefixWord ++ tailWord_3639190) baseStart_3639190 baseEnd_3639190 := by
    simpa [prefixWord, tailWord_3639190, baseEnd_3639190] using wordTrace_append hprefix tailTrace_3639190
  have hstable : (prefixWord ++ tailWord_3639190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639190).length < 2 ^ (prefixWord ++ tailWord_3639190).sum := by decide
  have hdescent : baseEnd_3639190 < baseStart_3639190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639274 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_3639274 : Nat := 118140960795 + 3639274 * 2 ^ 59
def prefixEnd_3639274 : Nat := 4983230072969 + 3 ^ 40 * 3639274 * 2
def baseEnd_3639274 : Nat := 1245797863607133038292193

theorem tailTrace_3639274 : CollatzResearch.WordTrace tailWord_3639274 prefixEnd_3639274 1245797863607133038292193 := by
  unfold tailWord_3639274
  simp only [CollatzResearch.WordTrace]
  refine ⟨33183806854384827840275219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88490151611692874240733917 33183806854384827840275219)
  ·
    refine ⟨49775710281577241760412829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33183806854384827840275219 49775710281577241760412829)
    ·
      refine ⟨18665891355591465660154811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49775710281577241760412829 18665891355591465660154811)
      ·
        refine ⟨27998837033387198490232217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18665891355591465660154811 27998837033387198490232217)
        ·
          refine ⟨20999127775040398867674163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27998837033387198490232217 20999127775040398867674163)
          ·
            refine ⟨31498691662560598301511245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20999127775040398867674163 31498691662560598301511245)
            ·
              refine ⟨11812009373460224363066717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31498691662560598301511245 11812009373460224363066717)
              ·
                refine ⟨4429503515047584136150019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11812009373460224363066717 4429503515047584136150019)
                ·
                  refine ⟨6644255272571376204225029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429503515047584136150019 6644255272571376204225029)
                  ·
                    refine ⟨1245797863607133038292193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6644255272571376204225029 1245797863607133038292193)
                    ·
                      rfl

theorem cell22_3639274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_3639274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639274 prefixEnd_3639274 := by exact prefixLift 3639274
  have htrace : WordTrace (prefixWord ++ tailWord_3639274) baseStart_3639274 baseEnd_3639274 := by
    simpa [prefixWord, tailWord_3639274, baseEnd_3639274] using wordTrace_append hprefix tailTrace_3639274
  have hstable : (prefixWord ++ tailWord_3639274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639274).length < 2 ^ (prefixWord ++ tailWord_3639274).sum := by decide
  have hdescent : baseEnd_3639274 < baseStart_3639274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639289 : List Nat := [1, 2, 1, 3, 1, 4, 2, 4, 4]
def baseStart_3639289 : Nat := 118140960795 + 3639289 * 2 ^ 59
def prefixEnd_3639289 : Nat := 4983230072969 + 3 ^ 40 * 3639289 * 2
def baseEnd_3639289 : Nat := 415267666137892666389049

theorem tailTrace_3639289 : CollatzResearch.WordTrace tailWord_3639289 prefixEnd_3639289 415267666137892666389049 := by
  unfold tailWord_3639289
  simp only [CollatzResearch.WordTrace]
  refine ⟨132735774512484968922896921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88490516341656645948597947 132735774512484968922896921)
  ·
    refine ⟨99551830884363726692172691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132735774512484968922896921 99551830884363726692172691)
    ·
      refine ⟨149327746326545590038259037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99551830884363726692172691 149327746326545590038259037)
      ·
        refine ⟨55997904872454596264347139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149327746326545590038259037 55997904872454596264347139)
        ·
          refine ⟨83996857308681894396520709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55997904872454596264347139 83996857308681894396520709)
          ·
            refine ⟨15749410745377855199347633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83996857308681894396520709 15749410745377855199347633)
            ·
              refine ⟨11812058059033391399510725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15749410745377855199347633 11812058059033391399510725)
              ·
                refine ⟨2214760886068760887408261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11812058059033391399510725 2214760886068760887408261)
                ·
                  refine ⟨415267666137892666389049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2214760886068760887408261 415267666137892666389049)
                  ·
                    rfl

theorem cell22_3639289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 4].length) (baseStart_3639289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639289 prefixEnd_3639289 := by exact prefixLift 3639289
  have htrace : WordTrace (prefixWord ++ tailWord_3639289) baseStart_3639289 baseEnd_3639289 := by
    simpa [prefixWord, tailWord_3639289, baseEnd_3639289] using wordTrace_append hprefix tailTrace_3639289
  have hstable : (prefixWord ++ tailWord_3639289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639289).length < 2 ^ (prefixWord ++ tailWord_3639289).sum := by decide
  have hdescent : baseEnd_3639289 < baseStart_3639289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639377 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_3639377 : Nat := 118140960795 + 3639377 * 2 ^ 59
def prefixEnd_3639377 : Nat := 4983230072969 + 3 ^ 40 * 3639377 * 2
def baseEnd_3639377 : Nat := 1245833122612075102966877

theorem tailTrace_3639377 : CollatzResearch.WordTrace tailWord_3639377 prefixEnd_3639377 1245833122612075102966877 := by
  unfold tailWord_3639377
  simp only [CollatzResearch.WordTrace]
  refine ⟨132738984136166159952100385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88492656090777439968066923 132738984136166159952100385)
  ·
    refine ⟨99554238102124619964075289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132738984136166159952100385 99554238102124619964075289)
    ·
      refine ⟨74665678576593464973056467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99554238102124619964075289 74665678576593464973056467)
      ·
        refine ⟨111998517864890197459584701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74665678576593464973056467 111998517864890197459584701)
        ·
          refine ⟨41999444199333824047344263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111998517864890197459584701 41999444199333824047344263)
          ·
            refine ⟨62999166299000736071016395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41999444199333824047344263 62999166299000736071016395)
            ·
              refine ⟨94498749448501104106524593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62999166299000736071016395 94498749448501104106524593)
              ·
                refine ⟨70874062086375828079893445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94498749448501104106524593 70874062086375828079893445)
                ·
                  refine ⟨13288886641195467764980021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70874062086375828079893445 13288886641195467764980021)
                  ·
                    refine ⟨1245833122612075102966877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13288886641195467764980021 1245833122612075102966877)
                    ·
                      rfl

theorem cell22_3639377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_3639377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639377 prefixEnd_3639377 := by exact prefixLift 3639377
  have htrace : WordTrace (prefixWord ++ tailWord_3639377) baseStart_3639377 baseEnd_3639377 := by
    simpa [prefixWord, tailWord_3639377, baseEnd_3639377] using wordTrace_append hprefix tailTrace_3639377
  have hstable : (prefixWord ++ tailWord_3639377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639377).length < 2 ^ (prefixWord ++ tailWord_3639377).sum := by decide
  have hdescent : baseEnd_3639377 < baseStart_3639377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639456 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 4, 3]
def baseStart_3639456 : Nat := 118140960795 + 3639456 * 2 ^ 59
def prefixEnd_3639456 : Nat := 4983230072969 + 3 ^ 40 * 3639456 * 2
def baseEnd_3639456 : Nat := 1245860165926545230241635

theorem tailTrace_3639456 : CollatzResearch.WordTrace tailWord_3639456 prefixEnd_3639456 1245860165926545230241635 := by
  unfold tailWord_3639456
  simp only [CollatzResearch.WordTrace]
  refine ⟨66370932751439978222113111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88494577001919970962817481 66370932751439978222113111)
  ·
    refine ⟨99556399127159967333169667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66370932751439978222113111 99556399127159967333169667)
    ·
      refine ⟨149334598690739950999754501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99556399127159967333169667 149334598690739950999754501)
      ·
        refine ⟨28000237254513740812453969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149334598690739950999754501 28000237254513740812453969)
        ·
          refine ⟨21000177940885305609340477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28000237254513740812453969 21000177940885305609340477)
          ·
            refine ⟨7875066727831989603502679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21000177940885305609340477 7875066727831989603502679)
            ·
              refine ⟨11812600091747984405254019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7875066727831989603502679 11812600091747984405254019)
              ·
                refine ⟨17718900137621976607881029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11812600091747984405254019 17718900137621976607881029)
                ·
                  refine ⟨3322293775804120613977693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17718900137621976607881029 3322293775804120613977693)
                  ·
                    refine ⟨1245860165926545230241635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3322293775804120613977693 1245860165926545230241635)
                    ·
                      rfl

theorem cell22_3639456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_3639456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639456 prefixEnd_3639456 := by exact prefixLift 3639456
  have htrace : WordTrace (prefixWord ++ tailWord_3639456) baseStart_3639456 baseEnd_3639456 := by
    simpa [prefixWord, tailWord_3639456, baseEnd_3639456] using wordTrace_append hprefix tailTrace_3639456
  have hstable : (prefixWord ++ tailWord_3639456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639456).length < 2 ^ (prefixWord ++ tailWord_3639456).sum := by decide
  have hdescent : baseEnd_3639456 < baseStart_3639456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639458 : List Nat := [3, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_3639458 : Nat := 118140960795 + 3639458 * 2 ^ 59
def prefixEnd_3639458 : Nat := 4983230072969 + 3 ^ 40 * 3639458 * 2
def baseEnd_3639458 : Nat := 415286950189139297230543

theorem tailTrace_3639458 : CollatzResearch.WordTrace tailWord_3639458 prefixEnd_3639458 415286950189139297230543 := by
  unfold tailWord_3639458
  simp only [CollatzResearch.WordTrace]
  refine ⟨33185484612218177696449757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88494625632581807190532685 33185484612218177696449757)
  ·
    refine ⟨12444556729581816636168659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33185484612218177696449757 12444556729581816636168659)
    ·
      refine ⟨18666835094372724954252989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12444556729581816636168659 18666835094372724954252989)
      ·
        refine ⟨7000063160389771857844871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18666835094372724954252989 7000063160389771857844871)
        ·
          refine ⟨10500094740584657786767307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7000063160389771857844871 10500094740584657786767307)
          ·
            refine ⟨15750142110876986680150961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10500094740584657786767307 15750142110876986680150961)
            ·
              refine ⟨11812606583157740010113221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15750142110876986680150961 11812606583157740010113221)
              ·
                refine ⟨2214863734342076251896229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11812606583157740010113221 2214863734342076251896229)
                ·
                  refine ⟨415286950189139297230543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2214863734342076251896229 415286950189139297230543)
                  ·
                    rfl

theorem cell22_3639458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_3639458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639458 prefixEnd_3639458 := by exact prefixLift 3639458
  have htrace : WordTrace (prefixWord ++ tailWord_3639458) baseStart_3639458 baseEnd_3639458 := by
    simpa [prefixWord, tailWord_3639458, baseEnd_3639458] using wordTrace_append hprefix tailTrace_3639458
  have hstable : (prefixWord ++ tailWord_3639458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639458).length < 2 ^ (prefixWord ++ tailWord_3639458).sum := by decide
  have hdescent : baseEnd_3639458 < baseStart_3639458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639473 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 1, 5]
def baseStart_3639473 : Nat := 118140960795 + 3639473 * 2 ^ 59
def prefixEnd_3639473 : Nat := 4983230072969 + 3 ^ 40 * 3639473 * 2
def baseEnd_3639473 : Nat := 1245865985373962852566583

theorem tailTrace_3639473 : CollatzResearch.WordTrace tailWord_3639473 prefixEnd_3639473 1245865985373962852566583 := by
  unfold tailWord_3639473
  simp only [CollatzResearch.WordTrace]
  refine ⟨132742485543818368347595073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88494990362545578898396715 132742485543818368347595073)
  ·
    refine ⟨99556864157863776260696305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132742485543818368347595073 99556864157863776260696305)
    ·
      refine ⟨74667648118397832195522229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99556864157863776260696305 74667648118397832195522229)
      ·
        refine ⟨7000092011099796768330209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74667648118397832195522229 7000092011099796768330209)
        ·
          refine ⟨5250069008324847576247657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7000092011099796768330209 5250069008324847576247657)
          ·
            refine ⟨3937551756243635682185743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5250069008324847576247657 3937551756243635682185743)
            ·
              refine ⟨5906327634365453523278615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937551756243635682185743 5906327634365453523278615)
              ·
                refine ⟨8859491451548180284917923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906327634365453523278615 8859491451548180284917923)
                ·
                  refine ⟨13289237177322270427376885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8859491451548180284917923 13289237177322270427376885)
                  ·
                    refine ⟨1245865985373962852566583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13289237177322270427376885 1245865985373962852566583)
                    ·
                      rfl

theorem cell22_3639473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_3639473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639473 prefixEnd_3639473 := by exact prefixLift 3639473
  have htrace : WordTrace (prefixWord ++ tailWord_3639473) baseStart_3639473 baseEnd_3639473 := by
    simpa [prefixWord, tailWord_3639473, baseEnd_3639473] using wordTrace_append hprefix tailTrace_3639473
  have hstable : (prefixWord ++ tailWord_3639473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639473).length < 2 ^ (prefixWord ++ tailWord_3639473).sum := by decide
  have hdescent : baseEnd_3639473 < baseStart_3639473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639486 : List Nat := [4, 2, 1, 1, 4, 1, 1, 8]
def baseStart_3639486 : Nat := 118140960795 + 3639486 * 2 ^ 59
def prefixEnd_3639486 : Nat := 4983230072969 + 3 ^ 40 * 3639486 * 2
def baseEnd_3639486 : Nat := 138430048393292794665727

theorem tailTrace_3639486 : CollatzResearch.WordTrace tailWord_3639486 prefixEnd_3639486 138430048393292794665727 := by
  unfold tailWord_3639486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592869961596408945977289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88495306461847514378545541 16592869961596408945977289)
  ·
    refine ⟨12444652471197306709482967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16592869961596408945977289 12444652471197306709482967)
    ·
      refine ⟨18666978706795960064224451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12444652471197306709482967 18666978706795960064224451)
      ·
        refine ⟨28000468060193940096336677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18666978706795960064224451 28000468060193940096336677)
        ·
          refine ⟨5250087761286363768063127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28000468060193940096336677 5250087761286363768063127)
          ·
            refine ⟨7875131641929545652094691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250087761286363768063127 7875131641929545652094691)
            ·
              refine ⟨11812697462894318478142037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7875131641929545652094691 11812697462894318478142037)
              ·
                refine ⟨138430048393292794665727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11812697462894318478142037 138430048393292794665727)
                ·
                  rfl

theorem cell22_3639486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_3639486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639486 prefixEnd_3639486 := by exact prefixLift 3639486
  have htrace : WordTrace (prefixWord ++ tailWord_3639486) baseStart_3639486 baseEnd_3639486 := by
    simpa [prefixWord, tailWord_3639486, baseEnd_3639486] using wordTrace_append hprefix tailTrace_3639486
  have hstable : (prefixWord ++ tailWord_3639486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639486).length < 2 ^ (prefixWord ++ tailWord_3639486).sum := by decide
  have hdescent : baseEnd_3639486 < baseStart_3639486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639490 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3639490 : Nat := 118140960795 + 3639490 * 2 ^ 59
def prefixEnd_3639490 : Nat := 4983230072969 + 3 ^ 40 * 3639490 * 2
def baseEnd_3639490 : Nat := 1245871804821380474891531

theorem tailTrace_3639490 : CollatzResearch.WordTrace tailWord_3639490 prefixEnd_3639490 1245871804821380474891531 := by
  unfold tailWord_3639490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33185776396189195062740981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88495403723171186833975949 33185776396189195062740981)
  ·
    refine ⟨3111166537142737037131967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33185776396189195062740981 3111166537142737037131967)
    ·
      refine ⟨4666749805714105555697951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3111166537142737037131967 4666749805714105555697951)
      ·
        refine ⟨7000124708571158333546927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4666749805714105555697951 7000124708571158333546927)
        ·
          refine ⟨10500187062856737500320391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7000124708571158333546927 10500187062856737500320391)
          ·
            refine ⟨15750280594285106250480587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10500187062856737500320391 15750280594285106250480587)
            ·
              refine ⟨23625420891427659375720881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15750280594285106250480587 23625420891427659375720881)
              ·
                refine ⟨17719065668570744531790661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23625420891427659375720881 17719065668570744531790661)
                ·
                  refine ⟨3322324812857014599710749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17719065668570744531790661 3322324812857014599710749)
                  ·
                    refine ⟨1245871804821380474891531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3322324812857014599710749 1245871804821380474891531)
                    ·
                      rfl

theorem cell22_3639490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3639490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639490 prefixEnd_3639490 := by exact prefixLift 3639490
  have htrace : WordTrace (prefixWord ++ tailWord_3639490) baseStart_3639490 baseEnd_3639490 := by
    simpa [prefixWord, tailWord_3639490, baseEnd_3639490] using wordTrace_append hprefix tailTrace_3639490
  have hstable : (prefixWord ++ tailWord_3639490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639490).length < 2 ^ (prefixWord ++ tailWord_3639490).sum := by decide
  have hdescent : baseEnd_3639490 < baseStart_3639490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639514 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_3639514 : Nat := 118140960795 + 3639514 * 2 ^ 59
def prefixEnd_3639514 : Nat := 4983230072969 + 3 ^ 40 * 3639514 * 2
def baseEnd_3639514 : Nat := 415293340170617470763819

theorem tailTrace_3639514 : CollatzResearch.WordTrace tailWord_3639514 prefixEnd_3639514 415293340170617470763819 := by
  unfold tailWord_3639514
  simp only [CollatzResearch.WordTrace]
  refine ⟨33185995234167458087459399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88495987291113221566558397 33185995234167458087459399)
  ·
    refine ⟨49778992851251187131189099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33185995234167458087459399 49778992851251187131189099)
    ·
      refine ⟨74668489276876780696783649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49778992851251187131189099 74668489276876780696783649)
      ·
        refine ⟨56001366957657585522587737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74668489276876780696783649 56001366957657585522587737)
        ·
          refine ⟨42001025218243189141940803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56001366957657585522587737 42001025218243189141940803)
          ·
            refine ⟨63001537827364783712911205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42001025218243189141940803 63001537827364783712911205)
            ·
              refine ⟨11812788342630896946170851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63001537827364783712911205 11812788342630896946170851)
              ·
                refine ⟨17719182513946345419256277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11812788342630896946170851 17719182513946345419256277)
                ·
                  refine ⟨415293340170617470763819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17719182513946345419256277 415293340170617470763819)
                  ·
                    rfl

theorem cell22_3639514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_3639514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639514 prefixEnd_3639514 := by exact prefixLift 3639514
  have htrace : WordTrace (prefixWord ++ tailWord_3639514) baseStart_3639514 baseEnd_3639514 := by
    simpa [prefixWord, tailWord_3639514, baseEnd_3639514] using wordTrace_append hprefix tailTrace_3639514
  have hstable : (prefixWord ++ tailWord_3639514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639514).length < 2 ^ (prefixWord ++ tailWord_3639514).sum := by decide
  have hdescent : baseEnd_3639514 < baseStart_3639514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639646 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3639646 : Nat := 118140960795 + 3639646 * 2 ^ 59
def prefixEnd_3639646 : Nat := 4983230072969 + 3 ^ 40 * 3639646 * 2
def baseEnd_3639646 : Nat := 1245925206809448067991053

theorem tailTrace_3639646 : CollatzResearch.WordTrace tailWord_3639646 prefixEnd_3639646 1245925206809448067991053 := by
  unfold tailWord_3639646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16593599421523952361705349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88499196914794412595761861 16593599421523952361705349)
  ·
    refine ⟨3111299891535741067819753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16593599421523952361705349 3111299891535741067819753)
    ·
      refine ⟨2333474918651805800864815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3111299891535741067819753 2333474918651805800864815)
      ·
        refine ⟨3500212377977708701297223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333474918651805800864815 3500212377977708701297223)
        ·
          refine ⟨5250318566966563051945835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500212377977708701297223 5250318566966563051945835)
          ·
            refine ⟨7875477850449844577918753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250318566966563051945835 7875477850449844577918753)
            ·
              refine ⟨5906608387837383433439065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7875477850449844577918753 5906608387837383433439065)
              ·
                refine ⟨4429956290878037575079299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5906608387837383433439065 4429956290878037575079299)
                ·
                  refine ⟨6644934436317056362618949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429956290878037575079299 6644934436317056362618949)
                  ·
                    refine ⟨1245925206809448067991053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6644934436317056362618949 1245925206809448067991053)
                    ·
                      rfl

theorem cell22_3639646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3639646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639646 prefixEnd_3639646 := by exact prefixLift 3639646
  have htrace : WordTrace (prefixWord ++ tailWord_3639646) baseStart_3639646 baseEnd_3639646 := by
    simpa [prefixWord, tailWord_3639646, baseEnd_3639646] using wordTrace_append hprefix tailTrace_3639646
  have hstable : (prefixWord ++ tailWord_3639646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639646).length < 2 ^ (prefixWord ++ tailWord_3639646).sum := by decide
  have hdescent : baseEnd_3639646 < baseStart_3639646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639653 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_3639653 : Nat := 118140960795 + 3639653 * 2 ^ 59
def prefixEnd_3639653 : Nat := 4983230072969 + 3 ^ 40 * 3639653 * 2
def baseEnd_3639653 : Nat := 1245927603052502383066031

theorem tailTrace_3639653 : CollatzResearch.WordTrace tailWord_3639653 prefixEnd_3639653 1245927603052502383066031 := by
  unfold tailWord_3639653
  simp only [CollatzResearch.WordTrace]
  refine ⟨132749050683166259089147613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88499367122110839392765075 132749050683166259089147613)
  ·
    refine ⟨49780894006187347158430355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132749050683166259089147613 49780894006187347158430355)
    ·
      refine ⟨74671341009281020737645533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49780894006187347158430355 74671341009281020737645533)
      ·
        refine ⟨28001752878480382776617075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74671341009281020737645533 28001752878480382776617075)
        ·
          refine ⟨42002629317720574164925613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28001752878480382776617075 42002629317720574164925613)
          ·
            refine ⟨15750985994145215311847105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42002629317720574164925613 15750985994145215311847105)
            ·
              refine ⟨11813239495608911483885329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15750985994145215311847105 11813239495608911483885329)
              ·
                refine ⟨8859929621706683612913997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11813239495608911483885329 8859929621706683612913997)
                ·
                  refine ⟨3322473608140006354842749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8859929621706683612913997 3322473608140006354842749)
                  ·
                    refine ⟨1245927603052502383066031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3322473608140006354842749 1245927603052502383066031)
                    ·
                      rfl

theorem cell22_3639653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_3639653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639653 prefixEnd_3639653 := by exact prefixLift 3639653
  have htrace : WordTrace (prefixWord ++ tailWord_3639653) baseStart_3639653 baseEnd_3639653 := by
    simpa [prefixWord, tailWord_3639653, baseEnd_3639653] using wordTrace_append hprefix tailTrace_3639653
  have hstable : (prefixWord ++ tailWord_3639653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639653).length < 2 ^ (prefixWord ++ tailWord_3639653).sum := by decide
  have hdescent : baseEnd_3639653 < baseStart_3639653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639666 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_3639666 : Nat := 118140960795 + 3639666 * 2 ^ 59
def prefixEnd_3639666 : Nat := 4983230072969 + 3 ^ 40 * 3639666 * 2
def baseEnd_3639666 : Nat := 415310684406058227496997

theorem tailTrace_3639666 : CollatzResearch.WordTrace tailWord_3639666 prefixEnd_3639666 415310684406058227496997 := by
  unfold tailWord_3639666
  simp only [CollatzResearch.WordTrace]
  refine ⟨33187381208029790577342713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88499683221412774872913901 33187381208029790577342713)
  ·
    refine ⟨24890535906022342933007035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33187381208029790577342713 24890535906022342933007035)
    ·
      refine ⟨37335803859033514399510553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24890535906022342933007035 37335803859033514399510553)
      ·
        refine ⟨28001852894275135799632915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37335803859033514399510553 28001852894275135799632915)
        ·
          refine ⟨42002779341412703699449373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28001852894275135799632915 42002779341412703699449373)
          ·
            refine ⟨15751042253029763887293515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42002779341412703699449373 15751042253029763887293515)
            ·
              refine ⟨23626563379544645830940273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15751042253029763887293515 23626563379544645830940273)
              ·
                refine ⟨17719922534658484373205205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23626563379544645830940273 17719922534658484373205205)
                ·
                  refine ⟨415310684406058227496997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17719922534658484373205205 415310684406058227496997)
                  ·
                    rfl

theorem cell22_3639666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_3639666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639666 prefixEnd_3639666 := by exact prefixLift 3639666
  have htrace : WordTrace (prefixWord ++ tailWord_3639666) baseStart_3639666 baseEnd_3639666 := by
    simpa [prefixWord, tailWord_3639666, baseEnd_3639666] using wordTrace_append hprefix tailTrace_3639666
  have hstable : (prefixWord ++ tailWord_3639666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639666).length < 2 ^ (prefixWord ++ tailWord_3639666).sum := by decide
  have hdescent : baseEnd_3639666 < baseStart_3639666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639687 : List Nat := [1, 1, 4, 2, 2, 1, 5, 2, 1, 3]
def baseStart_3639687 : Nat := 118140960795 + 3639687 * 2 ^ 59
def prefixEnd_3639687 : Nat := 4983230072969 + 3 ^ 40 * 3639687 * 2
def baseEnd_3639687 : Nat := 1245939241947337627715927

theorem tailTrace_3639687 : CollatzResearch.WordTrace tailWord_3639687 prefixEnd_3639687 1245939241947337627715927 := by
  unfold tailWord_3639687
  simp only [CollatzResearch.WordTrace]
  refine ⟨132750290765043082895885315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88500193843362055263923543 132750290765043082895885315)
  ·
    refine ⟨199125436147564624343827973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132750290765043082895885315 199125436147564624343827973)
    ·
      refine ⟨37336019277668367064467745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199125436147564624343827973 37336019277668367064467745)
      ·
        refine ⟨28002014458251275298350809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37336019277668367064467745 28002014458251275298350809)
        ·
          refine ⟨21001510843688456473763107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28002014458251275298350809 21001510843688456473763107)
          ·
            refine ⟨31502266265532684710644661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21001510843688456473763107 31502266265532684710644661)
            ·
              refine ⟨2953337462393689191622937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31502266265532684710644661 2953337462393689191622937)
              ·
                refine ⟨2215003096795266893717203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2953337462393689191622937 2215003096795266893717203)
                ·
                  refine ⟨3322504645192900340575805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215003096795266893717203 3322504645192900340575805)
                  ·
                    refine ⟨1245939241947337627715927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3322504645192900340575805 1245939241947337627715927)
                    ·
                      rfl

theorem cell22_3639687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_3639687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639687 prefixEnd_3639687 := by exact prefixLift 3639687
  have htrace : WordTrace (prefixWord ++ tailWord_3639687) baseStart_3639687 baseEnd_3639687 := by
    simpa [prefixWord, tailWord_3639687, baseEnd_3639687] using wordTrace_append hprefix tailTrace_3639687
  have hstable : (prefixWord ++ tailWord_3639687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639687).length < 2 ^ (prefixWord ++ tailWord_3639687).sum := by decide
  have hdescent : baseEnd_3639687 < baseStart_3639687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639700 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 5]
def baseStart_3639700 : Nat := 118140960795 + 3639700 * 2 ^ 59
def prefixEnd_3639700 : Nat := 4983230072969 + 3 ^ 40 * 3639700 * 2
def baseEnd_3639700 : Nat := 415314564037669975713629

theorem tailTrace_3639700 : CollatzResearch.WordTrace tailWord_3639700 prefixEnd_3639700 415314564037669975713629 := by
  unfold tailWord_3639700
  simp only [CollatzResearch.WordTrace]
  refine ⟨66375382456997993058054277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88500509942663990744072369 66375382456997993058054277)
  ·
    refine ⟨12445384210687123698385177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66375382456997993058054277 12445384210687123698385177)
    ·
      refine ⟨9334038158015342773788883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12445384210687123698385177 9334038158015342773788883)
      ·
        refine ⟨14001057237023014160683325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9334038158015342773788883 14001057237023014160683325)
        ·
          refine ⟨5250396463883630310256247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14001057237023014160683325 5250396463883630310256247)
          ·
            refine ⟨7875594695825445465384371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250396463883630310256247 7875594695825445465384371)
            ·
              refine ⟨11813392043738168198076557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7875594695825445465384371 11813392043738168198076557)
              ·
                refine ⟨4430022016401813074278709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11813392043738168198076557 4430022016401813074278709)
                ·
                  refine ⟨415314564037669975713629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4430022016401813074278709 415314564037669975713629)
                  ·
                    rfl

theorem cell22_3639700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_3639700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639700 prefixEnd_3639700 := by exact prefixLift 3639700
  have htrace : WordTrace (prefixWord ++ tailWord_3639700) baseStart_3639700 baseEnd_3639700 := by
    simpa [prefixWord, tailWord_3639700, baseEnd_3639700] using wordTrace_append hprefix tailTrace_3639700
  have hstable : (prefixWord ++ tailWord_3639700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639700).length < 2 ^ (prefixWord ++ tailWord_3639700).sum := by decide
  have hdescent : baseEnd_3639700 < baseStart_3639700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639711 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 8]
def baseStart_3639711 : Nat := 118140960795 + 3639711 * 2 ^ 59
def prefixEnd_3639711 : Nat := 4983230072969 + 3 ^ 40 * 3639711 * 2
def baseEnd_3639711 : Nat := 415315819212603188371951

theorem tailTrace_3639711 : CollatzResearch.WordTrace tailWord_3639711 prefixEnd_3639711 415315819212603188371951 := by
  unfold tailWord_3639711
  simp only [CollatzResearch.WordTrace]
  refine ⟨132751166116956134994758987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88500777411304089996505991 132751166116956134994758987)
  ·
    refine ⟨199126749175434202492138481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132751166116956134994758987 199126749175434202492138481)
    ·
      refine ⟨149345061881575651869103861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199126749175434202492138481 149345061881575651869103861)
      ·
        refine ⟨14001099551397717362728487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149345061881575651869103861 14001099551397717362728487)
        ·
          refine ⟨21001649327096576044092731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14001099551397717362728487 21001649327096576044092731)
          ·
            refine ⟨31502473990644864066139097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21001649327096576044092731 31502473990644864066139097)
            ·
              refine ⟨23626855492983648049604323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31502473990644864066139097 23626855492983648049604323)
              ·
                refine ⟨35440283239475472074406485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23626855492983648049604323 35440283239475472074406485)
                ·
                  refine ⟨415315819212603188371951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35440283239475472074406485 415315819212603188371951)
                  ·
                    rfl

theorem cell22_3639711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 8].length) (baseStart_3639711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639711 prefixEnd_3639711 := by exact prefixLift 3639711
  have htrace : WordTrace (prefixWord ++ tailWord_3639711) baseStart_3639711 baseEnd_3639711 := by
    simpa [prefixWord, tailWord_3639711, baseEnd_3639711] using wordTrace_append hprefix tailTrace_3639711
  have hstable : (prefixWord ++ tailWord_3639711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639711).length < 2 ^ (prefixWord ++ tailWord_3639711).sum := by decide
  have hdescent : baseEnd_3639711 < baseStart_3639711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639730 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_3639730 : Nat := 118140960795 + 3639730 * 2 ^ 59
def prefixEnd_3639730 : Nat := 4983230072969 + 3 ^ 40 * 3639730 * 2
def baseEnd_3639730 : Nat := 1245953961726099848890795

theorem tailTrace_3639730 : CollatzResearch.WordTrace tailWord_3639730 prefixEnd_3639730 1245953961726099848890795 := by
  unfold tailWord_3639730
  simp only [CollatzResearch.WordTrace]
  refine ⟨33187964775971825309925161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88501239402591534159800429 33187964775971825309925161)
  ·
    refine ⟨24890973581978868982443871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33187964775971825309925161 24890973581978868982443871)
    ·
      refine ⟨37336460372968303473665807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24890973581978868982443871 37336460372968303473665807)
      ·
        refine ⟨56004690559452455210498711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37336460372968303473665807 56004690559452455210498711)
        ·
          refine ⟨84007035839178682815748067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56004690559452455210498711 84007035839178682815748067)
          ·
            refine ⟨126010553758768024223622101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84007035839178682815748067 126010553758768024223622101)
            ·
              refine ⟨2953372353721125567741143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 126010553758768024223622101 2953372353721125567741143)
              ·
                refine ⟨4430058530581688351611715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953372353721125567741143 4430058530581688351611715)
                ·
                  refine ⟨6645087795872532527417573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4430058530581688351611715 6645087795872532527417573)
                  ·
                    refine ⟨1245953961726099848890795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6645087795872532527417573 1245953961726099848890795)
                    ·
                      rfl

theorem cell22_3639730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_3639730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639730 prefixEnd_3639730 := by exact prefixLift 3639730
  have htrace : WordTrace (prefixWord ++ tailWord_3639730) baseStart_3639730 baseEnd_3639730 := by
    simpa [prefixWord, tailWord_3639730, baseEnd_3639730] using wordTrace_append hprefix tailTrace_3639730
  have hstable : (prefixWord ++ tailWord_3639730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639730).length < 2 ^ (prefixWord ++ tailWord_3639730).sum := by decide
  have hdescent : baseEnd_3639730 < baseStart_3639730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639775 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 2, 4]
def baseStart_3639775 : Nat := 118140960795 + 3639775 * 2 ^ 59
def prefixEnd_3639775 : Nat := 4983230072969 + 3 ^ 40 * 3639775 * 2
def baseEnd_3639775 : Nat := 1245969366145734731515657

theorem tailTrace_3639775 : CollatzResearch.WordTrace tailWord_3639775 prefixEnd_3639775 1245969366145734731515657 := by
  unfold tailWord_3639775
  simp only [CollatzResearch.WordTrace]
  refine ⟨132753500388724273925088779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88502333592482849283392519 132753500388724273925088779)
  ·
    refine ⟨199130250583086410887633169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132753500388724273925088779 199130250583086410887633169)
    ·
      refine ⟨149347687937314808165724877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199130250583086410887633169 149347687937314808165724877)
      ·
        refine ⟨56005382976493053062146829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149347687937314808165724877 56005382976493053062146829)
        ·
          refine ⟨21002018616184894898305061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56005382976493053062146829 21002018616184894898305061)
          ·
            refine ⟨3937878490534667793432199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21002018616184894898305061 3937878490534667793432199)
            ·
              refine ⟨5906817735802001690148299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937878490534667793432199 5906817735802001690148299)
              ·
                refine ⟨8860226603703002535222449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906817735802001690148299 8860226603703002535222449)
                ·
                  refine ⟨6645169952777251901416837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8860226603703002535222449 6645169952777251901416837)
                  ·
                    refine ⟨1245969366145734731515657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6645169952777251901416837 1245969366145734731515657)
                    ·
                      rfl

theorem cell22_3639775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_3639775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639775 prefixEnd_3639775 := by exact prefixLift 3639775
  have htrace : WordTrace (prefixWord ++ tailWord_3639775) baseStart_3639775 baseEnd_3639775 := by
    simpa [prefixWord, tailWord_3639775, baseEnd_3639775] using wordTrace_append hprefix tailTrace_3639775
  have hstable : (prefixWord ++ tailWord_3639775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639775).length < 2 ^ (prefixWord ++ tailWord_3639775).sum := by decide
  have hdescent : baseEnd_3639775 < baseStart_3639775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639788 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_3639788 : Nat := 118140960795 + 3639788 * 2 ^ 59
def prefixEnd_3639788 : Nat := 4983230072969 + 3 ^ 40 * 3639788 * 2
def baseEnd_3639788 : Nat := 1245973816311407030940617

theorem tailTrace_3639788 : CollatzResearch.WordTrace tailWord_3639788 prefixEnd_3639788 1245973816311407030940617 := by
  unfold tailWord_3639788
  simp only [CollatzResearch.WordTrace]
  refine ⟨66376987268838588572656009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88502649691784784763541345 66376987268838588572656009)
  ·
    refine ⟨49782740451628941429492007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66376987268838588572656009 49782740451628941429492007)
    ·
      refine ⟨74674110677443412144238011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49782740451628941429492007 74674110677443412144238011)
      ·
        refine ⟨112011166016165118216357017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74674110677443412144238011 112011166016165118216357017)
        ·
          refine ⟨84008374512123838662267763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112011166016165118216357017 84008374512123838662267763)
          ·
            refine ⟨126012561768185757993401645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84008374512123838662267763 126012561768185757993401645)
            ·
              refine ⟨47254710663069659247525617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126012561768185757993401645 47254710663069659247525617)
              ·
                refine ⟨35441032997302244435644213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47254710663069659247525617 35441032997302244435644213)
                ·
                  refine ⟨3322596843497085415841645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35441032997302244435644213 3322596843497085415841645)
                  ·
                    refine ⟨1245973816311407030940617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3322596843497085415841645 1245973816311407030940617)
                    ·
                      rfl

theorem cell22_3639788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_3639788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639788 prefixEnd_3639788 := by exact prefixLift 3639788
  have htrace : WordTrace (prefixWord ++ tailWord_3639788) baseStart_3639788 baseEnd_3639788 := by
    simpa [prefixWord, tailWord_3639788, baseEnd_3639788] using wordTrace_append hprefix tailTrace_3639788
  have hstable : (prefixWord ++ tailWord_3639788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639788).length < 2 ^ (prefixWord ++ tailWord_3639788).sum := by decide
  have hdescent : baseEnd_3639788 < baseStart_3639788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639794 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_3639794 : Nat := 118140960795 + 3639794 * 2 ^ 59
def prefixEnd_3639794 : Nat := 4983230072969 + 3 ^ 40 * 3639794 * 2
def baseEnd_3639794 : Nat := 1245975870234025015290599

theorem tailTrace_3639794 : CollatzResearch.WordTrace tailWord_3639794 prefixEnd_3639794 1245975870234025015290599 := by
  unfold tailWord_3639794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33188548343913860042507609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88502795583770293446686957 33188548343913860042507609)
  ·
    refine ⟨24891411257935395031880707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33188548343913860042507609 24891411257935395031880707)
    ·
      refine ⟨37337116886903092547821061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24891411257935395031880707 37337116886903092547821061)
      ·
        refine ⟨7000709416294329852716449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37337116886903092547821061 7000709416294329852716449)
        ·
          refine ⟨5250532062220747389537337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7000709416294329852716449 5250532062220747389537337)
          ·
            refine ⟨3937899046665560542153003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5250532062220747389537337 3937899046665560542153003)
            ·
              refine ⟨5906848569998340813229505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937899046665560542153003 5906848569998340813229505)
              ·
                refine ⟨4430136427498755609922129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5906848569998340813229505 4430136427498755609922129)
                ·
                  refine ⟨3322602320624066707441597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4430136427498755609922129 3322602320624066707441597)
                  ·
                    refine ⟨1245975870234025015290599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3322602320624066707441597 1245975870234025015290599)
                    ·
                      rfl

theorem cell22_3639794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_3639794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639794 prefixEnd_3639794 := by exact prefixLift 3639794
  have htrace : WordTrace (prefixWord ++ tailWord_3639794) baseStart_3639794 baseEnd_3639794 := by
    simpa [prefixWord, tailWord_3639794, baseEnd_3639794] using wordTrace_append hprefix tailTrace_3639794
  have hstable : (prefixWord ++ tailWord_3639794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639794).length < 2 ^ (prefixWord ++ tailWord_3639794).sum := by decide
  have hdescent : baseEnd_3639794 < baseStart_3639794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639805 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_3639805 : Nat := 118140960795 + 3639805 * 2 ^ 59
def prefixEnd_3639805 : Nat := 4983230072969 + 3 ^ 40 * 3639805 * 2
def baseEnd_3639805 : Nat := 1245979635758824653265565

theorem tailTrace_3639805 : CollatzResearch.WordTrace tailWord_3639805 prefixEnd_3639805 1245979635758824653265565 := by
  unfold tailWord_3639805
  simp only [CollatzResearch.WordTrace]
  refine ⟨132754594578615589048680869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88503063052410392699120579 132754594578615589048680869)
  ·
    refine ⟨24891486483490422946627663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132754594578615589048680869 24891486483490422946627663)
    ·
      refine ⟨37337229725235634419941495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24891486483490422946627663 37337229725235634419941495)
      ·
        refine ⟨56005844587853451629912243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37337229725235634419941495 56005844587853451629912243)
        ·
          refine ⟨84008766881780177444868365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56005844587853451629912243 84008766881780177444868365)
          ·
            refine ⟨31503287580667566541825637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84008766881780177444868365 31503287580667566541825637)
            ·
              refine ⟨5906866421375168726592307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31503287580667566541825637 5906866421375168726592307)
              ·
                refine ⟨8860299632062753089888461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906866421375168726592307 8860299632062753089888461)
                ·
                  refine ⟨3322612362023532408708173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8860299632062753089888461 3322612362023532408708173)
                  ·
                    refine ⟨1245979635758824653265565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3322612362023532408708173 1245979635758824653265565)
                    ·
                      rfl

theorem cell22_3639805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_3639805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639805 prefixEnd_3639805 := by exact prefixLift 3639805
  have htrace : WordTrace (prefixWord ++ tailWord_3639805) baseStart_3639805 baseEnd_3639805 := by
    simpa [prefixWord, tailWord_3639805, baseEnd_3639805] using wordTrace_append hprefix tailTrace_3639805
  have hstable : (prefixWord ++ tailWord_3639805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639805).length < 2 ^ (prefixWord ++ tailWord_3639805).sum := by decide
  have hdescent : baseEnd_3639805 < baseStart_3639805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639882 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_3639882 : Nat := 118140960795 + 3639882 * 2 ^ 59
def prefixEnd_3639882 : Nat := 4983230072969 + 3 ^ 40 * 3639882 * 2
def baseEnd_3639882 : Nat := 1246005994432422119090329

theorem tailTrace_3639882 : CollatzResearch.WordTrace tailWord_3639882 prefixEnd_3639882 1246005994432422119090329 := by
  unfold tailWord_3639882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33189350749834157799808475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88504935332891087466155933 33189350749834157799808475)
  ·
    refine ⟨49784026124751236699712713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33189350749834157799808475 49784026124751236699712713)
    ·
      refine ⟨37338019593563427524784535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49784026124751236699712713 37338019593563427524784535)
      ·
        refine ⟨56007029390345141287176803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37338019593563427524784535 56007029390345141287176803)
        ·
          refine ⟨84010544085517711930765205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56007029390345141287176803 84010544085517711930765205)
          ·
            refine ⟨3937994254008642746754619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84010544085517711930765205 3937994254008642746754619)
            ·
              refine ⟨5906991381012964120131929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937994254008642746754619 5906991381012964120131929)
              ·
                refine ⟨4430243535759723090098947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5906991381012964120131929 4430243535759723090098947)
                ·
                  refine ⟨6645365303639584635148421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4430243535759723090098947 6645365303639584635148421)
                  ·
                    refine ⟨1246005994432422119090329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6645365303639584635148421 1246005994432422119090329)
                    ·
                      rfl

theorem cell22_3639882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_3639882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639882 prefixEnd_3639882 := by exact prefixLift 3639882
  have htrace : WordTrace (prefixWord ++ tailWord_3639882) baseStart_3639882 baseEnd_3639882 := by
    simpa [prefixWord, tailWord_3639882, baseEnd_3639882] using wordTrace_append hprefix tailTrace_3639882
  have hstable : (prefixWord ++ tailWord_3639882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639882).length < 2 ^ (prefixWord ++ tailWord_3639882).sum := by decide
  have hdescent : baseEnd_3639882 < baseStart_3639882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639893 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3639893 : Nat := 118140960795 + 3639893 * 2 ^ 59
def prefixEnd_3639893 : Nat := 4983230072969 + 3 ^ 40 * 3639893 * 2
def baseEnd_3639893 : Nat := 1246009759957221757065295

theorem tailTrace_3639893 : CollatzResearch.WordTrace tailWord_3639893 prefixEnd_3639893 1246009759957221757065295 := by
  unfold tailWord_3639893
  simp only [CollatzResearch.WordTrace]
  refine ⟨132757804202296780077884333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88505202801531186718589555 132757804202296780077884333)
  ·
    refine ⟨49784176575861292529206625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132757804202296780077884333 49784176575861292529206625)
    ·
      refine ⟨37338132431895969396904969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49784176575861292529206625 37338132431895969396904969)
      ·
        refine ⟨28003599323921977047678727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37338132431895969396904969 28003599323921977047678727)
        ·
          refine ⟨42005398985882965571518091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28003599323921977047678727 42005398985882965571518091)
          ·
            refine ⟨63008098478824448357277137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42005398985882965571518091 63008098478824448357277137)
            ·
              refine ⟨47256073859118336267957853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63008098478824448357277137 47256073859118336267957853)
              ·
                refine ⟨17721027697169376100484195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47256073859118336267957853 17721027697169376100484195)
                ·
                  refine ⟨26581541545754064150726293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17721027697169376100484195 26581541545754064150726293)
                  ·
                    refine ⟨1246009759957221757065295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26581541545754064150726293 1246009759957221757065295)
                    ·
                      rfl

theorem cell22_3639893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3639893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639893 prefixEnd_3639893 := by exact prefixLift 3639893
  have htrace : WordTrace (prefixWord ++ tailWord_3639893) baseStart_3639893 baseEnd_3639893 := by
    simpa [prefixWord, tailWord_3639893, baseEnd_3639893] using wordTrace_append hprefix tailTrace_3639893
  have hstable : (prefixWord ++ tailWord_3639893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639893).length < 2 ^ (prefixWord ++ tailWord_3639893).sum := by decide
  have hdescent : baseEnd_3639893 < baseStart_3639893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639987 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 5]
def baseStart_3639987 : Nat := 118140960795 + 3639987 * 2 ^ 59
def prefixEnd_3639987 : Nat := 4983230072969 + 3 ^ 40 * 3639987 * 2
def baseEnd_3639987 : Nat := 415347312692745615071669

theorem tailTrace_3639987 : CollatzResearch.WordTrace tailWord_3639987 prefixEnd_3639987 415347312692745615071669 := by
  unfold tailWord_3639987
  simp only [CollatzResearch.WordTrace]
  refine ⟨132761232663956234131806215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88507488442637489421204143 132761232663956234131806215)
  ·
    refine ⟨199141848995934351197709323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132761232663956234131806215 199141848995934351197709323)
    ·
      refine ⟨298712773493901526796563985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199141848995934351197709323 298712773493901526796563985)
      ·
        refine ⟨224034580120426145097422989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298712773493901526796563985 224034580120426145097422989)
        ·
          refine ⟨84012967545159804411533621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224034580120426145097422989 84012967545159804411533621)
          ·
            refine ⟨7876215707358731663581277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84012967545159804411533621 7876215707358731663581277)
            ·
              refine ⟨2953580890259524373842979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7876215707358731663581277 2953580890259524373842979)
              ·
                refine ⟨4430371335389286560764469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953580890259524373842979 4430371335389286560764469)
                ·
                  refine ⟨415347312692745615071669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4430371335389286560764469 415347312692745615071669)
                  ·
                    rfl

theorem cell22_3639987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 5].length) (baseStart_3639987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3639987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3639987 prefixEnd_3639987 := by exact prefixLift 3639987
  have htrace : WordTrace (prefixWord ++ tailWord_3639987) baseStart_3639987 baseEnd_3639987 := by
    simpa [prefixWord, tailWord_3639987, baseEnd_3639987] using wordTrace_append hprefix tailTrace_3639987
  have hstable : (prefixWord ++ tailWord_3639987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639987).length < 2 ^ (prefixWord ++ tailWord_3639987).sum := by decide
  have hdescent : baseEnd_3639987 < baseStart_3639987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640060 : List Nat := [2, 2, 2, 1, 3, 2, 2, 8]
def baseStart_3640060 : Nat := 118140960795 + 3640060 * 2 ^ 59
def prefixEnd_3640060 : Nat := 4983230072969 + 3 ^ 40 * 3640060 * 2
def baseEnd_3640060 : Nat := 138451880830009887571087

theorem tailTrace_3640060 : CollatzResearch.WordTrace tailWord_3640060 prefixEnd_3640060 138451880830009887571087 := by
  unfold tailWord_3640060
  simp only [CollatzResearch.WordTrace]
  refine ⟨66381947596345883799606817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88509263461794511732809089 66381947596345883799606817)
  ·
    refine ⟨49786460697259412849705113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66381947596345883799606817 49786460697259412849705113)
    ·
      refine ⟨37339845522944559637278835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49786460697259412849705113 37339845522944559637278835)
      ·
        refine ⟨56009768284416839455918253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37339845522944559637278835 56009768284416839455918253)
        ·
          refine ⟨21003663106656314795969345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56009768284416839455918253 21003663106656314795969345)
          ·
            refine ⟨15752747329992236096977009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21003663106656314795969345 15752747329992236096977009)
            ·
              refine ⟨11814560497494177072732757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15752747329992236096977009 11814560497494177072732757)
              ·
                refine ⟨138451880830009887571087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11814560497494177072732757 138451880830009887571087)
                ·
                  rfl

theorem cell22_3640060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 8].length) (baseStart_3640060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640060 prefixEnd_3640060 := by exact prefixLift 3640060
  have htrace : WordTrace (prefixWord ++ tailWord_3640060) baseStart_3640060 baseEnd_3640060 := by
    simpa [prefixWord, tailWord_3640060, baseEnd_3640060] using wordTrace_append hprefix tailTrace_3640060
  have hstable : (prefixWord ++ tailWord_3640060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640060).length < 2 ^ (prefixWord ++ tailWord_3640060).sum := by decide
  have hdescent : baseEnd_3640060 < baseStart_3640060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640090 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_3640090 : Nat := 118140960795 + 3640090 * 2 ^ 59
def prefixEnd_3640090 : Nat := 4983230072969 + 3 ^ 40 * 3640090 * 2
def baseEnd_3640090 : Nat := 1246077197083178909889691

theorem tailTrace_3640090 : CollatzResearch.WordTrace tailWord_3640090 prefixEnd_3640090 1246077197083178909889691 := by
  unfold tailWord_3640090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33191247345645770680701431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88509992921722055148537149 33191247345645770680701431)
  ·
    refine ⟨49786871018468656021052147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33191247345645770680701431 49786871018468656021052147)
    ·
      refine ⟨74680306527702984031578221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49786871018468656021052147 74680306527702984031578221)
      ·
        refine ⟨28005114947888619011841833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74680306527702984031578221 28005114947888619011841833)
        ·
          refine ⟨21003836210916464258881375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28005114947888619011841833 21003836210916464258881375)
          ·
            refine ⟨31505754316374696388322063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21003836210916464258881375 31505754316374696388322063)
            ·
              refine ⟨47258631474562044582483095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31505754316374696388322063 47258631474562044582483095)
              ·
                refine ⟨70887947211843066873724643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47258631474562044582483095 70887947211843066873724643)
                ·
                  refine ⟨106331920817764600310586965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70887947211843066873724643 106331920817764600310586965)
                  ·
                    refine ⟨1246077197083178909889691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106331920817764600310586965 1246077197083178909889691)
                    ·
                      rfl

theorem cell22_3640090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_3640090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640090 prefixEnd_3640090 := by exact prefixLift 3640090
  have htrace : WordTrace (prefixWord ++ tailWord_3640090) baseStart_3640090 baseEnd_3640090 := by
    simpa [prefixWord, tailWord_3640090, baseEnd_3640090] using wordTrace_append hprefix tailTrace_3640090
  have hstable : (prefixWord ++ tailWord_3640090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640090).length < 2 ^ (prefixWord ++ tailWord_3640090).sum := by decide
  have hdescent : baseEnd_3640090 < baseStart_3640090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640120 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_3640120 : Nat := 118140960795 + 3640120 * 2 ^ 59
def prefixEnd_3640120 : Nat := 4983230072969 + 3 ^ 40 * 3640120 * 2
def baseEnd_3640120 : Nat := 1246087466696268831639599

theorem tailTrace_3640120 : CollatzResearch.WordTrace tailWord_3640120 prefixEnd_3640120 1246087466696268831639599 := by
  unfold tailWord_3640120
  simp only [CollatzResearch.WordTrace]
  refine ⟨66383041786237198923198907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88510722381649598564265209 66383041786237198923198907)
  ·
    refine ⟨99574562679355798384798361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66383041786237198923198907 99574562679355798384798361)
    ·
      refine ⟨74680922009516848788598771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99574562679355798384798361 74680922009516848788598771)
      ·
        refine ⟨112021383014275273182898157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74680922009516848788598771 112021383014275273182898157)
        ·
          refine ⟨42008018630353227443586809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112021383014275273182898157 42008018630353227443586809)
          ·
            refine ⟨31506013972764920582690107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42008018630353227443586809 31506013972764920582690107)
            ·
              refine ⟨47259020959147380874035161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31506013972764920582690107 47259020959147380874035161)
              ·
                refine ⟨35444265719360535655526371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47259020959147380874035161 35444265719360535655526371)
                ·
                  refine ⟨53166398579040803483289557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35444265719360535655526371 53166398579040803483289557)
                  ·
                    refine ⟨1246087466696268831639599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53166398579040803483289557 1246087466696268831639599)
                    ·
                      rfl

theorem cell22_3640120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_3640120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640120 prefixEnd_3640120 := by exact prefixLift 3640120
  have htrace : WordTrace (prefixWord ++ tailWord_3640120) baseStart_3640120 baseEnd_3640120 := by
    simpa [prefixWord, tailWord_3640120, baseEnd_3640120] using wordTrace_append hprefix tailTrace_3640120
  have hstable : (prefixWord ++ tailWord_3640120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640120).length < 2 ^ (prefixWord ++ tailWord_3640120).sum := by decide
  have hdescent : baseEnd_3640120 < baseStart_3640120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640156 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 5]
def baseStart_3640156 : Nat := 118140960795 + 3640156 * 2 ^ 59
def prefixEnd_3640156 : Nat := 4983230072969 + 3 ^ 40 * 3640156 * 2
def baseEnd_3640156 : Nat := 415366596743992245913163

theorem tailTrace_3640156 : CollatzResearch.WordTrace tailWord_3640156 prefixEnd_3640156 415366596743992245913163 := by
  unfold tailWord_3640156
  simp only [CollatzResearch.WordTrace]
  refine ⟨66383698300171987997354161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88511597733562650663138881 66383698300171987997354161)
  ·
    refine ⟨49787773725128990998015621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66383698300171987997354161 49787773725128990998015621)
    ·
      refine ⟨9335207573461685812127929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49787773725128990998015621 9335207573461685812127929)
      ·
        refine ⟨7001405680096264359095947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9335207573461685812127929 7001405680096264359095947)
        ·
          refine ⟨10502108520144396538643921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7001405680096264359095947 10502108520144396538643921)
          ·
            refine ⟨7876581390108297403982941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10502108520144396538643921 7876581390108297403982941)
            ·
              refine ⟨2953718021290611526493603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7876581390108297403982941 2953718021290611526493603)
              ·
                refine ⟨4430577031935917289740405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953718021290611526493603 4430577031935917289740405)
                ·
                  refine ⟨415366596743992245913163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4430577031935917289740405 415366596743992245913163)
                  ·
                    rfl

theorem cell22_3640156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_3640156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640156 prefixEnd_3640156 := by exact prefixLift 3640156
  have htrace : WordTrace (prefixWord ++ tailWord_3640156) baseStart_3640156 baseEnd_3640156 := by
    simpa [prefixWord, tailWord_3640156, baseEnd_3640156] using wordTrace_append hprefix tailTrace_3640156
  have hstable : (prefixWord ++ tailWord_3640156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640156).length < 2 ^ (prefixWord ++ tailWord_3640156).sum := by decide
  have hdescent : baseEnd_3640156 < baseStart_3640156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640167 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 6]
def baseStart_3640167 : Nat := 118140960795 + 3640167 * 2 ^ 59
def prefixEnd_3640167 : Nat := 4983230072969 + 3 ^ 40 * 3640167 * 2
def baseEnd_3640167 : Nat := 415367851918925458571485

theorem tailTrace_3640167 : CollatzResearch.WordTrace tailWord_3640167 prefixEnd_3640167 415367851918925458571485 := by
  unfold tailWord_3640167
  simp only [CollatzResearch.WordTrace]
  refine ⟨132767797803304124873358755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88511865202202749915572503 132767797803304124873358755)
  ·
    refine ⟨199151696704956187310038133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132767797803304124873358755 199151696704956187310038133)
    ·
      refine ⟨18670471566089642560316075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199151696704956187310038133 18670471566089642560316075)
      ·
        refine ⟨28005707349134463840474113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18670471566089642560316075 28005707349134463840474113)
        ·
          refine ⟨21004280511850847880355585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28005707349134463840474113 21004280511850847880355585)
          ·
            refine ⟨15753210383888135910266689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21004280511850847880355585 15753210383888135910266689)
            ·
              refine ⟨11814907787916101932700017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15753210383888135910266689 11814907787916101932700017)
              ·
                refine ⟨8861180840937076449525013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11814907787916101932700017 8861180840937076449525013)
                ·
                  refine ⟨415367851918925458571485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8861180840937076449525013 415367851918925458571485)
                  ·
                    rfl

theorem cell22_3640167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 6].length) (baseStart_3640167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640167 prefixEnd_3640167 := by exact prefixLift 3640167
  have htrace : WordTrace (prefixWord ++ tailWord_3640167) baseStart_3640167 baseEnd_3640167 := by
    simpa [prefixWord, tailWord_3640167, baseEnd_3640167] using wordTrace_append hprefix tailTrace_3640167
  have hstable : (prefixWord ++ tailWord_3640167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640167).length < 2 ^ (prefixWord ++ tailWord_3640167).sum := by decide
  have hdescent : baseEnd_3640167 < baseStart_3640167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640197 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_3640197 : Nat := 118140960795 + 3640197 * 2 ^ 59
def prefixEnd_3640197 : Nat := 4983230072969 + 3 ^ 40 * 3640197 * 2
def baseEnd_3640197 : Nat := 1246113825369866297464363

theorem tailTrace_3640197 : CollatzResearch.WordTrace tailWord_3640197 prefixEnd_3640197 1246113825369866297464363 := by
  unfold tailWord_3640197
  simp only [CollatzResearch.WordTrace]
  refine ⟨132768891993195439996950845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88512594662130293331300563 132768891993195439996950845)
  ·
    refine ⟨49788334497448289998856567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132768891993195439996950845 49788334497448289998856567)
    ·
      refine ⟨74682501746172434998284851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49788334497448289998856567 74682501746172434998284851)
      ·
        refine ⟨112023752619258652497427277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74682501746172434998284851 112023752619258652497427277)
        ·
          refine ⟨42008907232221994686535229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112023752619258652497427277 42008907232221994686535229)
          ·
            refine ⟨15753340212083248007450711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42008907232221994686535229 15753340212083248007450711)
            ·
              refine ⟨23630010318124872011176067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15753340212083248007450711 23630010318124872011176067)
              ·
                refine ⟨35445015477187308016764101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23630010318124872011176067 35445015477187308016764101)
                ·
                  refine ⟨6645940401972620253143269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35445015477187308016764101 6645940401972620253143269)
                  ·
                    refine ⟨1246113825369866297464363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6645940401972620253143269 1246113825369866297464363)
                    ·
                      rfl

theorem cell22_3640197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_3640197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640197 prefixEnd_3640197 := by exact prefixLift 3640197
  have htrace : WordTrace (prefixWord ++ tailWord_3640197) baseStart_3640197 baseEnd_3640197 := by
    simpa [prefixWord, tailWord_3640197, baseEnd_3640197] using wordTrace_append hprefix tailTrace_3640197
  have hstable : (prefixWord ++ tailWord_3640197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640197).length < 2 ^ (prefixWord ++ tailWord_3640197).sum := by decide
  have hdescent : baseEnd_3640197 < baseStart_3640197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640199 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 4, 3]
def baseStart_3640199 : Nat := 118140960795 + 3640199 * 2 ^ 59
def prefixEnd_3640199 : Nat := 4983230072969 + 3 ^ 40 * 3640199 * 2
def baseEnd_3640199 : Nat := 1246114510010738958914357

theorem tailTrace_3640199 : CollatzResearch.WordTrace tailWord_3640199 prefixEnd_3640199 1246114510010738958914357 := by
  unfold tailWord_3640199
  simp only [CollatzResearch.WordTrace]
  refine ⟨132768964939188194338523651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88512643292792129559015767 132768964939188194338523651)
  ·
    refine ⟨199153447408782291507785477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132768964939188194338523651 199153447408782291507785477)
    ·
      refine ⟨37341271389146679657709777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199153447408782291507785477 37341271389146679657709777)
      ·
        refine ⟨28005953541860009743282333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37341271389146679657709777 28005953541860009743282333)
        ·
          refine ⟨10502232578197503653730875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28005953541860009743282333 10502232578197503653730875)
          ·
            refine ⟨15753348867296255480596313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502232578197503653730875 15753348867296255480596313)
            ·
              refine ⟨11815011650472191610447235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15753348867296255480596313 11815011650472191610447235)
              ·
                refine ⟨17722517475708287415670853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11815011650472191610447235 17722517475708287415670853)
                ·
                  refine ⟨3322972026695303890438285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17722517475708287415670853 3322972026695303890438285)
                  ·
                    refine ⟨1246114510010738958914357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3322972026695303890438285 1246114510010738958914357)
                    ·
                      rfl

theorem cell22_3640199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_3640199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640199 prefixEnd_3640199 := by exact prefixLift 3640199
  have htrace : WordTrace (prefixWord ++ tailWord_3640199) baseStart_3640199 baseEnd_3640199 := by
    simpa [prefixWord, tailWord_3640199, baseEnd_3640199] using wordTrace_append hprefix tailTrace_3640199
  have hstable : (prefixWord ++ tailWord_3640199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640199).length < 2 ^ (prefixWord ++ tailWord_3640199).sum := by decide
  have hdescent : baseEnd_3640199 < baseStart_3640199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640201 : List Nat := [1, 2, 1, 1, 5, 3, 3, 2, 4]
def baseStart_3640201 : Nat := 118140960795 + 3640201 * 2 ^ 59
def prefixEnd_3640201 : Nat := 4983230072969 + 3 ^ 40 * 3640201 * 2
def baseEnd_3640201 : Nat := 415371731550537206788117

theorem tailTrace_3640201 : CollatzResearch.WordTrace tailWord_3640201 prefixEnd_3640201 415371731550537206788117 := by
  unfold tailWord_3640201
  simp only [CollatzResearch.WordTrace]
  refine ⟨132769037885180948680096457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88512691923453965786730971 132769037885180948680096457)
  ·
    refine ⟨99576778413885711510072343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132769037885180948680096457 99576778413885711510072343)
    ·
      refine ⟨149365167620828567265108515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99576778413885711510072343 149365167620828567265108515)
      ·
        refine ⟨224047751431242850897662773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149365167620828567265108515 224047751431242850897662773)
        ·
          refine ⟨21004476696679017271655885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224047751431242850897662773 21004476696679017271655885)
          ·
            refine ⟨7876678761254631476870957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21004476696679017271655885 7876678761254631476870957)
            ·
              refine ⟨2953754535470486803826609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7876678761254631476870957 2953754535470486803826609)
              ·
                refine ⟨2215315901602865102869957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2953754535470486803826609 2215315901602865102869957)
                ·
                  refine ⟨415371731550537206788117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2215315901602865102869957 415371731550537206788117)
                  ·
                    rfl

theorem cell22_3640201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 4].length) (baseStart_3640201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640201 prefixEnd_3640201 := by exact prefixLift 3640201
  have htrace : WordTrace (prefixWord ++ tailWord_3640201) baseStart_3640201 baseEnd_3640201 := by
    simpa [prefixWord, tailWord_3640201, baseEnd_3640201] using wordTrace_append hprefix tailTrace_3640201
  have hstable : (prefixWord ++ tailWord_3640201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640201).length < 2 ^ (prefixWord ++ tailWord_3640201).sum := by decide
  have hdescent : baseEnd_3640201 < baseStart_3640201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640231 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3640231 : Nat := 118140960795 + 3640231 * 2 ^ 59
def prefixEnd_3640231 : Nat := 4983230072969 + 3 ^ 40 * 3640231 * 2
def baseEnd_3640231 : Nat := 1246125464264701542114259

theorem tailTrace_3640231 : CollatzResearch.WordTrace tailWord_3640231 prefixEnd_3640231 1246125464264701542114259 := by
  unfold tailWord_3640231
  simp only [CollatzResearch.WordTrace]
  refine ⟨132770132075072263803688547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88513421383381509202459031 132770132075072263803688547)
  ·
    refine ⟨199155198112608395705532821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132770132075072263803688547 199155198112608395705532821)
    ·
      refine ⟨9335399911528518548696851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199155198112608395705532821 9335399911528518548696851)
      ·
        refine ⟨14003099867292777823045277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335399911528518548696851 14003099867292777823045277)
        ·
          refine ⟨5251162450234791683641979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14003099867292777823045277 5251162450234791683641979)
          ·
            refine ⟨7876743675352187525462969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5251162450234791683641979 7876743675352187525462969)
            ·
              refine ⟨5907557756514140644097227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7876743675352187525462969 5907557756514140644097227)
              ·
                refine ⟨8861336634771210966145841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907557756514140644097227 8861336634771210966145841)
                ·
                  refine ⟨6646002476078408224609381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8861336634771210966145841 6646002476078408224609381)
                  ·
                    refine ⟨1246125464264701542114259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6646002476078408224609381 1246125464264701542114259)
                    ·
                      rfl

theorem cell22_3640231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3640231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640231 prefixEnd_3640231 := by exact prefixLift 3640231
  have htrace : WordTrace (prefixWord ++ tailWord_3640231) baseStart_3640231 baseEnd_3640231 := by
    simpa [prefixWord, tailWord_3640231, baseEnd_3640231] using wordTrace_append hprefix tailTrace_3640231
  have hstable : (prefixWord ++ tailWord_3640231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640231).length < 2 ^ (prefixWord ++ tailWord_3640231).sum := by decide
  have hdescent : baseEnd_3640231 < baseStart_3640231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640246 : List Nat := [5, 1, 4, 1, 11]
def baseStart_3640246 : Nat := 118140960795 + 3640246 * 2 ^ 59
def prefixEnd_3640246 : Nat := 4983230072969 + 3 ^ 40 * 3640246 * 2
def baseEnd_3640246 : Nat := 5128109461198545279791

theorem tailTrace_3640246 : CollatzResearch.WordTrace tailWord_3640246 prefixEnd_3640246 5128109461198545279791 := by
  unfold tailWord_3640246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8298167448126120085342787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88513786113345280910323061 8298167448126120085342787)
  ·
    refine ⟨12447251172189180128014181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8298167448126120085342787 12447251172189180128014181)
    ·
      refine ⟨2333859594785471274002659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12447251172189180128014181 2333859594785471274002659)
      ·
        refine ⟨3500789392178206911003989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333859594785471274002659 3500789392178206911003989)
        ·
          refine ⟨5128109461198545279791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3500789392178206911003989 5128109461198545279791)
          ·
            rfl

theorem cell22_3640246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 11].length) (baseStart_3640246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640246 prefixEnd_3640246 := by exact prefixLift 3640246
  have htrace : WordTrace (prefixWord ++ tailWord_3640246) baseStart_3640246 baseEnd_3640246 := by
    simpa [prefixWord, tailWord_3640246, baseEnd_3640246] using wordTrace_append hprefix tailTrace_3640246
  have hstable : (prefixWord ++ tailWord_3640246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640246).length < 2 ^ (prefixWord ++ tailWord_3640246).sum := by decide
  have hdescent : baseEnd_3640246 < baseStart_3640246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640278 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3640278 : Nat := 118140960795 + 3640278 * 2 ^ 59
def prefixEnd_3640278 : Nat := 4983230072969 + 3 ^ 40 * 3640278 * 2
def baseEnd_3640278 : Nat := 1246141553325209086189115

theorem tailTrace_3640278 : CollatzResearch.WordTrace tailWord_3640278 prefixEnd_3640278 1246141553325209086189115 := by
  unfold tailWord_3640278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8298240394118874426915593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88514564203934660553766325 8298240394118874426915593)
  ·
    refine ⟨6223680295589155820186695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8298240394118874426915593 6223680295589155820186695)
    ·
      refine ⟨9335520443383733730280043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223680295589155820186695 9335520443383733730280043)
      ·
        refine ⟨14003280665075600595420065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335520443383733730280043 14003280665075600595420065)
        ·
          refine ⟨10502460498806700446565049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14003280665075600595420065 10502460498806700446565049)
          ·
            refine ⟨7876845374105025334923787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10502460498806700446565049 7876845374105025334923787)
            ·
              refine ⟨11815268061157538002385681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7876845374105025334923787 11815268061157538002385681)
              ·
                refine ⟨8861451045868153501789261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11815268061157538002385681 8861451045868153501789261)
                ·
                  refine ⟨3323044142200557563170973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8861451045868153501789261 3323044142200557563170973)
                  ·
                    refine ⟨1246141553325209086189115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3323044142200557563170973 1246141553325209086189115)
                    ·
                      rfl

theorem cell22_3640278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3640278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640278 prefixEnd_3640278 := by exact prefixLift 3640278
  have htrace : WordTrace (prefixWord ++ tailWord_3640278) baseStart_3640278 baseEnd_3640278 := by
    simpa [prefixWord, tailWord_3640278, baseEnd_3640278] using wordTrace_append hprefix tailTrace_3640278
  have hstable : (prefixWord ++ tailWord_3640278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640278).length < 2 ^ (prefixWord ++ tailWord_3640278).sum := by decide
  have hdescent : baseEnd_3640278 < baseStart_3640278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640353 : List Nat := [1, 2, 3, 2, 3, 3, 1, 3, 4]
def baseStart_3640353 : Nat := 118140960795 + 3640353 * 2 ^ 59
def prefixEnd_3640353 : Nat := 4983230072969 + 3 ^ 40 * 3640353 * 2
def baseEnd_3640353 : Nat := 415389075785977963521295

theorem tailTrace_3640353 : CollatzResearch.WordTrace tailWord_3640353 prefixEnd_3640353 415389075785977963521295 := by
  unfold tailWord_3640353
  simp only [CollatzResearch.WordTrace]
  refine ⟨132774581780630278639629713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88516387853753519093086475 132774581780630278639629713)
  ·
    refine ⟨99580936335472708979722285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132774581780630278639629713 99580936335472708979722285)
    ·
      refine ⟨37342851125802265867395857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99580936335472708979722285 37342851125802265867395857)
      ·
        refine ⟨28007138344351699400546893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37342851125802265867395857 28007138344351699400546893)
        ·
          refine ⟨10502676879131887275205085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28007138344351699400546893 10502676879131887275205085)
          ·
            refine ⟨3938503829674457728201907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10502676879131887275205085 3938503829674457728201907)
            ·
              refine ⟨5907755744511686592302861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938503829674457728201907 5907755744511686592302861)
              ·
                refine ⟨2215408404191882472113573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5907755744511686592302861 2215408404191882472113573)
                ·
                  refine ⟨415389075785977963521295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2215408404191882472113573 415389075785977963521295)
                  ·
                    rfl

theorem cell22_3640353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 4].length) (baseStart_3640353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640353 prefixEnd_3640353 := by exact prefixLift 3640353
  have htrace : WordTrace (prefixWord ++ tailWord_3640353) baseStart_3640353 baseEnd_3640353 := by
    simpa [prefixWord, tailWord_3640353, baseEnd_3640353] using wordTrace_append hprefix tailTrace_3640353
  have hstable : (prefixWord ++ tailWord_3640353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640353).length < 2 ^ (prefixWord ++ tailWord_3640353).sum := by decide
  have hdescent : baseEnd_3640353 < baseStart_3640353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640366 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3640366 : Nat := 118140960795 + 3640366 * 2 ^ 59
def prefixEnd_3640366 : Nat := 4983230072969 + 3 ^ 40 * 3640366 * 2
def baseEnd_3640366 : Nat := 1246171677523606189988845

theorem tailTrace_3640366 : CollatzResearch.WordTrace tailWord_3640366 prefixEnd_3640366 1246171677523606189988845 := by
  unfold tailWord_3640366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16596881991197897732481619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88516703953055454573235301 16596881991197897732481619)
  ·
    refine ⟨24895322986796846598722429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16596881991197897732481619 24895322986796846598722429)
    ·
      refine ⟨9335746120048817474520911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24895322986796846598722429 9335746120048817474520911)
      ·
        refine ⟨14003619180073226211781367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335746120048817474520911 14003619180073226211781367)
        ·
          refine ⟨21005428770109839317672051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14003619180073226211781367 21005428770109839317672051)
          ·
            refine ⟨31508143155164758976508077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21005428770109839317672051 31508143155164758976508077)
            ·
              refine ⟨11815553683186784616190529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31508143155164758976508077 11815553683186784616190529)
              ·
                refine ⟨8861665262390088462142897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11815553683186784616190529 8861665262390088462142897)
                ·
                  refine ⟨6646248946792566346607173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8861665262390088462142897 6646248946792566346607173)
                  ·
                    refine ⟨1246171677523606189988845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6646248946792566346607173 1246171677523606189988845)
                    ·
                      rfl

theorem cell22_3640366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3640366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640366 prefixEnd_3640366 := by exact prefixLift 3640366
  have htrace : WordTrace (prefixWord ++ tailWord_3640366) baseStart_3640366 baseEnd_3640366 := by
    simpa [prefixWord, tailWord_3640366, baseEnd_3640366] using wordTrace_append hprefix tailTrace_3640366
  have hstable : (prefixWord ++ tailWord_3640366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640366).length < 2 ^ (prefixWord ++ tailWord_3640366).sum := by decide
  have hdescent : baseEnd_3640366 < baseStart_3640366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640426 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_3640426 : Nat := 118140960795 + 3640426 * 2 ^ 59
def prefixEnd_3640426 : Nat := 4983230072969 + 3 ^ 40 * 3640426 * 2
def baseEnd_3640426 : Nat := 415397405583262011162887

theorem tailTrace_3640426 : CollatzResearch.WordTrace tailWord_3640426 prefixEnd_3640426 415397405583262011162887 := by
  unfold tailWord_3640426
  simp only [CollatzResearch.WordTrace]
  refine ⟨33194311077341453026759283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88518162872910541404691421 33194311077341453026759283)
  ·
    refine ⟨49791466616012179540138925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33194311077341453026759283 49791466616012179540138925)
    ·
      refine ⟨18671799981004567327552097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49791466616012179540138925 18671799981004567327552097)
      ·
        refine ⟨14003849985753425495664073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18671799981004567327552097 14003849985753425495664073)
        ·
          refine ⟨10502887489315069121748055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14003849985753425495664073 10502887489315069121748055)
          ·
            refine ⟨15754331233972603682622083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502887489315069121748055 15754331233972603682622083)
            ·
              refine ⟨23631496850958905523933125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15754331233972603682622083 23631496850958905523933125)
              ·
                refine ⟨4430905659554794785737461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23631496850958905523933125 4430905659554794785737461)
                ·
                  refine ⟨415397405583262011162887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4430905659554794785737461 415397405583262011162887)
                  ·
                    rfl

theorem cell22_3640426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_3640426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640426 prefixEnd_3640426 := by exact prefixLift 3640426
  have htrace : WordTrace (prefixWord ++ tailWord_3640426) baseStart_3640426 baseEnd_3640426 := by
    simpa [prefixWord, tailWord_3640426, baseEnd_3640426] using wordTrace_append hprefix tailTrace_3640426
  have hstable : (prefixWord ++ tailWord_3640426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640426).length < 2 ^ (prefixWord ++ tailWord_3640426).sum := by decide
  have hdescent : baseEnd_3640426 < baseStart_3640426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640430 : List Nat := [4, 1, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_3640430 : Nat := 118140960795 + 3640430 * 2 ^ 59
def prefixEnd_3640430 : Nat := 4983230072969 + 3 ^ 40 * 3640430 * 2
def baseEnd_3640430 : Nat := 1246193586031531356388649

theorem tailTrace_3640430 : CollatzResearch.WordTrace tailWord_3640430 prefixEnd_3640430 1246193586031531356388649 := by
  unfold tailWord_3640430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16597173775168915098772843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88518260134234213860121829 16597173775168915098772843)
  ·
    refine ⟨24895760662753372648159265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16597173775168915098772843 24895760662753372648159265)
    ·
      refine ⟨18671820497065029486119449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24895760662753372648159265 18671820497065029486119449)
      ·
        refine ⟨14003865372798772114589587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18671820497065029486119449 14003865372798772114589587)
        ·
          refine ⟨21005798059198158171884381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14003865372798772114589587 21005798059198158171884381)
          ·
            refine ⟨7877174272199309314456643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21005798059198158171884381 7877174272199309314456643)
            ·
              refine ⟨11815761408298963971684965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7877174272199309314456643 11815761408298963971684965)
              ·
                refine ⟨2215455264056055744690931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11815761408298963971684965 2215455264056055744690931)
                ·
                  refine ⟨3323182896084083617036397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215455264056055744690931 3323182896084083617036397)
                  ·
                    refine ⟨1246193586031531356388649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3323182896084083617036397 1246193586031531356388649)
                    ·
                      rfl

theorem cell22_3640430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_3640430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640430 prefixEnd_3640430 := by exact prefixLift 3640430
  have htrace : WordTrace (prefixWord ++ tailWord_3640430) baseStart_3640430 baseEnd_3640430 := by
    simpa [prefixWord, tailWord_3640430, baseEnd_3640430] using wordTrace_append hprefix tailTrace_3640430
  have hstable : (prefixWord ++ tailWord_3640430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640430).length < 2 ^ (prefixWord ++ tailWord_3640430).sum := by decide
  have hdescent : baseEnd_3640430 < baseStart_3640430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640439 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 5, 4]
def baseStart_3640439 : Nat := 118140960795 + 3640439 * 2 ^ 59
def prefixEnd_3640439 : Nat := 4983230072969 + 3 ^ 40 * 3640439 * 2
def baseEnd_3640439 : Nat := 1246196666915458332913621

theorem tailTrace_3640439 : CollatzResearch.WordTrace tailWord_3640439 prefixEnd_3640439 1246196666915458332913621 := by
  unfold tailWord_3640439
  simp only [CollatzResearch.WordTrace]
  refine ⟨132777718458318715327260371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88518478972212476884840247 132777718458318715327260371)
  ·
    refine ⟨199166577687478072990890557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132777718458318715327260371 199166577687478072990890557)
    ·
      refine ⟨74687466632804277371583959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199166577687478072990890557 74687466632804277371583959)
      ·
        refine ⟨112031199949206416057375939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74687466632804277371583959 112031199949206416057375939)
        ·
          refine ⟨168046799923809624086063909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112031199949206416057375939 168046799923809624086063909)
          ·
            refine ⟨31508774985714304516136983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168046799923809624086063909 31508774985714304516136983)
            ·
              refine ⟨47263162478571456774205475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31508774985714304516136983 47263162478571456774205475)
              ·
                refine ⟨70894743717857185161308213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47263162478571456774205475 70894743717857185161308213)
                ·
                  refine ⟨6646382223549111108872645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70894743717857185161308213 6646382223549111108872645)
                  ·
                    refine ⟨1246196666915458332913621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6646382223549111108872645 1246196666915458332913621)
                    ·
                      rfl

theorem cell22_3640439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_3640439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640439 prefixEnd_3640439 := by exact prefixLift 3640439
  have htrace : WordTrace (prefixWord ++ tailWord_3640439) baseStart_3640439 baseEnd_3640439 := by
    simpa [prefixWord, tailWord_3640439, baseEnd_3640439] using wordTrace_append hprefix tailTrace_3640439
  have hstable : (prefixWord ++ tailWord_3640439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640439).length < 2 ^ (prefixWord ++ tailWord_3640439).sum := by decide
  have hdescent : baseEnd_3640439 < baseStart_3640439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640441 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_3640441 : Nat := 118140960795 + 3640441 * 2 ^ 59
def prefixEnd_3640441 : Nat := 4983230072969 + 3 ^ 40 * 3640441 * 2
def baseEnd_3640441 : Nat := 1246197351556330994363615

theorem tailTrace_3640441 : CollatzResearch.WordTrace tailWord_3640441 prefixEnd_3640441 1246197351556330994363615 := by
  unfold tailWord_3640441
  simp only [CollatzResearch.WordTrace]
  refine ⟨132777791404311469668833177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88518527602874313112555451 132777791404311469668833177)
  ·
    refine ⟨99583343553233602251624883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132777791404311469668833177 99583343553233602251624883)
    ·
      refine ⟨149375015329850403377437325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99583343553233602251624883 149375015329850403377437325)
      ·
        refine ⟨56015630748693901266538997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149375015329850403377437325 56015630748693901266538997)
        ·
          refine ⟨5251465382690053243738031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56015630748693901266538997 5251465382690053243738031)
          ·
            refine ⟨7877198074035079865607047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5251465382690053243738031 7877198074035079865607047)
            ·
              refine ⟨11815797111052619798410571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7877198074035079865607047 11815797111052619798410571)
              ·
                refine ⟨17723695666578929697615857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11815797111052619798410571 17723695666578929697615857)
                ·
                  refine ⟨13292771749934197273211893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17723695666578929697615857 13292771749934197273211893)
                  ·
                    refine ⟨1246197351556330994363615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13292771749934197273211893 1246197351556330994363615)
                    ·
                      rfl

theorem cell22_3640441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_3640441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640441 prefixEnd_3640441 := by exact prefixLift 3640441
  have htrace : WordTrace (prefixWord ++ tailWord_3640441) baseStart_3640441 baseEnd_3640441 := by
    simpa [prefixWord, tailWord_3640441, baseEnd_3640441] using wordTrace_append hprefix tailTrace_3640441
  have hstable : (prefixWord ++ tailWord_3640441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640441).length < 2 ^ (prefixWord ++ tailWord_3640441).sum := by decide
  have hdescent : baseEnd_3640441 < baseStart_3640441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640469 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3640469 : Nat := 118140960795 + 3640469 * 2 ^ 59
def prefixEnd_3640469 : Nat := 4983230072969 + 3 ^ 40 * 3640469 * 2
def baseEnd_3640469 : Nat := 1246206936528548254663529

theorem tailTrace_3640469 : CollatzResearch.WordTrace tailWord_3640469 prefixEnd_3640469 1246206936528548254663529 := by
  unfold tailWord_3640469
  simp only [CollatzResearch.WordTrace]
  refine ⟨132778812648210030450852461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88519208432140020300568307 132778812648210030450852461)
  ·
    refine ⟨49792054743078761419069673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132778812648210030450852461 49792054743078761419069673)
    ·
      refine ⟨37344041057309071064302255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49792054743078761419069673 37344041057309071064302255)
      ·
        refine ⟨56016061585963606596453383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37344041057309071064302255 56016061585963606596453383)
        ·
          refine ⟨84024092378945409894680075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56016061585963606596453383 84024092378945409894680075)
          ·
            refine ⟨126036138568418114842020113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84024092378945409894680075 126036138568418114842020113)
            ·
              refine ⟨94527103926313586131515085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126036138568418114842020113 94527103926313586131515085)
              ·
                refine ⟨35447663972367594799318157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94527103926313586131515085 35447663972367594799318157)
                ·
                  refine ⟨13292873989637848049744309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35447663972367594799318157 13292873989637848049744309)
                  ·
                    refine ⟨1246206936528548254663529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13292873989637848049744309 1246206936528548254663529)
                    ·
                      rfl

theorem cell22_3640469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3640469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640469 prefixEnd_3640469 := by exact prefixLift 3640469
  have htrace : WordTrace (prefixWord ++ tailWord_3640469) baseStart_3640469 baseEnd_3640469 := by
    simpa [prefixWord, tailWord_3640469, baseEnd_3640469] using wordTrace_append hprefix tailTrace_3640469
  have hstable : (prefixWord ++ tailWord_3640469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640469).length < 2 ^ (prefixWord ++ tailWord_3640469).sum := by decide
  have hdescent : baseEnd_3640469 < baseStart_3640469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640529 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_3640529 : Nat := 118140960795 + 3640529 * 2 ^ 59
def prefixEnd_3640529 : Nat := 4983230072969 + 3 ^ 40 * 3640529 * 2
def baseEnd_3640529 : Nat := 1246227475754728098163345

theorem tailTrace_3640529 : CollatzResearch.WordTrace tailWord_3640529 prefixEnd_3640529 1246227475754728098163345 := by
  unfold tailWord_3640529
  simp only [CollatzResearch.WordTrace]
  refine ⟨132781001027992660698036641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88520667351995107132024427 132781001027992660698036641)
  ·
    refine ⟨99585750770994495523527481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132781001027992660698036641 99585750770994495523527481)
    ·
      refine ⟨74689313078245871642645611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99585750770994495523527481 74689313078245871642645611)
      ·
        refine ⟨112033969617368807463968417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74689313078245871642645611 112033969617368807463968417)
        ·
          refine ⟨84025477213026605597976313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112033969617368807463968417 84025477213026605597976313)
          ·
            refine ⟨63019107909769954198482235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84025477213026605597976313 63019107909769954198482235)
            ·
              refine ⟨94528661864654931297723353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63019107909769954198482235 94528661864654931297723353)
              ·
                refine ⟨70896496398491198473292515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94528661864654931297723353 70896496398491198473292515)
                ·
                  refine ⟨106344744597736797709938773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70896496398491198473292515 106344744597736797709938773)
                  ·
                    refine ⟨1246227475754728098163345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106344744597736797709938773 1246227475754728098163345)
                    ·
                      rfl

theorem cell22_3640529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_3640529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640529 prefixEnd_3640529 := by exact prefixLift 3640529
  have htrace : WordTrace (prefixWord ++ tailWord_3640529) baseStart_3640529 baseEnd_3640529 := by
    simpa [prefixWord, tailWord_3640529, baseEnd_3640529] using wordTrace_append hprefix tailTrace_3640529
  have hstable : (prefixWord ++ tailWord_3640529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640529).length < 2 ^ (prefixWord ++ tailWord_3640529).sum := by decide
  have hdescent : baseEnd_3640529 < baseStart_3640529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640548 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_3640548 : Nat := 118140960795 + 3640548 * 2 ^ 59
def prefixEnd_3640548 : Nat := 4983230072969 + 3 ^ 40 * 3640548 * 2
def baseEnd_3640548 : Nat := 1246233979843018381938287

theorem tailTrace_3640548 : CollatzResearch.WordTrace tailWord_3640548 prefixEnd_3640548 1246233979843018381938287 := by
  unfold tailWord_3640548
  simp only [CollatzResearch.WordTrace]
  refine ⟨66390847007461913471489149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88521129343282551295318865 66390847007461913471489149)
  ·
    refine ⟨24896567627798217551808431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66390847007461913471489149 24896567627798217551808431)
    ·
      refine ⟨37344851441697326327712647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24896567627798217551808431 37344851441697326327712647)
      ·
        refine ⟨56017277162545989491568971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37344851441697326327712647 56017277162545989491568971)
        ·
          refine ⟨84025915743818984237353457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56017277162545989491568971 84025915743818984237353457)
          ·
            refine ⟨63019436807864238178015093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84025915743818984237353457 63019436807864238178015093)
            ·
              refine ⟨5908072200737272329188915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63019436807864238178015093 5908072200737272329188915)
              ·
                refine ⟨8862108301105908493783373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5908072200737272329188915 8862108301105908493783373)
                ·
                  refine ⟨3323290612914715685168765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8862108301105908493783373 3323290612914715685168765)
                  ·
                    refine ⟨1246233979843018381938287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3323290612914715685168765 1246233979843018381938287)
                    ·
                      rfl

theorem cell22_3640548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_3640548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640548 prefixEnd_3640548 := by exact prefixLift 3640548
  have htrace : WordTrace (prefixWord ++ tailWord_3640548) baseStart_3640548 baseEnd_3640548 := by
    simpa [prefixWord, tailWord_3640548, baseEnd_3640548] using wordTrace_append hprefix tailTrace_3640548
  have hstable : (prefixWord ++ tailWord_3640548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640548).length < 2 ^ (prefixWord ++ tailWord_3640548).sum := by decide
  have hdescent : baseEnd_3640548 < baseStart_3640548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640638 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3640638 : Nat := 118140960795 + 3640638 * 2 ^ 59
def prefixEnd_3640638 : Nat := 4983230072969 + 3 ^ 40 * 3640638 * 2
def baseEnd_3640638 : Nat := 1246264788682288147188011

theorem tailTrace_3640638 : CollatzResearch.WordTrace tailWord_3640638 prefixEnd_3640638 1246264788682288147188011 := by
  unfold tailWord_3640638
  simp only [CollatzResearch.WordTrace]
  refine ⟨16598122073074721539219321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88523317723065181542503045 16598122073074721539219321)
  ·
    refine ⟨12448591554806041154414491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16598122073074721539219321 12448591554806041154414491)
    ·
      refine ⟨18672887332209061731621737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12448591554806041154414491 18672887332209061731621737)
      ·
        refine ⟨14004665499156796298716303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18672887332209061731621737 14004665499156796298716303)
        ·
          refine ⟨21006998248735194448074455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14004665499156796298716303 21006998248735194448074455)
          ·
            refine ⟨31510497373102791672111683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21006998248735194448074455 31510497373102791672111683)
            ·
              refine ⟨47265746059654187508167525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31510497373102791672111683 47265746059654187508167525)
              ·
                refine ⟨8862327386185160157781411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47265746059654187508167525 8862327386185160157781411)
                ·
                  refine ⟨13293491079277740236672117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8862327386185160157781411 13293491079277740236672117)
                  ·
                    refine ⟨1246264788682288147188011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13293491079277740236672117 1246264788682288147188011)
                    ·
                      rfl

theorem cell22_3640638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3640638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640638 prefixEnd_3640638 := by exact prefixLift 3640638
  have htrace : WordTrace (prefixWord ++ tailWord_3640638) baseStart_3640638 baseEnd_3640638 := by
    simpa [prefixWord, tailWord_3640638, baseEnd_3640638] using wordTrace_append hprefix tailTrace_3640638
  have hstable : (prefixWord ++ tailWord_3640638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640638).length < 2 ^ (prefixWord ++ tailWord_3640638).sum := by decide
  have hdescent : baseEnd_3640638 < baseStart_3640638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640646 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3640646 : Nat := 118140960795 + 3640646 * 2 ^ 59
def prefixEnd_3640646 : Nat := 4983230072969 + 3 ^ 40 * 3640646 * 2
def baseEnd_3640646 : Nat := 415422509081926264329329

theorem tailTrace_3640646 : CollatzResearch.WordTrace tailWord_3640646 prefixEnd_3640646 415422509081926264329329 := by
  unfold tailWord_3640646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149539636517774677501431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88523512245712526453363861 4149539636517774677501431)
  ·
    refine ⟨6224309454776662016252147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149539636517774677501431 6224309454776662016252147)
    ·
      refine ⟨9336464182164993024378221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6224309454776662016252147 9336464182164993024378221)
      ·
        refine ⟨3501174068311872384141833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9336464182164993024378221 3501174068311872384141833)
        ·
          refine ⟨2625880551233904288106375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3501174068311872384141833 2625880551233904288106375)
          ·
            refine ⟨3938820826850856432159563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625880551233904288106375 3938820826850856432159563)
            ·
              refine ⟨5908231240276284648239345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938820826850856432159563 5908231240276284648239345)
              ·
                refine ⟨4431173430207213486179509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5908231240276284648239345 4431173430207213486179509)
                ·
                  refine ⟨415422509081926264329329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4431173430207213486179509 415422509081926264329329)
                  ·
                    rfl

theorem cell22_3640646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3640646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640646 prefixEnd_3640646 := by exact prefixLift 3640646
  have htrace : WordTrace (prefixWord ++ tailWord_3640646) baseStart_3640646 baseEnd_3640646 := by
    simpa [prefixWord, tailWord_3640646, baseEnd_3640646] using wordTrace_append hprefix tailTrace_3640646
  have hstable : (prefixWord ++ tailWord_3640646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640646).length < 2 ^ (prefixWord ++ tailWord_3640646).sum := by decide
  have hdescent : baseEnd_3640646 < baseStart_3640646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640672 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 2, 3]
def baseStart_3640672 : Nat := 118140960795 + 3640672 * 2 ^ 59
def prefixEnd_3640672 : Nat := 4983230072969 + 3 ^ 40 * 3640672 * 2
def baseEnd_3640672 : Nat := 1246276427577123391837907

theorem tailTrace_3640672 : CollatzResearch.WordTrace tailWord_3640672 prefixEnd_3640672 1246276427577123391837907 := by
  unfold tailWord_3640672
  simp only [CollatzResearch.WordTrace]
  refine ⟨66393108333237298060246135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88524144444316397413661513 66393108333237298060246135)
  ·
    refine ⟨99589662499855947090369203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66393108333237298060246135 99589662499855947090369203)
    ·
      refine ⟨149384493749783920635553805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99589662499855947090369203 149384493749783920635553805)
      ·
        refine ⟨56019185156168970238332677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149384493749783920635553805 56019185156168970238332677)
        ·
          refine ⟨10503597216781681919687377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56019185156168970238332677 10503597216781681919687377)
          ·
            refine ⟨7877697912586261439765533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10503597216781681919687377 7877697912586261439765533)
            ·
              refine ⟨2954136717219848039912075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7877697912586261439765533 2954136717219848039912075)
              ·
                refine ⟨4431205075829772059868113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954136717219848039912075 4431205075829772059868113)
                ·
                  refine ⟨3323403806872329044901085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4431205075829772059868113 3323403806872329044901085)
                  ·
                    refine ⟨1246276427577123391837907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3323403806872329044901085 1246276427577123391837907)
                    ·
                      rfl

theorem cell22_3640672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 2, 3].length) (baseStart_3640672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640672 prefixEnd_3640672 := by exact prefixLift 3640672
  have htrace : WordTrace (prefixWord ++ tailWord_3640672) baseStart_3640672 baseEnd_3640672 := by
    simpa [prefixWord, tailWord_3640672, baseEnd_3640672] using wordTrace_append hprefix tailTrace_3640672
  have hstable : (prefixWord ++ tailWord_3640672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640672).length < 2 ^ (prefixWord ++ tailWord_3640672).sum := by decide
  have hdescent : baseEnd_3640672 < baseStart_3640672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640685 : List Nat := [1, 5, 1, 1, 1, 5, 2, 6]
def baseStart_3640685 : Nat := 118140960795 + 3640685 * 2 ^ 59
def prefixEnd_3640685 : Nat := 4983230072969 + 3 ^ 40 * 3640685 * 2
def baseEnd_3640685 : Nat := 138475653082532854584763

theorem tailTrace_3640685 : CollatzResearch.WordTrace tailWord_3640685 prefixEnd_3640685 138475653082532854584763 := by
  unfold tailWord_3640685
  simp only [CollatzResearch.WordTrace]
  refine ⟨132786690815427499340715509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88524460543618332893810339 132786690815427499340715509)
  ·
    refine ⟨12448752263946328063192079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132786690815427499340715509 12448752263946328063192079)
    ·
      refine ⟨18673128395919492094788119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12448752263946328063192079 18673128395919492094788119)
      ·
        refine ⟨28009692593879238142182179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18673128395919492094788119 28009692593879238142182179)
        ·
          refine ⟨42014538890818857213273269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28009692593879238142182179 42014538890818857213273269)
          ·
            refine ⟨3938863021014267863744369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42014538890818857213273269 3938863021014267863744369)
            ·
              refine ⟨2954147265760700897808277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3938863021014267863744369 2954147265760700897808277)
              ·
                refine ⟨138475653082532854584763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2954147265760700897808277 138475653082532854584763)
                ·
                  rfl

theorem cell22_3640685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 6].length) (baseStart_3640685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640685 prefixEnd_3640685 := by exact prefixLift 3640685
  have htrace : WordTrace (prefixWord ++ tailWord_3640685) baseStart_3640685 baseEnd_3640685 := by
    simpa [prefixWord, tailWord_3640685, baseEnd_3640685] using wordTrace_append hprefix tailTrace_3640685
  have hstable : (prefixWord ++ tailWord_3640685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640685).length < 2 ^ (prefixWord ++ tailWord_3640685).sum := by decide
  have hdescent : baseEnd_3640685 < baseStart_3640685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640702 : List Nat := [4, 2, 3, 2, 1, 2, 8]
def baseStart_3640702 : Nat := 118140960795 + 3640702 * 2 ^ 59
def prefixEnd_3640702 : Nat := 4983230072969 + 3 ^ 40 * 3640702 * 2
def baseEnd_3640702 : Nat := 46158766562600493095845

theorem tailTrace_3640702 : CollatzResearch.WordTrace tailWord_3640702 prefixEnd_3640702 46158766562600493095845 := by
  unfold tailWord_3640702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16598413857045738905510545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88524873904243940829389573 16598413857045738905510545)
  ·
    refine ⟨12448810392784304179132909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16598413857045738905510545 12448810392784304179132909)
    ·
      refine ⟨4668303897294114067174841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12448810392784304179132909 4668303897294114067174841)
      ·
        refine ⟨3501227922970585550381131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4668303897294114067174841 3501227922970585550381131)
        ·
          refine ⟨5251841884455878325571697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3501227922970585550381131 5251841884455878325571697)
          ·
            refine ⟨3938881413341908744178773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5251841884455878325571697 3938881413341908744178773)
            ·
              refine ⟨46158766562600493095845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3938881413341908744178773 46158766562600493095845)
              ·
                rfl

theorem cell22_3640702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 8].length) (baseStart_3640702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640702 prefixEnd_3640702 := by exact prefixLift 3640702
  have htrace : WordTrace (prefixWord ++ tailWord_3640702) baseStart_3640702 baseEnd_3640702 := by
    simpa [prefixWord, tailWord_3640702, baseEnd_3640702] using wordTrace_append hprefix tailTrace_3640702
  have hstable : (prefixWord ++ tailWord_3640702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640702).length < 2 ^ (prefixWord ++ tailWord_3640702).sum := by decide
  have hdescent : baseEnd_3640702 < baseStart_3640702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640775 : List Nat := [1, 1, 4, 1, 1, 3, 3, 4, 4]
def baseStart_3640775 : Nat := 118140960795 + 3640775 * 2 ^ 59
def prefixEnd_3640775 : Nat := 4983230072969 + 3 ^ 40 * 3640775 * 2
def baseEnd_3640775 : Nat := 415437228860688485504197

theorem tailTrace_3640775 : CollatzResearch.WordTrace tailWord_3640775 prefixEnd_3640775 415437228860688485504197 := by
  unfold tailWord_3640775
  simp only [CollatzResearch.WordTrace]
  refine ⟨132789973385101444711491779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88526648923400963140994519 132789973385101444711491779)
  ·
    refine ⟨199184960077652167067237669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132789973385101444711491779 199184960077652167067237669)
    ·
      refine ⟨37347180014559781325107063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199184960077652167067237669 37347180014559781325107063)
      ·
        refine ⟨56020770021839671987660595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37347180014559781325107063 56020770021839671987660595)
        ·
          refine ⟨84031155032759507981490893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56020770021839671987660595 84031155032759507981490893)
          ·
            refine ⟨31511683137284815493059085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84031155032759507981490893 31511683137284815493059085)
            ·
              refine ⟨11816881176481805809897157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31511683137284815493059085 11816881176481805809897157)
              ·
                refine ⟨2215665220590338589355717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11816881176481805809897157 2215665220590338589355717)
                ·
                  refine ⟨415437228860688485504197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2215665220590338589355717 415437228860688485504197)
                  ·
                    rfl

theorem cell22_3640775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 4].length) (baseStart_3640775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640775 prefixEnd_3640775 := by exact prefixLift 3640775
  have htrace : WordTrace (prefixWord ++ tailWord_3640775) baseStart_3640775 baseEnd_3640775 := by
    simpa [prefixWord, tailWord_3640775, baseEnd_3640775] using wordTrace_append hprefix tailTrace_3640775
  have hstable : (prefixWord ++ tailWord_3640775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640775).length < 2 ^ (prefixWord ++ tailWord_3640775).sum := by decide
  have hdescent : baseEnd_3640775 < baseStart_3640775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640805 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_3640805 : Nat := 118140960795 + 3640805 * 2 ^ 59
def prefixEnd_3640805 : Nat := 4983230072969 + 3 ^ 40 * 3640805 * 2
def baseEnd_3640805 : Nat := 1246321956195155378262499

theorem tailTrace_3640805 : CollatzResearch.WordTrace tailWord_3640805 prefixEnd_3640805 1246321956195155378262499 := by
  unfold tailWord_3640805
  simp only [CollatzResearch.WordTrace]
  refine ⟨132791067574992759835083869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88527378383328506556722579 132791067574992759835083869)
  ·
    refine ⟨49796650340622284938156451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132791067574992759835083869 49796650340622284938156451)
    ·
      refine ⟨74694975510933427407234677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49796650340622284938156451 74694975510933427407234677)
      ·
        refine ⟨7002653954150008819428251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74694975510933427407234677 7002653954150008819428251)
        ·
          refine ⟨10503980931225013229142377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7002653954150008819428251 10503980931225013229142377)
          ·
            refine ⟨7877985698418759921856783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10503980931225013229142377 7877985698418759921856783)
            ·
              refine ⟨11816978547628139882785175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7877985698418759921856783 11816978547628139882785175)
              ·
                refine ⟨17725467821442209824177763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11816978547628139882785175 17725467821442209824177763)
                ·
                  refine ⟨26588201732163314736266645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17725467821442209824177763 26588201732163314736266645)
                  ·
                    refine ⟨1246321956195155378262499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26588201732163314736266645 1246321956195155378262499)
                    ·
                      rfl

theorem cell22_3640805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_3640805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640805 prefixEnd_3640805 := by exact prefixLift 3640805
  have htrace : WordTrace (prefixWord ++ tailWord_3640805) baseStart_3640805 baseEnd_3640805 := by
    simpa [prefixWord, tailWord_3640805, baseEnd_3640805] using wordTrace_append hprefix tailTrace_3640805
  have hstable : (prefixWord ++ tailWord_3640805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640805).length < 2 ^ (prefixWord ++ tailWord_3640805).sum := by decide
  have hdescent : baseEnd_3640805 < baseStart_3640805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640863 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 1, 7]
def baseStart_3640863 : Nat := 118140960795 + 3640863 * 2 ^ 59
def prefixEnd_3640863 : Nat := 4983230072969 + 3 ^ 40 * 3640863 * 2
def baseEnd_3640863 : Nat := 1246341810780462560312321

theorem tailTrace_3640863 : CollatzResearch.WordTrace tailWord_3640863 prefixEnd_3640863 1246341810780462560312321 := by
  unfold tailWord_3640863
  simp only [CollatzResearch.WordTrace]
  refine ⟨132793183008782635740695243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88528788672521757160463495 132793183008782635740695243)
  ·
    refine ⟨199189774513173953611042865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132793183008782635740695243 199189774513173953611042865)
    ·
      refine ⟨149392330884880465208282149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199189774513173953611042865 149392330884880465208282149)
      ·
        refine ⟨28011062040915087226552903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149392330884880465208282149 28011062040915087226552903)
        ·
          refine ⟨42016593061372630839829355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28011062040915087226552903 42016593061372630839829355)
          ·
            refine ⟨63024889592058946259744033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42016593061372630839829355 63024889592058946259744033)
            ·
              refine ⟨47268667194044209694808025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63024889592058946259744033 47268667194044209694808025)
              ·
                refine ⟨35451500395533157271106019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47268667194044209694808025 35451500395533157271106019)
                ·
                  refine ⟨53177250593299735906659029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35451500395533157271106019 53177250593299735906659029)
                  ·
                    refine ⟨1246341810780462560312321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53177250593299735906659029 1246341810780462560312321)
                    ·
                      rfl

theorem cell22_3640863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_3640863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640863 prefixEnd_3640863 := by exact prefixLift 3640863
  have htrace : WordTrace (prefixWord ++ tailWord_3640863) baseStart_3640863 baseEnd_3640863 := by
    simpa [prefixWord, tailWord_3640863, baseEnd_3640863] using wordTrace_append hprefix tailTrace_3640863
  have hstable : (prefixWord ++ tailWord_3640863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640863).length < 2 ^ (prefixWord ++ tailWord_3640863).sum := by decide
  have hdescent : baseEnd_3640863 < baseStart_3640863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640886 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3640886 : Nat := 118140960795 + 3640886 * 2 ^ 59
def prefixEnd_3640886 : Nat := 4983230072969 + 3 ^ 40 * 3640886 * 2
def baseEnd_3640886 : Nat := 1246349684150498166987251

theorem tailTrace_3640886 : CollatzResearch.WordTrace tailWord_3640886 prefixEnd_3640886 1246349684150498166987251 := by
  unfold tailWord_3640886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8299626367981206916798907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88529347925132873779188341 8299626367981206916798907)
  ·
    refine ⟨12449439551971810375198361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8299626367981206916798907 12449439551971810375198361)
    ·
      refine ⟨9337079663978857781398771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12449439551971810375198361 9337079663978857781398771)
      ·
        refine ⟨14005619495968286672098157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9337079663978857781398771 14005619495968286672098157)
        ·
          refine ⟨5252107310988107502036809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14005619495968286672098157 5252107310988107502036809)
          ·
            refine ⟨3939080483241080626527607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5252107310988107502036809 3939080483241080626527607)
            ·
              refine ⟨5908620724861620939791411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939080483241080626527607 5908620724861620939791411)
              ·
                refine ⟨8862931087292431409687117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5908620724861620939791411 8862931087292431409687117)
                ·
                  refine ⟨3323599157734661778632669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8862931087292431409687117 3323599157734661778632669)
                  ·
                    refine ⟨1246349684150498166987251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3323599157734661778632669 1246349684150498166987251)
                    ·
                      rfl

theorem cell22_3640886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3640886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640886 prefixEnd_3640886 := by exact prefixLift 3640886
  have htrace : WordTrace (prefixWord ++ tailWord_3640886) baseStart_3640886 baseEnd_3640886 := by
    simpa [prefixWord, tailWord_3640886, baseEnd_3640886] using wordTrace_append hprefix tailTrace_3640886
  have hstable : (prefixWord ++ tailWord_3640886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640886).length < 2 ^ (prefixWord ++ tailWord_3640886).sum := by decide
  have hdescent : baseEnd_3640886 < baseStart_3640886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640944 : List Nat := [2, 1, 1, 1, 6, 1, 4, 2, 4]
def baseStart_3640944 : Nat := 118140960795 + 3640944 * 2 ^ 59
def prefixEnd_3640944 : Nat := 4983230072969 + 3 ^ 40 * 3640944 * 2
def baseEnd_3640944 : Nat := 415456512911935116345691

theorem tailTrace_3640944 : CollatzResearch.WordTrace tailWord_3640944 prefixEnd_3640944 415456512911935116345691 := by
  unfold tailWord_3640944
  simp only [CollatzResearch.WordTrace]
  refine ⟨66398068660744593287196943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88530758214326124382929257 66398068660744593287196943)
  ·
    refine ⟨99597102991116889930795415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66398068660744593287196943 99597102991116889930795415)
    ·
      refine ⟨149395654486675334896193123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99597102991116889930795415 149395654486675334896193123)
      ·
        refine ⟨224093481730013002344289685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149395654486675334896193123 224093481730013002344289685)
        ·
          refine ⟨10504381956094359484888579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 224093481730013002344289685 10504381956094359484888579)
          ·
            refine ⟨15756572934141539227332869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10504381956094359484888579 15756572934141539227332869)
            ·
              refine ⟨2954357425151538605124913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15756572934141539227332869 2954357425151538605124913)
              ·
                refine ⟨2215768068863653953843685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954357425151538605124913 2215768068863653953843685)
                ·
                  refine ⟨415456512911935116345691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2215768068863653953843685 415456512911935116345691)
                  ·
                    rfl

theorem cell22_3640944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 4].length) (baseStart_3640944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640944 prefixEnd_3640944 := by exact prefixLift 3640944
  have htrace : WordTrace (prefixWord ++ tailWord_3640944) baseStart_3640944 baseEnd_3640944 := by
    simpa [prefixWord, tailWord_3640944, baseEnd_3640944] using wordTrace_append hprefix tailTrace_3640944
  have hstable : (prefixWord ++ tailWord_3640944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640944).length < 2 ^ (prefixWord ++ tailWord_3640944).sum := by decide
  have hdescent : baseEnd_3640944 < baseStart_3640944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640974 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_3640974 : Nat := 118140960795 + 3640974 * 2 ^ 59
def prefixEnd_3640974 : Nat := 4983230072969 + 3 ^ 40 * 3640974 * 2
def baseEnd_3640974 : Nat := 1246379808348895270786981

theorem tailTrace_3640974 : CollatzResearch.WordTrace tailWord_3640974 prefixEnd_3640974 1246379808348895270786981 := by
  unfold tailWord_3640974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16599653938922562712248247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88531487674253667798657317 16599653938922562712248247)
  ·
    refine ⟨24899480908383844068372371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16599653938922562712248247 24899480908383844068372371)
    ·
      refine ⟨37349221362575766102558557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24899480908383844068372371 37349221362575766102558557)
      ·
        refine ⟨14005958010965912288459459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37349221362575766102558557 14005958010965912288459459)
        ·
          refine ⟨21008937016448868432689189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14005958010965912288459459 21008937016448868432689189)
          ·
            refine ⟨3939175690584162831129223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21008937016448868432689189 3939175690584162831129223)
            ·
              refine ⟨5908763535876244246693835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939175690584162831129223 5908763535876244246693835)
              ·
                refine ⟨8863145303814366370040753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5908763535876244246693835 8863145303814366370040753)
                ·
                  refine ⟨6647358977860774777530565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8863145303814366370040753 6647358977860774777530565)
                  ·
                    refine ⟨1246379808348895270786981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647358977860774777530565 1246379808348895270786981)
                    ·
                      rfl

theorem cell22_3640974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_3640974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3640974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3640974 prefixEnd_3640974 := by exact prefixLift 3640974
  have htrace : WordTrace (prefixWord ++ tailWord_3640974) baseStart_3640974 baseEnd_3640974 := by
    simpa [prefixWord, tailWord_3640974, baseEnd_3640974] using wordTrace_append hprefix tailTrace_3640974
  have hstable : (prefixWord ++ tailWord_3640974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640974).length < 2 ^ (prefixWord ++ tailWord_3640974).sum := by decide
  have hdescent : baseEnd_3640974 < baseStart_3640974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641047 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 1, 4]
def baseStart_3641047 : Nat := 118140960795 + 3641047 * 2 ^ 59
def prefixEnd_3641047 : Nat := 4983230072969 + 3 ^ 40 * 3641047 * 2
def baseEnd_3641047 : Nat := 1246404797740747413711757

theorem tailTrace_3641047 : CollatzResearch.WordTrace tailWord_3641047 prefixEnd_3641047 1246404797740747413711757 := by
  unfold tailWord_3641047
  simp only [CollatzResearch.WordTrace]
  refine ⟨132799894040116035165393395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88533262693410690110262263 132799894040116035165393395)
  ·
    refine ⟨199199841060174052748090093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132799894040116035165393395 199199841060174052748090093)
    ·
      refine ⟨74699940397565269780533785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199199841060174052748090093 74699940397565269780533785)
      ·
        refine ⟨56024955298173952335400339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74699940397565269780533785 56024955298173952335400339)
        ·
          refine ⟨84037432947260928503100509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56024955298173952335400339 84037432947260928503100509)
          ·
            refine ⟨31514037355222848188662691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84037432947260928503100509 31514037355222848188662691)
            ·
              refine ⟨47271056032834272282994037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31514037355222848188662691 47271056032834272282994037)
              ·
                refine ⟨4431661503078213026530691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47271056032834272282994037 4431661503078213026530691)
                ·
                  refine ⟨6647492254617319539796037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431661503078213026530691 6647492254617319539796037)
                  ·
                    refine ⟨1246404797740747413711757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647492254617319539796037 1246404797740747413711757)
                    ·
                      rfl

theorem cell22_3641047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_3641047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641047 prefixEnd_3641047 := by exact prefixLift 3641047
  have htrace : WordTrace (prefixWord ++ tailWord_3641047) baseStart_3641047 baseEnd_3641047 := by
    simpa [prefixWord, tailWord_3641047, baseEnd_3641047] using wordTrace_append hprefix tailTrace_3641047
  have hstable : (prefixWord ++ tailWord_3641047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641047).length < 2 ^ (prefixWord ++ tailWord_3641047).sum := by decide
  have hdescent : baseEnd_3641047 < baseStart_3641047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641075 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 3, 6]
def baseStart_3641075 : Nat := 118140960795 + 3641075 * 2 ^ 59
def prefixEnd_3641075 : Nat := 4983230072969 + 3 ^ 40 * 3641075 * 2
def baseEnd_3641075 : Nat := 1246414382712964674011671

theorem tailTrace_3641075 : CollatzResearch.WordTrace tailWord_3641075 prefixEnd_3641075 1246414382712964674011671 := by
  unfold tailWord_3641075
  simp only [CollatzResearch.WordTrace]
  refine ⟨132800915284014595947412679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88533943522676397298275119 132800915284014595947412679)
  ·
    refine ⟨199201372926021893921119019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132800915284014595947412679 199201372926021893921119019)
    ·
      refine ⟨298802059389032840881678529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199201372926021893921119019 298802059389032840881678529)
      ·
        refine ⟨224101544541774630661258897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298802059389032840881678529 224101544541774630661258897)
        ·
          refine ⟨168076158406330972995944173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224101544541774630661258897 168076158406330972995944173)
          ·
            refine ⟨63028559402374114873479065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168076158406330972995944173 63028559402374114873479065)
            ·
              refine ⟨47271419551780586155109299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63028559402374114873479065 47271419551780586155109299)
              ·
                refine ⟨70907129327670879232663949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47271419551780586155109299 70907129327670879232663949)
                ·
                  refine ⟨26590173497876579712248981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70907129327670879232663949 26590173497876579712248981)
                  ·
                    refine ⟨1246414382712964674011671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26590173497876579712248981 1246414382712964674011671)
                    ·
                      rfl

theorem cell22_3641075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_3641075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641075 prefixEnd_3641075 := by exact prefixLift 3641075
  have htrace : WordTrace (prefixWord ++ tailWord_3641075) baseStart_3641075 baseEnd_3641075 := by
    simpa [prefixWord, tailWord_3641075, baseEnd_3641075] using wordTrace_append hprefix tailTrace_3641075
  have hstable : (prefixWord ++ tailWord_3641075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641075).length < 2 ^ (prefixWord ++ tailWord_3641075).sum := by decide
  have hdescent : baseEnd_3641075 < baseStart_3641075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641111 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 2, 3]
def baseStart_3641111 : Nat := 118140960795 + 3641111 * 2 ^ 59
def prefixEnd_3641111 : Nat := 4983230072969 + 3 ^ 40 * 3641111 * 2
def baseEnd_3641111 : Nat := 1246426706248672580111561

theorem tailTrace_3641111 : CollatzResearch.WordTrace tailWord_3641111 prefixEnd_3641111 1246426706248672580111561 := by
  unfold tailWord_3641111
  simp only [CollatzResearch.WordTrace]
  refine ⟨132802228311884174095723187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88534818874589449397148791 132802228311884174095723187)
  ·
    refine ⟨199203342467826261143584781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132802228311884174095723187 199203342467826261143584781)
    ·
      refine ⟨74701253425434847928844293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199203342467826261143584781 74701253425434847928844293)
      ·
        refine ⟨14006485017269033986658305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74701253425434847928844293 14006485017269033986658305)
        ·
          refine ⟨10504863762951775489993729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14006485017269033986658305 10504863762951775489993729)
          ·
            refine ⟨7878647822213831617495297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10504863762951775489993729 7878647822213831617495297)
            ·
              refine ⟨5908985866660373713121473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7878647822213831617495297 5908985866660373713121473)
              ·
                refine ⟨4431739399995280284841105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5908985866660373713121473 4431739399995280284841105)
                ·
                  refine ⟨3323804549996460213630829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4431739399995280284841105 3323804549996460213630829)
                  ·
                    refine ⟨1246426706248672580111561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3323804549996460213630829 1246426706248672580111561)
                    ·
                      rfl

theorem cell22_3641111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_3641111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641111 prefixEnd_3641111 := by exact prefixLift 3641111
  have htrace : WordTrace (prefixWord ++ tailWord_3641111) baseStart_3641111 baseEnd_3641111 := by
    simpa [prefixWord, tailWord_3641111, baseEnd_3641111] using wordTrace_append hprefix tailTrace_3641111
  have hstable : (prefixWord ++ tailWord_3641111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641111).length < 2 ^ (prefixWord ++ tailWord_3641111).sum := by decide
  have hdescent : baseEnd_3641111 < baseStart_3641111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641124 : List Nat := [2, 3, 1, 3, 2, 3, 1, 7]
def baseStart_3641124 : Nat := 118140960795 + 3641124 * 2 ^ 59
def prefixEnd_3641124 : Nat := 4983230072969 + 3 ^ 40 * 3641124 * 2
def baseEnd_3641124 : Nat := 138492350712704986615169

theorem tailTrace_3641124 : CollatzResearch.WordTrace tailWord_3641124 prefixEnd_3641124 138492350712704986615169 := by
  unfold tailWord_3641124
  simp only [CollatzResearch.WordTrace]
  refine ⟨66401351230418538657973213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88535134973891384877297617 66401351230418538657973213)
  ·
    refine ⟨24900506711406951996739955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66401351230418538657973213 24900506711406951996739955)
    ·
      refine ⟨37350760067110427995109933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24900506711406951996739955 37350760067110427995109933)
      ·
        refine ⟨14006535025166410498166225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37350760067110427995109933 14006535025166410498166225)
        ·
          refine ⟨10504901268874807873624669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14006535025166410498166225 10504901268874807873624669)
          ·
            refine ⟨3939337975828052952609251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10504901268874807873624669 3939337975828052952609251)
            ·
              refine ⟨5909006963742079428913877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939337975828052952609251 5909006963742079428913877)
              ·
                refine ⟨138492350712704986615169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5909006963742079428913877 138492350712704986615169)
                ·
                  rfl

theorem cell22_3641124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 7].length) (baseStart_3641124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641124 prefixEnd_3641124 := by exact prefixLift 3641124
  have htrace : WordTrace (prefixWord ++ tailWord_3641124) baseStart_3641124 baseEnd_3641124 := by
    simpa [prefixWord, tailWord_3641124, baseEnd_3641124] using wordTrace_append hprefix tailTrace_3641124
  have hstable : (prefixWord ++ tailWord_3641124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641124).length < 2 ^ (prefixWord ++ tailWord_3641124).sum := by decide
  have hdescent : baseEnd_3641124 < baseStart_3641124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641169 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 5]
def baseStart_3641169 : Nat := 118140960795 + 3641169 * 2 ^ 59
def prefixEnd_3641169 : Nat := 4983230072969 + 3 ^ 40 * 3641169 * 2
def baseEnd_3641169 : Nat := 415482186944659920720461

theorem tailTrace_3641169 : CollatzResearch.WordTrace tailWord_3641169 prefixEnd_3641169 415482186944659920720461 := by
  unfold tailWord_3641169
  simp only [CollatzResearch.WordTrace]
  refine ⟨132804343745674050001334561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88536229163782700000889707 132804343745674050001334561)
  ·
    refine ⟨99603257809255537501000921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132804343745674050001334561 99603257809255537501000921)
    ·
      refine ⟨74702443356941653125750691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99603257809255537501000921 74702443356941653125750691)
      ·
        refine ⟨112053665035412479688626037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74702443356941653125750691 112053665035412479688626037)
        ·
          refine ⟨10505031097069919970808691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112053665035412479688626037 10505031097069919970808691)
          ·
            refine ⟨15757546645604879956213037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10505031097069919970808691 15757546645604879956213037)
            ·
              refine ⟨5909079992101829983579889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15757546645604879956213037 5909079992101829983579889)
              ·
                refine ⟨4431809994076372487684917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5909079992101829983579889 4431809994076372487684917)
                ·
                  refine ⟨415482186944659920720461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4431809994076372487684917 415482186944659920720461)
                  ·
                    rfl

theorem cell22_3641169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_3641169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641169 prefixEnd_3641169 := by exact prefixLift 3641169
  have htrace : WordTrace (prefixWord ++ tailWord_3641169) baseStart_3641169 baseEnd_3641169 := by
    simpa [prefixWord, tailWord_3641169, baseEnd_3641169] using wordTrace_append hprefix tailTrace_3641169
  have hstable : (prefixWord ++ tailWord_3641169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641169).length < 2 ^ (prefixWord ++ tailWord_3641169).sum := by decide
  have hdescent : baseEnd_3641169 < baseStart_3641169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641250 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_3641250 : Nat := 118140960795 + 3641250 * 2 ^ 59
def prefixEnd_3641250 : Nat := 4983230072969 + 3 ^ 40 * 3641250 * 2
def baseEnd_3641250 : Nat := 1246474288789322550886135

theorem tailTrace_3641250 : CollatzResearch.WordTrace tailWord_3641250 prefixEnd_3641250 1246474288789322550886135 := by
  unfold tailWord_3641250
  simp only [CollatzResearch.WordTrace]
  refine ⟨33201824514595150208758301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88538198705587067223355469 33201824514595150208758301)
  ·
    refine ⟨12450684192973181328284363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33201824514595150208758301 12450684192973181328284363)
    ·
      refine ⟨18676026289459771992426545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12450684192973181328284363 18676026289459771992426545)
      ·
        refine ⟨14007019717094828994319909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18676026289459771992426545 14007019717094828994319909)
        ·
          refine ⟨2626316196955280436434983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14007019717094828994319909 2626316196955280436434983)
          ·
            refine ⟨3939474295432920654652475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626316196955280436434983 3939474295432920654652475)
            ·
              refine ⟨5909211443149380981978713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939474295432920654652475 5909211443149380981978713)
              ·
                refine ⟨4431908582362035736484035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5909211443149380981978713 4431908582362035736484035)
                ·
                  refine ⟨6647862873543053604726053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431908582362035736484035 6647862873543053604726053)
                  ·
                    refine ⟨1246474288789322550886135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6647862873543053604726053 1246474288789322550886135)
                    ·
                      rfl

theorem cell22_3641250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_3641250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641250 prefixEnd_3641250 := by exact prefixLift 3641250
  have htrace : WordTrace (prefixWord ++ tailWord_3641250) baseStart_3641250 baseEnd_3641250 := by
    simpa [prefixWord, tailWord_3641250, baseEnd_3641250] using wordTrace_append hprefix tailTrace_3641250
  have hstable : (prefixWord ++ tailWord_3641250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641250).length < 2 ^ (prefixWord ++ tailWord_3641250).sum := by decide
  have hdescent : baseEnd_3641250 < baseStart_3641250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641274 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_3641274 : Nat := 118140960795 + 3641274 * 2 ^ 59
def prefixEnd_3641274 : Nat := 4983230072969 + 3 ^ 40 * 3641274 * 2
def baseEnd_3641274 : Nat := 1246482504479794488286061

theorem tailTrace_3641274 : CollatzResearch.WordTrace tailWord_3641274 prefixEnd_3641274 1246482504479794488286061 := by
  unfold tailWord_3641274
  simp only [CollatzResearch.WordTrace]
  refine ⟨33202043352573413233476719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88538782273529101955937917 33202043352573413233476719)
  ·
    refine ⟨49803065028860119850215079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33202043352573413233476719 49803065028860119850215079)
    ·
      refine ⟨74704597543290179775322619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49803065028860119850215079 74704597543290179775322619)
      ·
        refine ⟨112056896314935269662983929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74704597543290179775322619 112056896314935269662983929)
        ·
          refine ⟨84042672236201452247237947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112056896314935269662983929 84042672236201452247237947)
          ·
            refine ⟨126064008354302178370856921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84042672236201452247237947 126064008354302178370856921)
            ·
              refine ⟨94548006265726633778142691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126064008354302178370856921 94548006265726633778142691)
              ·
                refine ⟨141822009398589950667214037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94548006265726633778142691 141822009398589950667214037)
                ·
                  refine ⟨3323953345279451968762829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 141822009398589950667214037 3323953345279451968762829)
                  ·
                    refine ⟨1246482504479794488286061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3323953345279451968762829 1246482504479794488286061)
                    ·
                      rfl

theorem cell22_3641274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_3641274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641274 prefixEnd_3641274 := by exact prefixLift 3641274
  have htrace : WordTrace (prefixWord ++ tailWord_3641274) baseStart_3641274 baseEnd_3641274 := by
    simpa [prefixWord, tailWord_3641274, baseEnd_3641274] using wordTrace_append hprefix tailTrace_3641274
  have hstable : (prefixWord ++ tailWord_3641274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641274).length < 2 ^ (prefixWord ++ tailWord_3641274).sum := by decide
  have hdescent : baseEnd_3641274 < baseStart_3641274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641276 : List Nat := [2, 2, 2, 5, 2, 9]
def baseStart_3641276 : Nat := 118140960795 + 3641276 * 2 ^ 59
def prefixEnd_3641276 : Nat := 4983230072969 + 3 ^ 40 * 3641276 * 2
def baseEnd_3641276 : Nat := 15388681347168730243655

theorem tailTrace_3641276 : CollatzResearch.WordTrace tailWord_3641276 prefixEnd_3641276 15388681347168730243655 := by
  unfold tailWord_3641276
  simp only [CollatzResearch.WordTrace]
  refine ⟨66404123178143203637739841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88538830904190938183653121 66404123178143203637739841)
  ·
    refine ⟨49803092383607402728304881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66404123178143203637739841 49803092383607402728304881)
    ·
      refine ⟨37352319287705552046228661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49803092383607402728304881 37352319287705552046228661)
      ·
        refine ⟨3501779933222395504333937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37352319287705552046228661 3501779933222395504333937)
        ·
          refine ⟨2626334949916796628250453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3501779933222395504333937 2626334949916796628250453)
          ·
            refine ⟨15388681347168730243655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2626334949916796628250453 15388681347168730243655)
            ·
              rfl

theorem cell22_3641276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 9].length) (baseStart_3641276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641276 prefixEnd_3641276 := by exact prefixLift 3641276
  have htrace : WordTrace (prefixWord ++ tailWord_3641276) baseStart_3641276 baseEnd_3641276 := by
    simpa [prefixWord, tailWord_3641276, baseEnd_3641276] using wordTrace_append hprefix tailTrace_3641276
  have hstable : (prefixWord ++ tailWord_3641276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641276).length < 2 ^ (prefixWord ++ tailWord_3641276).sum := by decide
  have hdescent : baseEnd_3641276 < baseStart_3641276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641304 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 5]
def baseStart_3641304 : Nat := 118140960795 + 3641304 * 2 ^ 59
def prefixEnd_3641304 : Nat := 4983230072969 + 3 ^ 40 * 3641304 * 2
def baseEnd_3641304 : Nat := 415497591364294803345323

theorem tailTrace_3641304 : CollatzResearch.WordTrace tailWord_3641304 prefixEnd_3641304 415497591364294803345323 := by
  unfold tailWord_3641304
  simp only [CollatzResearch.WordTrace]
  refine ⟨66404633800092484028749483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88539511733456645371665977 66404633800092484028749483)
  ·
    refine ⟨99606950700138726043124225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66404633800092484028749483 99606950700138726043124225)
    ·
      refine ⟨74705213025104044532343169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99606950700138726043124225 74705213025104044532343169)
      ·
        refine ⟨56028909768828033399257377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74705213025104044532343169 56028909768828033399257377)
        ·
          refine ⟨42021682326621025049443033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56028909768828033399257377 42021682326621025049443033)
          ·
            refine ⟨31516261744965768787082275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42021682326621025049443033 31516261744965768787082275)
            ·
              refine ⟨47274392617448653180623413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31516261744965768787082275 47274392617448653180623413)
              ·
                refine ⟨4431974307885811235683445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47274392617448653180623413 4431974307885811235683445)
                ·
                  refine ⟨415497591364294803345323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4431974307885811235683445 415497591364294803345323)
                  ·
                    rfl

theorem cell22_3641304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_3641304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641304 prefixEnd_3641304 := by exact prefixLift 3641304
  have htrace : WordTrace (prefixWord ++ tailWord_3641304) baseStart_3641304 baseEnd_3641304 := by
    simpa [prefixWord, tailWord_3641304, baseEnd_3641304] using wordTrace_append hprefix tailTrace_3641304
  have hstable : (prefixWord ++ tailWord_3641304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641304).length < 2 ^ (prefixWord ++ tailWord_3641304).sum := by decide
  have hdescent : baseEnd_3641304 < baseStart_3641304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641349 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 6]
def baseStart_3641349 : Nat := 118140960795 + 3641349 * 2 ^ 59
def prefixEnd_3641349 : Nat := 4983230072969 + 3 ^ 40 * 3641349 * 2
def baseEnd_3641349 : Nat := 415502726170839764220277

theorem tailTrace_3641349 : CollatzResearch.WordTrace tailWord_3641349 prefixEnd_3641349 415502726170839764220277 := by
  unfold tailWord_3641349
  simp only [CollatzResearch.WordTrace]
  refine ⟨132810908885021940742887101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88540605923347960495258067 132810908885021940742887101)
  ·
    refine ⟨49804090831883227778582663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132810908885021940742887101 49804090831883227778582663)
    ·
      refine ⟨74706136247824841667873995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49804090831883227778582663 74706136247824841667873995)
      ·
        refine ⟨112059204371737262501810993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74706136247824841667873995 112059204371737262501810993)
        ·
          refine ⟨84044403278802946876358245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112059204371737262501810993 84044403278802946876358245)
          ·
            refine ⟨15758325614775552539317171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84044403278802946876358245 15758325614775552539317171)
            ·
              refine ⟨23637488422163328808975757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15758325614775552539317171 23637488422163328808975757)
              ·
                refine ⟨8864058158311248303365909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23637488422163328808975757 8864058158311248303365909)
                ·
                  refine ⟨415502726170839764220277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8864058158311248303365909 415502726170839764220277)
                  ·
                    rfl

theorem cell22_3641349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_3641349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641349 prefixEnd_3641349 := by exact prefixLift 3641349
  have htrace : WordTrace (prefixWord ++ tailWord_3641349) baseStart_3641349 baseEnd_3641349 := by
    simpa [prefixWord, tailWord_3641349, baseEnd_3641349] using wordTrace_append hprefix tailTrace_3641349
  have hstable : (prefixWord ++ tailWord_3641349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641349).length < 2 ^ (prefixWord ++ tailWord_3641349).sum := by decide
  have hdescent : baseEnd_3641349 < baseStart_3641349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641379 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 1, 6]
def baseStart_3641379 : Nat := 118140960795 + 3641379 * 2 ^ 59
def prefixEnd_3641379 : Nat := 4983230072969 + 3 ^ 40 * 3641379 * 2
def baseEnd_3641379 : Nat := 1246518448125609214410739

theorem tailTrace_3641379 : CollatzResearch.WordTrace tailWord_3641379 prefixEnd_3641379 1246518448125609214410739 := by
  unfold tailWord_3641379
  simp only [CollatzResearch.WordTrace]
  refine ⟨132812003074913255866479191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88541335383275503910986127 132812003074913255866479191)
  ·
    refine ⟨199218004612369883799718787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132812003074913255866479191 199218004612369883799718787)
    ·
      refine ⟨298827006918554825699578181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199218004612369883799718787 298827006918554825699578181)
      ·
        refine ⟨56030063797229029818670909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298827006918554825699578181 56030063797229029818670909)
        ·
          refine ⟨21011273923960886182001591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56030063797229029818670909 21011273923960886182001591)
          ·
            refine ⟨31516910885941329273002387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21011273923960886182001591 31516910885941329273002387)
            ·
              refine ⟨47275366328911993909503581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31516910885941329273002387 47275366328911993909503581)
              ·
                refine ⟨17728262373341997716063843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47275366328911993909503581 17728262373341997716063843)
                ·
                  refine ⟨26592393560012996574095765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17728262373341997716063843 26592393560012996574095765)
                  ·
                    refine ⟨1246518448125609214410739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26592393560012996574095765 1246518448125609214410739)
                    ·
                      rfl

theorem cell22_3641379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_3641379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641379 prefixEnd_3641379 := by exact prefixLift 3641379
  have htrace : WordTrace (prefixWord ++ tailWord_3641379) baseStart_3641379 baseEnd_3641379 := by
    simpa [prefixWord, tailWord_3641379, baseEnd_3641379] using wordTrace_append hprefix tailTrace_3641379
  have hstable : (prefixWord ++ tailWord_3641379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641379).length < 2 ^ (prefixWord ++ tailWord_3641379).sum := by decide
  have hdescent : baseEnd_3641379 < baseStart_3641379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641381 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_3641381 : Nat := 118140960795 + 3641381 * 2 ^ 59
def prefixEnd_3641381 : Nat := 4983230072969 + 3 ^ 40 * 3641381 * 2
def baseEnd_3641381 : Nat := 1246519132766481875860733

theorem tailTrace_3641381 : CollatzResearch.WordTrace tailWord_3641381 prefixEnd_3641381 1246519132766481875860733 := by
  unfold tailWord_3641381
  simp only [CollatzResearch.WordTrace]
  refine ⟨132812076020906010208051997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88541384013937340138701331 132812076020906010208051997)
  ·
    refine ⟨49804528507839753828019499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132812076020906010208051997 49804528507839753828019499)
    ·
      refine ⟨74706792761759630742029249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49804528507839753828019499 74706792761759630742029249)
      ·
        refine ⟨56030094571319723056521937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74706792761759630742029249 56030094571319723056521937)
        ·
          refine ⟨42022570928489792292391453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56030094571319723056521937 42022570928489792292391453)
          ·
            refine ⟨15758464098183672109646795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42022570928489792292391453 15758464098183672109646795)
            ·
              refine ⟨23637696147275508164470193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15758464098183672109646795 23637696147275508164470193)
              ·
                refine ⟨17728272110456631123352645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23637696147275508164470193 17728272110456631123352645)
                ·
                  refine ⟨3324051020710618335628621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17728272110456631123352645 3324051020710618335628621)
                  ·
                    refine ⟨1246519132766481875860733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324051020710618335628621 1246519132766481875860733)
                    ·
                      rfl

theorem cell22_3641381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_3641381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641381 prefixEnd_3641381 := by exact prefixLift 3641381
  have htrace : WordTrace (prefixWord ++ tailWord_3641381) baseStart_3641381 baseEnd_3641381 := by
    simpa [prefixWord, tailWord_3641381, baseEnd_3641381] using wordTrace_append hprefix tailTrace_3641381
  have hstable : (prefixWord ++ tailWord_3641381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641381).length < 2 ^ (prefixWord ++ tailWord_3641381).sum := by decide
  have hdescent : baseEnd_3641381 < baseStart_3641381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641394 : List Nat := [3, 2, 1, 1, 2, 3, 10]
def baseStart_3641394 : Nat := 118140960795 + 3641394 * 2 ^ 59
def prefixEnd_3641394 : Nat := 4983230072969 + 3 ^ 40 * 3641394 * 2
def baseEnd_3641394 : Nat := 46167540108598302788359

theorem tailTrace_3641394 : CollatzResearch.WordTrace tailWord_3641394 prefixEnd_3641394 46167540108598302788359 := by
  unfold tailWord_3641394
  simp only [CollatzResearch.WordTrace]
  refine ⟨33203137542464728357068809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88541700113239275618850157 33203137542464728357068809)
  ·
    refine ⟨24902353156848546267801607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33203137542464728357068809 24902353156848546267801607)
    ·
      refine ⟨37353529735272819401702411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24902353156848546267801607 37353529735272819401702411)
      ·
        refine ⟨56030294602909229102553617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37353529735272819401702411 56030294602909229102553617)
        ·
          refine ⟨42022720952181921826915213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56030294602909229102553617 42022720952181921826915213)
          ·
            refine ⟨15758520357068220685093205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42022720952181921826915213 15758520357068220685093205)
            ·
              refine ⟨46167540108598302788359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15758520357068220685093205 46167540108598302788359)
              ·
                rfl

theorem cell22_3641394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 10].length) (baseStart_3641394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641394 prefixEnd_3641394 := by exact prefixLift 3641394
  have htrace : WordTrace (prefixWord ++ tailWord_3641394) baseStart_3641394 baseEnd_3641394 := by
    simpa [prefixWord, tailWord_3641394, baseEnd_3641394] using wordTrace_append hprefix tailTrace_3641394
  have hstable : (prefixWord ++ tailWord_3641394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641394).length < 2 ^ (prefixWord ++ tailWord_3641394).sum := by decide
  have hdescent : baseEnd_3641394 < baseStart_3641394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641398 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_3641398 : Nat := 118140960795 + 3641398 * 2 ^ 59
def prefixEnd_3641398 : Nat := 4983230072969 + 3 ^ 40 * 3641398 * 2
def baseEnd_3641398 : Nat := 1246524952213899498185681

theorem tailTrace_3641398 : CollatzResearch.WordTrace tailWord_3641398 prefixEnd_3641398 1246524952213899498185681 := by
  unfold tailWord_3641398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300793503865276381963803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88541797374562948074280565 8300793503865276381963803)
  ·
    refine ⟨12451190255797914572945705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8300793503865276381963803 12451190255797914572945705)
    ·
      refine ⟨9338392691848435929709279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12451190255797914572945705 9338392691848435929709279)
      ·
        refine ⟨14007589037772653894563919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9338392691848435929709279 14007589037772653894563919)
        ·
          refine ⟨21011383556658980841845879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14007589037772653894563919 21011383556658980841845879)
          ·
            refine ⟨31517075334988471262768819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21011383556658980841845879 31517075334988471262768819)
            ·
              refine ⟨47275613002482706894153229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31517075334988471262768819 47275613002482706894153229)
              ·
                refine ⟨17728354875931015085307461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47275613002482706894153229 17728354875931015085307461)
                ·
                  refine ⟨3324066539237065328495149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17728354875931015085307461 3324066539237065328495149)
                  ·
                    refine ⟨1246524952213899498185681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324066539237065328495149 1246524952213899498185681)
                    ·
                      rfl

theorem cell22_3641398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_3641398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641398 prefixEnd_3641398 := by exact prefixLift 3641398
  have htrace : WordTrace (prefixWord ++ tailWord_3641398) baseStart_3641398 baseEnd_3641398 := by
    simpa [prefixWord, tailWord_3641398, baseEnd_3641398] using wordTrace_append hprefix tailTrace_3641398
  have hstable : (prefixWord ++ tailWord_3641398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641398).length < 2 ^ (prefixWord ++ tailWord_3641398).sum := by decide
  have hdescent : baseEnd_3641398 < baseStart_3641398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641400 : List Nat := [2, 1, 2, 1, 6, 1, 3, 2, 4]
def baseStart_3641400 : Nat := 118140960795 + 3641400 * 2 ^ 59
def prefixEnd_3641400 : Nat := 4983230072969 + 3 ^ 40 * 3641400 * 2
def baseEnd_3641400 : Nat := 415508545618257386545225

theorem tailTrace_3641400 : CollatzResearch.WordTrace tailWord_3641400 prefixEnd_3641400 415508545618257386545225 := by
  unfold tailWord_3641400
  simp only [CollatzResearch.WordTrace]
  refine ⟨66406384503918588226496827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88541846005224784301995769 66406384503918588226496827)
  ·
    refine ⟨99609576755877882339745241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66406384503918588226496827 99609576755877882339745241)
    ·
      refine ⟨74707182566908411754808931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99609576755877882339745241 74707182566908411754808931)
      ·
        refine ⟨112060773850362617632213397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74707182566908411754808931 112060773850362617632213397)
        ·
          refine ⟨5252848774235747701510003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112060773850362617632213397 5252848774235747701510003)
          ·
            refine ⟨7879273161353621552265005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5252848774235747701510003 7879273161353621552265005)
            ·
              refine ⟨2954727435507608082099377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7879273161353621552265005 2954727435507608082099377)
              ·
                refine ⟨2216045576630706061574533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954727435507608082099377 2216045576630706061574533)
                ·
                  refine ⟨415508545618257386545225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2216045576630706061574533 415508545618257386545225)
                  ·
                    rfl

theorem cell22_3641400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 4].length) (baseStart_3641400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641400 prefixEnd_3641400 := by exact prefixLift 3641400
  have htrace : WordTrace (prefixWord ++ tailWord_3641400) baseStart_3641400 baseEnd_3641400 := by
    simpa [prefixWord, tailWord_3641400, baseEnd_3641400] using wordTrace_append hprefix tailTrace_3641400
  have hstable : (prefixWord ++ tailWord_3641400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641400).length < 2 ^ (prefixWord ++ tailWord_3641400).sum := by decide
  have hdescent : baseEnd_3641400 < baseStart_3641400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641430 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3641430 : Nat := 118140960795 + 3641430 * 2 ^ 59
def prefixEnd_3641430 : Nat := 4983230072969 + 3 ^ 40 * 3641430 * 2
def baseEnd_3641430 : Nat := 1246535906467862081385583

theorem tailTrace_3641430 : CollatzResearch.WordTrace tailWord_3641430 prefixEnd_3641430 1246535906467862081385583 := by
  unfold tailWord_3641430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300866449858030723536609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88542575465152327717723829 8300866449858030723536609)
  ·
    refine ⟨6225649837393523042652457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8300866449858030723536609 6225649837393523042652457)
    ·
      refine ⟨4669237378045142281989343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6225649837393523042652457 4669237378045142281989343)
      ·
        refine ⟨7003856067067713422984015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4669237378045142281989343 7003856067067713422984015)
        ·
          refine ⟨10505784100601570134476023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7003856067067713422984015 10505784100601570134476023)
          ·
            refine ⟨15758676150902355201714035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10505784100601570134476023 15758676150902355201714035)
            ·
              refine ⟨23638014226353532802571053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15758676150902355201714035 23638014226353532802571053)
              ·
                refine ⟨8864255334882574800964145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23638014226353532802571053 8864255334882574800964145)
                ·
                  refine ⟨6648191501161931100723109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8864255334882574800964145 6648191501161931100723109)
                  ·
                    refine ⟨1246535906467862081385583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6648191501161931100723109 1246535906467862081385583)
                    ·
                      rfl

theorem cell22_3641430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3641430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641430 prefixEnd_3641430 := by exact prefixLift 3641430
  have htrace : WordTrace (prefixWord ++ tailWord_3641430) baseStart_3641430 baseEnd_3641430 := by
    simpa [prefixWord, tailWord_3641430, baseEnd_3641430] using wordTrace_append hprefix tailTrace_3641430
  have hstable : (prefixWord ++ tailWord_3641430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641430).length < 2 ^ (prefixWord ++ tailWord_3641430).sum := by decide
  have hdescent : baseEnd_3641430 < baseStart_3641430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641439 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 7]
def baseStart_3641439 : Nat := 118140960795 + 3641439 * 2 ^ 59
def prefixEnd_3641439 : Nat := 4983230072969 + 3 ^ 40 * 3641439 * 2
def baseEnd_3641439 : Nat := 415512995783929685970185

theorem tailTrace_3641439 : CollatzResearch.WordTrace tailWord_3641439 prefixEnd_3641439 415512995783929685970185 := by
  unfold tailWord_3641439
  simp only [CollatzResearch.WordTrace]
  refine ⟨132814191454695886113663371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88542794303130590742442247 132814191454695886113663371)
  ·
    refine ⟨199221287182043829170495057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132814191454695886113663371 199221287182043829170495057)
    ·
      refine ⟨149415965386532871877871293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199221287182043829170495057 149415965386532871877871293)
      ·
        refine ⟨56030987019949826954201735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149415965386532871877871293 56030987019949826954201735)
        ·
          refine ⟨84046480529924740431302603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56030987019949826954201735 84046480529924740431302603)
          ·
            refine ⟨126069720794887110646953905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84046480529924740431302603 126069720794887110646953905)
            ·
              refine ⟨94552290596165332985215429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126069720794887110646953905 94552290596165332985215429)
              ·
                refine ⟨17728554486780999934727893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94552290596165332985215429 17728554486780999934727893)
                ·
                  refine ⟨415512995783929685970185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17728554486780999934727893 415512995783929685970185)
                  ·
                    rfl

theorem cell22_3641439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 7].length) (baseStart_3641439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641439 prefixEnd_3641439 := by exact prefixLift 3641439
  have htrace : WordTrace (prefixWord ++ tailWord_3641439) baseStart_3641439 baseEnd_3641439 := by
    simpa [prefixWord, tailWord_3641439, baseEnd_3641439] using wordTrace_append hprefix tailTrace_3641439
  have hstable : (prefixWord ++ tailWord_3641439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641439).length < 2 ^ (prefixWord ++ tailWord_3641439).sum := by decide
  have hdescent : baseEnd_3641439 < baseStart_3641439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641456 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 5]
def baseStart_3641456 : Nat := 118140960795 + 3641456 * 2 ^ 59
def prefixEnd_3641456 : Nat := 4983230072969 + 3 ^ 40 * 3641456 * 2
def baseEnd_3641456 : Nat := 415514935599735560078501

theorem tailTrace_3641456 : CollatzResearch.WordTrace tailWord_3641456 prefixEnd_3641456 415514935599735560078501 := by
  unfold tailWord_3641456
  simp only [CollatzResearch.WordTrace]
  refine ⟨66407405747817149008516111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88543207663756198678021481 66407405747817149008516111)
  ·
    refine ⟨99611108621725723512774167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66407405747817149008516111 99611108621725723512774167)
    ·
      refine ⟨149416662932588585269161251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99611108621725723512774167 149416662932588585269161251)
      ·
        refine ⟨224124994398882877903741877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149416662932588585269161251 224124994398882877903741877)
        ·
          refine ⟨21011718224895269803475801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224124994398882877903741877 21011718224895269803475801)
          ·
            refine ⟨15758788668671452352606851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21011718224895269803475801 15758788668671452352606851)
            ·
              refine ⟨23638183003007178528910277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15758788668671452352606851 23638183003007178528910277)
              ·
                refine ⟨4432159313063845974170677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23638183003007178528910277 4432159313063845974170677)
                ·
                  refine ⟨415514935599735560078501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4432159313063845974170677 415514935599735560078501)
                  ·
                    rfl

theorem cell22_3641456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_3641456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641456 prefixEnd_3641456 := by exact prefixLift 3641456
  have htrace : WordTrace (prefixWord ++ tailWord_3641456) baseStart_3641456 baseEnd_3641456 := by
    simpa [prefixWord, tailWord_3641456, baseEnd_3641456] using wordTrace_append hprefix tailTrace_3641456
  have hstable : (prefixWord ++ tailWord_3641456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641456).length < 2 ^ (prefixWord ++ tailWord_3641456).sum := by decide
  have hdescent : baseEnd_3641456 < baseStart_3641456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641537 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3641537 : Nat := 118140960795 + 3641537 * 2 ^ 59
def prefixEnd_3641537 : Nat := 4983230072969 + 3 ^ 40 * 3641537 * 2
def baseEnd_3641537 : Nat := 1246572534754549468960255

theorem tailTrace_3641537 : CollatzResearch.WordTrace tailWord_3641537 prefixEnd_3641537 1246572534754549468960255 := by
  unfold tailWord_3641537
  simp only [CollatzResearch.WordTrace]
  refine ⟨132817765808340848850730865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88545177205560565900487243 132817765808340848850730865)
  ·
    refine ⟨99613324356255636638048149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132817765808340848850730865 99613324356255636638048149)
    ·
      refine ⟨4669374579199482967408507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99613324356255636638048149 4669374579199482967408507)
      ·
        refine ⟨7004061868799224451112761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4669374579199482967408507 7004061868799224451112761)
        ·
          refine ⟨5253046401599418338334571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7004061868799224451112761 5253046401599418338334571)
          ·
            refine ⟨7879569602399127507501857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253046401599418338334571 7879569602399127507501857)
            ·
              refine ⟨5909677201799345630626393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7879569602399127507501857 5909677201799345630626393)
              ·
                refine ⟨4432257901349509222969795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5909677201799345630626393 4432257901349509222969795)
                ·
                  refine ⟨6648386852024263834454693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432257901349509222969795 6648386852024263834454693)
                  ·
                    refine ⟨1246572534754549468960255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6648386852024263834454693 1246572534754549468960255)
                    ·
                      rfl

theorem cell22_3641537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3641537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641537 prefixEnd_3641537 := by exact prefixLift 3641537
  have htrace : WordTrace (prefixWord ++ tailWord_3641537) baseStart_3641537 baseEnd_3641537 := by
    simpa [prefixWord, tailWord_3641537, baseEnd_3641537] using wordTrace_append hprefix tailTrace_3641537
  have hstable : (prefixWord ++ tailWord_3641537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641537).length < 2 ^ (prefixWord ++ tailWord_3641537).sum := by decide
  have hdescent : baseEnd_3641537 < baseStart_3641537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641546 : List Nat := [3, 1, 2, 1, 3, 1, 3, 8]
def baseStart_3641546 : Nat := 118140960795 + 3641546 * 2 ^ 59
def prefixEnd_3641546 : Nat := 4983230072969 + 3 ^ 40 * 3641546 * 2
def baseEnd_3641546 : Nat := 138508401737608493942803

theorem tailTrace_3641546 : CollatzResearch.WordTrace tailWord_3641546 prefixEnd_3641546 138508401737608493942803 := by
  unfold tailWord_3641546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33204523516327060846952123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88545396043538828925205661 33204523516327060846952123)
  ·
    refine ⟨49806785274490591270428185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33204523516327060846952123 49806785274490591270428185)
    ·
      refine ⟨37355088955867943452821139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49806785274490591270428185 37355088955867943452821139)
      ·
        refine ⟨56032633433801915179231709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37355088955867943452821139 56032633433801915179231709)
        ·
          refine ⟨21012237537675718192211891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56032633433801915179231709 21012237537675718192211891)
          ·
            refine ⟨31518356306513577288317837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21012237537675718192211891 31518356306513577288317837)
            ·
              refine ⟨11819383614942591483119189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31518356306513577288317837 11819383614942591483119189)
              ·
                refine ⟨138508401737608493942803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11819383614942591483119189 138508401737608493942803)
                ·
                  rfl

theorem cell22_3641546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_3641546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641546 prefixEnd_3641546 := by exact prefixLift 3641546
  have htrace : WordTrace (prefixWord ++ tailWord_3641546) baseStart_3641546 baseEnd_3641546 := by
    simpa [prefixWord, tailWord_3641546, baseEnd_3641546] using wordTrace_append hprefix tailTrace_3641546
  have hstable : (prefixWord ++ tailWord_3641546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641546).length < 2 ^ (prefixWord ++ tailWord_3641546).sum := by decide
  have hdescent : baseEnd_3641546 < baseStart_3641546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641565 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3641565 : Nat := 118140960795 + 3641565 * 2 ^ 59
def prefixEnd_3641565 : Nat := 4983230072969 + 3 ^ 40 * 3641565 * 2
def baseEnd_3641565 : Nat := 1246582119726766729260169

theorem tailTrace_3641565 : CollatzResearch.WordTrace tailWord_3641565 prefixEnd_3641565 1246582119726766729260169 := by
  unfold tailWord_3641565
  simp only [CollatzResearch.WordTrace]
  refine ⟨132818787052239409632750149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88545858034826273088500099 132818787052239409632750149)
  ·
    refine ⟨24903522572294889306140653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132818787052239409632750149 24903522572294889306140653)
    ·
      refine ⟨9338820964610583489802745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24903522572294889306140653 9338820964610583489802745)
      ·
        refine ⟨7004115723457937617352059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9338820964610583489802745 7004115723457937617352059)
        ·
          refine ⟨10506173585186906426028089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7004115723457937617352059 10506173585186906426028089)
          ·
            refine ⟨7879630188890179819521067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10506173585186906426028089 7879630188890179819521067)
            ·
              refine ⟨11819445283335269729281601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7879630188890179819521067 11819445283335269729281601)
              ·
                refine ⟨8864583962501452296961201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11819445283335269729281601 8864583962501452296961201)
                ·
                  refine ⟨6648437971876089222720901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8864583962501452296961201 6648437971876089222720901)
                  ·
                    refine ⟨1246582119726766729260169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6648437971876089222720901 1246582119726766729260169)
                    ·
                      rfl

theorem cell22_3641565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3641565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641565 prefixEnd_3641565 := by exact prefixLift 3641565
  have htrace : WordTrace (prefixWord ++ tailWord_3641565) baseStart_3641565 baseEnd_3641565 := by
    simpa [prefixWord, tailWord_3641565, baseEnd_3641565] using wordTrace_append hprefix tailTrace_3641565
  have hstable : (prefixWord ++ tailWord_3641565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641565).length < 2 ^ (prefixWord ++ tailWord_3641565).sum := by decide
  have hdescent : baseEnd_3641565 < baseStart_3641565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641629 : List Nat := [1, 4, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_3641629 : Nat := 118140960795 + 3641629 * 2 ^ 59
def prefixEnd_3641629 : Nat := 4983230072969 + 3 ^ 40 * 3641629 * 2
def baseEnd_3641629 : Nat := 1246604028234691895659973

theorem tailTrace_3641629 : CollatzResearch.WordTrace tailWord_3641629 prefixEnd_3641629 1246604028234691895659973 := by
  unfold tailWord_3641629
  simp only [CollatzResearch.WordTrace]
  refine ⟨132821121324007548563079941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88547414216005032375386627 132821121324007548563079941)
  ·
    refine ⟨24903960248251415355577489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132821121324007548563079941 24903960248251415355577489)
    ·
      refine ⟨18677970186188561516683117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24903960248251415355577489 18677970186188561516683117)
      ·
        refine ⟨7004238819820710568756169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18677970186188561516683117 7004238819820710568756169)
        ·
          refine ⟨5253179114865532926567127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7004238819820710568756169 5253179114865532926567127)
          ·
            refine ⟨7879768672298299389850691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253179114865532926567127 7879768672298299389850691)
            ·
              refine ⟨11819653008447449084776037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7879768672298299389850691 11819653008447449084776037)
              ·
                refine ⟨2216184939083896703395507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11819653008447449084776037 2216184939083896703395507)
                ·
                  refine ⟨3324277408625845055093261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216184939083896703395507 3324277408625845055093261)
                  ·
                    refine ⟨1246604028234691895659973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324277408625845055093261 1246604028234691895659973)
                    ·
                      rfl

theorem cell22_3641629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_3641629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641629 prefixEnd_3641629 := by exact prefixLift 3641629
  have htrace : WordTrace (prefixWord ++ tailWord_3641629) baseStart_3641629 baseEnd_3641629 := by
    simpa [prefixWord, tailWord_3641629, baseEnd_3641629] using wordTrace_append hprefix tailTrace_3641629
  have hstable : (prefixWord ++ tailWord_3641629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641629).length < 2 ^ (prefixWord ++ tailWord_3641629).sum := by decide
  have hdescent : baseEnd_3641629 < baseStart_3641629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641640 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3641640 : Nat := 118140960795 + 3641640 * 2 ^ 59
def prefixEnd_3641640 : Nat := 4983230072969 + 3 ^ 40 * 3641640 * 2
def baseEnd_3641640 : Nat := 1246607793759491533634939

theorem tailTrace_3641640 : CollatzResearch.WordTrace tailWord_3641640 prefixEnd_3641640 1246607793759491533634939 := by
  unfold tailWord_3641640
  simp only [CollatzResearch.WordTrace]
  refine ⟨66410761263483848720865187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88547681684645131627820249 66410761263483848720865187)
  ·
    refine ⟨99616141895225773081297781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66410761263483848720865187 99616141895225773081297781)
    ·
      refine ⟨9339013302677416226371667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99616141895225773081297781 9339013302677416226371667)
      ·
        refine ⟨14008519954016124339557501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9339013302677416226371667 14008519954016124339557501)
        ·
          refine ⟨5253194982756046627334063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14008519954016124339557501 5253194982756046627334063)
          ·
            refine ⟨7879792474134069941001095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253194982756046627334063 7879792474134069941001095)
            ·
              refine ⟨11819688711201104911501643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7879792474134069941001095 11819688711201104911501643)
              ·
                refine ⟨17729533066801657367252465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11819688711201104911501643 17729533066801657367252465)
                ·
                  refine ⟨13297149800101243025439349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17729533066801657367252465 13297149800101243025439349)
                  ·
                    refine ⟨1246607793759491533634939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13297149800101243025439349 1246607793759491533634939)
                    ·
                      rfl

theorem cell22_3641640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3641640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641640 prefixEnd_3641640 := by exact prefixLift 3641640
  have htrace : WordTrace (prefixWord ++ tailWord_3641640) baseStart_3641640 baseEnd_3641640 := by
    simpa [prefixWord, tailWord_3641640, baseEnd_3641640] using wordTrace_append hprefix tailTrace_3641640
  have hstable : (prefixWord ++ tailWord_3641640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641640).length < 2 ^ (prefixWord ++ tailWord_3641640).sum := by decide
  have hdescent : baseEnd_3641640 < baseStart_3641640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641653 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 6]
def baseStart_3641653 : Nat := 118140960795 + 3641653 * 2 ^ 59
def prefixEnd_3641653 : Nat := 4983230072969 + 3 ^ 40 * 3641653 * 2
def baseEnd_3641653 : Nat := 415537414641721277686633

theorem tailTrace_3641653 : CollatzResearch.WordTrace tailWord_3641653 prefixEnd_3641653 415537414641721277686633 := by
  unfold tailWord_3641653
  simp only [CollatzResearch.WordTrace]
  refine ⟨132821996675920600661953613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88547997783947067107969075 132821996675920600661953613)
  ·
    refine ⟨49808248753470225248232605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132821996675920600661953613 49808248753470225248232605)
    ·
      refine ⟨18678093282551334468087227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49808248753470225248232605 18678093282551334468087227)
      ·
        refine ⟨28017139923827001702130841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18678093282551334468087227 28017139923827001702130841)
        ·
          refine ⟨21012854942870251276598131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28017139923827001702130841 21012854942870251276598131)
          ·
            refine ⟨31519282414305376914897197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21012854942870251276598131 31519282414305376914897197)
            ·
              refine ⟨11819730905364516343086449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31519282414305376914897197 11819730905364516343086449)
              ·
                refine ⟨8864798179023387257314837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11819730905364516343086449 8864798179023387257314837)
                ·
                  refine ⟨415537414641721277686633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8864798179023387257314837 415537414641721277686633)
                  ·
                    rfl

theorem cell22_3641653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_3641653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641653 prefixEnd_3641653 := by exact prefixLift 3641653
  have htrace : WordTrace (prefixWord ++ tailWord_3641653) baseStart_3641653 baseEnd_3641653 := by
    simpa [prefixWord, tailWord_3641653, baseEnd_3641653] using wordTrace_append hprefix tailTrace_3641653
  have hstable : (prefixWord ++ tailWord_3641653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641653).length < 2 ^ (prefixWord ++ tailWord_3641653).sum := by decide
  have hdescent : baseEnd_3641653 < baseStart_3641653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641760 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 5]
def baseStart_3641760 : Nat := 118140960795 + 3641760 * 2 ^ 59
def prefixEnd_3641760 : Nat := 4983230072969 + 3 ^ 40 * 3641760 * 2
def baseEnd_3641760 : Nat := 415549624070617073544857

theorem tailTrace_3641760 : CollatzResearch.WordTrace tailWord_3641760 prefixEnd_3641760 415549624070617073544857 := by
  unfold tailWord_3641760
  simp only [CollatzResearch.WordTrace]
  refine ⟨66412949643266478968049367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88550599524355305290732489 66412949643266478968049367)
  ·
    refine ⟨99619424464899718452074051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66412949643266478968049367 99619424464899718452074051)
    ·
      refine ⟨149429136697349577678111077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99619424464899718452074051 149429136697349577678111077)
      ·
        refine ⟨28017963130753045814645827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149429136697349577678111077 28017963130753045814645827)
        ·
          refine ⟨42026944696129568721968741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28017963130753045814645827 42026944696129568721968741)
          ·
            refine ⟨7880052130524294135369139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42026944696129568721968741 7880052130524294135369139)
            ·
              refine ⟨11820078195786441203053709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880052130524294135369139 11820078195786441203053709)
              ·
                refine ⟨4432529323419915451145141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11820078195786441203053709 4432529323419915451145141)
                ·
                  refine ⟨415549624070617073544857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4432529323419915451145141 415549624070617073544857)
                  ·
                    rfl

theorem cell22_3641760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_3641760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641760 prefixEnd_3641760 := by exact prefixLift 3641760
  have htrace : WordTrace (prefixWord ++ tailWord_3641760) baseStart_3641760 baseEnd_3641760 := by
    simpa [prefixWord, tailWord_3641760, baseEnd_3641760] using wordTrace_append hprefix tailTrace_3641760
  have hstable : (prefixWord ++ tailWord_3641760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641760).length < 2 ^ (prefixWord ++ tailWord_3641760).sum := by decide
  have hdescent : baseEnd_3641760 < baseStart_3641760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641803 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 5, 5]
def baseStart_3641803 : Nat := 118140960795 + 3641803 * 2 ^ 59
def prefixEnd_3641803 : Nat := 4983230072969 + 3 ^ 40 * 3641803 * 2
def baseEnd_3641803 : Nat := 1246663591990613441809439

theorem tailTrace_3641803 : CollatzResearch.WordTrace tailWord_3641803 prefixEnd_3641803 1246663591990613441809439 := by
  unfold tailWord_3641803
  simp only [CollatzResearch.WordTrace]
  refine ⟨132827467625377176279914063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88551645083584784186609375 132827467625377176279914063)
  ·
    refine ⟨199241201438065764419871095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132827467625377176279914063 199241201438065764419871095)
    ·
      refine ⟨298861802157098646629806643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199241201438065764419871095 298861802157098646629806643)
      ·
        refine ⟨448292703235647969944709965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298861802157098646629806643 448292703235647969944709965)
        ·
          refine ⟨168109763713367988729266237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448292703235647969944709965 168109763713367988729266237)
          ·
            refine ⟨63041161392512995773474839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168109763713367988729266237 63041161392512995773474839)
            ·
              refine ⟨94561742088769493660212259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63041161392512995773474839 94561742088769493660212259)
              ·
                refine ⟨141842613133154240490318389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94561742088769493660212259 141842613133154240490318389)
                ·
                  refine ⟨13297744981233210045967349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141842613133154240490318389 13297744981233210045967349)
                  ·
                    refine ⟨1246663591990613441809439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13297744981233210045967349 1246663591990613441809439)
                    ·
                      rfl

theorem cell22_3641803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_3641803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641803 prefixEnd_3641803 := by exact prefixLift 3641803
  have htrace : WordTrace (prefixWord ++ tailWord_3641803) baseStart_3641803 baseEnd_3641803 := by
    simpa [prefixWord, tailWord_3641803, baseEnd_3641803] using wordTrace_append hprefix tailTrace_3641803
  have hstable : (prefixWord ++ tailWord_3641803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641803).length < 2 ^ (prefixWord ++ tailWord_3641803).sum := by decide
  have hdescent : baseEnd_3641803 < baseStart_3641803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641837 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3641837 : Nat := 118140960795 + 3641837 * 2 ^ 59
def prefixEnd_3641837 : Nat := 4983230072969 + 3 ^ 40 * 3641837 * 2
def baseEnd_3641837 : Nat := 1246675230885448686459335

theorem tailTrace_3641837 : CollatzResearch.WordTrace tailWord_3641837 prefixEnd_3641837 1246675230885448686459335 := by
  unfold tailWord_3641837
  simp only [CollatzResearch.WordTrace]
  refine ⟨132828707707254000086651765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88552471804836000057767843 132828707707254000086651765)
  ·
    refine ⟨12452691347555062508123603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132828707707254000086651765 12452691347555062508123603)
    ·
      refine ⟨18679037021332593762185405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12452691347555062508123603 18679037021332593762185405)
      ·
        refine ⟨7004638882999722660819527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18679037021332593762185405 7004638882999722660819527)
        ·
          refine ⟨10506958324499583991229291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7004638882999722660819527 10506958324499583991229291)
          ·
            refine ⟨15760437486749375986843937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10506958324499583991229291 15760437486749375986843937)
            ·
              refine ⟨11820328115062031990132953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15760437486749375986843937 11820328115062031990132953)
              ·
                refine ⟨8865246086296523992599715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11820328115062031990132953 8865246086296523992599715)
                ·
                  refine ⟨13297869129444785988899573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8865246086296523992599715 13297869129444785988899573)
                  ·
                    refine ⟨1246675230885448686459335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13297869129444785988899573 1246675230885448686459335)
                    ·
                      rfl

theorem cell22_3641837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3641837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641837 prefixEnd_3641837 := by exact prefixLift 3641837
  have htrace : WordTrace (prefixWord ++ tailWord_3641837) baseStart_3641837 baseEnd_3641837 := by
    simpa [prefixWord, tailWord_3641837, baseEnd_3641837] using wordTrace_append hprefix tailTrace_3641837
  have hstable : (prefixWord ++ tailWord_3641837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641837).length < 2 ^ (prefixWord ++ tailWord_3641837).sum := by decide
  have hdescent : baseEnd_3641837 < baseStart_3641837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641869 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3641869 : Nat := 118140960795 + 3641869 * 2 ^ 59
def prefixEnd_3641869 : Nat := 4983230072969 + 3 ^ 40 * 3641869 * 2
def baseEnd_3641869 : Nat := 1246686185139411269659237

theorem tailTrace_3641869 : CollatzResearch.WordTrace tailWord_3641869 prefixEnd_3641869 1246686185139411269659237 := by
  unfold tailWord_3641869
  simp only [CollatzResearch.WordTrace]
  refine ⟨132829874843138069551816661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88553249895425379701211107 132829874843138069551816661)
  ·
    refine ⟨3113200191636048505120703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 132829874843138069551816661 3113200191636048505120703)
    ·
      refine ⟨4669800287454072757681055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3113200191636048505120703 4669800287454072757681055)
      ·
        refine ⟨7004700431181109136521583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4669800287454072757681055 7004700431181109136521583)
        ·
          refine ⟨10507050646771663704782375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7004700431181109136521583 10507050646771663704782375)
          ·
            refine ⟨15760575970157495557173563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507050646771663704782375 15760575970157495557173563)
            ·
              refine ⟨23640863955236243335760345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15760575970157495557173563 23640863955236243335760345)
              ·
                refine ⟨17730647966427182501820259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23640863955236243335760345 17730647966427182501820259)
                ·
                  refine ⟨26595971949640773752730389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17730647966427182501820259 26595971949640773752730389)
                  ·
                    refine ⟨1246686185139411269659237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26595971949640773752730389 1246686185139411269659237)
                    ·
                      rfl

theorem cell22_3641869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3641869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641869 prefixEnd_3641869 := by exact prefixLift 3641869
  have htrace : WordTrace (prefixWord ++ tailWord_3641869) baseStart_3641869 baseEnd_3641869 := by
    simpa [prefixWord, tailWord_3641869, baseEnd_3641869] using wordTrace_append hprefix tailTrace_3641869
  have hstable : (prefixWord ++ tailWord_3641869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641869).length < 2 ^ (prefixWord ++ tailWord_3641869).sum := by decide
  have hdescent : baseEnd_3641869 < baseStart_3641869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641882 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_3641882 : Nat := 118140960795 + 3641882 * 2 ^ 59
def prefixEnd_3641882 : Nat := 4983230072969 + 3 ^ 40 * 3641882 * 2
def baseEnd_3641882 : Nat := 1246690635305083569084197

theorem tailTrace_3641882 : CollatzResearch.WordTrace tailWord_3641882 prefixEnd_3641882 1246690635305083569084197 := by
  unfold tailWord_3641882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33207587248022743193009975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88553565994727315181359933 33207587248022743193009975)
  ·
    refine ⟨49811380872034114789514963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33207587248022743193009975 49811380872034114789514963)
    ·
      refine ⟨74717071308051172184272445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49811380872034114789514963 74717071308051172184272445)
      ·
        refine ⟨28018901740519189569102167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74717071308051172184272445 28018901740519189569102167)
        ·
          refine ⟨42028352610778784353653251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28018901740519189569102167 42028352610778784353653251)
          ·
            refine ⟨63042528916168176530479877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42028352610778784353653251 63042528916168176530479877)
            ·
              refine ⟨11820474171781533099464977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63042528916168176530479877 11820474171781533099464977)
              ·
                refine ⟨8865355628836149824598733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11820474171781533099464977 8865355628836149824598733)
                ·
                  refine ⟨3324508360813556184224525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8865355628836149824598733 3324508360813556184224525)
                  ·
                    refine ⟨1246690635305083569084197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324508360813556184224525 1246690635305083569084197)
                    ·
                      rfl

theorem cell22_3641882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_3641882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641882 prefixEnd_3641882 := by exact prefixLift 3641882
  have htrace : WordTrace (prefixWord ++ tailWord_3641882) baseStart_3641882 baseEnd_3641882 := by
    simpa [prefixWord, tailWord_3641882, baseEnd_3641882] using wordTrace_append hprefix tailTrace_3641882
  have hstable : (prefixWord ++ tailWord_3641882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641882).length < 2 ^ (prefixWord ++ tailWord_3641882).sum := by decide
  have hdescent : baseEnd_3641882 < baseStart_3641882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641901 : List Nat := [1, 5, 4, 1, 1, 2, 8]
def baseStart_3641901 : Nat := 118140960795 + 3641901 * 2 ^ 59
def prefixEnd_3641901 : Nat := 4983230072969 + 3 ^ 40 * 3641901 * 2
def baseEnd_3641901 : Nat := 46173968125680513068857

theorem tailTrace_3641901 : CollatzResearch.WordTrace tailWord_3641901 prefixEnd_3641901 46173968125680513068857 := by
  unfold tailWord_3641901
  simp only [CollatzResearch.WordTrace]
  refine ⟨132831041979022139016981557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88554027986014759344654371 132831041979022139016981557)
  ·
    refine ⟨12452910185533325532842021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132831041979022139016981557 12452910185533325532842021)
    ·
      refine ⟨2334920659787498537407879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12452910185533325532842021 2334920659787498537407879)
      ·
        refine ⟨3502380989681247806111819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2334920659787498537407879 3502380989681247806111819)
        ·
          refine ⟨5253571484521871709167729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502380989681247806111819 5253571484521871709167729)
          ·
            refine ⟨3940178613391403781875797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5253571484521871709167729 3940178613391403781875797)
            ·
              refine ⟨46173968125680513068857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3940178613391403781875797 46173968125680513068857)
              ·
                rfl

theorem cell22_3641901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 8].length) (baseStart_3641901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641901 prefixEnd_3641901 := by exact prefixLift 3641901
  have htrace : WordTrace (prefixWord ++ tailWord_3641901) baseStart_3641901 baseEnd_3641901 := by
    simpa [prefixWord, tailWord_3641901, baseEnd_3641901] using wordTrace_append hprefix tailTrace_3641901
  have hstable : (prefixWord ++ tailWord_3641901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641901).length < 2 ^ (prefixWord ++ tailWord_3641901).sum := by decide
  have hdescent : baseEnd_3641901 < baseStart_3641901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641989 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_3641989 : Nat := 118140960795 + 3641989 * 2 ^ 59
def prefixEnd_3641989 : Nat := 4983230072969 + 3 ^ 40 * 3641989 * 2
def baseEnd_3641989 : Nat := 1246727263591770956658869

theorem tailTrace_3641989 : CollatzResearch.WordTrace tailWord_3641989 prefixEnd_3641989 1246727263591770956658869 := by
  unfold tailWord_3641989
  simp only [CollatzResearch.WordTrace]
  refine ⟨132834251602703330046185021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88556167735135553364123347 132834251602703330046185021)
  ·
    refine ⟨49812844351013748767319383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132834251602703330046185021 49812844351013748767319383)
    ·
      refine ⟨74719266526520623150979075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49812844351013748767319383 74719266526520623150979075)
      ·
        refine ⟨112078899789780934726468613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74719266526520623150979075 112078899789780934726468613)
        ·
          refine ⟨21014793710583925261212865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112078899789780934726468613 21014793710583925261212865)
          ·
            refine ⟨15761095282937943945909649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21014793710583925261212865 15761095282937943945909649)
            ·
              refine ⟨11820821462203457959432237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15761095282937943945909649 11820821462203457959432237)
              ·
                refine ⟨4432808048326296734787089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11820821462203457959432237 4432808048326296734787089)
                ·
                  refine ⟨3324606036244722551090317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4432808048326296734787089 3324606036244722551090317)
                  ·
                    refine ⟨1246727263591770956658869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324606036244722551090317 1246727263591770956658869)
                    ·
                      rfl

theorem cell22_3641989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_3641989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3641989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3641989 prefixEnd_3641989 := by exact prefixLift 3641989
  have htrace : WordTrace (prefixWord ++ tailWord_3641989) baseStart_3641989 baseEnd_3641989 := by
    simpa [prefixWord, tailWord_3641989, baseEnd_3641989] using wordTrace_append hprefix tailTrace_3641989
  have hstable : (prefixWord ++ tailWord_3641989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641989).length < 2 ^ (prefixWord ++ tailWord_3641989).sum := by decide
  have hdescent : baseEnd_3641989 < baseStart_3641989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642004 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3642004 : Nat := 118140960795 + 3642004 * 2 ^ 59
def prefixEnd_3642004 : Nat := 4983230072969 + 3 ^ 40 * 3642004 * 2
def baseEnd_3642004 : Nat := 1246732398398315917533823

theorem tailTrace_3642004 : CollatzResearch.WordTrace tailWord_3642004 prefixEnd_3642004 1246732398398315917533823 := by
  unfold tailWord_3642004
  simp only [CollatzResearch.WordTrace]
  refine ⟨66417399348824493803990533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88556532465099325071987377 66417399348824493803990533)
  ·
    refine ⟨12453262377904592588248225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66417399348824493803990533 12453262377904592588248225)
    ·
      refine ⟨9339946783428444441186169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12453262377904592588248225 9339946783428444441186169)
      ·
        refine ⟨7004960087571333330889627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9339946783428444441186169 7004960087571333330889627)
        ·
          refine ⟨10507440131356999996334441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7004960087571333330889627 10507440131356999996334441)
          ·
            refine ⟨7880580098517749997250831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10507440131356999996334441 7880580098517749997250831)
            ·
              refine ⟨11820870147776624995876247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880580098517749997250831 11820870147776624995876247)
              ·
                refine ⟨17731305221664937493814371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11820870147776624995876247 17731305221664937493814371)
                ·
                  refine ⟨26596957832497406240721557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17731305221664937493814371 26596957832497406240721557)
                  ·
                    refine ⟨1246732398398315917533823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26596957832497406240721557 1246732398398315917533823)
                    ·
                      rfl

theorem cell22_3642004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3642004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642004 prefixEnd_3642004 := by exact prefixLift 3642004
  have htrace : WordTrace (prefixWord ++ tailWord_3642004) baseStart_3642004 baseEnd_3642004 := by
    simpa [prefixWord, tailWord_3642004, baseEnd_3642004] using wordTrace_append hprefix tailTrace_3642004
  have hstable : (prefixWord ++ tailWord_3642004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642004).length < 2 ^ (prefixWord ++ tailWord_3642004).sum := by decide
  have hdescent : baseEnd_3642004 < baseStart_3642004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642010 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 1, 4]
def baseStart_3642010 : Nat := 118140960795 + 3642010 * 2 ^ 59
def prefixEnd_3642010 : Nat := 4983230072969 + 3 ^ 40 * 3642010 * 2
def baseEnd_3642010 : Nat := 1246734452320933901883805

theorem tailTrace_3642010 : CollatzResearch.WordTrace tailWord_3642010 prefixEnd_3642010 1246734452320933901883805 := by
  unfold tailWord_3642010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33208754383906812658174871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88556678357084833755132989 33208754383906812658174871)
  ·
    refine ⟨49813131575860218987262307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33208754383906812658174871 49813131575860218987262307)
    ·
      refine ⟨74719697363790328480893461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49813131575860218987262307 74719697363790328480893461)
      ·
        refine ⟨3502485813927671647541881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74719697363790328480893461 3502485813927671647541881)
        ·
          refine ⟨2626864360445753735656411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3502485813927671647541881 2626864360445753735656411)
          ·
            refine ⟨3940296540668630603484617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626864360445753735656411 3940296540668630603484617)
            ·
              refine ⟨2955222405501472952613463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3940296540668630603484617 2955222405501472952613463)
              ·
                refine ⟨4432833608252209428920195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955222405501472952613463 4432833608252209428920195)
                ·
                  refine ⟨6649250412378314143380293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432833608252209428920195 6649250412378314143380293)
                  ·
                    refine ⟨1246734452320933901883805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6649250412378314143380293 1246734452320933901883805)
                    ·
                      rfl

theorem cell22_3642010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_3642010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642010 prefixEnd_3642010 := by exact prefixLift 3642010
  have htrace : WordTrace (prefixWord ++ tailWord_3642010) baseStart_3642010 baseEnd_3642010 := by
    simpa [prefixWord, tailWord_3642010, baseEnd_3642010] using wordTrace_append hprefix tailTrace_3642010
  have hstable : (prefixWord ++ tailWord_3642010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642010).length < 2 ^ (prefixWord ++ tailWord_3642010).sum := by decide
  have hdescent : baseEnd_3642010 < baseStart_3642010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642143 : List Nat := [1, 1, 2, 4, 2, 4, 2, 2, 4]
def baseStart_3642143 : Nat := 118140960795 + 3642143 * 2 ^ 59
def prefixEnd_3642143 : Nat := 4983230072969 + 3 ^ 40 * 3642143 * 2
def baseEnd_3642143 : Nat := 415593326979655296102799

theorem tailTrace_3642143 : CollatzResearch.WordTrace tailWord_3642143 prefixEnd_3642143 415593326979655296102799 := by
  unfold tailWord_3642143
  simp only [CollatzResearch.WordTrace]
  refine ⟨132839868444145414347291083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88559912296096942898194055 132839868444145414347291083)
  ·
    refine ⟨199259802666218121520936625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132839868444145414347291083 199259802666218121520936625)
    ·
      refine ⟨149444851999663591140702469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199259802666218121520936625 149444851999663591140702469)
      ·
        refine ⟨28020909749936923338881713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149444851999663591140702469 28020909749936923338881713)
        ·
          refine ⟨21015682312452692504161285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28020909749936923338881713 21015682312452692504161285)
          ·
            refine ⟨3940440433584879844530241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21015682312452692504161285 3940440433584879844530241)
            ·
              refine ⟨2955330325188659883397681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3940440433584879844530241 2955330325188659883397681)
              ·
                refine ⟨2216497743891494912548261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955330325188659883397681 2216497743891494912548261)
                ·
                  refine ⟨415593326979655296102799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2216497743891494912548261 415593326979655296102799)
                  ·
                    rfl

theorem cell22_3642143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 4].length) (baseStart_3642143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642143 prefixEnd_3642143 := by exact prefixLift 3642143
  have htrace : WordTrace (prefixWord ++ tailWord_3642143) baseStart_3642143 baseEnd_3642143 := by
    simpa [prefixWord, tailWord_3642143, baseEnd_3642143] using wordTrace_append hprefix tailTrace_3642143
  have hstable : (prefixWord ++ tailWord_3642143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642143).length < 2 ^ (prefixWord ++ tailWord_3642143).sum := by decide
  have hdescent : baseEnd_3642143 < baseStart_3642143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642158 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3642158 : Nat := 118140960795 + 3642158 * 2 ^ 59
def prefixEnd_3642158 : Nat := 4983230072969 + 3 ^ 40 * 3642158 * 2
def baseEnd_3642158 : Nat := 1246785115745510849183351

theorem tailTrace_3642158 : CollatzResearch.WordTrace tailWord_3642158 prefixEnd_3642158 1246785115745510849183351 := by
  unfold tailWord_3642158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16605051942386383988635891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88560277026060714606058085 16605051942386383988635891)
  ·
    refine ⟨24907577913579575982953837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16605051942386383988635891 24907577913579575982953837)
    ·
      refine ⟨9340341717592340993607689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24907577913579575982953837 9340341717592340993607689)
      ·
        refine ⟨7005256288194255745205767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9340341717592340993607689 7005256288194255745205767)
        ·
          refine ⟨10507884432291383617808651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005256288194255745205767 10507884432291383617808651)
          ·
            refine ⟨15761826648437075426712977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507884432291383617808651 15761826648437075426712977)
            ·
              refine ⟨11821369986327806570034733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15761826648437075426712977 11821369986327806570034733)
              ·
                refine ⟨4433013744872927463763025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11821369986327806570034733 4433013744872927463763025)
                ·
                  refine ⟨3324760308654695597822269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4433013744872927463763025 3324760308654695597822269)
                  ·
                    refine ⟨1246785115745510849183351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324760308654695597822269 1246785115745510849183351)
                    ·
                      rfl

theorem cell22_3642158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3642158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642158 prefixEnd_3642158 := by exact prefixLift 3642158
  have htrace : WordTrace (prefixWord ++ tailWord_3642158) baseStart_3642158 baseEnd_3642158 := by
    simpa [prefixWord, tailWord_3642158, baseEnd_3642158] using wordTrace_append hprefix tailTrace_3642158
  have hstable : (prefixWord ++ tailWord_3642158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642158).length < 2 ^ (prefixWord ++ tailWord_3642158).sum := by decide
  have hdescent : baseEnd_3642158 < baseStart_3642158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642167 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 2, 6]
def baseStart_3642167 : Nat := 118140960795 + 3642167 * 2 ^ 59
def prefixEnd_3642167 : Nat := 4983230072969 + 3 ^ 40 * 3642167 * 2
def baseEnd_3642167 : Nat := 1246788196629437825708323

theorem tailTrace_3642167 : CollatzResearch.WordTrace tailWord_3642167 prefixEnd_3642167 1246788196629437825708323 := by
  unfold tailWord_3642167
  simp only [CollatzResearch.WordTrace]
  refine ⟨132840743796058466446164755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88560495864038977630776503 132840743796058466446164755)
  ·
    refine ⟨199261115694087699669247133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132840743796058466446164755 199261115694087699669247133)
    ·
      refine ⟨74722918385282887375967675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199261115694087699669247133 74722918385282887375967675)
      ·
        refine ⟨112084377577924331063951513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74722918385282887375967675 112084377577924331063951513)
        ·
          refine ⟨84063283183443248297963635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112084377577924331063951513 84063283183443248297963635)
          ·
            refine ⟨126094924775164872446945453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84063283183443248297963635 126094924775164872446945453)
            ·
              refine ⟨47285596790686827167604545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126094924775164872446945453 47285596790686827167604545)
              ·
                refine ⟨35464197593015120375703409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47285596790686827167604545 35464197593015120375703409)
                ·
                  refine ⟨26598148194761340281777557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35464197593015120375703409 26598148194761340281777557)
                  ·
                    refine ⟨1246788196629437825708323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26598148194761340281777557 1246788196629437825708323)
                    ·
                      rfl

theorem cell22_3642167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_3642167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642167 prefixEnd_3642167 := by exact prefixLift 3642167
  have htrace : WordTrace (prefixWord ++ tailWord_3642167) baseStart_3642167 baseEnd_3642167 := by
    simpa [prefixWord, tailWord_3642167, baseEnd_3642167] using wordTrace_append hprefix tailTrace_3642167
  have hstable : (prefixWord ++ tailWord_3642167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642167).length < 2 ^ (prefixWord ++ tailWord_3642167).sum := by decide
  have hdescent : baseEnd_3642167 < baseStart_3642167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642173 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_3642173 : Nat := 118140960795 + 3642173 * 2 ^ 59
def prefixEnd_3642173 : Nat := 4983230072969 + 3 ^ 40 * 3642173 * 2
def baseEnd_3642173 : Nat := 1246790250552055810058305

theorem tailTrace_3642173 : CollatzResearch.WordTrace tailWord_3642173 prefixEnd_3642173 1246790250552055810058305 := by
  unfold tailWord_3642173
  simp only [CollatzResearch.WordTrace]
  refine ⟨132840962634036729470883173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88560641756024486313922115 132840962634036729470883173)
  ·
    refine ⟨24907680493881886775790595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132840962634036729470883173 24907680493881886775790595)
    ·
      refine ⟨37361520740822830163685893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24907680493881886775790595 37361520740822830163685893)
      ·
        refine ⟨7005285138904280655691105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37361520740822830163685893 7005285138904280655691105)
        ·
          refine ⟨5253963854178210491768329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7005285138904280655691105 5253963854178210491768329)
          ·
            refine ⟨3940472890633657868826247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5253963854178210491768329 3940472890633657868826247)
            ·
              refine ⟨5910709335950486803239371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940472890633657868826247 5910709335950486803239371)
              ·
                refine ⟨8866064003925730204859057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910709335950486803239371 8866064003925730204859057)
                ·
                  refine ⟨6649548002944297653644293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8866064003925730204859057 6649548002944297653644293)
                  ·
                    refine ⟨1246790250552055810058305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6649548002944297653644293 1246790250552055810058305)
                    ·
                      rfl

theorem cell22_3642173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_3642173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642173 prefixEnd_3642173 := by exact prefixLift 3642173
  have htrace : WordTrace (prefixWord ++ tailWord_3642173) baseStart_3642173 baseEnd_3642173 := by
    simpa [prefixWord, tailWord_3642173, baseEnd_3642173] using wordTrace_append hprefix tailTrace_3642173
  have hstable : (prefixWord ++ tailWord_3642173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642173).length < 2 ^ (prefixWord ++ tailWord_3642173).sum := by decide
  have hdescent : baseEnd_3642173 < baseStart_3642173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642199 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 7]
def baseStart_3642199 : Nat := 118140960795 + 3642199 * 2 ^ 59
def prefixEnd_3642199 : Nat := 4983230072969 + 3 ^ 40 * 3642199 * 2
def baseEnd_3642199 : Nat := 415599716961133469636075

theorem tailTrace_3642199 : CollatzResearch.WordTrace tailWord_3642199 prefixEnd_3642199 415599716961133469636075 := by
  unfold tailWord_3642199
  simp only [CollatzResearch.WordTrace]
  refine ⟨132841910931942535911329651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88561273954628357274219767 132841910931942535911329651)
  ·
    refine ⟨199262866397913803866994477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132841910931942535911329651 199262866397913803866994477)
    ·
      refine ⟨74723574899217676450122929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199262866397913803866994477 74723574899217676450122929)
      ·
        refine ⟨56042681174413257337592197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74723574899217676450122929 56042681174413257337592197)
        ·
          refine ⟨10508002720202485750798537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56042681174413257337592197 10508002720202485750798537)
          ·
            refine ⟨7881002040151864313098903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10508002720202485750798537 7881002040151864313098903)
            ·
              refine ⟨11821503060227796469648355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7881002040151864313098903 11821503060227796469648355)
              ·
                refine ⟨17732254590341694704472533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11821503060227796469648355 17732254590341694704472533)
                ·
                  refine ⟨415599716961133469636075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17732254590341694704472533 415599716961133469636075)
                  ·
                    rfl

theorem cell22_3642199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 7].length) (baseStart_3642199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642199 prefixEnd_3642199 := by exact prefixLift 3642199
  have htrace : WordTrace (prefixWord ++ tailWord_3642199) baseStart_3642199 baseEnd_3642199 := by
    simpa [prefixWord, tailWord_3642199, baseEnd_3642199] using wordTrace_append hprefix tailTrace_3642199
  have hstable : (prefixWord ++ tailWord_3642199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642199).length < 2 ^ (prefixWord ++ tailWord_3642199).sum := by decide
  have hdescent : baseEnd_3642199 < baseStart_3642199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642261 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 6]
def baseStart_3642261 : Nat := 118140960795 + 3642261 * 2 ^ 59
def prefixEnd_3642261 : Nat := 4983230072969 + 3 ^ 40 * 3642261 * 2
def baseEnd_3642261 : Nat := 415606791583484304619345

theorem tailTrace_3642261 : CollatzResearch.WordTrace tailWord_3642261 prefixEnd_3642261 415606791583484304619345 := by
  unfold tailWord_3642261
  simp only [CollatzResearch.WordTrace]
  refine ⟨132844172257717920500086637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88562781505145280333391091 132844172257717920500086637)
  ·
    refine ⟨49816564596644220187532489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132844172257717920500086637 49816564596644220187532489)
    ·
      refine ⟨37362423447483165140649367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49816564596644220187532489 37362423447483165140649367)
      ·
        refine ⟨56043635171224747710974051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37362423447483165140649367 56043635171224747710974051)
        ·
          refine ⟨84065452756837121566461077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56043635171224747710974051 84065452756837121566461077)
          ·
            refine ⟨3940568097976740073427863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84065452756837121566461077 3940568097976740073427863)
            ·
              refine ⟨5910852146965110110141795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940568097976740073427863 5910852146965110110141795)
              ·
                refine ⟨8866278220447665165212693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910852146965110110141795 8866278220447665165212693)
                ·
                  refine ⟨415606791583484304619345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8866278220447665165212693 415606791583484304619345)
                  ·
                    rfl

theorem cell22_3642261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_3642261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642261 prefixEnd_3642261 := by exact prefixLift 3642261
  have htrace : WordTrace (prefixWord ++ tailWord_3642261) baseStart_3642261 baseEnd_3642261 := by
    simpa [prefixWord, tailWord_3642261, baseEnd_3642261] using wordTrace_append hprefix tailTrace_3642261
  have hstable : (prefixWord ++ tailWord_3642261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642261).length < 2 ^ (prefixWord ++ tailWord_3642261).sum := by decide
  have hdescent : baseEnd_3642261 < baseStart_3642261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642312 : List Nat := [2, 1, 3, 1, 6, 1, 2, 2, 4]
def baseStart_3642312 : Nat := 118140960795 + 3642312 * 2 ^ 59
def prefixEnd_3642312 : Nat := 4983230072969 + 3 ^ 40 * 3642312 * 2
def baseEnd_3642312 : Nat := 415612611030901926944293

theorem tailTrace_3642312 : CollatzResearch.WordTrace tailWord_3642312 prefixEnd_3642312 415612611030901926944293 := by
  unfold tailWord_3642312
  simp only [CollatzResearch.WordTrace]
  refine ⟨66423016190266578105096595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88564021587022104140128793 66423016190266578105096595)
  ·
    refine ⟨99634524285399867157644893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66423016190266578105096595 99634524285399867157644893)
    ·
      refine ⟨37362946607024950184116835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99634524285399867157644893 37362946607024950184116835)
      ·
        refine ⟨56044419910537425276175253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37362946607024950184116835 56044419910537425276175253)
        ·
          refine ⟨2627082183306441809820715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56044419910537425276175253 2627082183306441809820715)
          ·
            refine ⟨3940623274959662714731073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627082183306441809820715 3940623274959662714731073)
            ·
              refine ⟨2955467456219747036048305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3940623274959662714731073 2955467456219747036048305)
              ·
                refine ⟨2216600592164810277036229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955467456219747036048305 2216600592164810277036229)
                ·
                  refine ⟨415612611030901926944293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2216600592164810277036229 415612611030901926944293)
                  ·
                    rfl

theorem cell22_3642312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 4].length) (baseStart_3642312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642312 prefixEnd_3642312 := by exact prefixLift 3642312
  have htrace : WordTrace (prefixWord ++ tailWord_3642312) baseStart_3642312 baseEnd_3642312 := by
    simpa [prefixWord, tailWord_3642312, baseEnd_3642312] using wordTrace_append hprefix tailTrace_3642312
  have hstable : (prefixWord ++ tailWord_3642312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642312).length < 2 ^ (prefixWord ++ tailWord_3642312).sum := by decide
  have hdescent : baseEnd_3642312 < baseStart_3642312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642319 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 2, 6]
def baseStart_3642319 : Nat := 118140960795 + 3642319 * 2 ^ 59
def prefixEnd_3642319 : Nat := 4983230072969 + 3 ^ 40 * 3642319 * 2
def baseEnd_3642319 : Nat := 1246840229335760095907857

theorem tailTrace_3642319 : CollatzResearch.WordTrace tailWord_3642319 prefixEnd_3642319 1246840229335760095907857 := by
  unfold tailWord_3642319
  simp only [CollatzResearch.WordTrace]
  refine ⟨132846287691507796405698011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88564191794338530937132007 132846287691507796405698011)
  ·
    refine ⟨199269431537261694608547017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132846287691507796405698011 199269431537261694608547017)
    ·
      refine ⟨149452073652946270956410263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199269431537261694608547017 149452073652946270956410263)
      ·
        refine ⟨224178110479419406434615395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149452073652946270956410263 224178110479419406434615395)
        ·
          refine ⟨336267165719129109651923093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224178110479419406434615395 336267165719129109651923093)
          ·
            refine ⟨15762523393084177014933895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 336267165719129109651923093 15762523393084177014933895)
            ·
              refine ⟨23643785089626265522400843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15762523393084177014933895 23643785089626265522400843)
              ·
                refine ⟨35465677634439398283601265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23643785089626265522400843 35465677634439398283601265)
                ·
                  refine ⟨26599258225829548712700949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35465677634439398283601265 26599258225829548712700949)
                  ·
                    refine ⟨1246840229335760095907857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26599258225829548712700949 1246840229335760095907857)
                    ·
                      rfl

theorem cell22_3642319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_3642319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642319 prefixEnd_3642319 := by exact prefixLift 3642319
  have htrace : WordTrace (prefixWord ++ tailWord_3642319) baseStart_3642319 baseEnd_3642319 := by
    simpa [prefixWord, tailWord_3642319, baseEnd_3642319] using wordTrace_append hprefix tailTrace_3642319
  have hstable : (prefixWord ++ tailWord_3642319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642319).length < 2 ^ (prefixWord ++ tailWord_3642319).sum := by decide
  have hdescent : baseEnd_3642319 < baseStart_3642319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642321 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 3, 3]
def baseStart_3642321 : Nat := 118140960795 + 3642321 * 2 ^ 59
def prefixEnd_3642321 : Nat := 4983230072969 + 3 ^ 40 * 3642321 * 2
def baseEnd_3642321 : Nat := 1246840913976632757357851

theorem tailTrace_3642321 : CollatzResearch.WordTrace tailWord_3642321 prefixEnd_3642321 1246840913976632757357851 := by
  unfold tailWord_3642321
  simp only [CollatzResearch.WordTrace]
  refine ⟨132846360637500550747270817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88564240425000367164847211 132846360637500550747270817)
  ·
    refine ⟨99634770478125413060453113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132846360637500550747270817 99634770478125413060453113)
    ·
      refine ⟨74726077858594059795339835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99634770478125413060453113 74726077858594059795339835)
      ·
        refine ⟨112089116787891089693009753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74726077858594059795339835 112089116787891089693009753)
        ·
          refine ⟨84066837590918317269757315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112089116787891089693009753 84066837590918317269757315)
          ·
            refine ⟨126100256386377475904635973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84066837590918317269757315 126100256386377475904635973)
            ·
              refine ⟨23643798072445776732119245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126100256386377475904635973 23643798072445776732119245)
              ·
                refine ⟨8866424277167166274544717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23643798072445776732119245 8866424277167166274544717)
                ·
                  refine ⟨3324909103937687352954269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8866424277167166274544717 3324909103937687352954269)
                  ·
                    refine ⟨1246840913976632757357851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324909103937687352954269 1246840913976632757357851)
                    ·
                      rfl

theorem cell22_3642321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_3642321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642321 prefixEnd_3642321 := by exact prefixLift 3642321
  have htrace : WordTrace (prefixWord ++ tailWord_3642321) baseStart_3642321 baseEnd_3642321 := by
    simpa [prefixWord, tailWord_3642321, baseEnd_3642321] using wordTrace_append hprefix tailTrace_3642321
  have hstable : (prefixWord ++ tailWord_3642321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642321).length < 2 ^ (prefixWord ++ tailWord_3642321).sum := by decide
  have hdescent : baseEnd_3642321 < baseStart_3642321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642411 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 6, 3]
def baseStart_3642411 : Nat := 118140960795 + 3642411 * 2 ^ 59
def prefixEnd_3642411 : Nat := 4983230072969 + 3 ^ 40 * 3642411 * 2
def baseEnd_3642411 : Nat := 1246871722815902522607575

theorem tailTrace_3642411 : CollatzResearch.WordTrace tailWord_3642411 prefixEnd_3642411 1246871722815902522607575 := by
  unfold tailWord_3642411
  simp only [CollatzResearch.WordTrace]
  refine ⟨132849643207174496118047087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88566428804782997412031391 132849643207174496118047087)
  ·
    refine ⟨199274464810761744177070631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132849643207174496118047087 199274464810761744177070631)
    ·
      refine ⟨298911697216142616265605947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199274464810761744177070631 298911697216142616265605947)
      ·
        refine ⟨448367545824213924398408921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298911697216142616265605947 448367545824213924398408921)
        ·
          refine ⟨336275659368160443298806691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448367545824213924398408921 336275659368160443298806691)
          ·
            refine ⟨504413489052240664948210037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336275659368160443298806691 504413489052240664948210037)
            ·
              refine ⟨47288764598647562338894691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 504413489052240664948210037 47288764598647562338894691)
              ·
                refine ⟨70933146897971343508342037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47288764598647562338894691 70933146897971343508342037)
                ·
                  refine ⟨3324991260842406726953533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70933146897971343508342037 3324991260842406726953533)
                  ·
                    refine ⟨1246871722815902522607575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3324991260842406726953533 1246871722815902522607575)
                    ·
                      rfl

theorem cell22_3642411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 3].length) (baseStart_3642411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642411 prefixEnd_3642411 := by exact prefixLift 3642411
  have htrace : WordTrace (prefixWord ++ tailWord_3642411) baseStart_3642411 baseEnd_3642411 := by
    simpa [prefixWord, tailWord_3642411, baseEnd_3642411] using wordTrace_append hprefix tailTrace_3642411
  have hstable : (prefixWord ++ tailWord_3642411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642411).length < 2 ^ (prefixWord ++ tailWord_3642411).sum := by decide
  have hdescent : baseEnd_3642411 < baseStart_3642411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642426 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_3642426 : Nat := 118140960795 + 3642426 * 2 ^ 59
def prefixEnd_3642426 : Nat := 4983230072969 + 3 ^ 40 * 3642426 * 2
def baseEnd_3642426 : Nat := 1246876857622447483482529

theorem tailTrace_3642426 : CollatzResearch.WordTrace tailWord_3642426 prefixEnd_3642426 1246876857622447483482529 := by
  unfold tailWord_3642426
  simp only [CollatzResearch.WordTrace]
  refine ⟨33212547575530038419960783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88566793534746769119895421 33212547575530038419960783)
  ·
    refine ⟨49818821363295057629941175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33212547575530038419960783 49818821363295057629941175)
    ·
      refine ⟨74728232044942586444911763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49818821363295057629941175 74728232044942586444911763)
      ·
        refine ⟨112092348067413879667367645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74728232044942586444911763 112092348067413879667367645)
        ·
          refine ⟨42034630525280204875262867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112092348067413879667367645 42034630525280204875262867)
          ·
            refine ⟨63051945787920307312894301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42034630525280204875262867 63051945787920307312894301)
            ·
              refine ⟨23644479670470115242335363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63051945787920307312894301 23644479670470115242335363)
              ·
                refine ⟨35466719505705172863503045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23644479670470115242335363 35466719505705172863503045)
                ·
                  refine ⟨6650009907319719911906821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35466719505705172863503045 6650009907319719911906821)
                  ·
                    refine ⟨1246876857622447483482529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6650009907319719911906821 1246876857622447483482529)
                    ·
                      rfl

theorem cell22_3642426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_3642426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642426 prefixEnd_3642426 := by exact prefixLift 3642426
  have htrace : WordTrace (prefixWord ++ tailWord_3642426) baseStart_3642426 baseEnd_3642426 := by
    simpa [prefixWord, tailWord_3642426, baseEnd_3642426] using wordTrace_append hprefix tailTrace_3642426
  have hstable : (prefixWord ++ tailWord_3642426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642426).length < 2 ^ (prefixWord ++ tailWord_3642426).sum := by decide
  have hdescent : baseEnd_3642426 < baseStart_3642426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642428 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_3642428 : Nat := 118140960795 + 3642428 * 2 ^ 59
def prefixEnd_3642428 : Nat := 4983230072969 + 3 ^ 40 * 3642428 * 2
def baseEnd_3642428 : Nat := 1246877542263320144932523

theorem tailTrace_3642428 : CollatzResearch.WordTrace tailWord_3642428 prefixEnd_3642428 1246877542263320144932523 := by
  unfold tailWord_3642428
  simp only [CollatzResearch.WordTrace]
  refine ⟨66425131624056454010707969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88566842165408605347610625 66425131624056454010707969)
  ·
    refine ⟨49818848718042340508030977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66425131624056454010707969 49818848718042340508030977)
    ·
      refine ⟨37364136538531755381023233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49818848718042340508030977 37364136538531755381023233)
      ·
        refine ⟨28023102403898816535767425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37364136538531755381023233 28023102403898816535767425)
        ·
          refine ⟨21017326802924112401825569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28023102403898816535767425 21017326802924112401825569)
          ·
            refine ⟨15762995102193084301369177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21017326802924112401825569 15762995102193084301369177)
            ·
              refine ⟨11822246326644813226026883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15762995102193084301369177 11822246326644813226026883)
              ·
                refine ⟨17733369489967219839040325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11822246326644813226026883 17733369489967219839040325)
                ·
                  refine ⟨3325006779368853719820061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17733369489967219839040325 3325006779368853719820061)
                  ·
                    refine ⟨1246877542263320144932523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325006779368853719820061 1246877542263320144932523)
                    ·
                      rfl

theorem cell22_3642428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_3642428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642428 prefixEnd_3642428 := by exact prefixLift 3642428
  have htrace : WordTrace (prefixWord ++ tailWord_3642428) baseStart_3642428 baseEnd_3642428 := by
    simpa [prefixWord, tailWord_3642428, baseEnd_3642428] using wordTrace_append hprefix tailTrace_3642428
  have hstable : (prefixWord ++ tailWord_3642428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642428).length < 2 ^ (prefixWord ++ tailWord_3642428).sum := by decide
  have hdescent : baseEnd_3642428 < baseStart_3642428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642430 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3642430 : Nat := 118140960795 + 3642430 * 2 ^ 59
def prefixEnd_3642430 : Nat := 4983230072969 + 3 ^ 40 * 3642430 * 2
def baseEnd_3642430 : Nat := 415626075634730935460839

theorem tailTrace_3642430 : CollatzResearch.WordTrace tailWord_3642430 prefixEnd_3642430 415626075634730935460839 := by
  unfold tailWord_3642430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606292024263207795373593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88566890796070441575325829 16606292024263207795373593)
  ·
    refine ⟨12454719018197405846530195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16606292024263207795373593 12454719018197405846530195)
    ·
      refine ⟨18682078527296108769795293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12454719018197405846530195 18682078527296108769795293)
      ·
        refine ⟨7005779447736040788673235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18682078527296108769795293 7005779447736040788673235)
        ·
          refine ⟨10508669171604061183009853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005779447736040788673235 10508669171604061183009853)
          ·
            refine ⟨3940750939351522943628695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10508669171604061183009853 3940750939351522943628695)
            ·
              refine ⟨5911126409027284415443043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940750939351522943628695 5911126409027284415443043)
              ·
                refine ⟨8866689613540926623164565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911126409027284415443043 8866689613540926623164565)
                ·
                  refine ⟨415626075634730935460839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8866689613540926623164565 415626075634730935460839)
                  ·
                    rfl

theorem cell22_3642430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3642430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642430 prefixEnd_3642430 := by exact prefixLift 3642430
  have htrace : WordTrace (prefixWord ++ tailWord_3642430) baseStart_3642430 baseEnd_3642430 := by
    simpa [prefixWord, tailWord_3642430, baseEnd_3642430] using wordTrace_append hprefix tailTrace_3642430
  have hstable : (prefixWord ++ tailWord_3642430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642430).length < 2 ^ (prefixWord ++ tailWord_3642430).sum := by decide
  have hdescent : baseEnd_3642430 < baseStart_3642430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642462 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3642462 : Nat := 118140960795 + 3642462 * 2 ^ 59
def prefixEnd_3642462 : Nat := 4983230072969 + 3 ^ 40 * 3642462 * 2
def baseEnd_3642462 : Nat := 1246889181158155389582419

theorem tailTrace_3642462 : CollatzResearch.WordTrace tailWord_3642462 prefixEnd_3642462 1246889181158155389582419 := by
  unfold tailWord_3642462
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606437916248716478519205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88567668886659821218769093 16606437916248716478519205)
  ·
    refine ⟨3113707109296634339722351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16606437916248716478519205 3113707109296634339722351)
    ·
      refine ⟨4670560663944951509583527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3113707109296634339722351 4670560663944951509583527)
      ·
        refine ⟨7005840995917427264375291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4670560663944951509583527 7005840995917427264375291)
        ·
          refine ⟨10508761493876140896562937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005840995917427264375291 10508761493876140896562937)
          ·
            refine ⟨7881571120407105672422203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10508761493876140896562937 7881571120407105672422203)
            ·
              refine ⟨11822356680610658508633305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7881571120407105672422203 11822356680610658508633305)
              ·
                refine ⟨8866767510457993881474979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11822356680610658508633305 8866767510457993881474979)
                ·
                  refine ⟨13300151265686990822212469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8866767510457993881474979 13300151265686990822212469)
                  ·
                    refine ⟨1246889181158155389582419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13300151265686990822212469 1246889181158155389582419)
                    ·
                      rfl

theorem cell22_3642462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3642462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642462 prefixEnd_3642462 := by exact prefixLift 3642462
  have htrace : WordTrace (prefixWord ++ tailWord_3642462) baseStart_3642462 baseEnd_3642462 := by
    simpa [prefixWord, tailWord_3642462, baseEnd_3642462] using wordTrace_append hprefix tailTrace_3642462
  have hstable : (prefixWord ++ tailWord_3642462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642462).length < 2 ^ (prefixWord ++ tailWord_3642462).sum := by decide
  have hdescent : baseEnd_3642462 < baseStart_3642462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642578 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_3642578 : Nat := 118140960795 + 3642578 * 2 ^ 59
def prefixEnd_3642578 : Nat := 4983230072969 + 3 ^ 40 * 3642578 * 2
def baseEnd_3642578 : Nat := 1246928890328769753682063

theorem tailTrace_3642578 : CollatzResearch.WordTrace tailWord_3642578 prefixEnd_3642578 1246928890328769753682063 := by
  unfold tailWord_3642578
  simp only [CollatzResearch.WordTrace]
  refine ⟨33213933549392370909844097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88570489465046322426250925 33213933549392370909844097)
  ·
    refine ⟨24910450162044278182383073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33213933549392370909844097 24910450162044278182383073)
    ·
      refine ⟨18682837621533208636787305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24910450162044278182383073 18682837621533208636787305)
      ·
        refine ⟨14012128216149906477590479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18682837621533208636787305 14012128216149906477590479)
        ·
          refine ⟨21018192324224859716385719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14012128216149906477590479 21018192324224859716385719)
          ·
            refine ⟨31527288486337289574578579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21018192324224859716385719 31527288486337289574578579)
            ·
              refine ⟨47290932729505934361867869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31527288486337289574578579 47290932729505934361867869)
              ·
                refine ⟨17734099773564725385700451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47290932729505934361867869 17734099773564725385700451)
                ·
                  refine ⟨26601149660347088078550677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17734099773564725385700451 26601149660347088078550677)
                  ·
                    refine ⟨1246928890328769753682063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26601149660347088078550677 1246928890328769753682063)
                    ·
                      rfl

theorem cell22_3642578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_3642578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642578 prefixEnd_3642578 := by exact prefixLift 3642578
  have htrace : WordTrace (prefixWord ++ tailWord_3642578) baseStart_3642578 baseEnd_3642578 := by
    simpa [prefixWord, tailWord_3642578, baseEnd_3642578] using wordTrace_append hprefix tailTrace_3642578
  have hstable : (prefixWord ++ tailWord_3642578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642578).length < 2 ^ (prefixWord ++ tailWord_3642578).sum := by decide
  have hdescent : baseEnd_3642578 < baseStart_3642578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642593 : List Nat := [1, 2, 3, 1, 3, 4, 8]
def baseStart_3642593 : Nat := 118140960795 + 3642593 * 2 ^ 59
def prefixEnd_3642593 : Nat := 4983230072969 + 3 ^ 40 * 3642593 * 2
def baseEnd_3642593 : Nat := 46182741671678322761371

theorem tailTrace_3642593 : CollatzResearch.WordTrace tailWord_3642593 prefixEnd_3642593 46182741671678322761371 := by
  unfold tailWord_3642593
  simp only [CollatzResearch.WordTrace]
  refine ⟨132856281292515141201172433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88570854195010094134114955 132856281292515141201172433)
  ·
    refine ⟨99642210969386355900879325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132856281292515141201172433 99642210969386355900879325)
    ·
      refine ⟨37365829113519883462829747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99642210969386355900879325 37365829113519883462829747)
      ·
        refine ⟨56048743670279825194244621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37365829113519883462829747 56048743670279825194244621)
        ·
          refine ⟨21018278876354934447841733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56048743670279825194244621 21018278876354934447841733)
          ·
            refine ⟨3940927289316550208970325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21018278876354934447841733 3940927289316550208970325)
            ·
              refine ⟨46182741671678322761371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3940927289316550208970325 46182741671678322761371)
              ·
                rfl

theorem cell22_3642593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 8].length) (baseStart_3642593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642593 prefixEnd_3642593 := by exact prefixLift 3642593
  have htrace : WordTrace (prefixWord ++ tailWord_3642593) baseStart_3642593 baseEnd_3642593 := by
    simpa [prefixWord, tailWord_3642593, baseEnd_3642593] using wordTrace_append hprefix tailTrace_3642593
  have hstable : (prefixWord ++ tailWord_3642593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642593).length < 2 ^ (prefixWord ++ tailWord_3642593).sum := by decide
  have hdescent : baseEnd_3642593 < baseStart_3642593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642599 : List Nat := [1, 1, 5, 3, 2, 1, 3, 2, 4]
def baseStart_3642599 : Nat := 118140960795 + 3642599 * 2 ^ 59
def prefixEnd_3642599 : Nat := 4983230072969 + 3 ^ 40 * 3642599 * 2
def baseEnd_3642599 : Nat := 415645359685977566302333

theorem tailTrace_3642599 : CollatzResearch.WordTrace tailWord_3642599 prefixEnd_3642599 415645359685977566302333 := by
  unfold tailWord_3642599
  simp only [CollatzResearch.WordTrace]
  refine ⟨132856500130493404225890851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88571000086995602817260567 132856500130493404225890851)
  ·
    refine ⟨199284750195740106338836277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132856500130493404225890851 199284750195740106338836277)
    ·
      refine ⟨18682945330850634969265901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199284750195740106338836277 18682945330850634969265901)
      ·
        refine ⟨7006104499068988113474713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18682945330850634969265901 7006104499068988113474713)
        ·
          refine ⟨5254578374301741085106035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7006104499068988113474713 5254578374301741085106035)
          ·
            refine ⟨7881867561452611627659053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254578374301741085106035 7881867561452611627659053)
            ·
              refine ⟨2955700335544729360372145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7881867561452611627659053 2955700335544729360372145)
              ·
                refine ⟨2216775251658547020279109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955700335544729360372145 2216775251658547020279109)
                ·
                  refine ⟨415645359685977566302333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2216775251658547020279109 415645359685977566302333)
                  ·
                    rfl

theorem cell22_3642599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 4].length) (baseStart_3642599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642599 prefixEnd_3642599 := by exact prefixLift 3642599
  have htrace : WordTrace (prefixWord ++ tailWord_3642599) baseStart_3642599 baseEnd_3642599 := by
    simpa [prefixWord, tailWord_3642599, baseEnd_3642599] using wordTrace_append hprefix tailTrace_3642599
  have hstable : (prefixWord ++ tailWord_3642599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642599).length < 2 ^ (prefixWord ++ tailWord_3642599).sum := by decide
  have hdescent : baseEnd_3642599 < baseStart_3642599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642610 : List Nat := [3, 2, 1, 3, 3, 1, 2, 7]
def baseStart_3642610 : Nat := 118140960795 + 3642610 * 2 ^ 59
def prefixEnd_3642610 : Nat := 4983230072969 + 3 ^ 40 * 3642610 * 2
def baseEnd_3642610 : Nat := 138548871620303592986885

theorem tailTrace_3642610 : CollatzResearch.WordTrace tailWord_3642610 prefixEnd_3642610 138548871620303592986885 := by
  unfold tailWord_3642610
  simp only [CollatzResearch.WordTrace]
  refine ⟨33214225333363388276135321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88571267555635702069694189 33214225333363388276135321)
  ·
    refine ⟨24910669000022541207101491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33214225333363388276135321 24910669000022541207101491)
    ·
      refine ⟨37366003500033811810652237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24910669000022541207101491 37366003500033811810652237)
      ·
        refine ⟨14012251312512679428994589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37366003500033811810652237 14012251312512679428994589)
        ·
          refine ⟨5254594242192254785872971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14012251312512679428994589 5254594242192254785872971)
          ·
            refine ⟨7881891363288382178809457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254594242192254785872971 7881891363288382178809457)
            ·
              refine ⟨5911418522466286634107093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7881891363288382178809457 5911418522466286634107093)
              ·
                refine ⟨138548871620303592986885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5911418522466286634107093 138548871620303592986885)
                ·
                  rfl

theorem cell22_3642610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_3642610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642610 prefixEnd_3642610 := by exact prefixLift 3642610
  have htrace : WordTrace (prefixWord ++ tailWord_3642610) baseStart_3642610 baseEnd_3642610 := by
    simpa [prefixWord, tailWord_3642610, baseEnd_3642610] using wordTrace_append hprefix tailTrace_3642610
  have hstable : (prefixWord ++ tailWord_3642610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642610).length < 2 ^ (prefixWord ++ tailWord_3642610).sum := by decide
  have hdescent : baseEnd_3642610 < baseStart_3642610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642659 : List Nat := [1, 1, 1, 4, 2, 3, 4, 2, 1, 3]
def baseStart_3642659 : Nat := 118140960795 + 3642659 * 2 ^ 59
def prefixEnd_3642659 : Nat := 4983230072969 + 3 ^ 40 * 3642659 * 2
def baseEnd_3642659 : Nat := 1246956618284112542406815

theorem tailTrace_3642659 : CollatzResearch.WordTrace tailWord_3642659 prefixEnd_3642659 1246956618284112542406815 := by
  unfold tailWord_3642659
  simp only [CollatzResearch.WordTrace]
  refine ⟨132858688510276034473075031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88572459006850689648716687 132858688510276034473075031)
  ·
    refine ⟨199288032765414051709612547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132858688510276034473075031 199288032765414051709612547)
    ·
      refine ⟨298932049148121077564418821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199288032765414051709612547 298932049148121077564418821)
      ·
        refine ⟨56049759215272702043328529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298932049148121077564418821 56049759215272702043328529)
        ·
          refine ⟨42037319411454526532496397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56049759215272702043328529 42037319411454526532496397)
          ·
            refine ⟨15763994779295447449686149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42037319411454526532496397 15763994779295447449686149)
            ·
              refine ⟨2955749021117896396816153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15763994779295447449686149 2955749021117896396816153)
              ·
                refine ⟨2216811765838422297612115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955749021117896396816153 2216811765838422297612115)
                ·
                  refine ⟨3325217648757633446418173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216811765838422297612115 3325217648757633446418173)
                  ·
                    refine ⟨1246956618284112542406815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325217648757633446418173 1246956618284112542406815)
                    ·
                      rfl

theorem cell22_3642659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 3].length) (baseStart_3642659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642659 prefixEnd_3642659 := by exact prefixLift 3642659
  have htrace : WordTrace (prefixWord ++ tailWord_3642659) baseStart_3642659 baseEnd_3642659 := by
    simpa [prefixWord, tailWord_3642659, baseEnd_3642659] using wordTrace_append hprefix tailTrace_3642659
  have hstable : (prefixWord ++ tailWord_3642659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642659).length < 2 ^ (prefixWord ++ tailWord_3642659).sum := by decide
  have hdescent : baseEnd_3642659 < baseStart_3642659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642732 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_3642732 : Nat := 118140960795 + 3642732 * 2 ^ 59
def prefixEnd_3642732 : Nat := 4983230072969 + 3 ^ 40 * 3642732 * 2
def baseEnd_3642732 : Nat := 1246981607675964685331591

theorem tailTrace_3642732 : CollatzResearch.WordTrace tailWord_3642732 prefixEnd_3642732 1246981607675964685331591 := by
  unfold tailWord_3642732
  simp only [CollatzResearch.WordTrace]
  refine ⟨66430675519505783970241225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88574234026007711960321633 66430675519505783970241225)
  ·
    refine ⟨49823006639629337977680919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66430675519505783970241225 49823006639629337977680919)
    ·
      refine ⟨74734509959444006966521379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49823006639629337977680919 74734509959444006966521379)
      ·
        refine ⟨112101764939166010449782069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74734509959444006966521379 112101764939166010449782069)
        ·
          refine ⟨10509540463046813479667069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112101764939166010449782069 10509540463046813479667069)
          ·
            refine ⟨3941077673642555054875151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10509540463046813479667069 3941077673642555054875151)
            ·
              refine ⟨5911616510463832582312727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941077673642555054875151 5911616510463832582312727)
              ·
                refine ⟨8867424765695748873469091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911616510463832582312727 8867424765695748873469091)
                ·
                  refine ⟨13301137148543623310203637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8867424765695748873469091 13301137148543623310203637)
                  ·
                    refine ⟨1246981607675964685331591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13301137148543623310203637 1246981607675964685331591)
                    ·
                      rfl

theorem cell22_3642732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_3642732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642732 prefixEnd_3642732 := by exact prefixLift 3642732
  have htrace : WordTrace (prefixWord ++ tailWord_3642732) baseStart_3642732 baseEnd_3642732 := by
    simpa [prefixWord, tailWord_3642732, baseEnd_3642732] using wordTrace_append hprefix tailTrace_3642732
  have hstable : (prefixWord ++ tailWord_3642732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642732).length < 2 ^ (prefixWord ++ tailWord_3642732).sum := by decide
  have hdescent : baseEnd_3642732 < baseStart_3642732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642743 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 2, 7]
def baseStart_3642743 : Nat := 118140960795 + 3642743 * 2 ^ 59
def prefixEnd_3642743 : Nat := 4983230072969 + 3 ^ 40 * 3642743 * 2
def baseEnd_3642743 : Nat := 1246985373200764323306557

theorem tailTrace_3642743 : CollatzResearch.WordTrace tailWord_3642743 prefixEnd_3642743 1246985373200764323306557 := by
  unfold tailWord_3642743
  simp only [CollatzResearch.WordTrace]
  refine ⟨132861752241971716819132883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88574501494647811212755255 132861752241971716819132883)
  ·
    refine ⟨199292628362957575228699325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132861752241971716819132883 199292628362957575228699325)
    ·
      refine ⟨74734735636109090710762247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199292628362957575228699325 74734735636109090710762247)
      ·
        refine ⟨112102103454163636066143371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74734735636109090710762247 112102103454163636066143371)
        ·
          refine ⟨168153155181245454099215057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112102103454163636066143371 168153155181245454099215057)
          ·
            refine ⟨126114866385934090574411293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168153155181245454099215057 126114866385934090574411293)
            ·
              refine ⟨47293074894725283965404235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126114866385934090574411293 47293074894725283965404235)
              ·
                refine ⟨70939612342087925948106353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47293074894725283965404235 70939612342087925948106353)
                ·
                  refine ⟨53204709256565944461079765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70939612342087925948106353 53204709256565944461079765)
                  ·
                    refine ⟨1246985373200764323306557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53204709256565944461079765 1246985373200764323306557)
                    ·
                      rfl

theorem cell22_3642743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_3642743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642743 prefixEnd_3642743 := by exact prefixLift 3642743
  have htrace : WordTrace (prefixWord ++ tailWord_3642743) baseStart_3642743 baseEnd_3642743 := by
    simpa [prefixWord, tailWord_3642743, baseEnd_3642743] using wordTrace_append hprefix tailTrace_3642743
  have hstable : (prefixWord ++ tailWord_3642743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642743).length < 2 ^ (prefixWord ++ tailWord_3642743).sum := by decide
  have hdescent : baseEnd_3642743 < baseStart_3642743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642745 : List Nat := [1, 2, 1, 3, 2, 1, 6, 6]
def baseStart_3642745 : Nat := 118140960795 + 3642745 * 2 ^ 59
def prefixEnd_3642745 : Nat := 4983230072969 + 3 ^ 40 * 3642745 * 2
def baseEnd_3642745 : Nat := 138554006426848553861839

theorem tailTrace_3642745 : CollatzResearch.WordTrace tailWord_3642745 prefixEnd_3642745 138554006426848553861839 := by
  unfold tailWord_3642745
  simp only [CollatzResearch.WordTrace]
  refine ⟨132861825187964471160705689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88574550125309647440470459 132861825187964471160705689)
  ·
    refine ⟨99646368890973353370529267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132861825187964471160705689 99646368890973353370529267)
    ·
      refine ⟨149469553336460030055793901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99646368890973353370529267 149469553336460030055793901)
      ·
        refine ⟨56051082501172511270922713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149469553336460030055793901 56051082501172511270922713)
        ·
          refine ⟨42038311875879383453192035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56051082501172511270922713 42038311875879383453192035)
          ·
            refine ⟨63057467813819075179788053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42038311875879383453192035 63057467813819075179788053)
            ·
              refine ⟨2955818803772769149052565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63057467813819075179788053 2955818803772769149052565)
              ·
                refine ⟨138554006426848553861839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2955818803772769149052565 138554006426848553861839)
                ·
                  rfl

theorem cell22_3642745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 6].length) (baseStart_3642745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642745 prefixEnd_3642745 := by exact prefixLift 3642745
  have htrace : WordTrace (prefixWord ++ tailWord_3642745) baseStart_3642745 baseEnd_3642745 := by
    simpa [prefixWord, tailWord_3642745, baseEnd_3642745] using wordTrace_append hprefix tailTrace_3642745
  have hstable : (prefixWord ++ tailWord_3642745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642745).length < 2 ^ (prefixWord ++ tailWord_3642745).sum := by decide
  have hdescent : baseEnd_3642745 < baseStart_3642745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642777 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 3, 3]
def baseStart_3642777 : Nat := 118140960795 + 3642777 * 2 ^ 59
def prefixEnd_3642777 : Nat := 4983230072969 + 3 ^ 40 * 3642777 * 2
def baseEnd_3642777 : Nat := 1246997012095599567956453

theorem tailTrace_3642777 : CollatzResearch.WordTrace tailWord_3642777 prefixEnd_3642777 1246997012095599567956453 := by
  unfold tailWord_3642777
  simp only [CollatzResearch.WordTrace]
  refine ⟨132862992323848540625870585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88575328215899027083913723 132862992323848540625870585)
  ·
    refine ⟨99647244242886405469402939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132862992323848540625870585 99647244242886405469402939)
    ·
      refine ⟨149470866364329608204104409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99647244242886405469402939 149470866364329608204104409)
      ·
        refine ⟨112103149773247206153078307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149470866364329608204104409 112103149773247206153078307)
        ·
          refine ⟨168154724659870809229617461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112103149773247206153078307 168154724659870809229617461)
          ·
            refine ⟨15764505436862888365276637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168154724659870809229617461 15764505436862888365276637)
            ·
              refine ⟨5911689538823583136978739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15764505436862888365276637 5911689538823583136978739)
              ·
                refine ⟨8867534308235374705468109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911689538823583136978739 8867534308235374705468109)
                ·
                  refine ⟨3325325365588265514550541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8867534308235374705468109 3325325365588265514550541)
                  ·
                    refine ⟨1246997012095599567956453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325325365588265514550541 1246997012095599567956453)
                    ·
                      rfl

theorem cell22_3642777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_3642777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642777 prefixEnd_3642777 := by exact prefixLift 3642777
  have htrace : WordTrace (prefixWord ++ tailWord_3642777) baseStart_3642777 baseEnd_3642777 := by
    simpa [prefixWord, tailWord_3642777, baseEnd_3642777] using wordTrace_append hprefix tailTrace_3642777
  have hstable : (prefixWord ++ tailWord_3642777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642777).length < 2 ^ (prefixWord ++ tailWord_3642777).sum := by decide
  have hdescent : baseEnd_3642777 < baseStart_3642777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642828 : List Nat := [2, 2, 1, 4, 2, 3, 2, 2, 1, 3]
def baseStart_3642828 : Nat := 118140960795 + 3642828 * 2 ^ 59
def prefixEnd_3642828 : Nat := 4983230072969 + 3 ^ 40 * 3642828 * 2
def baseEnd_3642828 : Nat := 1247014470437852434931297

theorem tailTrace_3642828 : CollatzResearch.WordTrace tailWord_3642828 prefixEnd_3642828 1247014470437852434931297 := by
  unfold tailWord_3642828
  simp only [CollatzResearch.WordTrace]
  refine ⟨66432426223331888167988569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88576568297775850890651425 66432426223331888167988569)
  ·
    refine ⟨49824319667498916125991427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66432426223331888167988569 49824319667498916125991427)
    ·
      refine ⟨74736479501248374188987141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49824319667498916125991427 74736479501248374188987141)
      ·
        refine ⟨14013089906484070160435089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74736479501248374188987141 14013089906484070160435089)
        ·
          refine ⟨10509817429863052620326317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14013089906484070160435089 10509817429863052620326317)
          ·
            refine ⟨3941181536198644732622369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10509817429863052620326317 3941181536198644732622369)
            ·
              refine ⟨2955886152148983549466777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941181536198644732622369 2955886152148983549466777)
              ·
                refine ⟨2216914614111737662100083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955886152148983549466777 2216914614111737662100083)
                ·
                  refine ⟨3325371921167606493150125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216914614111737662100083 3325371921167606493150125)
                  ·
                    refine ⟨1247014470437852434931297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325371921167606493150125 1247014470437852434931297)
                    ·
                      rfl

theorem cell22_3642828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_3642828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642828 prefixEnd_3642828 := by exact prefixLift 3642828
  have htrace : WordTrace (prefixWord ++ tailWord_3642828) baseStart_3642828 baseEnd_3642828 := by
    simpa [prefixWord, tailWord_3642828, baseEnd_3642828] using wordTrace_append hprefix tailTrace_3642828
  have hstable : (prefixWord ++ tailWord_3642828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642828).length < 2 ^ (prefixWord ++ tailWord_3642828).sum := by decide
  have hdescent : baseEnd_3642828 < baseStart_3642828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642901 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 2, 3]
def baseStart_3642901 : Nat := 118140960795 + 3642901 * 2 ^ 59
def prefixEnd_3642901 : Nat := 4983230072969 + 3 ^ 40 * 3642901 * 2
def baseEnd_3642901 : Nat := 1247039459829704577856073

theorem tailTrace_3642901 : CollatzResearch.WordTrace tailWord_3642901 prefixEnd_3642901 1247039459829704577856073 := by
  unfold tailWord_3642901
  simp only [CollatzResearch.WordTrace]
  refine ⟨132867514975399309803384557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88578343316932873202256371 132867514975399309803384557)
  ·
    refine ⟨49825318115774741176269209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132867514975399309803384557 49825318115774741176269209)
    ·
      refine ⟨37368988586831055882201907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49825318115774741176269209 37368988586831055882201907)
      ·
        refine ⟨56053482880246583823302861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37368988586831055882201907 56053482880246583823302861)
        ·
          refine ⟨21020056080092468933738573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56053482880246583823302861 21020056080092468933738573)
          ·
            refine ⟨7882521030034675850151965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21020056080092468933738573 7882521030034675850151965)
            ·
              refine ⟨2955945386263003443806987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7882521030034675850151965 2955945386263003443806987)
              ·
                refine ⟨4433918079394505165710481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955945386263003443806987 4433918079394505165710481)
                ·
                  refine ⟨3325438559545878874282861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4433918079394505165710481 3325438559545878874282861)
                  ·
                    refine ⟨1247039459829704577856073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325438559545878874282861 1247039459829704577856073)
                    ·
                      rfl

theorem cell22_3642901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_3642901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642901 prefixEnd_3642901 := by exact prefixLift 3642901
  have htrace : WordTrace (prefixWord ++ tailWord_3642901) baseStart_3642901 baseEnd_3642901 := by
    simpa [prefixWord, tailWord_3642901, baseEnd_3642901] using wordTrace_append hprefix tailTrace_3642901
  have hstable : (prefixWord ++ tailWord_3642901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642901).length < 2 ^ (prefixWord ++ tailWord_3642901).sum := by decide
  have hdescent : baseEnd_3642901 < baseStart_3642901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642955 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 2, 8]
def baseStart_3642955 : Nat := 118140960795 + 3642955 * 2 ^ 59
def prefixEnd_3642955 : Nat := 4983230072969 + 3 ^ 40 * 3642955 * 2
def baseEnd_3642955 : Nat := 1247057945133266437005907

theorem tailTrace_3642955 : CollatzResearch.WordTrace tailWord_3642955 prefixEnd_3642955 1247057945133266437005907 := by
  unfold tailWord_3642955
  simp only [CollatzResearch.WordTrace]
  refine ⟨132869484517203677025850319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88579656344802451350566879 132869484517203677025850319)
  ·
    refine ⟨199304226775805515538775479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132869484517203677025850319 199304226775805515538775479)
    ·
      refine ⟨298956340163708273308163219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199304226775805515538775479 298956340163708273308163219)
      ·
        refine ⟨448434510245562409962244829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298956340163708273308163219 448434510245562409962244829)
        ·
          refine ⟨168162941342085903735841811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448434510245562409962244829 168162941342085903735841811)
          ·
            refine ⟨252244412013128855603762717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168162941342085903735841811 252244412013128855603762717)
            ·
              refine ⟨94591654504923320851411019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252244412013128855603762717 94591654504923320851411019)
              ·
                refine ⟨141887481757384981277116529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94591654504923320851411019 141887481757384981277116529)
                ·
                  refine ⟨106415611318038735957837397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141887481757384981277116529 106415611318038735957837397)
                  ·
                    refine ⟨1247057945133266437005907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106415611318038735957837397 1247057945133266437005907)
                    ·
                      rfl

theorem cell22_3642955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_3642955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3642955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3642955 prefixEnd_3642955 := by exact prefixLift 3642955
  have htrace : WordTrace (prefixWord ++ tailWord_3642955) baseStart_3642955 baseEnd_3642955 := by
    simpa [prefixWord, tailWord_3642955, baseEnd_3642955] using wordTrace_append hprefix tailTrace_3642955
  have hstable : (prefixWord ++ tailWord_3642955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642955).length < 2 ^ (prefixWord ++ tailWord_3642955).sum := by decide
  have hdescent : baseEnd_3642955 < baseStart_3642955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643017 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_3643017 : Nat := 118140960795 + 3643017 * 2 ^ 59
def prefixEnd_3643017 : Nat := 4983230072969 + 3 ^ 40 * 3643017 * 2
def baseEnd_3643017 : Nat := 1247079169000318941955717

theorem tailTrace_3643017 : CollatzResearch.WordTrace tailWord_3643017 prefixEnd_3643017 1247079169000318941955717 := by
  unfold tailWord_3643017
  simp only [CollatzResearch.WordTrace]
  refine ⟨132871745842979061614607305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88581163895319374409738203 132871745842979061614607305)
  ·
    refine ⟨99653809382234296210955479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132871745842979061614607305 99653809382234296210955479)
    ·
      refine ⟨149480714073351444316433219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99653809382234296210955479 149480714073351444316433219)
      ·
        refine ⟨224221071110027166474649829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149480714073351444316433219 224221071110027166474649829)
        ·
          refine ⟨42041450833130093713996843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224221071110027166474649829 42041450833130093713996843)
          ·
            refine ⟨63062176249695140570995265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42041450833130093713996843 63062176249695140570995265)
            ·
              refine ⟨47296632187271355428246449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63062176249695140570995265 47296632187271355428246449)
              ·
                refine ⟨35472474140453516571184837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47296632187271355428246449 35472474140453516571184837)
                ·
                  refine ⟨6651088901335034357097157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35472474140453516571184837 6651088901335034357097157)
                  ·
                    refine ⟨1247079169000318941955717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6651088901335034357097157 1247079169000318941955717)
                    ·
                      rfl

theorem cell22_3643017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_3643017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643017 prefixEnd_3643017 := by exact prefixLift 3643017
  have htrace : WordTrace (prefixWord ++ tailWord_3643017) baseStart_3643017 baseEnd_3643017 := by
    simpa [prefixWord, tailWord_3643017, baseEnd_3643017] using wordTrace_append hprefix tailTrace_3643017
  have hstable : (prefixWord ++ tailWord_3643017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643017).length < 2 ^ (prefixWord ++ tailWord_3643017).sum := by decide
  have hdescent : baseEnd_3643017 < baseStart_3643017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643019 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 2, 3]
def baseStart_3643019 : Nat := 118140960795 + 3643019 * 2 ^ 59
def prefixEnd_3643019 : Nat := 4983230072969 + 3 ^ 40 * 3643019 * 2
def baseEnd_3643019 : Nat := 1247079853641191603405711

theorem tailTrace_3643019 : CollatzResearch.WordTrace tailWord_3643019 prefixEnd_3643019 1247079853641191603405711 := by
  unfold tailWord_3643019
  simp only [CollatzResearch.WordTrace]
  refine ⟨132871818788971815956180111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88581212525981210637453407 132871818788971815956180111)
  ·
    refine ⟨199307728183457723934270167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132871818788971815956180111 199307728183457723934270167)
    ·
      refine ⟨298961592275186585901405251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199307728183457723934270167 298961592275186585901405251)
      ·
        refine ⟨448442388412779878852107877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298961592275186585901405251 448442388412779878852107877)
        ·
          refine ⟨84082947827396227284770227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 448442388412779878852107877 84082947827396227284770227)
          ·
            refine ⟨126124421741094340927155341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84082947827396227284770227 126124421741094340927155341)
            ·
              refine ⟨47296658152910377847683253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126124421741094340927155341 47296658152910377847683253)
              ·
                refine ⟨4434061701835347923220305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47296658152910377847683253 4434061701835347923220305)
                ·
                  refine ⟨3325546276376510942415229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434061701835347923220305 3325546276376510942415229)
                  ·
                    refine ⟨1247079853641191603405711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325546276376510942415229 1247079853641191603405711)
                    ·
                      rfl

theorem cell22_3643019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 3].length) (baseStart_3643019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643019 prefixEnd_3643019 := by exact prefixLift 3643019
  have htrace : WordTrace (prefixWord ++ tailWord_3643019) baseStart_3643019 baseEnd_3643019 := by
    simpa [prefixWord, tailWord_3643019, baseEnd_3643019] using wordTrace_append hprefix tailTrace_3643019
  have hstable : (prefixWord ++ tailWord_3643019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643019).length < 2 ^ (prefixWord ++ tailWord_3643019).sum := by decide
  have hdescent : baseEnd_3643019 < baseStart_3643019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643038 : List Nat := [4, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_3643038 : Nat := 118140960795 + 3643038 * 2 ^ 59
def prefixEnd_3643038 : Nat := 4983230072969 + 3 ^ 40 * 3643038 * 2
def baseEnd_3643038 : Nat := 415695452576493962393551

theorem tailTrace_3643038 : CollatzResearch.WordTrace tailWord_3643038 prefixEnd_3643038 415695452576493962393551 := by
  unfold tailWord_3643038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16609063971987872775140221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88581674517268654800747845 16609063971987872775140221)
  ·
    refine ⟨6228398989495452290677583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16609063971987872775140221 6228398989495452290677583)
    ·
      refine ⟨9342598484243178436016375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228398989495452290677583 9342598484243178436016375)
      ·
        refine ⟨14013897726364767654024563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9342598484243178436016375 14013897726364767654024563)
        ·
          refine ⟨21020846589547151481036845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14013897726364767654024563 21020846589547151481036845)
          ·
            refine ⟨7882817471080181805388817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21020846589547151481036845 7882817471080181805388817)
            ·
              refine ⟨5912113103310136354041613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7882817471080181805388817 5912113103310136354041613)
              ·
                refine ⟨2217042413741301132765605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5912113103310136354041613 2217042413741301132765605)
                ·
                  refine ⟨415695452576493962393551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217042413741301132765605 415695452576493962393551)
                  ·
                    rfl

theorem cell22_3643038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_3643038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643038 prefixEnd_3643038 := by exact prefixLift 3643038
  have htrace : WordTrace (prefixWord ++ tailWord_3643038) baseStart_3643038 baseEnd_3643038 := by
    simpa [prefixWord, tailWord_3643038, baseEnd_3643038] using wordTrace_append hprefix tailTrace_3643038
  have hstable : (prefixWord ++ tailWord_3643038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643038).length < 2 ^ (prefixWord ++ tailWord_3643038).sum := by decide
  have hdescent : baseEnd_3643038 < baseStart_3643038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643098 : List Nat := [3, 1, 1, 2, 2, 3, 3, 3, 1, 3]
def baseStart_3643098 : Nat := 118140960795 + 3643098 * 2 ^ 59
def prefixEnd_3643098 : Nat := 4983230072969 + 3 ^ 40 * 3643098 * 2
def baseEnd_3643098 : Nat := 1247106896955661730680469

theorem tailTrace_3643098 : CollatzResearch.WordTrace tailWord_3643098 prefixEnd_3643098 1247106896955661730680469 := by
  unfold tailWord_3643098
  simp only [CollatzResearch.WordTrace]
  refine ⟨33218675038921403112076487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88583133437123741632203965 33218675038921403112076487)
  ·
    refine ⟨49828012558382104668114731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33218675038921403112076487 49828012558382104668114731)
    ·
      refine ⟨74742018837573157002172097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49828012558382104668114731 74742018837573157002172097)
      ·
        refine ⟨56056514128179867751629073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74742018837573157002172097 56056514128179867751629073)
        ·
          refine ⟨42042385596134900813721805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56056514128179867751629073 42042385596134900813721805)
          ·
            refine ⟨15765894598550587805145677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42042385596134900813721805 15765894598550587805145677)
            ·
              refine ⟨5912210474456470426929629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15765894598550587805145677 5912210474456470426929629)
              ·
                refine ⟨2217078927921176410098611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5912210474456470426929629 2217078927921176410098611)
                ·
                  refine ⟨3325618391881764615147917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217078927921176410098611 3325618391881764615147917)
                  ·
                    refine ⟨1247106896955661730680469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325618391881764615147917 1247106896955661730680469)
                    ·
                      rfl

theorem cell22_3643098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_3643098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643098 prefixEnd_3643098 := by exact prefixLift 3643098
  have htrace : WordTrace (prefixWord ++ tailWord_3643098) baseStart_3643098 baseEnd_3643098 := by
    simpa [prefixWord, tailWord_3643098, baseEnd_3643098] using wordTrace_append hprefix tailTrace_3643098
  have hstable : (prefixWord ++ tailWord_3643098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643098).length < 2 ^ (prefixWord ++ tailWord_3643098).sum := by decide
  have hdescent : baseEnd_3643098 < baseStart_3643098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643166 : List Nat := [4, 3, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3643166 : Nat := 118140960795 + 3643166 * 2 ^ 59
def prefixEnd_3643166 : Nat := 4983230072969 + 3 ^ 40 * 3643166 * 2
def baseEnd_3643166 : Nat := 1247130174745332219980261

theorem tailTrace_3643166 : CollatzResearch.WordTrace tailWord_3643166 prefixEnd_3643166 1247130174745332219980261 := by
  unfold tailWord_3643166
  simp only [CollatzResearch.WordTrace]
  refine ⟨16609647539929907507722669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88584786879626173374520901 16609647539929907507722669)
  ·
    refine ⟨6228617827473715315396001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16609647539929907507722669 6228617827473715315396001)
    ·
      refine ⟨4671463370605286486547001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6228617827473715315396001 4671463370605286486547001)
      ·
        refine ⟨3503597527953964864910251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4671463370605286486547001 3503597527953964864910251)
        ·
          refine ⟨5255396291930947297365377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3503597527953964864910251 5255396291930947297365377)
          ·
            refine ⟨3941547218948210473024033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5255396291930947297365377 3941547218948210473024033)
            ·
              refine ⟨2956160414211157854768025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941547218948210473024033 2956160414211157854768025)
              ·
                refine ⟨2217120310658368391076019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2956160414211157854768025 2217120310658368391076019)
                ·
                  refine ⟨3325680465987552586614029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217120310658368391076019 3325680465987552586614029)
                  ·
                    refine ⟨1247130174745332219980261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325680465987552586614029 1247130174745332219980261)
                    ·
                      rfl

theorem cell22_3643166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3643166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643166 prefixEnd_3643166 := by exact prefixLift 3643166
  have htrace : WordTrace (prefixWord ++ tailWord_3643166) baseStart_3643166 baseEnd_3643166 := by
    simpa [prefixWord, tailWord_3643166, baseEnd_3643166] using wordTrace_append hprefix tailTrace_3643166
  have hstable : (prefixWord ++ tailWord_3643166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643166).length < 2 ^ (prefixWord ++ tailWord_3643166).sum := by decide
  have hdescent : baseEnd_3643166 < baseStart_3643166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643171 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 2, 3]
def baseStart_3643171 : Nat := 118140960795 + 3643171 * 2 ^ 59
def prefixEnd_3643171 : Nat := 4983230072969 + 3 ^ 40 * 3643171 * 2
def baseEnd_3643171 : Nat := 1247131886347513873605245

theorem tailTrace_3643171 : CollatzResearch.WordTrace tailWord_3643171 prefixEnd_3643171 1247131886347513873605245 := by
  unfold tailWord_3643171
  simp only [CollatzResearch.WordTrace]
  refine ⟨132877362684421145915713367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88584908456280763943808911 132877362684421145915713367)
  ·
    refine ⟨199316044026631718873570051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132877362684421145915713367 199316044026631718873570051)
    ·
      refine ⟨298974066039947578310355077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199316044026631718873570051 298974066039947578310355077)
      ·
        refine ⟨56057637382490170933191577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298974066039947578310355077 56057637382490170933191577)
        ·
          refine ⟨42043228036867628199893683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56057637382490170933191577 42043228036867628199893683)
          ·
            refine ⟨63064842055301442299840525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42043228036867628199893683 63064842055301442299840525)
            ·
              refine ⟨23649315770738040862440197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63064842055301442299840525 23649315770738040862440197)
              ·
                refine ⟨4434246707013382661707537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23649315770738040862440197 4434246707013382661707537)
                ·
                  refine ⟨3325685030260036996280653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434246707013382661707537 3325685030260036996280653)
                  ·
                    refine ⟨1247131886347513873605245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325685030260036996280653 1247131886347513873605245)
                    ·
                      rfl

theorem cell22_3643171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 3].length) (baseStart_3643171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643171 prefixEnd_3643171 := by exact prefixLift 3643171
  have htrace : WordTrace (prefixWord ++ tailWord_3643171) baseStart_3643171 baseEnd_3643171 := by
    simpa [prefixWord, tailWord_3643171, baseEnd_3643171] using wordTrace_append hprefix tailTrace_3643171
  have hstable : (prefixWord ++ tailWord_3643171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643171).length < 2 ^ (prefixWord ++ tailWord_3643171).sum := by decide
  have hdescent : baseEnd_3643171 < baseStart_3643171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643173 : List Nat := [1, 3, 1, 2, 3, 2, 4, 2, 4]
def baseStart_3643173 : Nat := 118140960795 + 3643173 * 2 ^ 59
def prefixEnd_3643173 : Nat := 4983230072969 + 3 ^ 40 * 3643173 * 2
def baseEnd_3643173 : Nat := 415710856996128845018413

theorem tailTrace_3643173 : CollatzResearch.WordTrace tailWord_3643173 prefixEnd_3643173 415710856996128845018413 := by
  unfold tailWord_3643173
  simp only [CollatzResearch.WordTrace]
  refine ⟨132877435630413900257286173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88584957086942600171524115 132877435630413900257286173)
  ·
    refine ⟨49829038361405212596482315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132877435630413900257286173 49829038361405212596482315)
    ·
      refine ⟨74743557542107818894723473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49829038361405212596482315 74743557542107818894723473)
      ·
        refine ⟨56057668156580864171042605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74743557542107818894723473 56057668156580864171042605)
        ·
          refine ⟨21021625558717824064140977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56057668156580864171042605 21021625558717824064140977)
          ·
            refine ⟨15766219169038368048105733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21021625558717824064140977 15766219169038368048105733)
            ·
              refine ⟨2956166094194694009019825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15766219169038368048105733 2956166094194694009019825)
              ·
                refine ⟨2217124570646020506764869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2956166094194694009019825 2217124570646020506764869)
                ·
                  refine ⟨415710856996128845018413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217124570646020506764869 415710856996128845018413)
                  ·
                    rfl

theorem cell22_3643173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_3643173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643173 prefixEnd_3643173 := by exact prefixLift 3643173
  have htrace : WordTrace (prefixWord ++ tailWord_3643173) baseStart_3643173 baseEnd_3643173 := by
    simpa [prefixWord, tailWord_3643173, baseEnd_3643173] using wordTrace_append hprefix tailTrace_3643173
  have hstable : (prefixWord ++ tailWord_3643173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643173).length < 2 ^ (prefixWord ++ tailWord_3643173).sum := by decide
  have hdescent : baseEnd_3643173 < baseStart_3643173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643188 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3643188 : Nat := 118140960795 + 3643188 * 2 ^ 59
def prefixEnd_3643188 : Nat := 4983230072969 + 3 ^ 40 * 3643188 * 2
def baseEnd_3643188 : Nat := 1247137705794931495930193

theorem tailTrace_3643188 : CollatzResearch.WordTrace tailWord_3643188 prefixEnd_3643188 1247137705794931495930193 := by
  unfold tailWord_3643188
  simp only [CollatzResearch.WordTrace]
  refine ⟨66438991362679778909541109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88585321816906371879388145 66438991362679778909541109)
  ·
    refine ⟨6228655440251229272769479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66438991362679778909541109 6228655440251229272769479)
    ·
      refine ⟨9342983160376843909154219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228655440251229272769479 9342983160376843909154219)
      ·
        refine ⟨14014474740565265863731329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9342983160376843909154219 14014474740565265863731329)
        ·
          refine ⟨10510856055423949397798497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14014474740565265863731329 10510856055423949397798497)
          ·
            refine ⟨7883142041567962048348873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10510856055423949397798497 7883142041567962048348873)
            ·
              refine ⟨5912356531175971536261655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7883142041567962048348873 5912356531175971536261655)
              ·
                refine ⟨8868534796763957304392483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5912356531175971536261655 8868534796763957304392483)
                ·
                  refine ⟨13302802195145935956588725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8868534796763957304392483 13302802195145935956588725)
                  ·
                    refine ⟨1247137705794931495930193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13302802195145935956588725 1247137705794931495930193)
                    ·
                      rfl

theorem cell22_3643188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3643188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643188 prefixEnd_3643188 := by exact prefixLift 3643188
  have htrace : WordTrace (prefixWord ++ tailWord_3643188) baseStart_3643188 baseEnd_3643188 := by
    simpa [prefixWord, tailWord_3643188, baseEnd_3643188] using wordTrace_append hprefix tailTrace_3643188
  have hstable : (prefixWord ++ tailWord_3643188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643188).length < 2 ^ (prefixWord ++ tailWord_3643188).sum := by decide
  have hdescent : baseEnd_3643188 < baseStart_3643188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643233 : List Nat := [1, 2, 3, 1, 1, 1, 3, 6, 1, 3]
def baseStart_3643233 : Nat := 118140960795 + 3643233 * 2 ^ 59
def prefixEnd_3643233 : Nat := 4983230072969 + 3 ^ 40 * 3643233 * 2
def baseEnd_3643233 : Nat := 1247153110214566378555055

theorem tailTrace_3643233 : CollatzResearch.WordTrace tailWord_3643233 prefixEnd_3643233 1247153110214566378555055 := by
  unfold tailWord_3643233
  simp only [CollatzResearch.WordTrace]
  refine ⟨132879624010196530504470353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88586416006797687002980235 132879624010196530504470353)
  ·
    refine ⟨99659718007647397878352765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132879624010196530504470353 99659718007647397878352765)
    ·
      refine ⟨37372394252867774204382287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99659718007647397878352765 37372394252867774204382287)
      ·
        refine ⟨56058591379301661306573431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37372394252867774204382287 56058591379301661306573431)
        ·
          refine ⟨84087887068952491959860147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56058591379301661306573431 84087887068952491959860147)
          ·
            refine ⟨126131830603428737939790221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84087887068952491959860147 126131830603428737939790221)
            ·
              refine ⟨47299436476285776727421333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126131830603428737939790221 47299436476285776727421333)
              ·
                refine ⟨2217161084825895784097875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47299436476285776727421333 2217161084825895784097875)
                ·
                  refine ⟨3325741627238843676146813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217161084825895784097875 3325741627238843676146813)
                  ·
                    refine ⟨1247153110214566378555055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325741627238843676146813 1247153110214566378555055)
                    ·
                      rfl

theorem cell22_3643233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_3643233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643233 prefixEnd_3643233 := by exact prefixLift 3643233
  have htrace : WordTrace (prefixWord ++ tailWord_3643233) baseStart_3643233 baseEnd_3643233 := by
    simpa [prefixWord, tailWord_3643233, baseEnd_3643233] using wordTrace_append hprefix tailTrace_3643233
  have hstable : (prefixWord ++ tailWord_3643233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643233).length < 2 ^ (prefixWord ++ tailWord_3643233).sum := by decide
  have hdescent : baseEnd_3643233 < baseStart_3643233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643297 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 5]
def baseStart_3643297 : Nat := 118140960795 + 3643297 * 2 ^ 59
def prefixEnd_3643297 : Nat := 4983230072969 + 3 ^ 40 * 3643297 * 2
def baseEnd_3643297 : Nat := 415725006240830514984953

theorem tailTrace_3643297 : CollatzResearch.WordTrace tailWord_3643297 prefixEnd_3643297 415725006240830514984953 := by
  unfold tailWord_3643297
  simp only [CollatzResearch.WordTrace]
  refine ⟨132881958281964669434800145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88587972187976446289866763 132881958281964669434800145)
  ·
    refine ⟨99661468711473502076100109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132881958281964669434800145 99661468711473502076100109)
    ·
      refine ⟨37373050766802563278537541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99661468711473502076100109 37373050766802563278537541)
      ·
        refine ⟨7007447018775480614725789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37373050766802563278537541 7007447018775480614725789)
        ·
          refine ⟨2627792632040805230522171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7007447018775480614725789 2627792632040805230522171)
          ·
            refine ⟨3941688948061207845783257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627792632040805230522171 3941688948061207845783257)
            ·
              refine ⟨2956266711045905884337443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941688948061207845783257 2956266711045905884337443)
              ·
                refine ⟨4434400066568858826506165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956266711045905884337443 4434400066568858826506165)
                ·
                  refine ⟨415725006240830514984953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4434400066568858826506165 415725006240830514984953)
                  ·
                    rfl

theorem cell22_3643297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 5].length) (baseStart_3643297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643297 prefixEnd_3643297 := by exact prefixLift 3643297
  have htrace : WordTrace (prefixWord ++ tailWord_3643297) baseStart_3643297 baseEnd_3643297 := by
    simpa [prefixWord, tailWord_3643297, baseEnd_3643297] using wordTrace_append hprefix tailTrace_3643297
  have hstable : (prefixWord ++ tailWord_3643297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643297).length < 2 ^ (prefixWord ++ tailWord_3643297).sum := by decide
  have hdescent : baseEnd_3643297 < baseStart_3643297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643340 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_3643340 : Nat := 118140960795 + 3643340 * 2 ^ 59
def prefixEnd_3643340 : Nat := 4983230072969 + 3 ^ 40 * 3643340 * 2
def baseEnd_3643340 : Nat := 1247189738501253766129727

theorem tailTrace_3643340 : CollatzResearch.WordTrace tailWord_3643340 prefixEnd_3643340 1247189738501253766129727 := by
  unfold tailWord_3643340
  simp only [CollatzResearch.WordTrace]
  refine ⟨66441763310404443889307737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88589017747205925185743649 66441763310404443889307737)
  ·
    refine ⟨49831322482803332916980803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66441763310404443889307737 49831322482803332916980803)
    ·
      refine ⟨74746983724204999375471205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49831322482803332916980803 74746983724204999375471205)
      ·
        refine ⟨14015059448288437382900851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74746983724204999375471205 14015059448288437382900851)
        ·
          refine ⟨21022589172432656074351277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14015059448288437382900851 21022589172432656074351277)
          ·
            refine ⟨7883470939662246027881729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21022589172432656074351277 7883470939662246027881729)
            ·
              refine ⟨5912603204746684520911297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7883470939662246027881729 5912603204746684520911297)
              ·
                refine ⟨4434452403560013390683473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912603204746684520911297 4434452403560013390683473)
                ·
                  refine ⟨3325839302670010043012605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434452403560013390683473 3325839302670010043012605)
                  ·
                    refine ⟨1247189738501253766129727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325839302670010043012605 1247189738501253766129727)
                    ·
                      rfl

theorem cell22_3643340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_3643340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643340 prefixEnd_3643340 := by exact prefixLift 3643340
  have htrace : WordTrace (prefixWord ++ tailWord_3643340) baseStart_3643340 baseEnd_3643340 := by
    simpa [prefixWord, tailWord_3643340, baseEnd_3643340] using wordTrace_append hprefix tailTrace_3643340
  have hstable : (prefixWord ++ tailWord_3643340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643340).length < 2 ^ (prefixWord ++ tailWord_3643340).sum := by decide
  have hdescent : baseEnd_3643340 < baseStart_3643340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643353 : List Nat := [1, 2, 1, 2, 6, 2, 1, 7]
def baseStart_3643353 : Nat := 118140960795 + 3643353 * 2 ^ 59
def prefixEnd_3643353 : Nat := 4983230072969 + 3 ^ 40 * 3643353 * 2
def baseEnd_3643353 : Nat := 138577132074102896172743

theorem tailTrace_3643353 : CollatzResearch.WordTrace tailWord_3643353 prefixEnd_3643353 138577132074102896172743 := by
  unfold tailWord_3643353
  simp only [CollatzResearch.WordTrace]
  refine ⟨132884000769761790998838713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88589333846507860665892475 132884000769761790998838713)
  ·
    refine ⟨99663000577321343249129035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132884000769761790998838713 99663000577321343249129035)
    ·
      refine ⟨149494500865982014873693553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99663000577321343249129035 149494500865982014873693553)
      ·
        refine ⟨112120875649486511155270165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149494500865982014873693553 112120875649486511155270165)
        ·
          refine ⟨5255666046069680210403289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112120875649486511155270165 5255666046069680210403289)
          ·
            refine ⟨3941749534552260157802467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5255666046069680210403289 3941749534552260157802467)
            ·
              refine ⟨5912624301828390236703701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941749534552260157802467 5912624301828390236703701)
              ·
                refine ⟨138577132074102896172743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5912624301828390236703701 138577132074102896172743)
                ·
                  rfl

theorem cell22_3643353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 7].length) (baseStart_3643353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643353 prefixEnd_3643353 := by exact prefixLift 3643353
  have htrace : WordTrace (prefixWord ++ tailWord_3643353) baseStart_3643353 baseEnd_3643353 := by
    simpa [prefixWord, tailWord_3643353, baseEnd_3643353] using wordTrace_append hprefix tailTrace_3643353
  have hstable : (prefixWord ++ tailWord_3643353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643353).length < 2 ^ (prefixWord ++ tailWord_3643353).sum := by decide
  have hdescent : baseEnd_3643353 < baseStart_3643353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643385 : List Nat := [1, 2, 1, 3, 1, 4, 1, 5, 1, 3]
def baseStart_3643385 : Nat := 118140960795 + 3643385 * 2 ^ 59
def prefixEnd_3643385 : Nat := 4983230072969 + 3 ^ 40 * 3643385 * 2
def baseEnd_3643385 : Nat := 1247205142920888648754589

theorem tailTrace_3643385 : CollatzResearch.WordTrace tailWord_3643385 prefixEnd_3643385 1247205142920888648754589 := by
  unfold tailWord_3643385
  simp only [CollatzResearch.WordTrace]
  refine ⟨132885167905645860464003609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88590111937097240309335739 132885167905645860464003609)
  ·
    refine ⟨99663875929234395348002707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132885167905645860464003609 99663875929234395348002707)
    ·
      refine ⟨149495813893851593022004061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99663875929234395348002707 149495813893851593022004061)
      ·
        refine ⟨56060930210194347383251523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149495813893851593022004061 56060930210194347383251523)
        ·
          refine ⟨84091395315291521074877285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56060930210194347383251523 84091395315291521074877285)
          ·
            refine ⟨15767136621617160201539491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84091395315291521074877285 15767136621617160201539491)
            ·
              refine ⟨23650704932425740302309237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15767136621617160201539491 23650704932425740302309237)
              ·
                refine ⟨2217253587414913153341491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23650704932425740302309237 2217253587414913153341491)
                ·
                  refine ⟨3325880381122369730012237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217253587414913153341491 3325880381122369730012237)
                  ·
                    refine ⟨1247205142920888648754589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3325880381122369730012237 1247205142920888648754589)
                    ·
                      rfl

theorem cell22_3643385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 3].length) (baseStart_3643385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643385 prefixEnd_3643385 := by exact prefixLift 3643385
  have htrace : WordTrace (prefixWord ++ tailWord_3643385) baseStart_3643385 baseEnd_3643385 := by
    simpa [prefixWord, tailWord_3643385, baseEnd_3643385] using wordTrace_append hprefix tailTrace_3643385
  have hstable : (prefixWord ++ tailWord_3643385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643385).length < 2 ^ (prefixWord ++ tailWord_3643385).sum := by decide
  have hdescent : baseEnd_3643385 < baseStart_3643385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643411 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 5, 4]
def baseStart_3643411 : Nat := 118140960795 + 3643411 * 2 ^ 59
def prefixEnd_3643411 : Nat := 4983230072969 + 3 ^ 40 * 3643411 * 2
def baseEnd_3643411 : Nat := 1247214043252233247604509

theorem tailTrace_3643411 : CollatzResearch.WordTrace tailWord_3643411 prefixEnd_3643411 1247214043252233247604509 := by
  unfold tailWord_3643411
  simp only [CollatzResearch.WordTrace]
  refine ⟨132886116203551666904450087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88590744135701111269633391 132886116203551666904450087)
  ·
    refine ⟨199329174305327500356675131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132886116203551666904450087 199329174305327500356675131)
    ·
      refine ⟨298993761457991250535012697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199329174305327500356675131 298993761457991250535012697)
      ·
        refine ⟨224245321093493437901259523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298993761457991250535012697 224245321093493437901259523)
        ·
          refine ⟨336367981640240156851889285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224245321093493437901259523 336367981640240156851889285)
          ·
            refine ⟨63068996557545029409729241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336367981640240156851889285 63068996557545029409729241)
            ·
              refine ⟨47301747418158772057296931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63068996557545029409729241 47301747418158772057296931)
              ·
                refine ⟨70952621127238158085945397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47301747418158772057296931 70952621127238158085945397)
                ·
                  refine ⟨6651808230678577320557381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70952621127238158085945397 6651808230678577320557381)
                  ·
                    refine ⟨1247214043252233247604509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6651808230678577320557381 1247214043252233247604509)
                    ·
                      rfl

theorem cell22_3643411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 4].length) (baseStart_3643411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643411 prefixEnd_3643411 := by exact prefixLift 3643411
  have htrace : WordTrace (prefixWord ++ tailWord_3643411) baseStart_3643411 baseEnd_3643411 := by
    simpa [prefixWord, tailWord_3643411, baseEnd_3643411] using wordTrace_append hprefix tailTrace_3643411
  have hstable : (prefixWord ++ tailWord_3643411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643411).length < 2 ^ (prefixWord ++ tailWord_3643411).sum := by decide
  have hdescent : baseEnd_3643411 < baseStart_3643411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643548 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3643548 : Nat := 118140960795 + 3643548 * 2 ^ 59
def prefixEnd_3643548 : Nat := 4983230072969 + 3 ^ 40 * 3643548 * 2
def baseEnd_3643548 : Nat := 1247260941152010556929089

theorem tailTrace_3643548 : CollatzResearch.WordTrace tailWord_3643548 prefixEnd_3643548 1247260941152010556929089 := by
  unfold tailWord_3643548
  simp only [CollatzResearch.WordTrace]
  refine ⟨66445556502027669651093649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88594075336036892868124865 66445556502027669651093649)
  ·
    refine ⟨49834167376520752238320237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66445556502027669651093649 49834167376520752238320237)
    ·
      refine ⟨18687812766195282089370089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49834167376520752238320237 18687812766195282089370089)
      ·
        refine ⟨14015859574646461567027567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18687812766195282089370089 14015859574646461567027567)
        ·
          refine ⟨21023789361969692350541351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14015859574646461567027567 21023789361969692350541351)
          ·
            refine ⟨31535684042954538525812027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21023789361969692350541351 31535684042954538525812027)
            ·
              refine ⟨47303526064431807788718041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31535684042954538525812027 47303526064431807788718041)
              ·
                refine ⟨35477644548323855841538531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47303526064431807788718041 35477644548323855841538531)
                ·
                  refine ⟨53216466822485783762307797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35477644548323855841538531 53216466822485783762307797)
                  ·
                    refine ⟨1247260941152010556929089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53216466822485783762307797 1247260941152010556929089)
                    ·
                      rfl

theorem cell22_3643548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3643548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643548 prefixEnd_3643548 := by exact prefixLift 3643548
  have htrace : WordTrace (prefixWord ++ tailWord_3643548) baseStart_3643548 baseEnd_3643548 := by
    simpa [prefixWord, tailWord_3643548, baseEnd_3643548] using wordTrace_append hprefix tailTrace_3643548
  have hstable : (prefixWord ++ tailWord_3643548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643548).length < 2 ^ (prefixWord ++ tailWord_3643548).sum := by decide
  have hdescent : baseEnd_3643548 < baseStart_3643548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643554 : List Nat := [3, 3, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_3643554 : Nat := 118140960795 + 3643554 * 2 ^ 59
def prefixEnd_3643554 : Nat := 4983230072969 + 3 ^ 40 * 3643554 * 2
def baseEnd_3643554 : Nat := 1247262995074628541279071

theorem tailTrace_3643554 : CollatzResearch.WordTrace tailWord_3643554 prefixEnd_3643554 1247262995074628541279071 := by
  unfold tailWord_3643554
  simp only [CollatzResearch.WordTrace]
  refine ⟨33222832960508400581726429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88594221228022401551270477 33222832960508400581726429)
  ·
    refine ⟨12458562360190650218147411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33222832960508400581726429 12458562360190650218147411)
    ·
      refine ⟨18687843540285975327221117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12458562360190650218147411 18687843540285975327221117)
      ·
        refine ⟨7007941327607240747707919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18687843540285975327221117 7007941327607240747707919)
        ·
          refine ⟨10511911991410861121561879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7007941327607240747707919 10511911991410861121561879)
          ·
            refine ⟨15767867987116291682342819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10511911991410861121561879 15767867987116291682342819)
            ·
              refine ⟨23651801980674437523514229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15767867987116291682342819 23651801980674437523514229)
              ·
                refine ⟨2217356435688228517829459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23651801980674437523514229 2217356435688228517829459)
                ·
                  refine ⟨3326034653532342776744189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217356435688228517829459 3326034653532342776744189)
                  ·
                    refine ⟨1247262995074628541279071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326034653532342776744189 1247262995074628541279071)
                    ·
                      rfl

theorem cell22_3643554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_3643554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643554 prefixEnd_3643554 := by exact prefixLift 3643554
  have htrace : WordTrace (prefixWord ++ tailWord_3643554) baseStart_3643554 baseEnd_3643554 := by
    simpa [prefixWord, tailWord_3643554, baseEnd_3643554] using wordTrace_append hprefix tailTrace_3643554
  have hstable : (prefixWord ++ tailWord_3643554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643554).length < 2 ^ (prefixWord ++ tailWord_3643554).sum := by decide
  have hdescent : baseEnd_3643554 < baseStart_3643554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643565 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3643565 : Nat := 118140960795 + 3643565 * 2 ^ 59
def prefixEnd_3643565 : Nat := 4983230072969 + 3 ^ 40 * 3643565 * 2
def baseEnd_3643565 : Nat := 1247266760599428179254037

theorem tailTrace_3643565 : CollatzResearch.WordTrace tailWord_3643565 prefixEnd_3643565 1247266760599428179254037 := by
  unfold tailWord_3643565
  simp only [CollatzResearch.WordTrace]
  refine ⟨132891733044993751205556149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88594488696662500803704099 132891733044993751205556149)
  ·
    refine ⟨12458599972968164175520889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132891733044993751205556149 12458599972968164175520889)
    ·
      refine ⟨9343949979726123131640667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12458599972968164175520889 9343949979726123131640667)
      ·
        refine ⟨14015924969589184697461001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9343949979726123131640667 14015924969589184697461001)
        ·
          refine ⟨10511943727191888523095751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14015924969589184697461001 10511943727191888523095751)
          ·
            refine ⟨15767915590787832784643627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10511943727191888523095751 15767915590787832784643627)
            ·
              refine ⟨23651873386181749176965441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15767915590787832784643627 23651873386181749176965441)
              ·
                refine ⟨17738905039636311882724081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23651873386181749176965441 17738905039636311882724081)
                ·
                  refine ⟨13304178779727233912043061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17738905039636311882724081 13304178779727233912043061)
                  ·
                    refine ⟨1247266760599428179254037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13304178779727233912043061 1247266760599428179254037)
                    ·
                      rfl

theorem cell22_3643565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3643565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643565 prefixEnd_3643565 := by exact prefixLift 3643565
  have htrace : WordTrace (prefixWord ++ tailWord_3643565) baseStart_3643565 baseEnd_3643565 := by
    simpa [prefixWord, tailWord_3643565, baseEnd_3643565] using wordTrace_append hprefix tailTrace_3643565
  have hstable : (prefixWord ++ tailWord_3643565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643565).length < 2 ^ (prefixWord ++ tailWord_3643565).sum := by decide
  have hdescent : baseEnd_3643565 < baseStart_3643565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643578 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_3643578 : Nat := 118140960795 + 3643578 * 2 ^ 59
def prefixEnd_3643578 : Nat := 4983230072969 + 3 ^ 40 * 3643578 * 2
def baseEnd_3643578 : Nat := 415757070255033492892999

theorem tailTrace_3643578 : CollatzResearch.WordTrace tailWord_3643578 prefixEnd_3643578 415757070255033492892999 := by
  unfold tailWord_3643578
  simp only [CollatzResearch.WordTrace]
  refine ⟨33223051798486663606444847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88594804795964436283852925 33223051798486663606444847)
  ·
    refine ⟨49834577697729995409667271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33223051798486663606444847 49834577697729995409667271)
    ·
      refine ⟨74751866546594993114500907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49834577697729995409667271 74751866546594993114500907)
      ·
        refine ⟨112127799819892489671751361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74751866546594993114500907 112127799819892489671751361)
        ·
          refine ⟨84095849864919367253813521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112127799819892489671751361 84095849864919367253813521)
          ·
            refine ⟨63071887398689525440360141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84095849864919367253813521 63071887398689525440360141)
            ·
              refine ⟨23651957774508572040135053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63071887398689525440360141 23651957774508572040135053)
              ·
                refine ⟨8869484165440714515050645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23651957774508572040135053 8869484165440714515050645)
                ·
                  refine ⟨415757070255033492892999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8869484165440714515050645 415757070255033492892999)
                  ·
                    rfl

theorem cell22_3643578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_3643578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643578 prefixEnd_3643578 := by exact prefixLift 3643578
  have htrace : WordTrace (prefixWord ++ tailWord_3643578) baseStart_3643578 baseEnd_3643578 := by
    simpa [prefixWord, tailWord_3643578, baseEnd_3643578] using wordTrace_append hprefix tailTrace_3643578
  have hstable : (prefixWord ++ tailWord_3643578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643578).length < 2 ^ (prefixWord ++ tailWord_3643578).sum := by decide
  have hdescent : baseEnd_3643578 < baseStart_3643578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643593 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_3643593 : Nat := 118140960795 + 3643593 * 2 ^ 59
def prefixEnd_3643593 : Nat := 4983230072969 + 3 ^ 40 * 3643593 * 2
def baseEnd_3643593 : Nat := 1247276345571645439553951

theorem tailTrace_3643593 : CollatzResearch.WordTrace tailWord_3643593 prefixEnd_3643593 1247276345571645439553951 := by
  unfold tailWord_3643593
  simp only [CollatzResearch.WordTrace]
  refine ⟨132892754288892311987575433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88595169525928207991716955 132892754288892311987575433)
  ·
    refine ⟨99669565716669233990681575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132892754288892311987575433 99669565716669233990681575)
    ·
      refine ⟨149504348575003850986022363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99669565716669233990681575 149504348575003850986022363)
      ·
        refine ⟨224256522862505776479033545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149504348575003850986022363 224256522862505776479033545)
        ·
          refine ⟨168192392146879332359275159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224256522862505776479033545 168192392146879332359275159)
          ·
            refine ⟨252288588220318998538912739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168192392146879332359275159 252288588220318998538912739)
            ·
              refine ⟨378432882330478497808369109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252288588220318998538912739 378432882330478497808369109)
              ·
                refine ⟨8869520679620589792383651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 378432882330478497808369109 8869520679620589792383651)
                ·
                  refine ⟨13304281019430884688575477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8869520679620589792383651 13304281019430884688575477)
                  ·
                    refine ⟨1247276345571645439553951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13304281019430884688575477 1247276345571645439553951)
                    ·
                      rfl

theorem cell22_3643593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_3643593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643593 prefixEnd_3643593 := by exact prefixLift 3643593
  have htrace : WordTrace (prefixWord ++ tailWord_3643593) baseStart_3643593 baseEnd_3643593 := by
    simpa [prefixWord, tailWord_3643593, baseEnd_3643593] using wordTrace_append hprefix tailTrace_3643593
  have hstable : (prefixWord ++ tailWord_3643593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643593).length < 2 ^ (prefixWord ++ tailWord_3643593).sum := by decide
  have hdescent : baseEnd_3643593 < baseStart_3643593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643610 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_3643610 : Nat := 118140960795 + 3643610 * 2 ^ 59
def prefixEnd_3643610 : Nat := 4983230072969 + 3 ^ 40 * 3643610 * 2
def baseEnd_3643610 : Nat := 1247282165019063061878899

theorem tailTrace_3643610 : CollatzResearch.WordTrace tailWord_3643610 prefixEnd_3643610 1247282165019063061878899 := by
  unfold tailWord_3643610
  simp only [CollatzResearch.WordTrace]
  refine ⟨33223343582457680972736071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88595582886553815927296189 33223343582457680972736071)
  ·
    refine ⟨49835015373686521459104107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33223343582457680972736071 49835015373686521459104107)
    ·
      refine ⟨74752523060529782188656161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49835015373686521459104107 74752523060529782188656161)
      ·
        refine ⟨56064392295397336641492121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74752523060529782188656161 56064392295397336641492121)
        ·
          refine ⟨42048294221548002481119091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56064392295397336641492121 42048294221548002481119091)
          ·
            refine ⟨63072441332322003721678637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42048294221548002481119091 63072441332322003721678637)
            ·
              refine ⟨23652165499620751395629489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63072441332322003721678637 23652165499620751395629489)
              ·
                refine ⟨17739124124715563546722117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23652165499620751395629489 17739124124715563546722117)
                ·
                  refine ⟨3326085773384168165010397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17739124124715563546722117 3326085773384168165010397)
                  ·
                    refine ⟨1247282165019063061878899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326085773384168165010397 1247282165019063061878899)
                    ·
                      rfl

theorem cell22_3643610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_3643610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643610 prefixEnd_3643610 := by exact prefixLift 3643610
  have htrace : WordTrace (prefixWord ++ tailWord_3643610) baseStart_3643610 baseEnd_3643610 := by
    simpa [prefixWord, tailWord_3643610, baseEnd_3643610] using wordTrace_append hprefix tailTrace_3643610
  have hstable : (prefixWord ++ tailWord_3643610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643610).length < 2 ^ (prefixWord ++ tailWord_3643610).sum := by decide
  have hdescent : baseEnd_3643610 < baseStart_3643610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643629 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3643629 : Nat := 118140960795 + 3643629 * 2 ^ 59
def prefixEnd_3643629 : Nat := 4983230072969 + 3 ^ 40 * 3643629 * 2
def baseEnd_3643629 : Nat := 415762889702451115217947

theorem tailTrace_3643629 : CollatzResearch.WordTrace tailWord_3643629 prefixEnd_3643629 415762889702451115217947 := by
  unfold tailWord_3643629
  simp only [CollatzResearch.WordTrace]
  refine ⟨132894067316761890135885941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88596044877841260090590627 132894067316761890135885941)
  ·
    refine ⟨12458818810946427200239307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132894067316761890135885941 12458818810946427200239307)
    ·
      refine ⟨18688228216419640800358961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12458818810946427200239307 18688228216419640800358961)
      ·
        refine ⟨14016171162314730600269221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18688228216419640800358961 14016171162314730600269221)
        ·
          refine ⟨2628032092934011987550479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14016171162314730600269221 2628032092934011987550479)
          ·
            refine ⟨3942048139401017981325719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628032092934011987550479 3942048139401017981325719)
            ·
              refine ⟨5913072209101526971988579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942048139401017981325719 5913072209101526971988579)
              ·
                refine ⟨8869608313652290457982869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5913072209101526971988579 8869608313652290457982869)
                ·
                  refine ⟨415762889702451115217947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8869608313652290457982869 415762889702451115217947)
                  ·
                    rfl

theorem cell22_3643629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3643629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643629 prefixEnd_3643629 := by exact prefixLift 3643629
  have htrace : WordTrace (prefixWord ++ tailWord_3643629) baseStart_3643629 baseEnd_3643629 := by
    simpa [prefixWord, tailWord_3643629, baseEnd_3643629] using wordTrace_append hprefix tailTrace_3643629
  have hstable : (prefixWord ++ tailWord_3643629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643629).length < 2 ^ (prefixWord ++ tailWord_3643629).sum := by decide
  have hdescent : baseEnd_3643629 < baseStart_3643629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643644 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 2, 3]
def baseStart_3643644 : Nat := 118140960795 + 3643644 * 2 ^ 59
def prefixEnd_3643644 : Nat := 4983230072969 + 3 ^ 40 * 3643644 * 2
def baseEnd_3643644 : Nat := 1247293803913898306528795

theorem tailTrace_3643644 : CollatzResearch.WordTrace tailWord_3643644 prefixEnd_3643644 1247293803913898306528795 := by
  unfold tailWord_3643644
  simp only [CollatzResearch.WordTrace]
  refine ⟨66447307205853773848840993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88596409607805031798454657 66447307205853773848840993)
  ·
    refine ⟨49835480404390330386630745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66447307205853773848840993 49835480404390330386630745)
    ·
      refine ⟨37376610303292747789973059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49835480404390330386630745 37376610303292747789973059)
      ·
        refine ⟨56064915454939121684959589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37376610303292747789973059 56064915454939121684959589)
        ·
          refine ⟨10512171647801085315929923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56064915454939121684959589 10512171647801085315929923)
          ·
            refine ⟨15768257471701627973894885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512171647801085315929923 15768257471701627973894885)
            ·
              refine ⟨2956548275944055245105291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15768257471701627973894885 2956548275944055245105291)
              ·
                refine ⟨4434822413916082867657937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956548275944055245105291 4434822413916082867657937)
                ·
                  refine ⟨3326116810437062150743453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434822413916082867657937 3326116810437062150743453)
                  ·
                    refine ⟨1247293803913898306528795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326116810437062150743453 1247293803913898306528795)
                    ·
                      rfl

theorem cell22_3643644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_3643644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643644 prefixEnd_3643644 := by exact prefixLift 3643644
  have htrace : WordTrace (prefixWord ++ tailWord_3643644) baseStart_3643644 baseEnd_3643644 := by
    simpa [prefixWord, tailWord_3643644, baseEnd_3643644] using wordTrace_append hprefix tailTrace_3643644
  have hstable : (prefixWord ++ tailWord_3643644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643644).length < 2 ^ (prefixWord ++ tailWord_3643644).sum := by decide
  have hdescent : baseEnd_3643644 < baseStart_3643644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643653 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_3643653 : Nat := 118140960795 + 3643653 * 2 ^ 59
def prefixEnd_3643653 : Nat := 4983230072969 + 3 ^ 40 * 3643653 * 2
def baseEnd_3643653 : Nat := 1247296884797825283053767

theorem tailTrace_3643653 : CollatzResearch.WordTrace tailWord_3643653 prefixEnd_3643653 1247296884797825283053767 := by
  unfold tailWord_3643653
  simp only [CollatzResearch.WordTrace]
  refine ⟨132894942668674942234759613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88596628445783294823173075 132894942668674942234759613)
  ·
    refine ⟨49835603500753103338034855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132894942668674942234759613 49835603500753103338034855)
    ·
      refine ⟨74753405251129655007052283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49835603500753103338034855 74753405251129655007052283)
      ·
        refine ⟨112130107876694482510578425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74753405251129655007052283 112130107876694482510578425)
        ·
          refine ⟨84097580907520861882933819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112130107876694482510578425 84097580907520861882933819)
          ·
            refine ⟨126146371361281292824400729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84097580907520861882933819 126146371361281292824400729)
            ·
              refine ⟨94609778520960969618300547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126146371361281292824400729 94609778520960969618300547)
              ·
                refine ⟨141914667781441454427450821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94609778520960969618300547 141914667781441454427450821)
                ·
                  refine ⟨26609000209020272705147029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141914667781441454427450821 26609000209020272705147029)
                  ·
                    refine ⟨1247296884797825283053767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26609000209020272705147029 1247296884797825283053767)
                    ·
                      rfl

theorem cell22_3643653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_3643653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643653 prefixEnd_3643653 := by exact prefixLift 3643653
  have htrace : WordTrace (prefixWord ++ tailWord_3643653) baseStart_3643653 baseEnd_3643653 := by
    simpa [prefixWord, tailWord_3643653, baseEnd_3643653] using wordTrace_append hprefix tailTrace_3643653
  have hstable : (prefixWord ++ tailWord_3643653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643653).length < 2 ^ (prefixWord ++ tailWord_3643653).sum := by decide
  have hdescent : baseEnd_3643653 < baseStart_3643653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643715 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 3, 4]
def baseStart_3643715 : Nat := 118140960795 + 3643715 * 2 ^ 59
def prefixEnd_3643715 : Nat := 4983230072969 + 3 ^ 40 * 3643715 * 2
def baseEnd_3643715 : Nat := 1247318108664877788003577

theorem tailTrace_3643715 : CollatzResearch.WordTrace tailWord_3643715 prefixEnd_3643715 1247318108664877788003577 := by
  unfold tailWord_3643715
  simp only [CollatzResearch.WordTrace]
  refine ⟨132897203994450326823516599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88598135996300217882344399 132897203994450326823516599)
  ·
    refine ⟨199345805991675490235274899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132897203994450326823516599 199345805991675490235274899)
    ·
      refine ⟨299018708987513235352912349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199345805991675490235274899 299018708987513235352912349)
      ·
        refine ⟨112132015870317463257342131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299018708987513235352912349 112132015870317463257342131)
        ·
          refine ⟨168198023805476194886013197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112132015870317463257342131 168198023805476194886013197)
          ·
            refine ⟨63074258927053573082254949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168198023805476194886013197 63074258927053573082254949)
            ·
              refine ⟨11826423548822544952922803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63074258927053573082254949 11826423548822544952922803)
              ·
                refine ⟨17739635323233817429384205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11826423548822544952922803 17739635323233817429384205)
                ·
                  refine ⟨6652363246212681536019077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17739635323233817429384205 6652363246212681536019077)
                  ·
                    refine ⟨1247318108664877788003577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6652363246212681536019077 1247318108664877788003577)
                    ·
                      rfl

theorem cell22_3643715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 4].length) (baseStart_3643715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643715 prefixEnd_3643715 := by exact prefixLift 3643715
  have htrace : WordTrace (prefixWord ++ tailWord_3643715) baseStart_3643715 baseEnd_3643715 := by
    simpa [prefixWord, tailWord_3643715, baseEnd_3643715] using wordTrace_append hprefix tailTrace_3643715
  have hstable : (prefixWord ++ tailWord_3643715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643715).length < 2 ^ (prefixWord ++ tailWord_3643715).sum := by decide
  have hdescent : baseEnd_3643715 < baseStart_3643715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643747 : List Nat := [1, 1, 1, 5, 2, 1, 1, 6, 4]
def baseStart_3643747 : Nat := 118140960795 + 3643747 * 2 ^ 59
def prefixEnd_3643747 : Nat := 4983230072969 + 3 ^ 40 * 3643747 * 2
def baseEnd_3643747 : Nat := 415776354306280123734493

theorem tailTrace_3643747 : CollatzResearch.WordTrace tailWord_3643747 prefixEnd_3643747 415776354306280123734493 := by
  unfold tailWord_3643747
  simp only [CollatzResearch.WordTrace]
  refine ⟨132898371130334396288681495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88598914086889597525787663 132898371130334396288681495)
  ·
    refine ⟨199347556695501594433022243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132898371130334396288681495 199347556695501594433022243)
    ·
      refine ⟨299021335043252391649533365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199347556695501594433022243 299021335043252391649533365)
      ·
        refine ⟨28033250160304911717143753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299021335043252391649533365 28033250160304911717143753)
        ·
          refine ⟨21024937620228683787857815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28033250160304911717143753 21024937620228683787857815)
          ·
            refine ⟨31537406430343025681786723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21024937620228683787857815 31537406430343025681786723)
            ·
              refine ⟨47306109645514538522680085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31537406430343025681786723 47306109645514538522680085)
              ·
                refine ⟨2217473889633493993250629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47306109645514538522680085 2217473889633493993250629)
                ·
                  refine ⟨415776354306280123734493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217473889633493993250629 415776354306280123734493)
                  ·
                    rfl

theorem cell22_3643747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 4].length) (baseStart_3643747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643747 prefixEnd_3643747 := by exact prefixLift 3643747
  have htrace : WordTrace (prefixWord ++ tailWord_3643747) baseStart_3643747 baseEnd_3643747 := by
    simpa [prefixWord, tailWord_3643747, baseEnd_3643747] using wordTrace_append hprefix tailTrace_3643747
  have hstable : (prefixWord ++ tailWord_3643747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643747).length < 2 ^ (prefixWord ++ tailWord_3643747).sum := by decide
  have hdescent : baseEnd_3643747 < baseStart_3643747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643760 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_3643760 : Nat := 118140960795 + 3643760 * 2 ^ 59
def prefixEnd_3643760 : Nat := 4983230072969 + 3 ^ 40 * 3643760 * 2
def baseEnd_3643760 : Nat := 1247333513084512670628439

theorem tailTrace_3643760 : CollatzResearch.WordTrace tailWord_3643760 prefixEnd_3643760 1247333513084512670628439 := by
  unfold tailWord_3643760
  simp only [CollatzResearch.WordTrace]
  refine ⟨66449422639643649754452367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88599230186191533005936489 66449422639643649754452367)
  ·
    refine ⟨99674133959465474631678551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66449422639643649754452367 99674133959465474631678551)
    ·
      refine ⟨149511200939198211947517827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99674133959465474631678551 149511200939198211947517827)
      ·
        refine ⟨224266801408797317921276741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149511200939198211947517827 224266801408797317921276741)
        ·
          refine ⟨42050025264149497110239389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224266801408797317921276741 42050025264149497110239389)
          ·
            refine ⟨15768759474056061416339771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42050025264149497110239389 15768759474056061416339771)
            ·
              refine ⟨23653139211084092124509657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15768759474056061416339771 23653139211084092124509657)
              ·
                refine ⟨17739854408313069093382243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23653139211084092124509657 17739854408313069093382243)
                ·
                  refine ⟨26609781612469603640073365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17739854408313069093382243 26609781612469603640073365)
                  ·
                    refine ⟨1247333513084512670628439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26609781612469603640073365 1247333513084512670628439)
                    ·
                      rfl

theorem cell22_3643760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_3643760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643760 prefixEnd_3643760 := by exact prefixLift 3643760
  have htrace : WordTrace (prefixWord ++ tailWord_3643760) baseStart_3643760 baseEnd_3643760 := by
    simpa [prefixWord, tailWord_3643760, baseEnd_3643760] using wordTrace_append hprefix tailTrace_3643760
  have hstable : (prefixWord ++ tailWord_3643760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643760).length < 2 ^ (prefixWord ++ tailWord_3643760).sum := by decide
  have hdescent : baseEnd_3643760 < baseStart_3643760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643762 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_3643762 : Nat := 118140960795 + 3643762 * 2 ^ 59
def prefixEnd_3643762 : Nat := 4983230072969 + 3 ^ 40 * 3643762 * 2
def baseEnd_3643762 : Nat := 1247334197725385332078433

theorem tailTrace_3643762 : CollatzResearch.WordTrace tailWord_3643762 prefixEnd_3643762 1247334197725385332078433 := by
  unfold tailWord_3643762
  simp only [CollatzResearch.WordTrace]
  refine ⟨33224729556320013462619385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88599278816853369233651693 33224729556320013462619385)
  ·
    refine ⟨24918547167240010096964539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33224729556320013462619385 24918547167240010096964539)
    ·
      refine ⟨37377820750860015145446809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24918547167240010096964539 37377820750860015145446809)
      ·
        refine ⟨28033365563145011359085107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37377820750860015145446809 28033365563145011359085107)
        ·
          refine ⟨42050048344717517038627661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28033365563145011359085107 42050048344717517038627661)
          ·
            refine ⟨15768768129269068889485373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42050048344717517038627661 15768768129269068889485373)
            ·
              refine ⟨5913288048475900833557015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15768768129269068889485373 5913288048475900833557015)
              ·
                refine ⟨8869932072713851250335523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5913288048475900833557015 8869932072713851250335523)
                ·
                  refine ⟨13304898109070776875503285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8869932072713851250335523 13304898109070776875503285)
                  ·
                    refine ⟨1247334197725385332078433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13304898109070776875503285 1247334197725385332078433)
                    ·
                      rfl

theorem cell22_3643762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_3643762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643762 prefixEnd_3643762 := by exact prefixLift 3643762
  have htrace : WordTrace (prefixWord ++ tailWord_3643762) baseStart_3643762 baseEnd_3643762 := by
    simpa [prefixWord, tailWord_3643762, baseEnd_3643762] using wordTrace_append hprefix tailTrace_3643762
  have hstable : (prefixWord ++ tailWord_3643762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643762).length < 2 ^ (prefixWord ++ tailWord_3643762).sum := by decide
  have hdescent : baseEnd_3643762 < baseStart_3643762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643777 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3643777 : Nat := 118140960795 + 3643777 * 2 ^ 59
def prefixEnd_3643777 : Nat := 4983230072969 + 3 ^ 40 * 3643777 * 2
def baseEnd_3643777 : Nat := 1247339332531930292953387

theorem tailTrace_3643777 : CollatzResearch.WordTrace tailWord_3643777 prefixEnd_3643777 1247339332531930292953387 := by
  unfold tailWord_3643777
  simp only [CollatzResearch.WordTrace]
  refine ⟨132899465320225711412273585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88599643546817140941515723 132899465320225711412273585)
  ·
    refine ⟨99674598990169283559205189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132899465320225711412273585 99674598990169283559205189)
    ·
      refine ⟨18688987310656740667350973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99674598990169283559205189 18688987310656740667350973)
      ·
        refine ⟨7008370241496277750256615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18688987310656740667350973 7008370241496277750256615)
        ·
          refine ⟨10512555362244416625384923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008370241496277750256615 10512555362244416625384923)
          ·
            refine ⟨15768833043366624938077385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512555362244416625384923 15768833043366624938077385)
            ·
              refine ⟨11826624782524968703558039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15768833043366624938077385 11826624782524968703558039)
              ·
                refine ⟨17739937173787453055337059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11826624782524968703558039 17739937173787453055337059)
                ·
                  refine ⟨26609905760681179583005589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17739937173787453055337059 26609905760681179583005589)
                  ·
                    refine ⟨1247339332531930292953387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26609905760681179583005589 1247339332531930292953387)
                    ·
                      rfl

theorem cell22_3643777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3643777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643777 prefixEnd_3643777 := by exact prefixLift 3643777
  have htrace : WordTrace (prefixWord ++ tailWord_3643777) baseStart_3643777 baseEnd_3643777 := by
    simpa [prefixWord, tailWord_3643777, baseEnd_3643777] using wordTrace_append hprefix tailTrace_3643777
  have hstable : (prefixWord ++ tailWord_3643777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643777).length < 2 ^ (prefixWord ++ tailWord_3643777).sum := by decide
  have hdescent : baseEnd_3643777 < baseStart_3643777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643809 : List Nat := [1, 2, 3, 5, 1, 1, 2, 7]
def baseStart_3643809 : Nat := 118140960795 + 3643809 * 2 ^ 59
def prefixEnd_3643809 : Nat := 4983230072969 + 3 ^ 40 * 3643809 * 2
def baseEnd_3643809 : Nat := 138594476309543652905921

theorem tailTrace_3643809 : CollatzResearch.WordTrace tailWord_3643809 prefixEnd_3643809 138594476309543652905921 := by
  unfold tailWord_3643809
  simp only [CollatzResearch.WordTrace]
  refine ⟨132900632456109780877438481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88600421637406520584958987 132900632456109780877438481)
  ·
    refine ⟨99675474342082335658078861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132900632456109780877438481 99675474342082335658078861)
    ·
      refine ⟨37378302878280875871779573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99675474342082335658078861 37378302878280875871779573)
      ·
        refine ⟨3504215894838832112979335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37378302878280875871779573 3504215894838832112979335)
        ·
          refine ⟨5256323842258248169469003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504215894838832112979335 5256323842258248169469003)
          ·
            refine ⟨7884485763387372254203505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256323842258248169469003 7884485763387372254203505)
            ·
              refine ⟨5913364322540529190652629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7884485763387372254203505 5913364322540529190652629)
              ·
                refine ⟨138594476309543652905921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5913364322540529190652629 138594476309543652905921)
                ·
                  rfl

theorem cell22_3643809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 7].length) (baseStart_3643809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643809 prefixEnd_3643809 := by exact prefixLift 3643809
  have htrace : WordTrace (prefixWord ++ tailWord_3643809) baseStart_3643809 baseEnd_3643809 := by
    simpa [prefixWord, tailWord_3643809, baseEnd_3643809] using wordTrace_append hprefix tailTrace_3643809
  have hstable : (prefixWord ++ tailWord_3643809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643809).length < 2 ^ (prefixWord ++ tailWord_3643809).sum := by decide
  have hdescent : baseEnd_3643809 < baseStart_3643809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643828 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3643828 : Nat := 118140960795 + 3643828 * 2 ^ 59
def prefixEnd_3643828 : Nat := 4983230072969 + 3 ^ 40 * 3643828 * 2
def baseEnd_3643828 : Nat := 1247356790874183159928231

theorem tailTrace_3643828 : CollatzResearch.WordTrace tailWord_3643828 prefixEnd_3643828 1247356790874183159928231 := by
  unfold tailWord_3643828
  simp only [CollatzResearch.WordTrace]
  refine ⟨66450662721520473561190069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88600883628693964748253425 66450662721520473561190069)
  ·
    refine ⟨6229749630142544396361569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66450662721520473561190069 6229749630142544396361569)
    ·
      refine ⟨4672312222606908297271177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6229749630142544396361569 4672312222606908297271177)
      ·
        refine ⟨3504234166955181222953383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4672312222606908297271177 3504234166955181222953383)
        ·
          refine ⟨5256351250432771834430075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504234166955181222953383 5256351250432771834430075)
          ·
            refine ⟨7884526875649157751645113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256351250432771834430075 7884526875649157751645113)
            ·
              refine ⟨5913395156736868313733835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7884526875649157751645113 5913395156736868313733835)
              ·
                refine ⟨8870092735105302470600753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5913395156736868313733835 8870092735105302470600753)
                ·
                  refine ⟨6652569551328976852950565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8870092735105302470600753 6652569551328976852950565)
                  ·
                    refine ⟨1247356790874183159928231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6652569551328976852950565 1247356790874183159928231)
                    ·
                      rfl

theorem cell22_3643828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3643828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643828 prefixEnd_3643828 := by exact prefixLift 3643828
  have htrace : WordTrace (prefixWord ++ tailWord_3643828) baseStart_3643828 baseEnd_3643828 := by
    simpa [prefixWord, tailWord_3643828, baseEnd_3643828] using wordTrace_append hprefix tailTrace_3643828
  have hstable : (prefixWord ++ tailWord_3643828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643828).length < 2 ^ (prefixWord ++ tailWord_3643828).sum := by decide
  have hdescent : baseEnd_3643828 < baseStart_3643828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643882 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_3643882 : Nat := 118140960795 + 3643882 * 2 ^ 59
def prefixEnd_3643882 : Nat := 4983230072969 + 3 ^ 40 * 3643882 * 2
def baseEnd_3643882 : Nat := 415791758725915006359355

theorem tailTrace_3643882 : CollatzResearch.WordTrace tailWord_3643882 prefixEnd_3643882 415791758725915006359355 := by
  unfold tailWord_3643882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33225823746211328586211475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88602196656563542896563933 33225823746211328586211475)
  ·
    refine ⟨49838735619316992879317213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33225823746211328586211475 49838735619316992879317213)
    ·
      refine ⟨18689525857243872329743955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49838735619316992879317213 18689525857243872329743955)
      ·
        refine ⟨28034288785865808494615933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18689525857243872329743955 28034288785865808494615933)
        ·
          refine ⟨10512858294699678185480975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28034288785865808494615933 10512858294699678185480975)
          ·
            refine ⟨15769287442049517278221463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512858294699678185480975 15769287442049517278221463)
            ·
              refine ⟨23653931163074275917332195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15769287442049517278221463 23653931163074275917332195)
              ·
                refine ⟨35480896744611413875998293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23653931163074275917332195 35480896744611413875998293)
                ·
                  refine ⟨415791758725915006359355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35480896744611413875998293 415791758725915006359355)
                  ·
                    rfl

theorem cell22_3643882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_3643882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643882 prefixEnd_3643882 := by exact prefixLift 3643882
  have htrace : WordTrace (prefixWord ++ tailWord_3643882) baseStart_3643882 baseEnd_3643882 := by
    simpa [prefixWord, tailWord_3643882, baseEnd_3643882] using wordTrace_append hprefix tailTrace_3643882
  have hstable : (prefixWord ++ tailWord_3643882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643882).length < 2 ^ (prefixWord ++ tailWord_3643882).sum := by decide
  have hdescent : baseEnd_3643882 < baseStart_3643882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643897 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_3643897 : Nat := 118140960795 + 3643897 * 2 ^ 59
def prefixEnd_3643897 : Nat := 4983230072969 + 3 ^ 40 * 3643897 * 2
def baseEnd_3643897 : Nat := 1247380410984289979953019

theorem tailTrace_3643897 : CollatzResearch.WordTrace tailWord_3643897 prefixEnd_3643897 1247380410984289979953019 := by
  unfold tailWord_3643897
  simp only [CollatzResearch.WordTrace]
  refine ⟨132903842079790971906641945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88602561386527314604427963 132903842079790971906641945)
  ·
    refine ⟨99677881559843228929981459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132903842079790971906641945 99677881559843228929981459)
    ·
      refine ⟨149516822339764843394972189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99677881559843228929981459 149516822339764843394972189)
      ·
        refine ⟨56068808377411816273114571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149516822339764843394972189 56068808377411816273114571)
        ·
          refine ⟨84103212566117724409671857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56068808377411816273114571 84103212566117724409671857)
          ·
            refine ⟨63077409424588293307253893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84103212566117724409671857 63077409424588293307253893)
            ·
              refine ⟨11827014267110304995110105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63077409424588293307253893 11827014267110304995110105)
              ·
                refine ⟨8870260700332728746332579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11827014267110304995110105 8870260700332728746332579)
                ·
                  refine ⟨13305391050499093119498869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8870260700332728746332579 13305391050499093119498869)
                  ·
                    refine ⟨1247380410984289979953019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13305391050499093119498869 1247380410984289979953019)
                    ·
                      rfl

theorem cell22_3643897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_3643897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643897 prefixEnd_3643897 := by exact prefixLift 3643897
  have htrace : WordTrace (prefixWord ++ tailWord_3643897) baseStart_3643897 baseEnd_3643897 := by
    simpa [prefixWord, tailWord_3643897, baseEnd_3643897] using wordTrace_append hprefix tailTrace_3643897
  have hstable : (prefixWord ++ tailWord_3643897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643897).length < 2 ^ (prefixWord ++ tailWord_3643897).sum := by decide
  have hdescent : baseEnd_3643897 < baseStart_3643897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643912 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_3643912 : Nat := 118140960795 + 3643912 * 2 ^ 59
def prefixEnd_3643912 : Nat := 4983230072969 + 3 ^ 40 * 3643912 * 2
def baseEnd_3643912 : Nat := 1247385545790834940827973

theorem tailTrace_3643912 : CollatzResearch.WordTrace tailWord_3643912 prefixEnd_3643912 1247385545790834940827973 := by
  unfold tailWord_3643912
  simp only [CollatzResearch.WordTrace]
  refine ⟨66452194587368314734218995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88602926116491086312291993 66452194587368314734218995)
  ·
    refine ⟨99678291881052472101328493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66452194587368314734218995 99678291881052472101328493)
    ·
      refine ⟨37379359455394677037998185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99678291881052472101328493 37379359455394677037998185)
      ·
        refine ⟨28034519591546007778498639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37379359455394677037998185 28034519591546007778498639)
        ·
          refine ⟨42051779387319011667747959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28034519591546007778498639 42051779387319011667747959)
          ·
            refine ⟨63077669080978517501621939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42051779387319011667747959 63077669080978517501621939)
            ·
              refine ⟨94616503621467776252432909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63077669080978517501621939 94616503621467776252432909)
              ·
                refine ⟨35481188858050416094662341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94616503621467776252432909 35481188858050416094662341)
                ·
                  refine ⟨6652722910884453017749189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35481188858050416094662341 6652722910884453017749189)
                  ·
                    refine ⟨1247385545790834940827973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6652722910884453017749189 1247385545790834940827973)
                    ·
                      rfl

theorem cell22_3643912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_3643912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643912 prefixEnd_3643912 := by exact prefixLift 3643912
  have htrace : WordTrace (prefixWord ++ tailWord_3643912) baseStart_3643912 baseEnd_3643912 := by
    simpa [prefixWord, tailWord_3643912, baseEnd_3643912] using wordTrace_append hprefix tailTrace_3643912
  have hstable : (prefixWord ++ tailWord_3643912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643912).length < 2 ^ (prefixWord ++ tailWord_3643912).sum := by decide
  have hdescent : baseEnd_3643912 < baseStart_3643912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643914 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_3643914 : Nat := 118140960795 + 3643914 * 2 ^ 59
def prefixEnd_3643914 : Nat := 4983230072969 + 3 ^ 40 * 3643914 * 2
def baseEnd_3643914 : Nat := 1247386230431707602277967

theorem tailTrace_3643914 : CollatzResearch.WordTrace tailWord_3643914 prefixEnd_3643914 1247386230431707602277967 := by
  unfold tailWord_3643914
  simp only [CollatzResearch.WordTrace]
  refine ⟨33226115530182345952502699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88602974747152922540007197 33226115530182345952502699)
  ·
    refine ⟨49839173295273518928754049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33226115530182345952502699 49839173295273518928754049)
    ·
      refine ⟨37379379971455139196565537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49839173295273518928754049 37379379971455139196565537)
      ·
        refine ⟨28034534978591354397424153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37379379971455139196565537 28034534978591354397424153)
        ·
          refine ⟨21025901233943515798068115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28034534978591354397424153 21025901233943515798068115)
          ·
            refine ⟨31538851850915273697102173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21025901233943515798068115 31538851850915273697102173)
            ·
              refine ⟨11827069444093227636413315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31538851850915273697102173 11827069444093227636413315)
              ·
                refine ⟨17740604166139841454619973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11827069444093227636413315 17740604166139841454619973)
                ·
                  refine ⟨3326363281151220272741245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17740604166139841454619973 3326363281151220272741245)
                  ·
                    refine ⟨1247386230431707602277967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326363281151220272741245 1247386230431707602277967)
                    ·
                      rfl

theorem cell22_3643914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_3643914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643914 prefixEnd_3643914 := by exact prefixLift 3643914
  have htrace : WordTrace (prefixWord ++ tailWord_3643914) baseStart_3643914 baseEnd_3643914 := by
    simpa [prefixWord, tailWord_3643914, baseEnd_3643914] using wordTrace_append hprefix tailTrace_3643914
  have hstable : (prefixWord ++ tailWord_3643914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643914).length < 2 ^ (prefixWord ++ tailWord_3643914).sum := by decide
  have hdescent : baseEnd_3643914 < baseStart_3643914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643944 : List Nat := [2, 1, 5, 2, 1, 2, 1, 8]
def baseStart_3643944 : Nat := 118140960795 + 3643944 * 2 ^ 59
def prefixEnd_3643944 : Nat := 4983230072969 + 3 ^ 40 * 3643944 * 2
def baseEnd_3643944 : Nat := 138599611116088613780875

theorem tailTrace_3643944 : CollatzResearch.WordTrace tailWord_3643944 prefixEnd_3643944 138599611116088613780875 := by
  unfold tailWord_3643944
  simp only [CollatzResearch.WordTrace]
  refine ⟨66452778155310349466801443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88603704207080465955735257 66452778155310349466801443)
  ·
    refine ⟨99679167232965524200202165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66452778155310349466801443 99679167232965524200202165)
    ·
      refine ⟨9344921928090517893768953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99679167232965524200202165 9344921928090517893768953)
      ·
        refine ⟨7008691446067888420326715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9344921928090517893768953 7008691446067888420326715)
        ·
          refine ⟨10513037169101832630490073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008691446067888420326715 10513037169101832630490073)
          ·
            refine ⟨7884777876826374472867555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10513037169101832630490073 7884777876826374472867555)
            ·
              refine ⟨11827166815239561709301333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7884777876826374472867555 11827166815239561709301333)
              ·
                refine ⟨138599611116088613780875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11827166815239561709301333 138599611116088613780875)
                ·
                  rfl

theorem cell22_3643944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 8].length) (baseStart_3643944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643944 prefixEnd_3643944 := by exact prefixLift 3643944
  have htrace : WordTrace (prefixWord ++ tailWord_3643944) baseStart_3643944 baseEnd_3643944 := by
    simpa [prefixWord, tailWord_3643944, baseEnd_3643944] using wordTrace_append hprefix tailTrace_3643944
  have hstable : (prefixWord ++ tailWord_3643944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643944).length < 2 ^ (prefixWord ++ tailWord_3643944).sum := by decide
  have hdescent : baseEnd_3643944 < baseStart_3643944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643950 : List Nat := [4, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_3643950 : Nat := 118140960795 + 3643950 * 2 ^ 59
def prefixEnd_3643950 : Nat := 4983230072969 + 3 ^ 40 * 3643950 * 2
def baseEnd_3643950 : Nat := 415799517989138502792619

theorem tailTrace_3643950 : CollatzResearch.WordTrace tailWord_3643950 prefixEnd_3643950 415799517989138502792619 := by
  unfold tailWord_3643950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16613221893574870244790163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88603850099065974638880869 16613221893574870244790163)
  ·
    refine ⟨24919832840362305367185245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16613221893574870244790163 24919832840362305367185245)
    ·
      refine ⟨9344937315135864512694467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24919832840362305367185245 9344937315135864512694467)
      ·
        refine ⟨14017405972703796769041701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9344937315135864512694467 14017405972703796769041701)
        ·
          refine ⟨2628263619881961894195319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14017405972703796769041701 2628263619881961894195319)
          ·
            refine ⟨3942395429822942841292979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628263619881961894195319 3942395429822942841292979)
            ·
              refine ⟨5913593144734414261939469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942395429822942841292979 5913593144734414261939469)
              ·
                refine ⟨2217597429275405348227301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5913593144734414261939469 2217597429275405348227301)
                ·
                  refine ⟨415799517989138502792619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217597429275405348227301 415799517989138502792619)
                  ·
                    rfl

theorem cell22_3643950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_3643950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643950 prefixEnd_3643950 := by exact prefixLift 3643950
  have htrace : WordTrace (prefixWord ++ tailWord_3643950) baseStart_3643950 baseEnd_3643950 := by
    simpa [prefixWord, tailWord_3643950, baseEnd_3643950] using wordTrace_append hprefix tailTrace_3643950
  have hstable : (prefixWord ++ tailWord_3643950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643950).length < 2 ^ (prefixWord ++ tailWord_3643950).sum := by decide
  have hdescent : baseEnd_3643950 < baseStart_3643950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643976 : List Nat := [2, 1, 3, 1, 1, 1, 1, 8, 1, 3]
def baseStart_3643976 : Nat := 118140960795 + 3643976 * 2 ^ 59
def prefixEnd_3643976 : Nat := 4983230072969 + 3 ^ 40 * 3643976 * 2
def baseEnd_3643976 : Nat := 1247407454298760107227777

theorem tailTrace_3643976 : CollatzResearch.WordTrace tailWord_3643976 prefixEnd_3643976 1247407454298760107227777 := by
  unfold tailWord_3643976
  simp only [CollatzResearch.WordTrace]
  refine ⟨66453361723252384199383891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88604482297669845599178521 66453361723252384199383891)
  ·
    refine ⟨99680042584878576299075837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66453361723252384199383891 99680042584878576299075837)
    ·
      refine ⟨37380015969329466112153439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99680042584878576299075837 37380015969329466112153439)
      ·
        refine ⟨56070023953994199168230159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37380015969329466112153439 56070023953994199168230159)
        ·
          refine ⟨84105035930991298752345239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56070023953994199168230159 84105035930991298752345239)
          ·
            refine ⟨126157553896486948128517859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84105035930991298752345239 126157553896486948128517859)
            ·
              refine ⟨189236330844730422192776789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126157553896486948128517859 189236330844730422192776789)
              ·
                refine ⟨2217613252086684635071603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 189236330844730422192776789 2217613252086684635071603)
                ·
                  refine ⟨3326419878130026952607405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217613252086684635071603 3326419878130026952607405)
                  ·
                    refine ⟨1247407454298760107227777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326419878130026952607405 1247407454298760107227777)
                    ·
                      rfl

theorem cell22_3643976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_3643976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3643976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3643976 prefixEnd_3643976 := by exact prefixLift 3643976
  have htrace : WordTrace (prefixWord ++ tailWord_3643976) baseStart_3643976 baseEnd_3643976 := by
    simpa [prefixWord, tailWord_3643976, baseEnd_3643976] using wordTrace_append hprefix tailTrace_3643976
  have hstable : (prefixWord ++ tailWord_3643976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643976).length < 2 ^ (prefixWord ++ tailWord_3643976).sum := by decide
  have hdescent : baseEnd_3643976 < baseStart_3643976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644047 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 3, 6]
def baseStart_3644047 : Nat := 118140960795 + 3644047 * 2 ^ 59
def prefixEnd_3644047 : Nat := 4983230072969 + 3 ^ 40 * 3644047 * 2
def baseEnd_3644047 : Nat := 1247431759049739588702559

theorem tailTrace_3644047 : CollatzResearch.WordTrace tailWord_3644047 prefixEnd_3644047 1247431759049739588702559 := by
  unfold tailWord_3644047
  simp only [CollatzResearch.WordTrace]
  refine ⟨132909313029247547524602395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88606208686165031683068263 132909313029247547524602395)
  ·
    refine ⟨199363969543871321286903593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132909313029247547524602395 199363969543871321286903593)
    ·
      refine ⟨149522977157903490965177695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199363969543871321286903593 149522977157903490965177695)
      ·
        refine ⟨224284465736855236447766543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149522977157903490965177695 224284465736855236447766543)
        ·
          refine ⟨336426698605282854671649815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224284465736855236447766543 336426698605282854671649815)
          ·
            refine ⟨504640047907924282007474723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336426698605282854671649815 504640047907924282007474723)
            ·
              refine ⟨756960071861886423011212085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504640047907924282007474723 756960071861886423011212085)
              ·
                refine ⟨70965006737051852157301133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 756960071861886423011212085 70965006737051852157301133)
                ·
                  refine ⟨26611877526394444558987925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70965006737051852157301133 26611877526394444558987925)
                  ·
                    refine ⟨1247431759049739588702559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26611877526394444558987925 1247431759049739588702559)
                    ·
                      rfl

theorem cell22_3644047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_3644047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644047 prefixEnd_3644047 := by exact prefixLift 3644047
  have htrace : WordTrace (prefixWord ++ tailWord_3644047) baseStart_3644047 baseEnd_3644047 := by
    simpa [prefixWord, tailWord_3644047, baseEnd_3644047] using wordTrace_append hprefix tailTrace_3644047
  have hstable : (prefixWord ++ tailWord_3644047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644047).length < 2 ^ (prefixWord ++ tailWord_3644047).sum := by decide
  have hdescent : baseEnd_3644047 < baseStart_3644047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644083 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 2, 3]
def baseStart_3644083 : Nat := 118140960795 + 3644083 * 2 ^ 59
def prefixEnd_3644083 : Nat := 4983230072969 + 3 ^ 40 * 3644083 * 2
def baseEnd_3644083 : Nat := 1247444082585447494802449

theorem tailTrace_3644083 : CollatzResearch.WordTrace tailWord_3644083 prefixEnd_3644083 1247444082585447494802449 := by
  unfold tailWord_3644083
  simp only [CollatzResearch.WordTrace]
  refine ⟨132910626057117125672912903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88607084038078083781941935 132910626057117125672912903)
  ·
    refine ⟨199365939085675688509369355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132910626057117125672912903 199365939085675688509369355)
    ·
      refine ⟨299048908628513532764054033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199365939085675688509369355 299048908628513532764054033)
      ·
        refine ⟨224286681471385149573040525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299048908628513532764054033 224286681471385149573040525)
        ·
          refine ⟨84107505551769431089890197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224286681471385149573040525 84107505551769431089890197)
          ·
            refine ⟨3942539322739192082338603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84107505551769431089890197 3942539322739192082338603)
            ·
              refine ⟨5913808984108788123507905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942539322739192082338603 5913808984108788123507905)
              ·
                refine ⟨4435356738081591092630929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5913808984108788123507905 4435356738081591092630929)
                ·
                  refine ⟨3326517553561193319473197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4435356738081591092630929 3326517553561193319473197)
                  ·
                    refine ⟨1247444082585447494802449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326517553561193319473197 1247444082585447494802449)
                    ·
                      rfl

theorem cell22_3644083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 3].length) (baseStart_3644083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644083 prefixEnd_3644083 := by exact prefixLift 3644083
  have htrace : WordTrace (prefixWord ++ tailWord_3644083) baseStart_3644083 baseEnd_3644083 := by
    simpa [prefixWord, tailWord_3644083, baseEnd_3644083] using wordTrace_append hprefix tailTrace_3644083
  have hstable : (prefixWord ++ tailWord_3644083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644083).length < 2 ^ (prefixWord ++ tailWord_3644083).sum := by decide
  have hdescent : baseEnd_3644083 < baseStart_3644083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644100 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3644100 : Nat := 118140960795 + 3644100 * 2 ^ 59
def prefixEnd_3644100 : Nat := 4983230072969 + 3 ^ 40 * 3644100 * 2
def baseEnd_3644100 : Nat := 1247449902032865117127397

theorem tailTrace_3644100 : CollatzResearch.WordTrace tailWord_3644100 prefixEnd_3644100 1247449902032865117127397 := by
  unfold tailWord_3644100
  simp only [CollatzResearch.WordTrace]
  refine ⟨66455623049027768788140877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88607497398703691717521169 66455623049027768788140877)
  ·
    refine ⟨24920858643385413295552829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66455623049027768788140877 24920858643385413295552829)
    ·
      refine ⟨9345321991269529985832311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24920858643385413295552829 9345321991269529985832311)
      ·
        refine ⟨14017982986904294978748467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9345321991269529985832311 14017982986904294978748467)
        ·
          refine ⟨21026974480356442468122701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14017982986904294978748467 21026974480356442468122701)
          ·
            refine ⟨7885115430133665925546013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21026974480356442468122701 7885115430133665925546013)
            ·
              refine ⟨2956918286300124722079755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7885115430133665925546013 2956918286300124722079755)
              ·
                refine ⟨4435377429450187083119633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956918286300124722079755 4435377429450187083119633)
                ·
                  refine ⟨3326533072087640312339725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4435377429450187083119633 3326533072087640312339725)
                  ·
                    refine ⟨1247449902032865117127397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326533072087640312339725 1247449902032865117127397)
                    ·
                      rfl

theorem cell22_3644100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3644100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644100 prefixEnd_3644100 := by exact prefixLift 3644100
  have htrace : WordTrace (prefixWord ++ tailWord_3644100) baseStart_3644100 baseEnd_3644100 := by
    simpa [prefixWord, tailWord_3644100, baseEnd_3644100] using wordTrace_append hprefix tailTrace_3644100
  have hstable : (prefixWord ++ tailWord_3644100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644100).length < 2 ^ (prefixWord ++ tailWord_3644100).sum := by decide
  have hdescent : baseEnd_3644100 < baseStart_3644100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644141 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 5]
def baseStart_3644141 : Nat := 118140960795 + 3644141 * 2 ^ 59
def prefixEnd_3644141 : Nat := 4983230072969 + 3 ^ 40 * 3644141 * 2
def baseEnd_3644141 : Nat := 415821312390251558950757

theorem tailTrace_3644141 : CollatzResearch.WordTrace tailWord_3644141 prefixEnd_3644141 415821312390251558950757 := by
  unfold tailWord_3644141
  simp only [CollatzResearch.WordTrace]
  refine ⟨132912741490907001578524277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88608494327271334385682851 132912741490907001578524277)
  ·
    refine ⟨12460569514772531397986651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132912741490907001578524277 12460569514772531397986651)
    ·
      refine ⟨18690854272158797096979977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12460569514772531397986651 18690854272158797096979977)
      ·
        refine ⟨14018140704119097822734983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18690854272158797096979977 14018140704119097822734983)
        ·
          refine ⟨21027211056178646734102475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14018140704119097822734983 21027211056178646734102475)
          ·
            refine ⟨31540816584267970101153713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21027211056178646734102475 31540816584267970101153713)
            ·
              refine ⟨23655612438200977575865285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31540816584267970101153713 23655612438200977575865285)
              ·
                refine ⟨4435427332162683295474741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23655612438200977575865285 4435427332162683295474741)
                ·
                  refine ⟨415821312390251558950757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4435427332162683295474741 415821312390251558950757)
                  ·
                    rfl

theorem cell22_3644141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_3644141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644141 prefixEnd_3644141 := by exact prefixLift 3644141
  have htrace : WordTrace (prefixWord ++ tailWord_3644141) baseStart_3644141 baseEnd_3644141 := by
    simpa [prefixWord, tailWord_3644141, baseEnd_3644141] using wordTrace_append hprefix tailTrace_3644141
  have hstable : (prefixWord ++ tailWord_3644141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644141).length < 2 ^ (prefixWord ++ tailWord_3644141).sum := by decide
  have hdescent : baseEnd_3644141 < baseStart_3644141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644145 : List Nat := [1, 2, 2, 2, 2, 2, 5, 2, 1, 3]
def baseStart_3644145 : Nat := 118140960795 + 3644145 * 2 ^ 59
def prefixEnd_3644145 : Nat := 4983230072969 + 3 ^ 40 * 3644145 * 2
def baseEnd_3644145 : Nat := 1247465306452499999752259

theorem tailTrace_3644145 : CollatzResearch.WordTrace tailWord_3644145 prefixEnd_3644145 1247465306452499999752259 := by
  unfold tailWord_3644145
  simp only [CollatzResearch.WordTrace]
  refine ⟨132912887382892510261669889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88608591588595006841113259 132912887382892510261669889)
  ·
    refine ⟨99684665537169382696252417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132912887382892510261669889 99684665537169382696252417)
    ·
      refine ⟨74763499152877037022189313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99684665537169382696252417 74763499152877037022189313)
      ·
        refine ⟨56072624364657777766641985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74763499152877037022189313 56072624364657777766641985)
        ·
          refine ⟨42054468273493333324981489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56072624364657777766641985 42054468273493333324981489)
          ·
            refine ⟨31540851205119999993736117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42054468273493333324981489 31540851205119999993736117)
            ·
              refine ⟨2956954800479999999412761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31540851205119999993736117 2956954800479999999412761)
              ·
                refine ⟨2217716100359999999559571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2956954800479999999412761 2217716100359999999559571)
                ·
                  refine ⟨3326574150539999999339357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217716100359999999559571 3326574150539999999339357)
                  ·
                    refine ⟨1247465306452499999752259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326574150539999999339357 1247465306452499999752259)
                    ·
                      rfl

theorem cell22_3644145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_3644145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644145 prefixEnd_3644145 := by exact prefixLift 3644145
  have htrace : WordTrace (prefixWord ++ tailWord_3644145) baseStart_3644145 baseEnd_3644145 := by
    simpa [prefixWord, tailWord_3644145, baseEnd_3644145] using wordTrace_append hprefix tailTrace_3644145
  have hstable : (prefixWord ++ tailWord_3644145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644145).length < 2 ^ (prefixWord ++ tailWord_3644145).sum := by decide
  have hdescent : baseEnd_3644145 < baseStart_3644145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644158 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3644158 : Nat := 118140960795 + 3644158 * 2 ^ 59
def prefixEnd_3644158 : Nat := 4983230072969 + 3 ^ 40 * 3644158 * 2
def baseEnd_3644158 : Nat := 415823252206057433059073

theorem tailTrace_3644158 : CollatzResearch.WordTrace tailWord_3644158 prefixEnd_3644158 415823252206057433059073 := by
  unfold tailWord_3644158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16614170191480676685236641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88608907687896942321262085 16614170191480676685236641)
  ·
    refine ⟨12460627643610507513927481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16614170191480676685236641 12460627643610507513927481)
    ·
      refine ⟨9345470732707880635445611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12460627643610507513927481 9345470732707880635445611)
      ·
        refine ⟨14018206099061820953168417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9345470732707880635445611 14018206099061820953168417)
        ·
          refine ⟨10513654574296365714876313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14018206099061820953168417 10513654574296365714876313)
          ·
            refine ⟨7885240930722274286157235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10513654574296365714876313 7885240930722274286157235)
            ·
              refine ⟨11827861396083411429235853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7885240930722274286157235 11827861396083411429235853)
              ·
                refine ⟨4435448023531279285963445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11827861396083411429235853 4435448023531279285963445)
                ·
                  refine ⟨415823252206057433059073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4435448023531279285963445 415823252206057433059073)
                  ·
                    rfl

theorem cell22_3644158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3644158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644158 prefixEnd_3644158 := by exact prefixLift 3644158
  have htrace : WordTrace (prefixWord ++ tailWord_3644158) baseStart_3644158 baseEnd_3644158 := by
    simpa [prefixWord, tailWord_3644158, baseEnd_3644158] using wordTrace_append hprefix tailTrace_3644158
  have hstable : (prefixWord ++ tailWord_3644158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644158).length < 2 ^ (prefixWord ++ tailWord_3644158).sum := by decide
  have hdescent : baseEnd_3644158 < baseStart_3644158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644169 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 6]
def baseStart_3644169 : Nat := 118140960795 + 3644169 * 2 ^ 59
def prefixEnd_3644169 : Nat := 4983230072969 + 3 ^ 40 * 3644169 * 2
def baseEnd_3644169 : Nat := 415824507380990645717395

theorem tailTrace_3644169 : CollatzResearch.WordTrace tailWord_3644169 prefixEnd_3644169 415824507380990645717395 := by
  unfold tailWord_3644169
  simp only [CollatzResearch.WordTrace]
  refine ⟨132913762734805562360543561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88609175156537041573695707 132913762734805562360543561)
  ·
    refine ⟨99685322051104171770407671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132913762734805562360543561 99685322051104171770407671)
    ·
      refine ⟨149527983076656257655611507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99685322051104171770407671 149527983076656257655611507)
      ·
        refine ⟨224291974614984386483417261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149527983076656257655611507 224291974614984386483417261)
        ·
          refine ⟨84109490480619144931281473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224291974614984386483417261 84109490480619144931281473)
          ·
            refine ⟨63082117860464358698461105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84109490480619144931281473 63082117860464358698461105)
            ·
              refine ⟨47311588395348269023845829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63082117860464358698461105 47311588395348269023845829)
              ·
                refine ⟨8870922824127800441971093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47311588395348269023845829 8870922824127800441971093)
                ·
                  refine ⟨415824507380990645717395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8870922824127800441971093 415824507380990645717395)
                  ·
                    rfl

theorem cell22_3644169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_3644169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644169 prefixEnd_3644169 := by exact prefixLift 3644169
  have htrace : WordTrace (prefixWord ++ tailWord_3644169) baseStart_3644169 baseEnd_3644169 := by
    simpa [prefixWord, tailWord_3644169, baseEnd_3644169] using wordTrace_append hprefix tailTrace_3644169
  have hstable : (prefixWord ++ tailWord_3644169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644169).length < 2 ^ (prefixWord ++ tailWord_3644169).sum := by decide
  have hdescent : baseEnd_3644169 < baseStart_3644169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644218 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_3644218 : Nat := 118140960795 + 3644218 * 2 ^ 59
def prefixEnd_3644218 : Nat := 4983230072969 + 3 ^ 40 * 3644218 * 2
def baseEnd_3644218 : Nat := 1247490295844352142677035

theorem tailTrace_3644218 : CollatzResearch.WordTrace tailWord_3644218 prefixEnd_3644218 1247490295844352142677035 := by
  unfold tailWord_3644218
  simp only [CollatzResearch.WordTrace]
  refine ⟨33228887477907010932269327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88610366607752029152718205 33228887477907010932269327)
  ·
    refine ⟨49843331216860516398403991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33228887477907010932269327 49843331216860516398403991)
    ·
      refine ⟨74764996825290774597605987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49843331216860516398403991 74764996825290774597605987)
      ·
        refine ⟨112147495237936161896408981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74764996825290774597605987 112147495237936161896408981)
        ·
          refine ⟨5256913839278257588894171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112147495237936161896408981 5256913839278257588894171)
          ·
            refine ⟨7885370758917386383341257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256913839278257588894171 7885370758917386383341257)
            ·
              refine ⟨5914028069188039787505943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7885370758917386383341257 5914028069188039787505943)
              ·
                refine ⟨8871042103782059681258915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5914028069188039787505943 8871042103782059681258915)
                ·
                  refine ⟨13306563155673089521888373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8871042103782059681258915 13306563155673089521888373)
                  ·
                    refine ⟨1247490295844352142677035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13306563155673089521888373 1247490295844352142677035)
                    ·
                      rfl

theorem cell22_3644218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_3644218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644218 prefixEnd_3644218 := by exact prefixLift 3644218
  have htrace : WordTrace (prefixWord ++ tailWord_3644218) baseStart_3644218 baseEnd_3644218 := by
    simpa [prefixWord, tailWord_3644218, baseEnd_3644218] using wordTrace_append hprefix tailTrace_3644218
  have hstable : (prefixWord ++ tailWord_3644218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644218).length < 2 ^ (prefixWord ++ tailWord_3644218).sum := by decide
  have hdescent : baseEnd_3644218 < baseStart_3644218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644229 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_3644229 : Nat := 118140960795 + 3644229 * 2 ^ 59
def prefixEnd_3644229 : Nat := 4983230072969 + 3 ^ 40 * 3644229 * 2
def baseEnd_3644229 : Nat := 1247494061369151780652001

theorem tailTrace_3644229 : CollatzResearch.WordTrace tailWord_3644229 prefixEnd_3644229 1247494061369151780652001 := by
  unfold tailWord_3644229
  simp only [CollatzResearch.WordTrace]
  refine ⟨132915951114588192607727741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88610634076392128405151827 132915951114588192607727741)
  ·
    refine ⟨49843481667970572227897903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132915951114588192607727741 49843481667970572227897903)
    ·
      refine ⟨74765222501955858341846855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49843481667970572227897903 74765222501955858341846855)
      ·
        refine ⟨112147833752933787512770283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74765222501955858341846855 112147833752933787512770283)
        ·
          refine ⟨168221750629400681269155425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112147833752933787512770283 168221750629400681269155425)
          ·
            refine ⟨126166312972050510951866569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168221750629400681269155425 126166312972050510951866569)
            ·
              refine ⟨94624734729037883213899927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126166312972050510951866569 94624734729037883213899927)
              ·
                refine ⟨141937102093556824820849891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94624734729037883213899927 141937102093556824820849891)
                ·
                  refine ⟨212905653140335237231274837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141937102093556824820849891 212905653140335237231274837)
                  ·
                    refine ⟨1247494061369151780652001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 212905653140335237231274837 1247494061369151780652001)
                    ·
                      rfl

theorem cell22_3644229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3644229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644229 prefixEnd_3644229 := by exact prefixLift 3644229
  have htrace : WordTrace (prefixWord ++ tailWord_3644229) baseStart_3644229 baseEnd_3644229 := by
    simpa [prefixWord, tailWord_3644229, baseEnd_3644229] using wordTrace_append hprefix tailTrace_3644229
  have hstable : (prefixWord ++ tailWord_3644229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644229).length < 2 ^ (prefixWord ++ tailWord_3644229).sum := by decide
  have hdescent : baseEnd_3644229 < baseStart_3644229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644233 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 2, 4]
def baseStart_3644233 : Nat := 118140960795 + 3644233 * 2 ^ 59
def prefixEnd_3644233 : Nat := 4983230072969 + 3 ^ 40 * 3644233 * 2
def baseEnd_3644233 : Nat := 1247495430650897103551989

theorem tailTrace_3644233 : CollatzResearch.WordTrace tailWord_3644233 prefixEnd_3644233 1247495430650897103551989 := by
  unfold tailWord_3644233
  simp only [CollatzResearch.WordTrace]
  refine ⟨132916097006573701290873353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88610731337715800860582235 132916097006573701290873353)
  ·
    refine ⟨99687072754930275968155015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132916097006573701290873353 99687072754930275968155015)
    ·
      refine ⟨149530609132395413952232523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99687072754930275968155015 149530609132395413952232523)
      ·
        refine ⟨224295913698593120928348785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149530609132395413952232523 224295913698593120928348785)
        ·
          refine ⟨168221935273944840696261589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224295913698593120928348785 168221935273944840696261589)
          ·
            refine ⟨3942701607983082203818631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168221935273944840696261589 3942701607983082203818631)
            ·
              refine ⟨5914052411974623305727947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942701607983082203818631 5914052411974623305727947)
              ·
                refine ⟨8871078617961934958591921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5914052411974623305727947 8871078617961934958591921)
                ·
                  refine ⟨6653308963471451218943941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8871078617961934958591921 6653308963471451218943941)
                  ·
                    refine ⟨1247495430650897103551989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6653308963471451218943941 1247495430650897103551989)
                    ·
                      rfl

theorem cell22_3644233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_3644233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644233 prefixEnd_3644233 := by exact prefixLift 3644233
  have htrace : WordTrace (prefixWord ++ tailWord_3644233) baseStart_3644233 baseEnd_3644233 := by
    simpa [prefixWord, tailWord_3644233, baseEnd_3644233] using wordTrace_append hprefix tailTrace_3644233
  have hstable : (prefixWord ++ tailWord_3644233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644233).length < 2 ^ (prefixWord ++ tailWord_3644233).sum := by decide
  have hdescent : baseEnd_3644233 < baseStart_3644233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644237 : List Nat := [1, 6, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3644237 : Nat := 118140960795 + 3644237 * 2 ^ 59
def prefixEnd_3644237 : Nat := 4983230072969 + 3 ^ 40 * 3644237 * 2
def baseEnd_3644237 : Nat := 415832266644214142150659

theorem tailTrace_3644237 : CollatzResearch.WordTrace tailWord_3644237 prefixEnd_3644237 415832266644214142150659 := by
  unfold tailWord_3644237
  simp only [CollatzResearch.WordTrace]
  refine ⟨132916242898559209974018965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88610828599039473316012643 132916242898559209974018965)
  ·
    refine ⟨6230448885869962967532139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132916242898559209974018965 6230448885869962967532139)
    ·
      refine ⟨9345673328804944451298209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6230448885869962967532139 9345673328804944451298209)
      ·
        refine ⟨7009254996603708338473657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9345673328804944451298209 7009254996603708338473657)
        ·
          refine ⟨5256941247452781253855243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7009254996603708338473657 5256941247452781253855243)
          ·
            refine ⟨7885411871179171880782865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256941247452781253855243 7885411871179171880782865)
            ·
              refine ⟨5914058903384378910587149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7885411871179171880782865 5914058903384378910587149)
              ·
                refine ⟨2217772088769142091470181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5914058903384378910587149 2217772088769142091470181)
                ·
                  refine ⟨415832266644214142150659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217772088769142091470181 415832266644214142150659)
                  ·
                    rfl

theorem cell22_3644237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3644237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644237 prefixEnd_3644237 := by exact prefixLift 3644237
  have htrace : WordTrace (prefixWord ++ tailWord_3644237) baseStart_3644237 baseEnd_3644237 := by
    simpa [prefixWord, tailWord_3644237, baseEnd_3644237] using wordTrace_append hprefix tailTrace_3644237
  have hstable : (prefixWord ++ tailWord_3644237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644237).length < 2 ^ (prefixWord ++ tailWord_3644237).sum := by decide
  have hdescent : baseEnd_3644237 < baseStart_3644237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644252 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3644252 : Nat := 118140960795 + 3644252 * 2 ^ 59
def prefixEnd_3644252 : Nat := 4983230072969 + 3 ^ 40 * 3644252 * 2
def baseEnd_3644252 : Nat := 1247501934739187387326931

theorem tailTrace_3644252 : CollatzResearch.WordTrace tailWord_3644252 prefixEnd_3644252 1247501934739187387326931 := by
  unfold tailWord_3644252
  simp only [CollatzResearch.WordTrace]
  refine ⟨66458394996752433767907505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88611193329003245023876673 66458394996752433767907505)
  ·
    refine ⟨49843796247564325325930629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66458394996752433767907505 49843796247564325325930629)
    ·
      refine ⟨9345711796418310998611993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49843796247564325325930629 9345711796418310998611993)
      ·
        refine ⟨7009283847313733248958995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9345711796418310998611993 7009283847313733248958995)
        ·
          refine ⟨10513925770970599873438493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7009283847313733248958995 10513925770970599873438493)
          ·
            refine ⟨3942722164113974952539435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10513925770970599873438493 3942722164113974952539435)
            ·
              refine ⟨5914083246170962428809153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942722164113974952539435 5914083246170962428809153)
              ·
                refine ⟨4435562434628221821606865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5914083246170962428809153 4435562434628221821606865)
                ·
                  refine ⟨3326671825971166366205149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4435562434628221821606865 3326671825971166366205149)
                  ·
                    refine ⟨1247501934739187387326931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326671825971166366205149 1247501934739187387326931)
                    ·
                      rfl

theorem cell22_3644252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3644252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644252 prefixEnd_3644252 := by exact prefixLift 3644252
  have htrace : WordTrace (prefixWord ++ tailWord_3644252) baseStart_3644252 baseEnd_3644252 := by
    simpa [prefixWord, tailWord_3644252, baseEnd_3644252] using wordTrace_append hprefix tailTrace_3644252
  have hstable : (prefixWord ++ tailWord_3644252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644252).length < 2 ^ (prefixWord ++ tailWord_3644252).sum := by decide
  have hdescent : baseEnd_3644252 < baseStart_3644252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644263 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3644263 : Nat := 118140960795 + 3644263 * 2 ^ 59
def prefixEnd_3644263 : Nat := 4983230072969 + 3 ^ 40 * 3644263 * 2
def baseEnd_3644263 : Nat := 1247505700263987025301897

theorem tailTrace_3644263 : CollatzResearch.WordTrace tailWord_3644263 prefixEnd_3644263 1247505700263987025301897 := by
  unfold tailWord_3644263
  simp only [CollatzResearch.WordTrace]
  refine ⟨132917191196465016414465443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88611460797643344276310295 132917191196465016414465443)
  ·
    refine ⟨199375786794697524621698165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132917191196465016414465443 199375786794697524621698165)
    ·
      refine ⟨18691480012002892933284203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199375786794697524621698165 18691480012002892933284203)
      ·
        refine ⟨28037220018004339399926305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18691480012002892933284203 28037220018004339399926305)
        ·
          refine ⟨21027915013503254549944729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28037220018004339399926305 21027915013503254549944729)
          ·
            refine ⟨15770936260127440912458547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21027915013503254549944729 15770936260127440912458547)
            ·
              refine ⟨23656404390191161368687821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15770936260127440912458547 23656404390191161368687821)
              ·
                refine ⟨8871151646321685513257933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23656404390191161368687821 8871151646321685513257933)
                ·
                  refine ⟨3326681867370632067471725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8871151646321685513257933 3326681867370632067471725)
                  ·
                    refine ⟨1247505700263987025301897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326681867370632067471725 1247505700263987025301897)
                    ·
                      rfl

theorem cell22_3644263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3644263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644263 prefixEnd_3644263 := by exact prefixLift 3644263
  have htrace : WordTrace (prefixWord ++ tailWord_3644263) baseStart_3644263 baseEnd_3644263 := by
    simpa [prefixWord, tailWord_3644263, baseEnd_3644263] using wordTrace_append hprefix tailTrace_3644263
  have hstable : (prefixWord ++ tailWord_3644263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644263).length < 2 ^ (prefixWord ++ tailWord_3644263).sum := by decide
  have hdescent : baseEnd_3644263 < baseStart_3644263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644297 : List Nat := [1, 2, 1, 1, 5, 4, 1, 3, 1, 3]
def baseStart_3644297 : Nat := 118140960795 + 3644297 * 2 ^ 59
def prefixEnd_3644297 : Nat := 4983230072969 + 3 ^ 40 * 3644297 * 2
def baseEnd_3644297 : Nat := 1247517339158822269951793

theorem tailTrace_3644297 : CollatzResearch.WordTrace tailWord_3644297 prefixEnd_3644297 1247517339158822269951793 := by
  unfold tailWord_3644297
  simp only [CollatzResearch.WordTrace]
  refine ⟨132918431278341840221203145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88612287518894560147468763 132918431278341840221203145)
  ·
    refine ⟨99688823458756380165902359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132918431278341840221203145 99688823458756380165902359)
    ·
      refine ⟨149533235188134570248853539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99688823458756380165902359 149533235188134570248853539)
      ·
        refine ⟨224299852782201855373280309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149533235188134570248853539 224299852782201855373280309)
        ·
          refine ⟨21028111198331423941245029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224299852782201855373280309 21028111198331423941245029)
          ·
            refine ⟨3942770849687141988983443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21028111198331423941245029 3942770849687141988983443)
            ·
              refine ⟨5914156274530712983475165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942770849687141988983443 5914156274530712983475165)
              ·
                refine ⟨2217808602949017368803187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5914156274530712983475165 2217808602949017368803187)
                ·
                  refine ⟨3326712904423526053204781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217808602949017368803187 3326712904423526053204781)
                  ·
                    refine ⟨1247517339158822269951793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326712904423526053204781 1247517339158822269951793)
                    ·
                      rfl

theorem cell22_3644297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 3].length) (baseStart_3644297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644297 prefixEnd_3644297 := by exact prefixLift 3644297
  have htrace : WordTrace (prefixWord ++ tailWord_3644297) baseStart_3644297 baseEnd_3644297 := by
    simpa [prefixWord, tailWord_3644297, baseEnd_3644297] using wordTrace_append hprefix tailTrace_3644297
  have hstable : (prefixWord ++ tailWord_3644297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644297).length < 2 ^ (prefixWord ++ tailWord_3644297).sum := by decide
  have hdescent : baseEnd_3644297 < baseStart_3644297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644314 : List Nat := [3, 1, 1, 4, 3, 1, 3, 2, 1, 3]
def baseStart_3644314 : Nat := 118140960795 + 3644314 * 2 ^ 59
def prefixEnd_3644314 : Nat := 4983230072969 + 3 ^ 40 * 3644314 * 2
def baseEnd_3644314 : Nat := 1247523158606239892276741

theorem tailTrace_3644314 : CollatzResearch.WordTrace tailWord_3644314 prefixEnd_3644314 1247523158606239892276741 := by
  unfold tailWord_3644314
  simp only [CollatzResearch.WordTrace]
  refine ⟨33229762829820063031142999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88612700879520168083047997 33229762829820063031142999)
  ·
    refine ⟨49844644244730094546714499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33229762829820063031142999 49844644244730094546714499)
    ·
      refine ⟨74766966367095141820071749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49844644244730094546714499 74766966367095141820071749)
      ·
        refine ⟨14018806193830339091263453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74766966367095141820071749 14018806193830339091263453)
        ·
          refine ⟨5257052322686377159223795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14018806193830339091263453 5257052322686377159223795)
          ·
            refine ⟨7885578484029565738835693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257052322686377159223795 7885578484029565738835693)
            ·
              refine ⟨2957091931511087152063385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7885578484029565738835693 2957091931511087152063385)
              ·
                refine ⟨2217818948633315364047539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957091931511087152063385 2217818948633315364047539)
                ·
                  refine ⟨3326728422949973046071309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217818948633315364047539 3326728422949973046071309)
                  ·
                    refine ⟨1247523158606239892276741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326728422949973046071309 1247523158606239892276741)
                    ·
                      rfl

theorem cell22_3644314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_3644314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644314 prefixEnd_3644314 := by exact prefixLift 3644314
  have htrace : WordTrace (prefixWord ++ tailWord_3644314) baseStart_3644314 baseEnd_3644314 := by
    simpa [prefixWord, tailWord_3644314, baseEnd_3644314] using wordTrace_append hprefix tailTrace_3644314
  have hstable : (prefixWord ++ tailWord_3644314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644314).length < 2 ^ (prefixWord ++ tailWord_3644314).sum := by decide
  have hdescent : baseEnd_3644314 < baseStart_3644314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644327 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 5]
def baseStart_3644327 : Nat := 118140960795 + 3644327 * 2 ^ 59
def prefixEnd_3644327 : Nat := 4983230072969 + 3 ^ 40 * 3644327 * 2
def baseEnd_3644327 : Nat := 415842536257304063900567

theorem tailTrace_3644327 : CollatzResearch.WordTrace tailWord_3644327 prefixEnd_3644327 415842536257304063900567 := by
  unfold tailWord_3644327
  simp only [CollatzResearch.WordTrace]
  refine ⟨132919525468233155344795235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88613016978822103563196823 132919525468233155344795235)
  ·
    refine ⟨199379288202349733017192853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132919525468233155344795235 199379288202349733017192853)
    ·
      refine ⟨9345904134485143735180915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199379288202349733017192853 9345904134485143735180915)
      ·
        refine ⟨14018856201727715602771373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9345904134485143735180915 14018856201727715602771373)
        ·
          refine ⟨5257071075647893351039265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14018856201727715602771373 5257071075647893351039265)
          ·
            refine ⟨3942803306735920013279449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5257071075647893351039265 3942803306735920013279449)
            ·
              refine ⟨2957102480051940009959587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3942803306735920013279449 2957102480051940009959587)
              ·
                refine ⟨4435653720077910014939381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957102480051940009959587 4435653720077910014939381)
                ·
                  refine ⟨415842536257304063900567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4435653720077910014939381 415842536257304063900567)
                  ·
                    rfl

theorem cell22_3644327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 5].length) (baseStart_3644327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644327 prefixEnd_3644327 := by exact prefixLift 3644327
  have htrace : WordTrace (prefixWord ++ tailWord_3644327) baseStart_3644327 baseEnd_3644327 := by
    simpa [prefixWord, tailWord_3644327, baseEnd_3644327] using wordTrace_append hprefix tailTrace_3644327
  have hstable : (prefixWord ++ tailWord_3644327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644327).length < 2 ^ (prefixWord ++ tailWord_3644327).sum := by decide
  have hdescent : baseEnd_3644327 < baseStart_3644327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644365 : List Nat := [1, 6, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3644365 : Nat := 118140960795 + 3644365 * 2 ^ 59
def prefixEnd_3644365 : Nat := 4983230072969 + 3 ^ 40 * 3644365 * 2
def baseEnd_3644365 : Nat := 1247540616948492759251585

theorem tailTrace_3644365 : CollatzResearch.WordTrace tailWord_3644365 prefixEnd_3644365 1247540616948492759251585 := by
  unfold tailWord_3644365
  simp only [CollatzResearch.WordTrace]
  refine ⟨132920911442095487834678549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88613940961396991889785699 132920911442095487834678549)
  ·
    refine ⟨6230667723848225992250557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132920911442095487834678549 6230667723848225992250557)
    ·
      refine ⟨2336500396443084747093959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6230667723848225992250557 2336500396443084747093959)
      ·
        refine ⟨3504750594664627120640939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336500396443084747093959 3504750594664627120640939)
        ·
          refine ⟨5257125891996940680961409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504750594664627120640939 5257125891996940680961409)
          ·
            refine ⟨3942844418997705510721057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5257125891996940680961409 3942844418997705510721057)
            ·
              refine ⟨2957133314248279133040793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3942844418997705510721057 2957133314248279133040793)
              ·
                refine ⟨2217849985686209349780595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957133314248279133040793 2217849985686209349780595)
                ·
                  refine ⟨3326774978529314024670893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217849985686209349780595 3326774978529314024670893)
                  ·
                    refine ⟨1247540616948492759251585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326774978529314024670893 1247540616948492759251585)
                    ·
                      rfl

theorem cell22_3644365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3644365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644365 prefixEnd_3644365 := by exact prefixLift 3644365
  have htrace : WordTrace (prefixWord ++ tailWord_3644365) baseStart_3644365 baseEnd_3644365 := by
    simpa [prefixWord, tailWord_3644365, baseEnd_3644365] using wordTrace_append hprefix tailTrace_3644365
  have hstable : (prefixWord ++ tailWord_3644365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644365).length < 2 ^ (prefixWord ++ tailWord_3644365).sum := by decide
  have hdescent : baseEnd_3644365 < baseStart_3644365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644366 : List Nat := [4, 1, 1, 1, 2, 13]
def baseStart_3644366 : Nat := 118140960795 + 3644366 * 2 ^ 59
def prefixEnd_3644366 : Nat := 4983230072969 + 3 ^ 40 * 3644366 * 2
def baseEnd_3644366 : Nat := 15401740237888013456501

theorem tailTrace_3644366 : CollatzResearch.WordTrace tailWord_3644366 prefixEnd_3644366 15401740237888013456501 := by
  unfold tailWord_3644366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16615118489386483125683119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88613965276727910003643301 16615118489386483125683119)
  ·
    refine ⟨24922677734079724688524679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16615118489386483125683119 24922677734079724688524679)
    ·
      refine ⟨37384016601119587032787019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24922677734079724688524679 37384016601119587032787019)
      ·
        refine ⟨56076024901679380549180529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37384016601119587032787019 56076024901679380549180529)
        ·
          refine ⟨42057018676259535411885397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56076024901679380549180529 42057018676259535411885397)
          ·
            refine ⟨15401740237888013456501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 42057018676259535411885397 15401740237888013456501)
            ·
              rfl

theorem cell22_3644366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 13].length) (baseStart_3644366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644366 prefixEnd_3644366 := by exact prefixLift 3644366
  have htrace : WordTrace (prefixWord ++ tailWord_3644366) baseStart_3644366 baseEnd_3644366 := by
    simpa [prefixWord, tailWord_3644366, baseEnd_3644366] using wordTrace_append hprefix tailTrace_3644366
  have hstable : (prefixWord ++ tailWord_3644366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644366).length < 2 ^ (prefixWord ++ tailWord_3644366).sum := by decide
  have hdescent : baseEnd_3644366 < baseStart_3644366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644372 : List Nat := [2, 4, 1, 2, 1, 2, 4, 2, 4]
def baseStart_3644372 : Nat := 118140960795 + 3644372 * 2 ^ 59
def prefixEnd_3644372 : Nat := 4983230072969 + 3 ^ 40 * 3644372 * 2
def baseEnd_3644372 : Nat := 415847671063849024775521

theorem tailTrace_3644372 : CollatzResearch.WordTrace tailWord_3644372 prefixEnd_3644372 415847671063849024775521 := by
  unfold tailWord_3644372
  simp only [CollatzResearch.WordTrace]
  refine ⟨66460583376535064015091685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88614111168713418686788913 66460583376535064015091685)
  ·
    refine ⟨12461359383100324502829691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66460583376535064015091685 12461359383100324502829691)
    ·
      refine ⟨18692039074650486754244537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12461359383100324502829691 18692039074650486754244537)
      ·
        refine ⟨14019029305987865065683403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18692039074650486754244537 14019029305987865065683403)
        ·
          refine ⟨21028543958981797598525105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14019029305987865065683403 21028543958981797598525105)
          ·
            refine ⟨15771407969236348198893829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21028543958981797598525105 15771407969236348198893829)
            ·
              refine ⟨2957138994231815287292593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15771407969236348198893829 2957138994231815287292593)
              ·
                refine ⟨2217854245673861465469445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957138994231815287292593 2217854245673861465469445)
                ·
                  refine ⟨415847671063849024775521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217854245673861465469445 415847671063849024775521)
                  ·
                    rfl

theorem cell22_3644372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_3644372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644372 prefixEnd_3644372 := by exact prefixLift 3644372
  have htrace : WordTrace (prefixWord ++ tailWord_3644372) baseStart_3644372 baseEnd_3644372 := by
    simpa [prefixWord, tailWord_3644372, baseEnd_3644372] using wordTrace_append hprefix tailTrace_3644372
  have hstable : (prefixWord ++ tailWord_3644372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644372).length < 2 ^ (prefixWord ++ tailWord_3644372).sum := by decide
  have hdescent : baseEnd_3644372 < baseStart_3644372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644411 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 7]
def baseStart_3644411 : Nat := 118140960795 + 3644411 * 2 ^ 59
def prefixEnd_3644411 : Nat := 4983230072969 + 3 ^ 40 * 3644411 * 2
def baseEnd_3644411 : Nat := 415852121229521324200481

theorem tailTrace_3644411 : CollatzResearch.WordTrace tailWord_3644411 prefixEnd_3644411 415852121229521324200481 := by
  unfold tailWord_3644411
  simp only [CollatzResearch.WordTrace]
  refine ⟨132922589199928837690853087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88615059466619225127235391 132922589199928837690853087)
  ·
    refine ⟨199383883799893256536279631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132922589199928837690853087 199383883799893256536279631)
    ·
      refine ⟨299075825699839884804419447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199383883799893256536279631 299075825699839884804419447)
      ·
        refine ⟨448613738549759827206629171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299075825699839884804419447 448613738549759827206629171)
        ·
          refine ⟨672920607824639740809943757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448613738549759827206629171 672920607824639740809943757)
          ·
            refine ⟨252345227934239902803728909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 672920607824639740809943757 252345227934239902803728909)
            ·
              refine ⟨94629460475339963551398341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252345227934239902803728909 94629460475339963551398341)
              ·
                refine ⟨17743023839126243165887189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94629460475339963551398341 17743023839126243165887189)
                ·
                  refine ⟨415852121229521324200481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17743023839126243165887189 415852121229521324200481)
                  ·
                    rfl

theorem cell22_3644411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 7].length) (baseStart_3644411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644411 prefixEnd_3644411 := by exact prefixLift 3644411
  have htrace : WordTrace (prefixWord ++ tailWord_3644411) baseStart_3644411 baseEnd_3644411 := by
    simpa [prefixWord, tailWord_3644411, baseEnd_3644411] using wordTrace_append hprefix tailTrace_3644411
  have hstable : (prefixWord ++ tailWord_3644411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644411).length < 2 ^ (prefixWord ++ tailWord_3644411).sum := by decide
  have hdescent : baseEnd_3644411 < baseStart_3644411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644428 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 7]
def baseStart_3644428 : Nat := 118140960795 + 3644428 * 2 ^ 59
def prefixEnd_3644428 : Nat := 4983230072969 + 3 ^ 40 * 3644428 * 2
def baseEnd_3644428 : Nat := 415854061045327198308797

theorem tailTrace_3644428 : CollatzResearch.WordTrace tailWord_3644428 prefixEnd_3644428 415854061045327198308797 := by
  unfold tailWord_3644428
  simp only [CollatzResearch.WordTrace]
  refine ⟨66461604620433624797110969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88615472827244833062814625 66461604620433624797110969)
  ·
    refine ⟨49846203465325218597833227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66461604620433624797110969 49846203465325218597833227)
    ·
      refine ⟨74769305197987827896749841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49846203465325218597833227 74769305197987827896749841)
      ·
        refine ⟨56076978898490870922562381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74769305197987827896749841 56076978898490870922562381)
        ·
          refine ⟨21028867086934076595960893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56076978898490870922562381 21028867086934076595960893)
          ·
            refine ⟨7885825157600278723485335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21028867086934076595960893 7885825157600278723485335)
            ·
              refine ⟨11828737736400418085228003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7885825157600278723485335 11828737736400418085228003)
              ·
                refine ⟨17743106604600627127842005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11828737736400418085228003 17743106604600627127842005)
                ·
                  refine ⟨415854061045327198308797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17743106604600627127842005 415854061045327198308797)
                  ·
                    rfl

theorem cell22_3644428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_3644428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644428 prefixEnd_3644428 := by exact prefixLift 3644428
  have htrace : WordTrace (prefixWord ++ tailWord_3644428) baseStart_3644428 baseEnd_3644428 := by
    simpa [prefixWord, tailWord_3644428, baseEnd_3644428] using wordTrace_append hprefix tailTrace_3644428
  have hstable : (prefixWord ++ tailWord_3644428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644428).length < 2 ^ (prefixWord ++ tailWord_3644428).sum := by decide
  have hdescent : baseEnd_3644428 < baseStart_3644428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644490 : List Nat := [3, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_3644490 : Nat := 118140960795 + 3644490 * 2 ^ 59
def prefixEnd_3644490 : Nat := 4983230072969 + 3 ^ 40 * 3644490 * 2
def baseEnd_3644490 : Nat := 415861135667678033292067

theorem tailTrace_3644490 : CollatzResearch.WordTrace tailWord_3644490 prefixEnd_3644490 415861135667678033292067 := by
  unfold tailWord_3644490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33231367641660658545744731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88616980377761756121985949 33231367641660658545744731)
  ·
    refine ⟨49847051462490987818617097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33231367641660658545744731 49847051462490987818617097)
    ·
      refine ⟨37385288596868240863962823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49847051462490987818617097 37385288596868240863962823)
      ·
        refine ⟨56077932895302361295944235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37385288596868240863962823 56077932895302361295944235)
        ·
          refine ⟨84116899342953541943916353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56077932895302361295944235 84116899342953541943916353)
          ·
            refine ⟨63087674507215156457937265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84116899342953541943916353 63087674507215156457937265)
            ·
              refine ⟨47315755880411367343452949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63087674507215156457937265 47315755880411367343452949)
              ·
                refine ⟨2217926056894282844224357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47315755880411367343452949 2217926056894282844224357)
                ·
                  refine ⟨415861135667678033292067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217926056894282844224357 415861135667678033292067)
                  ·
                    rfl

theorem cell22_3644490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_3644490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644490 prefixEnd_3644490 := by exact prefixLift 3644490
  have htrace : WordTrace (prefixWord ++ tailWord_3644490) baseStart_3644490 baseEnd_3644490 := by
    simpa [prefixWord, tailWord_3644490, baseEnd_3644490] using wordTrace_append hprefix tailTrace_3644490
  have hstable : (prefixWord ++ tailWord_3644490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644490).length < 2 ^ (prefixWord ++ tailWord_3644490).sum := by decide
  have hdescent : baseEnd_3644490 < baseStart_3644490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644503 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 6, 4]
def baseStart_3644503 : Nat := 118140960795 + 3644503 * 2 ^ 59
def prefixEnd_3644503 : Nat := 4983230072969 + 3 ^ 40 * 3644503 * 2
def baseEnd_3644503 : Nat := 1247587857168706399301161

theorem tailTrace_3644503 : CollatzResearch.WordTrace tailWord_3644503 prefixEnd_3644503 1247587857168706399301161 := by
  unfold tailWord_3644503
  simp only [CollatzResearch.WordTrace]
  refine ⟨132925944715595537403202163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88617296477063691602134775 132925944715595537403202163)
  ·
    refine ⟨199388917073393306104803245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132925944715595537403202163 199388917073393306104803245)
    ·
      refine ⟨74770843902522489789301217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199388917073393306104803245 74770843902522489789301217)
      ·
        refine ⟨56078132926891867341975913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74770843902522489789301217 56078132926891867341975913)
        ·
          refine ⟨42058599695168900506481935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56078132926891867341975913 42058599695168900506481935)
          ·
            refine ⟨63087899542753350759722903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42058599695168900506481935 63087899542753350759722903)
            ·
              refine ⟨94631849314130026139584355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63087899542753350759722903 94631849314130026139584355)
              ·
                refine ⟨141947773971195039209376533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94631849314130026139584355 141947773971195039209376533)
                ·
                  refine ⟨6653801904899767462939525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141947773971195039209376533 6653801904899767462939525)
                  ·
                    refine ⟨1247587857168706399301161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6653801904899767462939525 1247587857168706399301161)
                    ·
                      rfl

theorem cell22_3644503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3644503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644503 prefixEnd_3644503 := by exact prefixLift 3644503
  have htrace : WordTrace (prefixWord ++ tailWord_3644503) baseStart_3644503 baseEnd_3644503 := by
    simpa [prefixWord, tailWord_3644503, baseEnd_3644503] using wordTrace_append hprefix tailTrace_3644503
  have hstable : (prefixWord ++ tailWord_3644503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644503).length < 2 ^ (prefixWord ++ tailWord_3644503).sum := by decide
  have hdescent : baseEnd_3644503 < baseStart_3644503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644552 : List Nat := [2, 1, 3, 4, 2, 2, 1, 7]
def baseStart_3644552 : Nat := 118140960795 + 3644552 * 2 ^ 59
def prefixEnd_3644552 : Nat := 4983230072969 + 3 ^ 40 * 3644552 * 2
def baseEnd_3644552 : Nat := 138622736763342956091779

theorem tailTrace_3644552 : CollatzResearch.WordTrace tailWord_3644552 prefixEnd_3644552 138622736763342956091779 := by
  unfold tailWord_3644552
  simp only [CollatzResearch.WordTrace]
  refine ⟨66463865946209009385867955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88618487928278679181157273 66463865946209009385867955)
  ·
    refine ⟨99695798919313514078801933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66463865946209009385867955 99695798919313514078801933)
    ·
      refine ⟨37385924594742567779550725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99695798919313514078801933 37385924594742567779550725)
      ·
        refine ⟨7009860861514231458665761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37385924594742567779550725 7009860861514231458665761)
        ·
          refine ⟨5257395646135673593999321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7009860861514231458665761 5257395646135673593999321)
          ·
            refine ⟨3943046734601755195499491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5257395646135673593999321 3943046734601755195499491)
            ·
              refine ⟨5914570101902632793249237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943046734601755195499491 5914570101902632793249237)
              ·
                refine ⟨138622736763342956091779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5914570101902632793249237 138622736763342956091779)
                ·
                  rfl

theorem cell22_3644552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 7].length) (baseStart_3644552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644552 prefixEnd_3644552 := by exact prefixLift 3644552
  have htrace : WordTrace (prefixWord ++ tailWord_3644552) baseStart_3644552 baseEnd_3644552 := by
    simpa [prefixWord, tailWord_3644552, baseEnd_3644552] using wordTrace_append hprefix tailTrace_3644552
  have hstable : (prefixWord ++ tailWord_3644552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644552).length < 2 ^ (prefixWord ++ tailWord_3644552).sum := by decide
  have hdescent : baseEnd_3644552 < baseStart_3644552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644567 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 3, 3]
def baseStart_3644567 : Nat := 118140960795 + 3644567 * 2 ^ 59
def prefixEnd_3644567 : Nat := 4983230072969 + 3 ^ 40 * 3644567 * 2
def baseEnd_3644567 : Nat := 1247609765676631565700965

theorem tailTrace_3644567 : CollatzResearch.WordTrace tailWord_3644567 prefixEnd_3644567 1247609765676631565700965 := by
  unfold tailWord_3644567
  simp only [CollatzResearch.WordTrace]
  refine ⟨132928278987363676333531955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88618852658242450889021303 132928278987363676333531955)
  ·
    refine ⟨199392418481045514500297933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132928278987363676333531955 199392418481045514500297933)
    ·
      refine ⟨74772156930392067937611725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199392418481045514500297933 74772156930392067937611725)
      ·
        refine ⟨28039558848897025476604397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74772156930392067937611725 28039558848897025476604397)
        ·
          refine ⟨10514834568336384553726649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28039558848897025476604397 10514834568336384553726649)
          ·
            refine ⟨7886125926252288415294987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10514834568336384553726649 7886125926252288415294987)
            ·
              refine ⟨11829188889378432622942481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886125926252288415294987 11829188889378432622942481)
              ·
                refine ⟨8871891667033824467206861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11829188889378432622942481 8871891667033824467206861)
                ·
                  refine ⟨3326959375137684175202573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8871891667033824467206861 3326959375137684175202573)
                  ·
                    refine ⟨1247609765676631565700965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3326959375137684175202573 1247609765676631565700965)
                    ·
                      rfl

theorem cell22_3644567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_3644567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644567 prefixEnd_3644567 := by exact prefixLift 3644567
  have htrace : WordTrace (prefixWord ++ tailWord_3644567) baseStart_3644567 baseEnd_3644567 := by
    simpa [prefixWord, tailWord_3644567, baseEnd_3644567] using wordTrace_append hprefix tailTrace_3644567
  have hstable : (prefixWord ++ tailWord_3644567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644567).length < 2 ^ (prefixWord ++ tailWord_3644567).sum := by decide
  have hdescent : baseEnd_3644567 < baseStart_3644567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644657 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 2, 3]
def baseStart_3644657 : Nat := 118140960795 + 3644657 * 2 ^ 59
def prefixEnd_3644657 : Nat := 4983230072969 + 3 ^ 40 * 3644657 * 2
def baseEnd_3644657 : Nat := 1247640574515901330950689

theorem tailTrace_3644657 : CollatzResearch.WordTrace tailWord_3644657 prefixEnd_3644657 1247640574515901330950689 := by
  unfold tailWord_3644657
  simp only [CollatzResearch.WordTrace]
  refine ⟨132931561557037621704308225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88621041038025081136205483 132931561557037621704308225)
  ·
    refine ⟨99698671167778216278231169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132931561557037621704308225 99698671167778216278231169)
    ·
      refine ⟨74774003375833662208673377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99698671167778216278231169 74774003375833662208673377)
      ·
        refine ⟨56080502531875246656505033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74774003375833662208673377 56080502531875246656505033)
        ·
          refine ⟨42060376898906434992378775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56080502531875246656505033 42060376898906434992378775)
          ·
            refine ⟨63090565348359652488568163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42060376898906434992378775 63090565348359652488568163)
            ·
              refine ⟨94635848022539478732852245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63090565348359652488568163 94635848022539478732852245)
              ·
                refine ⟨4436055376056538065602449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94635848022539478732852245 4436055376056538065602449)
                ·
                  refine ⟨3327041532042403549201837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4436055376056538065602449 3327041532042403549201837)
                  ·
                    refine ⟨1247640574515901330950689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327041532042403549201837 1247640574515901330950689)
                    ·
                      rfl

theorem cell22_3644657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_3644657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644657 prefixEnd_3644657 := by exact prefixLift 3644657
  have htrace : WordTrace (prefixWord ++ tailWord_3644657) baseStart_3644657 baseEnd_3644657 := by
    simpa [prefixWord, tailWord_3644657, baseEnd_3644657] using wordTrace_append hprefix tailTrace_3644657
  have hstable : (prefixWord ++ tailWord_3644657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644657).length < 2 ^ (prefixWord ++ tailWord_3644657).sum := by decide
  have hdescent : baseEnd_3644657 < baseStart_3644657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644659 : List Nat := [1, 1, 1, 2, 2, 6, 3, 2, 4]
def baseStart_3644659 : Nat := 118140960795 + 3644659 * 2 ^ 59
def prefixEnd_3644659 : Nat := 4983230072969 + 3 ^ 40 * 3644659 * 2
def baseEnd_3644659 : Nat := 415880419718924664133561

theorem tailTrace_3644659 : CollatzResearch.WordTrace tailWord_3644659 prefixEnd_3644659 415880419718924664133561 := by
  unfold tailWord_3644659
  simp only [CollatzResearch.WordTrace]
  refine ⟨132931634503030376045881031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88621089668686917363920687 132931634503030376045881031)
  ·
    refine ⟨199397451754545564068821547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132931634503030376045881031 199397451754545564068821547)
    ·
      refine ⟨299096177631818346103232321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199397451754545564068821547 299096177631818346103232321)
      ·
        refine ⟨224322133223863759577424241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299096177631818346103232321 224322133223863759577424241)
        ·
          refine ⟨168241599917897819683068181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224322133223863759577424241 168241599917897819683068181)
          ·
            refine ⟨7886324996151460297643821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168241599917897819683068181 7886324996151460297643821)
            ·
              refine ⟨2957371873556797611616433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7886324996151460297643821 2957371873556797611616433)
              ·
                refine ⟨2218028905167598208712325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957371873556797611616433 2218028905167598208712325)
                ·
                  refine ⟨415880419718924664133561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2218028905167598208712325 415880419718924664133561)
                  ·
                    rfl

theorem cell22_3644659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 4].length) (baseStart_3644659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644659 prefixEnd_3644659 := by exact prefixLift 3644659
  have htrace : WordTrace (prefixWord ++ tailWord_3644659) baseStart_3644659 baseEnd_3644659 := by
    simpa [prefixWord, tailWord_3644659, baseEnd_3644659] using wordTrace_append hprefix tailTrace_3644659
  have hstable : (prefixWord ++ tailWord_3644659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644659).length < 2 ^ (prefixWord ++ tailWord_3644659).sum := by decide
  have hdescent : baseEnd_3644659 < baseStart_3644659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644732 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 5]
def baseStart_3644732 : Nat := 118140960795 + 3644732 * 2 ^ 59
def prefixEnd_3644732 : Nat := 4983230072969 + 3 ^ 40 * 3644732 * 2
def baseEnd_3644732 : Nat := 415888749516208711775153

theorem tailTrace_3644732 : CollatzResearch.WordTrace tailWord_3644732 prefixEnd_3644732 415888749516208711775153 := by
  unfold tailWord_3644732
  simp only [CollatzResearch.WordTrace]
  refine ⟨66467148515882954756644225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88622864687843939675525633 66467148515882954756644225)
  ·
    refine ⟨49850361386912216067483169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66467148515882954756644225 49850361386912216067483169)
    ·
      refine ⟨37387771040184162050612377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49850361386912216067483169 37387771040184162050612377)
      ·
        refine ⟨28040828280138121537959283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37387771040184162050612377 28040828280138121537959283)
        ·
          refine ⟨42061242420207182306938925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28040828280138121537959283 42061242420207182306938925)
          ·
            refine ⟨15772965907577693365102097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42061242420207182306938925 15772965907577693365102097)
            ·
              refine ⟨11829724430683270023826573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15772965907577693365102097 11829724430683270023826573)
              ·
                refine ⟨4436146661506226258934965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11829724430683270023826573 4436146661506226258934965)
                ·
                  refine ⟨415888749516208711775153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4436146661506226258934965 415888749516208711775153)
                  ·
                    rfl

theorem cell22_3644732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_3644732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644732 prefixEnd_3644732 := by exact prefixLift 3644732
  have htrace : WordTrace (prefixWord ++ tailWord_3644732) baseStart_3644732 baseEnd_3644732 := by
    simpa [prefixWord, tailWord_3644732, baseEnd_3644732] using wordTrace_append hprefix tailTrace_3644732
  have hstable : (prefixWord ++ tailWord_3644732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644732).length < 2 ^ (prefixWord ++ tailWord_3644732).sum := by decide
  have hdescent : baseEnd_3644732 < baseStart_3644732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644760 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 8]
def baseStart_3644760 : Nat := 118140960795 + 3644760 * 2 ^ 59
def prefixEnd_3644760 : Nat := 4983230072969 + 3 ^ 40 * 3644760 * 2
def baseEnd_3644760 : Nat := 415891944506947798541791

theorem tailTrace_3644760 : CollatzResearch.WordTrace tailWord_3644760 prefixEnd_3644760 415891944506947798541791 := by
  unfold tailWord_3644760
  simp only [CollatzResearch.WordTrace]
  refine ⟨66467659137832235147653867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88623545517109646863538489 66467659137832235147653867)
  ·
    refine ⟨99701488706748352721480801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66467659137832235147653867 99701488706748352721480801)
    ·
      refine ⟨74776116530061264541110601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99701488706748352721480801 74776116530061264541110601)
      ·
        refine ⟨56082087397545948405832951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74776116530061264541110601 56082087397545948405832951)
        ·
          refine ⟨84123131096318922608749427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56082087397545948405832951 84123131096318922608749427)
          ·
            refine ⟨126184696644478383913124141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84123131096318922608749427 126184696644478383913124141)
            ·
              refine ⟨47319261241679393967421553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126184696644478383913124141 47319261241679393967421553)
              ·
                refine ⟨35489445931259545475566165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47319261241679393967421553 35489445931259545475566165)
                ·
                  refine ⟨415891944506947798541791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35489445931259545475566165 415891944506947798541791)
                  ·
                    rfl

theorem cell22_3644760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_3644760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644760 prefixEnd_3644760 := by exact prefixLift 3644760
  have htrace : WordTrace (prefixWord ++ tailWord_3644760) baseStart_3644760 baseEnd_3644760 := by
    simpa [prefixWord, tailWord_3644760, baseEnd_3644760] using wordTrace_append hprefix tailTrace_3644760
  have hstable : (prefixWord ++ tailWord_3644760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644760).length < 2 ^ (prefixWord ++ tailWord_3644760).sum := by decide
  have hdescent : baseEnd_3644760 < baseStart_3644760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644807 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3644807 : Nat := 118140960795 + 3644807 * 2 ^ 59
def prefixEnd_3644807 : Nat := 4983230072969 + 3 ^ 40 * 3644807 * 2
def baseEnd_3644807 : Nat := 1247691922581350939700229

theorem tailTrace_3644807 : CollatzResearch.WordTrace tailWord_3644807 prefixEnd_3644807 1247691922581350939700229 := by
  unfold tailWord_3644807
  simp only [CollatzResearch.WordTrace]
  refine ⟨132937032506494197322268675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88624688337662798214845783 132937032506494197322268675)
  ·
    refine ⟨199405548759741295983403013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132937032506494197322268675 199405548759741295983403013)
    ·
      refine ⟨37388540392451492996888065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199405548759741295983403013 37388540392451492996888065)
      ·
        refine ⟨28041405294338619747666049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37388540392451492996888065 28041405294338619747666049)
        ·
          refine ⟨21031053970753964810749537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28041405294338619747666049 21031053970753964810749537)
          ·
            refine ⟨15773290478065473608062153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21031053970753964810749537 15773290478065473608062153)
            ·
              refine ⟨11829967858549105206046615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15773290478065473608062153 11829967858549105206046615)
              ·
                refine ⟨17744951787823657809069923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11829967858549105206046615 17744951787823657809069923)
                ·
                  refine ⟨26617427681735486713604885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17744951787823657809069923 26617427681735486713604885)
                  ·
                    refine ⟨1247691922581350939700229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26617427681735486713604885 1247691922581350939700229)
                    ·
                      rfl

theorem cell22_3644807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3644807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644807 prefixEnd_3644807 := by exact prefixLift 3644807
  have htrace : WordTrace (prefixWord ++ tailWord_3644807) baseStart_3644807 baseEnd_3644807 := by
    simpa [prefixWord, tailWord_3644807, baseEnd_3644807] using wordTrace_append hprefix tailTrace_3644807
  have hstable : (prefixWord ++ tailWord_3644807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644807).length < 2 ^ (prefixWord ++ tailWord_3644807).sum := by decide
  have hdescent : baseEnd_3644807 < baseStart_3644807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644828 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 6]
def baseStart_3644828 : Nat := 118140960795 + 3644828 * 2 ^ 59
def prefixEnd_3644828 : Nat := 4983230072969 + 3 ^ 40 * 3644828 * 2
def baseEnd_3644828 : Nat := 415899703770171294975055

theorem tailTrace_3644828 : CollatzResearch.WordTrace tailWord_3644828 prefixEnd_3644828 415899703770171294975055 := by
  unfold tailWord_3644828
  simp only [CollatzResearch.WordTrace]
  refine ⟨66468899219709058954391569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88625198959612078605855425 66468899219709058954391569)
  ·
    refine ⟨49851674414781794215793677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66468899219709058954391569 49851674414781794215793677)
    ·
      refine ⟨18694377905543172830922629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49851674414781794215793677 18694377905543172830922629)
      ·
        refine ⟨3505195857289344905797993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18694377905543172830922629 3505195857289344905797993)
        ·
          refine ⟨2628896892967008679348495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3505195857289344905797993 2628896892967008679348495)
          ·
            refine ⟨3943345339450513019022743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628896892967008679348495 3943345339450513019022743)
            ·
              refine ⟨5915018009175769528534115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943345339450513019022743 5915018009175769528534115)
              ·
                refine ⟨8872527013763654292801173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5915018009175769528534115 8872527013763654292801173)
                ·
                  refine ⟨415899703770171294975055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8872527013763654292801173 415899703770171294975055)
                  ·
                    rfl

theorem cell22_3644828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_3644828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644828 prefixEnd_3644828 := by exact prefixLift 3644828
  have htrace : WordTrace (prefixWord ++ tailWord_3644828) baseStart_3644828 baseEnd_3644828 := by
    simpa [prefixWord, tailWord_3644828, baseEnd_3644828] using wordTrace_append hprefix tailTrace_3644828
  have hstable : (prefixWord ++ tailWord_3644828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644828).length < 2 ^ (prefixWord ++ tailWord_3644828).sum := by decide
  have hdescent : baseEnd_3644828 < baseStart_3644828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644871 : List Nat := [1, 1, 4, 1, 1, 3, 2, 5, 1, 3]
def baseStart_3644871 : Nat := 118140960795 + 3644871 * 2 ^ 59
def prefixEnd_3644871 : Nat := 4983230072969 + 3 ^ 40 * 3644871 * 2
def baseEnd_3644871 : Nat := 1247713831089276106100033

theorem tailTrace_3644871 : CollatzResearch.WordTrace tailWord_3644871 prefixEnd_3644871 1247713831089276106100033 := by
  unfold tailWord_3644871
  simp only [CollatzResearch.WordTrace]
  refine ⟨132939366778262336252598467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88626244518841557501732311 132939366778262336252598467)
  ·
    refine ⟨199409050167393504378897701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132939366778262336252598467 199409050167393504378897701)
    ·
      refine ⟨37389196906386282071043319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199409050167393504378897701 37389196906386282071043319)
      ·
        refine ⟨56083795359579423106564979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37389196906386282071043319 56083795359579423106564979)
        ·
          refine ⟨84125693039369134659847469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56083795359579423106564979 84125693039369134659847469)
          ·
            refine ⟨31547134889763425497442801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84125693039369134659847469 31547134889763425497442801)
            ·
              refine ⟨23660351167322569123082101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31547134889763425497442801 23660351167322569123082101)
              ·
                refine ⟨2218157921936490855288947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23660351167322569123082101 2218157921936490855288947)
                ·
                  refine ⟨3327236882904736282933421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218157921936490855288947 3327236882904736282933421)
                  ·
                    refine ⟨1247713831089276106100033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327236882904736282933421 1247713831089276106100033)
                    ·
                      rfl

theorem cell22_3644871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_3644871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644871 prefixEnd_3644871 := by exact prefixLift 3644871
  have htrace : WordTrace (prefixWord ++ tailWord_3644871) baseStart_3644871 baseEnd_3644871 := by
    simpa [prefixWord, tailWord_3644871, baseEnd_3644871] using wordTrace_append hprefix tailTrace_3644871
  have hstable : (prefixWord ++ tailWord_3644871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644871).length < 2 ^ (prefixWord ++ tailWord_3644871).sum := by decide
  have hdescent : baseEnd_3644871 < baseStart_3644871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644888 : List Nat := [2, 1, 2, 2, 2, 1, 6, 2, 1, 3]
def baseStart_3644888 : Nat := 118140960795 + 3644888 * 2 ^ 59
def prefixEnd_3644888 : Nat := 4983230072969 + 3 ^ 40 * 3644888 * 2
def baseEnd_3644888 : Nat := 1247719650536693728424981

theorem tailTrace_3644888 : CollatzResearch.WordTrace tailWord_3644888 prefixEnd_3644888 1247719650536693728424981 := by
  unfold tailWord_3644888
  simp only [CollatzResearch.WordTrace]
  refine ⟨66469993409600374077983659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88626657879467165437311545 66469993409600374077983659)
  ·
    refine ⟨99704990114400561116975489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66469993409600374077983659 99704990114400561116975489)
    ·
      refine ⟨74778742585800420837731617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99704990114400561116975489 74778742585800420837731617)
      ·
        refine ⟨56084056939350315628298713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74778742585800420837731617 56084056939350315628298713)
        ·
          refine ⟨42063042704512736721224035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56084056939350315628298713 42063042704512736721224035)
          ·
            refine ⟨63094564056769105081836053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42063042704512736721224035 63094564056769105081836053)
            ·
              refine ⟨2957557690161051800711065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63094564056769105081836053 2957557690161051800711065)
              ·
                refine ⟨2218168267620788850533299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957557690161051800711065 2218168267620788850533299)
                ·
                  refine ⟨3327252401431183275799949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218168267620788850533299 3327252401431183275799949)
                  ·
                    refine ⟨1247719650536693728424981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327252401431183275799949 1247719650536693728424981)
                    ·
                      rfl

theorem cell22_3644888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_3644888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644888 prefixEnd_3644888 := by exact prefixLift 3644888
  have htrace : WordTrace (prefixWord ++ tailWord_3644888) baseStart_3644888 baseEnd_3644888 := by
    simpa [prefixWord, tailWord_3644888, baseEnd_3644888] using wordTrace_append hprefix tailTrace_3644888
  have hstable : (prefixWord ++ tailWord_3644888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644888).length < 2 ^ (prefixWord ++ tailWord_3644888).sum := by decide
  have hdescent : baseEnd_3644888 < baseStart_3644888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644899 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 2, 5]
def baseStart_3644899 : Nat := 118140960795 + 3644899 * 2 ^ 59
def prefixEnd_3644899 : Nat := 4983230072969 + 3 ^ 40 * 3644899 * 2
def baseEnd_3644899 : Nat := 1247723416061493366399947

theorem tailTrace_3644899 : CollatzResearch.WordTrace tailWord_3644899 prefixEnd_3644899 1247723416061493366399947 := by
  unfold tailWord_3644899
  simp only [CollatzResearch.WordTrace]
  refine ⟨132940388022160897034617751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88626925348107264689745167 132940388022160897034617751)
  ·
    refine ⟨199410582033241345551926627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132940388022160897034617751 199410582033241345551926627)
    ·
      refine ⟨299115873049862018327889941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199410582033241345551926627 299115873049862018327889941)
      ·
        refine ⟨14021056549212282109119841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 299115873049862018327889941 14021056549212282109119841)
        ·
          refine ⟨10515792411909211581839881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14021056549212282109119841 10515792411909211581839881)
          ·
            refine ⟨7886844308931908686379911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10515792411909211581839881 7886844308931908686379911)
            ·
              refine ⟨11830266463397863029569867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886844308931908686379911 11830266463397863029569867)
              ·
                refine ⟨17745399695096794544354801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11830266463397863029569867 17745399695096794544354801)
                ·
                  refine ⟨13309049771322595908266101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17745399695096794544354801 13309049771322595908266101)
                  ·
                    refine ⟨1247723416061493366399947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13309049771322595908266101 1247723416061493366399947)
                    ·
                      rfl

theorem cell22_3644899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 5].length) (baseStart_3644899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644899 prefixEnd_3644899 := by exact prefixLift 3644899
  have htrace : WordTrace (prefixWord ++ tailWord_3644899) baseStart_3644899 baseEnd_3644899 := by
    simpa [prefixWord, tailWord_3644899, baseEnd_3644899] using wordTrace_append hprefix tailTrace_3644899
  have hstable : (prefixWord ++ tailWord_3644899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644899).length < 2 ^ (prefixWord ++ tailWord_3644899).sum := by decide
  have hdescent : baseEnd_3644899 < baseStart_3644899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644912 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 8]
def baseStart_3644912 : Nat := 118140960795 + 3644912 * 2 ^ 59
def prefixEnd_3644912 : Nat := 4983230072969 + 3 ^ 40 * 3644912 * 2
def baseEnd_3644912 : Nat := 415909288742388555274969

theorem tailTrace_3644912 : CollatzResearch.WordTrace tailWord_3644912 prefixEnd_3644912 415909288742388555274969 := by
  unfold tailWord_3644912
  simp only [CollatzResearch.WordTrace]
  refine ⟨66470431085556900127420495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88627241447409200169893993 66470431085556900127420495)
  ·
    refine ⟨99705646628335350191130743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66470431085556900127420495 99705646628335350191130743)
    ·
      refine ⟨149558469942503025286696115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99705646628335350191130743 149558469942503025286696115)
      ·
        refine ⟨224337704913754537930044173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149558469942503025286696115 224337704913754537930044173)
        ·
          refine ⟨84126639342657951723766565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224337704913754537930044173 84126639342657951723766565)
          ·
            refine ⟨15773744876748365948206231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84126639342657951723766565 15773744876748365948206231)
            ·
              refine ⟨23660617315122548922309347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15773744876748365948206231 23660617315122548922309347)
              ·
                refine ⟨35490925972683823383464021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23660617315122548922309347 35490925972683823383464021)
                ·
                  refine ⟨415909288742388555274969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35490925972683823383464021 415909288742388555274969)
                  ·
                    rfl

theorem cell22_3644912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_3644912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644912 prefixEnd_3644912 := by exact prefixLift 3644912
  have htrace : WordTrace (prefixWord ++ tailWord_3644912) baseStart_3644912 baseEnd_3644912 := by
    simpa [prefixWord, tailWord_3644912, baseEnd_3644912] using wordTrace_append hprefix tailTrace_3644912
  have hstable : (prefixWord ++ tailWord_3644912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644912).length < 2 ^ (prefixWord ++ tailWord_3644912).sum := by decide
  have hdescent : baseEnd_3644912 < baseStart_3644912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644927 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 3, 5]
def baseStart_3644927 : Nat := 118140960795 + 3644927 * 2 ^ 59
def prefixEnd_3644927 : Nat := 4983230072969 + 3 ^ 40 * 3644927 * 2
def baseEnd_3644927 : Nat := 1247733001033710626699861

theorem tailTrace_3644927 : CollatzResearch.WordTrace tailWord_3644927 prefixEnd_3644927 1247733001033710626699861 := by
  unfold tailWord_3644927
  simp only [CollatzResearch.WordTrace]
  refine ⟨132941409266059457816637035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88627606177372971877758023 132941409266059457816637035)
  ·
    refine ⟨199412113899089186724955553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132941409266059457816637035 199412113899089186724955553)
    ·
      refine ⟨149559085424316890043716665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199412113899089186724955553 149559085424316890043716665)
      ·
        refine ⟨112169314068237667532787499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149559085424316890043716665 112169314068237667532787499)
        ·
          refine ⟨168253971102356501299181249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112169314068237667532787499 168253971102356501299181249)
          ·
            refine ⟨126190478326767375974385937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168253971102356501299181249 126190478326767375974385937)
            ·
              refine ⟨94642858745075531980789453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126190478326767375974385937 94642858745075531980789453)
              ·
                refine ⟨35491072029403324492796045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94642858745075531980789453 35491072029403324492796045)
                ·
                  refine ⟨13309152011026246684798517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35491072029403324492796045 13309152011026246684798517)
                  ·
                    refine ⟨1247733001033710626699861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13309152011026246684798517 1247733001033710626699861)
                    ·
                      rfl

theorem cell22_3644927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_3644927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644927 prefixEnd_3644927 := by exact prefixLift 3644927
  have htrace : WordTrace (prefixWord ++ tailWord_3644927) baseStart_3644927 baseEnd_3644927 := by
    simpa [prefixWord, tailWord_3644927, baseEnd_3644927] using wordTrace_append hprefix tailTrace_3644927
  have hstable : (prefixWord ++ tailWord_3644927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644927).length < 2 ^ (prefixWord ++ tailWord_3644927).sum := by decide
  have hdescent : baseEnd_3644927 < baseStart_3644927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644961 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 1, 5]
def baseStart_3644961 : Nat := 118140960795 + 3644961 * 2 ^ 59
def prefixEnd_3644961 : Nat := 4983230072969 + 3 ^ 40 * 3644961 * 2
def baseEnd_3644961 : Nat := 1247744639928545871349757

theorem tailTrace_3644961 : CollatzResearch.WordTrace tailWord_3644961 prefixEnd_3644961 1247744639928545871349757 := by
  unfold tailWord_3644961
  simp only [CollatzResearch.WordTrace]
  refine ⟨132942649347936281623374737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88628432898624187748916491 132942649347936281623374737)
  ·
    refine ⟨99706987010952211217531053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132942649347936281623374737 99706987010952211217531053)
    ·
      refine ⟨37390120129107079206574145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99706987010952211217531053 37390120129107079206574145)
      ·
        refine ⟨28042590096830309404930609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37390120129107079206574145 28042590096830309404930609)
        ·
          refine ⟨21031942572622732053697957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28042590096830309404930609 21031942572622732053697957)
          ·
            refine ⟨3943489232366762260068367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21031942572622732053697957 3943489232366762260068367)
            ·
              refine ⟨5915233848550143390102551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943489232366762260068367 5915233848550143390102551)
              ·
                refine ⟨8872850772825215085153827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5915233848550143390102551 8872850772825215085153827)
                ·
                  refine ⟨13309276159237822627730741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8872850772825215085153827 13309276159237822627730741)
                  ·
                    refine ⟨1247744639928545871349757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13309276159237822627730741 1247744639928545871349757)
                    ·
                      rfl

theorem cell22_3644961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_3644961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3644961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3644961 prefixEnd_3644961 := by exact prefixLift 3644961
  have htrace : WordTrace (prefixWord ++ tailWord_3644961) baseStart_3644961 baseEnd_3644961 := by
    simpa [prefixWord, tailWord_3644961, baseEnd_3644961] using wordTrace_append hprefix tailTrace_3644961
  have hstable : (prefixWord ++ tailWord_3644961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644961).length < 2 ^ (prefixWord ++ tailWord_3644961).sum := by decide
  have hdescent : baseEnd_3644961 < baseStart_3644961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645057 : List Nat := [1, 2, 4, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3645057 : Nat := 118140960795 + 3645057 * 2 ^ 59
def prefixEnd_3645057 : Nat := 4983230072969 + 3 ^ 40 * 3645057 * 2
def baseEnd_3645057 : Nat := 1247777502690433620949463

theorem tailTrace_3645057 : CollatzResearch.WordTrace tailWord_3645057 prefixEnd_3645057 1247777502690433620949463 := by
  unfold tailWord_3645057
  simp only [CollatzResearch.WordTrace]
  refine ⟨132946150755588490018869425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88630767170392326679246283 132946150755588490018869425)
  ·
    refine ⟨99709613066691367514152069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132946150755588490018869425 99709613066691367514152069)
    ·
      refine ⟨18695552450004631408903513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99709613066691367514152069 18695552450004631408903513)
      ·
        refine ⟨14021664337503473556677635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18695552450004631408903513 14021664337503473556677635)
        ·
          refine ⟨21032496506255210335016453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14021664337503473556677635 21032496506255210335016453)
          ·
            refine ⟨3943593094922851937815585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21032496506255210335016453 3943593094922851937815585)
            ·
              refine ⟨2957694821192138953361689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3943593094922851937815585 2957694821192138953361689)
              ·
                refine ⟨2218271115894104215021267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957694821192138953361689 2218271115894104215021267)
                ·
                  refine ⟨3327406673841156322531901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218271115894104215021267 3327406673841156322531901)
                  ·
                    refine ⟨1247777502690433620949463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327406673841156322531901 1247777502690433620949463)
                    ·
                      rfl

theorem cell22_3645057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3645057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645057 prefixEnd_3645057 := by exact prefixLift 3645057
  have htrace : WordTrace (prefixWord ++ tailWord_3645057) baseStart_3645057 baseEnd_3645057 := by
    simpa [prefixWord, tailWord_3645057, baseEnd_3645057] using wordTrace_append hprefix tailTrace_3645057
  have hstable : (prefixWord ++ tailWord_3645057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645057).length < 2 ^ (prefixWord ++ tailWord_3645057).sum := by decide
  have hdescent : baseEnd_3645057 < baseStart_3645057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645066 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_3645066 : Nat := 118140960795 + 3645066 * 2 ^ 59
def prefixEnd_3645066 : Nat := 4983230072969 + 3 ^ 40 * 3645066 * 2
def baseEnd_3645066 : Nat := 1247780583574360597474435

theorem tailTrace_3645066 : CollatzResearch.WordTrace tailWord_3645066 prefixEnd_3645066 1247780583574360597474435 := by
  unfold tailWord_3645066
  simp only [CollatzResearch.WordTrace]
  refine ⟨33236619753138971138986763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88630986008370589703964701 33236619753138971138986763)
  ·
    refine ⟨49854929629708456708480145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33236619753138971138986763 49854929629708456708480145)
    ·
      refine ⟨37391197222281342531360109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49854929629708456708480145 37391197222281342531360109)
      ·
        refine ⟨14021698958355503449260041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37391197222281342531360109 14021698958355503449260041)
        ·
          refine ⟨10516274218766627586945031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14021698958355503449260041 10516274218766627586945031)
          ·
            refine ⟨15774411328149941380417547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10516274218766627586945031 15774411328149941380417547)
            ·
              refine ⟨23661616992224912070626321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15774411328149941380417547 23661616992224912070626321)
              ·
                refine ⟨17746212744168684052969741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23661616992224912070626321 17746212744168684052969741)
                ·
                  refine ⟨6654829779063256519863653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17746212744168684052969741 6654829779063256519863653)
                  ·
                    refine ⟨1247780583574360597474435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6654829779063256519863653 1247780583574360597474435)
                    ·
                      rfl

theorem cell22_3645066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_3645066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645066 prefixEnd_3645066 := by exact prefixLift 3645066
  have htrace : WordTrace (prefixWord ++ tailWord_3645066) baseStart_3645066 baseEnd_3645066 := by
    simpa [prefixWord, tailWord_3645066, baseEnd_3645066] using wordTrace_append hprefix tailTrace_3645066
  have hstable : (prefixWord ++ tailWord_3645066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645066).length < 2 ^ (prefixWord ++ tailWord_3645066).sum := by decide
  have hdescent : baseEnd_3645066 < baseStart_3645066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645113 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 2, 3]
def baseStart_3645113 : Nat := 118140960795 + 3645113 * 2 ^ 59
def prefixEnd_3645113 : Nat := 4983230072969 + 3 ^ 40 * 3645113 * 2
def baseEnd_3645113 : Nat := 1247796672634868141549291

theorem tailTrace_3645113 : CollatzResearch.WordTrace tailWord_3645113 prefixEnd_3645113 1247796672634868141549291 := by
  unfold tailWord_3645113
  simp only [CollatzResearch.WordTrace]
  refine ⟨132948193243385611582907993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88632128828923741055271995 132948193243385611582907993)
  ·
    refine ⟨99711144932539208687180995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132948193243385611582907993 99711144932539208687180995)
    ·
      refine ⟨149566717398808813030771493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99711144932539208687180995 149566717398808813030771493)
      ·
        refine ⟨28043759512276652443269655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149566717398808813030771493 28043759512276652443269655)
        ·
          refine ⟨42065639268414978664904483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28043759512276652443269655 42065639268414978664904483)
          ·
            refine ⟨63098458902622467997356725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42065639268414978664904483 63098458902622467997356725)
            ·
              refine ⟨5915480522120856374752193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63098458902622467997356725 5915480522120856374752193)
              ·
                refine ⟨4436610391590642281064145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5915480522120856374752193 4436610391590642281064145)
                ·
                  refine ⟨3327457793692981710798109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4436610391590642281064145 3327457793692981710798109)
                  ·
                    refine ⟨1247796672634868141549291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327457793692981710798109 1247796672634868141549291)
                    ·
                      rfl

theorem cell22_3645113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_3645113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645113 prefixEnd_3645113 := by exact prefixLift 3645113
  have htrace : WordTrace (prefixWord ++ tailWord_3645113) baseStart_3645113 baseEnd_3645113 := by
    simpa [prefixWord, tailWord_3645113, baseEnd_3645113] using wordTrace_append hprefix tailTrace_3645113
  have hstable : (prefixWord ++ tailWord_3645113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645113).length < 2 ^ (prefixWord ++ tailWord_3645113).sum := by decide
  have hdescent : baseEnd_3645113 < baseStart_3645113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645130 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 1, 5]
def baseStart_3645130 : Nat := 118140960795 + 3645130 * 2 ^ 59
def prefixEnd_3645130 : Nat := 4983230072969 + 3 ^ 40 * 3645130 * 2
def baseEnd_3645130 : Nat := 1247802492082285763874239

theorem tailTrace_3645130 : CollatzResearch.WordTrace tailWord_3645130 prefixEnd_3645130 1247802492082285763874239 := by
  unfold tailWord_3645130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33237203321081005871569211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88632542189549348990851229 33237203321081005871569211)
  ·
    refine ⟨49855804981621508807353817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33237203321081005871569211 49855804981621508807353817)
    ·
      refine ⟨37391853736216131605515363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49855804981621508807353817 37391853736216131605515363)
      ·
        refine ⟨56087780604324197408273045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37391853736216131605515363 56087780604324197408273045)
        ·
          refine ⟨2629114715827696753512799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56087780604324197408273045 2629114715827696753512799)
          ·
            refine ⟨3943672073741545130269199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629114715827696753512799 3943672073741545130269199)
            ·
              refine ⟨5915508110612317695403799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943672073741545130269199 5915508110612317695403799)
              ·
                refine ⟨8873262165918476543105699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5915508110612317695403799 8873262165918476543105699)
                ·
                  refine ⟨13309893248877714814658549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8873262165918476543105699 13309893248877714814658549)
                  ·
                    refine ⟨1247802492082285763874239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13309893248877714814658549 1247802492082285763874239)
                    ·
                      rfl

theorem cell22_3645130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_3645130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645130 prefixEnd_3645130 := by exact prefixLift 3645130
  have htrace : WordTrace (prefixWord ++ tailWord_3645130) baseStart_3645130 baseEnd_3645130 := by
    simpa [prefixWord, tailWord_3645130, baseEnd_3645130] using wordTrace_append hprefix tailTrace_3645130
  have hstable : (prefixWord ++ tailWord_3645130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645130).length < 2 ^ (prefixWord ++ tailWord_3645130).sum := by decide
  have hdescent : baseEnd_3645130 < baseStart_3645130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645149 : List Nat := [1, 4, 3, 3, 2, 1, 1, 3, 4]
def baseStart_3645149 : Nat := 118140960795 + 3645149 * 2 ^ 59
def prefixEnd_3645149 : Nat := 4983230072969 + 3 ^ 40 * 3645149 * 2
def baseEnd_3645149 : Nat := 415936332056858682549727

theorem tailTrace_3645149 : CollatzResearch.WordTrace tailWord_3645149 prefixEnd_3645149 415936332056858682549727 := by
  unfold tailWord_3645149
  simp only [CollatzResearch.WordTrace]
  refine ⟨132949506271255189731218501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88633004180836793154145667 132949506271255189731218501)
  ·
    refine ⟨24928032425860348074603469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132949506271255189731218501 24928032425860348074603469)
    ·
      refine ⟨9348012159697630527976301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24928032425860348074603469 9348012159697630527976301)
      ·
        refine ⟨3505504559886611447991113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9348012159697630527976301 3505504559886611447991113)
        ·
          refine ⟨2629128419914958585993335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3505504559886611447991113 2629128419914958585993335)
          ·
            refine ⟨3943692629872437878990003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629128419914958585993335 3943692629872437878990003)
            ·
              refine ⟨5915538944808656818485005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943692629872437878990003 5915538944808656818485005)
              ·
                refine ⟨2218327104303246306931877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5915538944808656818485005 2218327104303246306931877)
                ·
                  refine ⟨415936332056858682549727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2218327104303246306931877 415936332056858682549727)
                  ·
                    rfl

theorem cell22_3645149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_3645149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645149 prefixEnd_3645149 := by exact prefixLift 3645149
  have htrace : WordTrace (prefixWord ++ tailWord_3645149) baseStart_3645149 baseEnd_3645149 := by
    simpa [prefixWord, tailWord_3645149, baseEnd_3645149] using wordTrace_append hprefix tailTrace_3645149
  have hstable : (prefixWord ++ tailWord_3645149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645149).length < 2 ^ (prefixWord ++ tailWord_3645149).sum := by decide
  have hdescent : baseEnd_3645149 < baseStart_3645149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645188 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 5]
def baseStart_3645188 : Nat := 118140960795 + 3645188 * 2 ^ 59
def prefixEnd_3645188 : Nat := 4983230072969 + 3 ^ 40 * 3645188 * 2
def baseEnd_3645188 : Nat := 415940782222530981974687

theorem tailTrace_3645188 : CollatzResearch.WordTrace tailWord_3645188 prefixEnd_3645188 415940782222530981974687 := by
  unfold tailWord_3645188
  simp only [CollatzResearch.WordTrace]
  refine ⟨66475464359056949695944109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88633952478742599594592145 66475464359056949695944109)
  ·
    refine ⟨24928299134646356135979041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66475464359056949695944109 24928299134646356135979041)
    ·
      refine ⟨18696224350984767101984281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24928299134646356135979041 18696224350984767101984281)
      ·
        refine ⟨14022168263238575326488211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18696224350984767101984281 14022168263238575326488211)
        ·
          refine ⟨21033252394857862989732317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14022168263238575326488211 21033252394857862989732317)
          ·
            refine ⟨7887469648071698621149619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21033252394857862989732317 7887469648071698621149619)
            ·
              refine ⟨11831204472107547931724429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887469648071698621149619 11831204472107547931724429)
              ·
                refine ⟨4436701677040330474396661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11831204472107547931724429 4436701677040330474396661)
                ·
                  refine ⟨415940782222530981974687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4436701677040330474396661 415940782222530981974687)
                  ·
                    rfl

theorem cell22_3645188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_3645188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645188 prefixEnd_3645188 := by exact prefixLift 3645188
  have htrace : WordTrace (prefixWord ++ tailWord_3645188) baseStart_3645188 baseEnd_3645188 := by
    simpa [prefixWord, tailWord_3645188, baseEnd_3645188] using wordTrace_append hprefix tailTrace_3645188
  have hstable : (prefixWord ++ tailWord_3645188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645188).length < 2 ^ (prefixWord ++ tailWord_3645188).sum := by decide
  have hdescent : baseEnd_3645188 < baseStart_3645188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645282 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3645282 : Nat := 118140960795 + 3645282 * 2 ^ 59
def prefixEnd_3645282 : Nat := 4983230072969 + 3 ^ 40 * 3645282 * 2
def baseEnd_3645282 : Nat := 1247854524788608034073773

theorem tailTrace_3645282 : CollatzResearch.WordTrace tailWord_3645282 prefixEnd_3645282 1247854524788608034073773 := by
  unfold tailWord_3645282
  simp only [CollatzResearch.WordTrace]
  refine ⟨33238589294943338361452525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88636238119848902297206733 33238589294943338361452525)
  ·
    refine ⟨12464470985603751885544697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33238589294943338361452525 12464470985603751885544697)
    ·
      refine ⟨9348353239202813914158523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12464470985603751885544697 9348353239202813914158523)
      ·
        refine ⟨14022529858804220871237785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9348353239202813914158523 14022529858804220871237785)
        ·
          refine ⟨10516897394103165653428339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14022529858804220871237785 10516897394103165653428339)
          ·
            refine ⟨15775346091154748480142509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10516897394103165653428339 15775346091154748480142509)
            ·
              refine ⟨5915754784183030680053441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15775346091154748480142509 5915754784183030680053441)
              ·
                refine ⟨4436816088137273010040081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5915754784183030680053441 4436816088137273010040081)
                ·
                  refine ⟨3327612066102954757530061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4436816088137273010040081 3327612066102954757530061)
                  ·
                    refine ⟨1247854524788608034073773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327612066102954757530061 1247854524788608034073773)
                    ·
                      rfl

theorem cell22_3645282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3645282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645282 prefixEnd_3645282 := by exact prefixLift 3645282
  have htrace : WordTrace (prefixWord ++ tailWord_3645282) baseStart_3645282 baseEnd_3645282 := by
    simpa [prefixWord, tailWord_3645282, baseEnd_3645282] using wordTrace_append hprefix tailTrace_3645282
  have hstable : (prefixWord ++ tailWord_3645282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645282).length < 2 ^ (prefixWord ++ tailWord_3645282).sum := by decide
  have hdescent : baseEnd_3645282 < baseStart_3645282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645402 : List Nat := [3, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_3645402 : Nat := 118140960795 + 3645402 * 2 ^ 59
def prefixEnd_3645402 : Nat := 4983230072969 + 3 ^ 40 * 3645402 * 2
def baseEnd_3645402 : Nat := 415965201080322573691135

theorem tailTrace_3645402 : CollatzResearch.WordTrace tailWord_3645402 prefixEnd_3645402 415965201080322573691135 := by
  unfold tailWord_3645402
  simp only [CollatzResearch.WordTrace]
  refine ⟨33239683484834653485044615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88639155959559075960118973 33239683484834653485044615)
  ·
    refine ⟨49859525227251980227566923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33239683484834653485044615 49859525227251980227566923)
    ·
      refine ⟨74789287840877970341350385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49859525227251980227566923 74789287840877970341350385)
      ·
        refine ⟨56091965880658477756012789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74789287840877970341350385 56091965880658477756012789)
        ·
          refine ⟨5258621801311732289626199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56091965880658477756012789 5258621801311732289626199)
          ·
            refine ⟨7887932701967598434439299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5258621801311732289626199 7887932701967598434439299)
            ·
              refine ⟨11831899052951397651658949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887932701967598434439299 11831899052951397651658949)
              ·
                refine ⟨2218481072428387059686053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11831899052951397651658949 2218481072428387059686053)
                ·
                  refine ⟨415965201080322573691135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2218481072428387059686053 415965201080322573691135)
                  ·
                    rfl

theorem cell22_3645402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_3645402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645402 prefixEnd_3645402 := by exact prefixLift 3645402
  have htrace : WordTrace (prefixWord ++ tailWord_3645402) baseStart_3645402 baseEnd_3645402 := by
    simpa [prefixWord, tailWord_3645402, baseEnd_3645402] using wordTrace_append hprefix tailTrace_3645402
  have hstable : (prefixWord ++ tailWord_3645402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645402).length < 2 ^ (prefixWord ++ tailWord_3645402).sum := by decide
  have hdescent : baseEnd_3645402 < baseStart_3645402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645496 : List Nat := [2, 1, 2, 1, 6, 2, 1, 3, 1, 3]
def baseStart_3645496 : Nat := 118140960795 + 3645496 * 2 ^ 59
def prefixEnd_3645496 : Nat := 4983230072969 + 3 ^ 40 * 3645496 * 2
def baseEnd_3645496 : Nat := 1247927781361982809223117

theorem tailTrace_3645496 : CollatzResearch.WordTrace tailWord_3645496 prefixEnd_3645496 1247927781361982809223117 := by
  unfold tailWord_3645496
  simp only [CollatzResearch.WordTrace]
  refine ⟨66481081200499033997050171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88641441600665378662733561 66481081200499033997050171)
  ·
    refine ⟨99721621800748550995575257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66481081200499033997050171 99721621800748550995575257)
    ·
      refine ⟨74791216350561413246681443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99721621800748550995575257 74791216350561413246681443)
      ·
        refine ⟨112186824525842119870022165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74791216350561413246681443 112186824525842119870022165)
        ·
          refine ⟨5258757399648849368907289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112186824525842119870022165 5258757399648849368907289)
          ·
            refine ⟨3944068049736637026680467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5258757399648849368907289 3944068049736637026680467)
            ·
              refine ⟨5916102074604955540020701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944068049736637026680467 5916102074604955540020701)
              ·
                refine ⟨2218538277976858327507763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5916102074604955540020701 2218538277976858327507763)
                ·
                  refine ⟨3327807416965287491261645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218538277976858327507763 3327807416965287491261645)
                  ·
                    refine ⟨1247927781361982809223117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327807416965287491261645 1247927781361982809223117)
                    ·
                      rfl

theorem cell22_3645496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_3645496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645496 prefixEnd_3645496 := by exact prefixLift 3645496
  have htrace : WordTrace (prefixWord ++ tailWord_3645496) baseStart_3645496 baseEnd_3645496 := by
    simpa [prefixWord, tailWord_3645496, baseEnd_3645496] using wordTrace_append hprefix tailTrace_3645496
  have hstable : (prefixWord ++ tailWord_3645496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645496).length < 2 ^ (prefixWord ++ tailWord_3645496).sum := by decide
  have hdescent : baseEnd_3645496 < baseStart_3645496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645503 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 8]
def baseStart_3645503 : Nat := 118140960795 + 3645503 * 2 ^ 59
def prefixEnd_3645503 : Nat := 4983230072969 + 3 ^ 40 * 3645503 * 2
def baseEnd_3645503 : Nat := 415976725868345708099365

theorem tailTrace_3645503 : CollatzResearch.WordTrace tailWord_3645503 prefixEnd_3645503 415976725868345708099365 := by
  unfold tailWord_3645503
  simp only [CollatzResearch.WordTrace]
  refine ⟨132962417711972708189605163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88641611807981805459736775 132962417711972708189605163)
  ·
    refine ⟨199443626567959062284407745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132962417711972708189605163 199443626567959062284407745)
    ·
      refine ⟨149582719925969296713305809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199443626567959062284407745 149582719925969296713305809)
      ·
        refine ⟨112187039944476972534979357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149582719925969296713305809 112187039944476972534979357)
        ·
          refine ⟨42070139979178864700617259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112187039944476972534979357 42070139979178864700617259)
          ·
            refine ⟨63105209968768297050925889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42070139979178864700617259 63105209968768297050925889)
            ·
              refine ⟨47328907476576222788194417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63105209968768297050925889 47328907476576222788194417)
              ·
                refine ⟨35496680607432167091145813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47328907476576222788194417 35496680607432167091145813)
                ·
                  refine ⟨415976725868345708099365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35496680607432167091145813 415976725868345708099365)
                  ·
                    rfl

theorem cell22_3645503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 8].length) (baseStart_3645503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645503 prefixEnd_3645503 := by exact prefixLift 3645503
  have htrace : WordTrace (prefixWord ++ tailWord_3645503) baseStart_3645503 baseEnd_3645503 := by
    simpa [prefixWord, tailWord_3645503, baseEnd_3645503] using wordTrace_append hprefix tailTrace_3645503
  have hstable : (prefixWord ++ tailWord_3645503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645503).length < 2 ^ (prefixWord ++ tailWord_3645503).sum := by decide
  have hdescent : baseEnd_3645503 < baseStart_3645503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645526 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3645526 : Nat := 118140960795 + 3645526 * 2 ^ 59
def prefixEnd_3645526 : Nat := 4983230072969 + 3 ^ 40 * 3645526 * 2
def baseEnd_3645526 : Nat := 415979350325024243657675

theorem tailTrace_3645526 : CollatzResearch.WordTrace tailWord_3645526 prefixEnd_3645526 415979350325024243657675 := by
  unfold tailWord_3645526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8310203536930586444855777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88642171060592922078461621 8310203536930586444855777)
  ·
    refine ⟨6232652652697939833641833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8310203536930586444855777 6232652652697939833641833)
    ·
      refine ⟨4674489489523454875231375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6232652652697939833641833 4674489489523454875231375)
      ·
        refine ⟨7011734234285182312847063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4674489489523454875231375 7011734234285182312847063)
        ·
          refine ⟨10517601351427773469270595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7011734234285182312847063 10517601351427773469270595)
          ·
            refine ⟨15776402027141660203905893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10517601351427773469270595 15776402027141660203905893)
            ·
              refine ⟨2958075380089061288232355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15776402027141660203905893 2958075380089061288232355)
              ·
                refine ⟨4437113070133591932348533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958075380089061288232355 4437113070133591932348533)
                ·
                  refine ⟨415979350325024243657675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4437113070133591932348533 415979350325024243657675)
                  ·
                    rfl

theorem cell22_3645526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3645526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645526 prefixEnd_3645526 := by exact prefixLift 3645526
  have htrace : WordTrace (prefixWord ++ tailWord_3645526) baseStart_3645526 baseEnd_3645526 := by
    simpa [prefixWord, tailWord_3645526, baseEnd_3645526] using wordTrace_append hprefix tailTrace_3645526
  have hstable : (prefixWord ++ tailWord_3645526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645526).length < 2 ^ (prefixWord ++ tailWord_3645526).sum := by decide
  have hdescent : baseEnd_3645526 < baseStart_3645526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645535 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 6, 3]
def baseStart_3645535 : Nat := 118140960795 + 3645535 * 2 ^ 59
def prefixEnd_3645535 : Nat := 4983230072969 + 3 ^ 40 * 3645535 * 2
def baseEnd_3645535 : Nat := 1247941131858999707497997

theorem tailTrace_3645535 : CollatzResearch.WordTrace tailWord_3645535 prefixEnd_3645535 1247941131858999707497997 := by
  unfold tailWord_3645535
  simp only [CollatzResearch.WordTrace]
  refine ⟨132963584847856777654770059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88642389898571185103180039 132963584847856777654770059)
  ·
    refine ⟨199445377271785166482155089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132963584847856777654770059 199445377271785166482155089)
    ·
      refine ⟨149584032953838874861616317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199445377271785166482155089 149584032953838874861616317)
      ·
        refine ⟨56094012357689578073106119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149584032953838874861616317 56094012357689578073106119)
        ·
          refine ⟨84141018536534367109659179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56094012357689578073106119 84141018536534367109659179)
          ·
            refine ⟨126211527804801550664488769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84141018536534367109659179 126211527804801550664488769)
            ·
              refine ⟨94658645853601162998366577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126211527804801550664488769 94658645853601162998366577)
              ·
                refine ⟨70993984390200872248774933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94658645853601162998366577 70993984390200872248774933)
                ·
                  refine ⟨3327843018290665886661325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70993984390200872248774933 3327843018290665886661325)
                  ·
                    refine ⟨1247941131858999707497997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327843018290665886661325 1247941131858999707497997)
                    ·
                      rfl

theorem cell22_3645535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_3645535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645535 prefixEnd_3645535 := by exact prefixLift 3645535
  have htrace : WordTrace (prefixWord ++ tailWord_3645535) baseStart_3645535 baseEnd_3645535 := by
    simpa [prefixWord, tailWord_3645535, baseEnd_3645535] using wordTrace_append hprefix tailTrace_3645535
  have hstable : (prefixWord ++ tailWord_3645535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645535).length < 2 ^ (prefixWord ++ tailWord_3645535).sum := by decide
  have hdescent : baseEnd_3645535 < baseStart_3645535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645597 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_3645597 : Nat := 118140960795 + 3645597 * 2 ^ 59
def prefixEnd_3645597 : Nat := 4983230072969 + 3 ^ 40 * 3645597 * 2
def baseEnd_3645597 : Nat := 1247962355726052212447807

theorem tailTrace_3645597 : CollatzResearch.WordTrace tailWord_3645597 prefixEnd_3645597 1247962355726052212447807 := by
  unfold tailWord_3645597
  simp only [CollatzResearch.WordTrace]
  refine ⟨132965846173632162243527045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88643897449088108162351363 132965846173632162243527045)
  ·
    refine ⟨24931096157556030420661321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132965846173632162243527045 24931096157556030420661321)
    ·
      refine ⟨18698322118167022815495991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24931096157556030420661321 18698322118167022815495991)
      ·
        refine ⟨28047483177250534223243987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18698322118167022815495991 28047483177250534223243987)
        ·
          refine ⟨42071224765875801334865981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28047483177250534223243987 42071224765875801334865981)
          ·
            refine ⟨15776709287203425500574743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42071224765875801334865981 15776709287203425500574743)
            ·
              refine ⟨23665063930805138250862115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15776709287203425500574743 23665063930805138250862115)
              ·
                refine ⟨35497595896207707376293173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23665063930805138250862115 35497595896207707376293173)
                ·
                  refine ⟨3327899615269472566527485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35497595896207707376293173 3327899615269472566527485)
                  ·
                    refine ⟨1247962355726052212447807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327899615269472566527485 1247962355726052212447807)
                    ·
                      rfl

theorem cell22_3645597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_3645597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645597 prefixEnd_3645597 := by exact prefixLift 3645597
  have htrace : WordTrace (prefixWord ++ tailWord_3645597) baseStart_3645597 baseEnd_3645597 := by
    simpa [prefixWord, tailWord_3645597, baseEnd_3645597] using wordTrace_append hprefix tailTrace_3645597
  have hstable : (prefixWord ++ tailWord_3645597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645597).length < 2 ^ (prefixWord ++ tailWord_3645597).sum := by decide
  have hdescent : baseEnd_3645597 < baseStart_3645597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645625 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_3645625 : Nat := 118140960795 + 3645625 * 2 ^ 59
def prefixEnd_3645625 : Nat := 4983230072969 + 3 ^ 40 * 3645625 * 2
def baseEnd_3645625 : Nat := 1247971940698269472747721

theorem tailTrace_3645625 : CollatzResearch.WordTrace tailWord_3645625 prefixEnd_3645625 1247971940698269472747721 := by
  unfold tailWord_3645625
  simp only [CollatzResearch.WordTrace]
  refine ⟨132966867417530723025546329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88644578278353815350364219 132966867417530723025546329)
  ·
    refine ⟨99725150563148042269159747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132966867417530723025546329 99725150563148042269159747)
    ·
      refine ⟨149587725844722063403739621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99725150563148042269159747 149587725844722063403739621)
      ·
        refine ⟨28047698595885386888201179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149587725844722063403739621 28047698595885386888201179)
        ·
          refine ⟨42071547893828080332301769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28047698595885386888201179 42071547893828080332301769)
          ·
            refine ⟨31553660920371060249226327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42071547893828080332301769 31553660920371060249226327)
            ·
              refine ⟨47330491380556590373839491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31553660920371060249226327 47330491380556590373839491)
              ·
                refine ⟨70995737070834885560759237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47330491380556590373839491 70995737070834885560759237)
                ·
                  refine ⟨13311700700781541042642357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70995737070834885560759237 13311700700781541042642357)
                  ·
                    refine ⟨1247971940698269472747721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13311700700781541042642357 1247971940698269472747721)
                    ·
                      rfl

theorem cell22_3645625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_3645625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645625 prefixEnd_3645625 := by exact prefixLift 3645625
  have htrace : WordTrace (prefixWord ++ tailWord_3645625) baseStart_3645625 baseEnd_3645625 := by
    simpa [prefixWord, tailWord_3645625, baseEnd_3645625] using wordTrace_append hprefix tailTrace_3645625
  have hstable : (prefixWord ++ tailWord_3645625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645625).length < 2 ^ (prefixWord ++ tailWord_3645625).sum := by decide
  have hdescent : baseEnd_3645625 < baseStart_3645625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645657 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_3645657 : Nat := 118140960795 + 3645657 * 2 ^ 59
def prefixEnd_3645657 : Nat := 4983230072969 + 3 ^ 40 * 3645657 * 2
def baseEnd_3645657 : Nat := 1247982894952232055947623

theorem tailTrace_3645657 : CollatzResearch.WordTrace tailWord_3645657 prefixEnd_3645657 1247982894952232055947623 := by
  unfold tailWord_3645657
  simp only [CollatzResearch.WordTrace]
  refine ⟨132968034553414792490711225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88645356368943194993807483 132968034553414792490711225)
  ·
    refine ⟨99726025915061094368033419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132968034553414792490711225 99726025915061094368033419)
    ·
      refine ⟨149589038872591641552050129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99726025915061094368033419 149589038872591641552050129)
      ·
        refine ⟨112191779154443731164037597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149589038872591641552050129 112191779154443731164037597)
        ·
          refine ⟨42071917182916399186514099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112191779154443731164037597 42071917182916399186514099)
          ·
            refine ⟨63107875774374598779771149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42071917182916399186514099 63107875774374598779771149)
            ·
              refine ⟨23665453415390474542414181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63107875774374598779771149 23665453415390474542414181)
              ·
                refine ⟨4437272515385713976702659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23665453415390474542414181 4437272515385713976702659)
                ·
                  refine ⟨6655908773078570965053989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437272515385713976702659 6655908773078570965053989)
                  ·
                    refine ⟨1247982894952232055947623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6655908773078570965053989 1247982894952232055947623)
                    ·
                      rfl

theorem cell22_3645657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_3645657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645657 prefixEnd_3645657 := by exact prefixLift 3645657
  have htrace : WordTrace (prefixWord ++ tailWord_3645657) baseStart_3645657 baseEnd_3645657 := by
    simpa [prefixWord, tailWord_3645657, baseEnd_3645657] using wordTrace_append hprefix tailTrace_3645657
  have hstable : (prefixWord ++ tailWord_3645657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645657).length < 2 ^ (prefixWord ++ tailWord_3645657).sum := by decide
  have hdescent : baseEnd_3645657 < baseStart_3645657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645715 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 2, 7]
def baseStart_3645715 : Nat := 118140960795 + 3645715 * 2 ^ 59
def prefixEnd_3645715 : Nat := 4983230072969 + 3 ^ 40 * 3645715 * 2
def baseEnd_3645715 : Nat := 1248002749537539237997445

theorem tailTrace_3645715 : CollatzResearch.WordTrace tailWord_3645715 prefixEnd_3645715 1248002749537539237997445 := by
  unfold tailWord_3645715
  simp only [CollatzResearch.WordTrace]
  refine ⟨132970149987204668396322599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88646766658136445597548399 132970149987204668396322599)
  ·
    refine ⟨199455224980807002594483899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132970149987204668396322599 199455224980807002594483899)
    ·
      refine ⟨299182837471210503891725849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199455224980807002594483899 299182837471210503891725849)
      ·
        refine ⟨224387128103407877918794387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299182837471210503891725849 224387128103407877918794387)
        ·
          refine ⟨336580692155111816878191581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224387128103407877918794387 336580692155111816878191581)
          ·
            refine ⟨126217759558166931329321843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336580692155111816878191581 126217759558166931329321843)
            ·
              refine ⟨189326639337250396993982765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126217759558166931329321843 189326639337250396993982765)
              ·
                refine ⟨70997489751468898872743537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189326639337250396993982765 70997489751468898872743537)
                ·
                  refine ⟨53248117313601674154557653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70997489751468898872743537 53248117313601674154557653)
                  ·
                    refine ⟨1248002749537539237997445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53248117313601674154557653 1248002749537539237997445)
                    ·
                      rfl

theorem cell22_3645715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_3645715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645715 prefixEnd_3645715 := by exact prefixLift 3645715
  have htrace : WordTrace (prefixWord ++ tailWord_3645715) baseStart_3645715 baseEnd_3645715 := by
    simpa [prefixWord, tailWord_3645715, baseEnd_3645715] using wordTrace_append hprefix tailTrace_3645715
  have hstable : (prefixWord ++ tailWord_3645715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645715).length < 2 ^ (prefixWord ++ tailWord_3645715).sum := by decide
  have hdescent : baseEnd_3645715 < baseStart_3645715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645719 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 2, 4]
def baseStart_3645719 : Nat := 118140960795 + 3645719 * 2 ^ 59
def prefixEnd_3645719 : Nat := 4983230072969 + 3 ^ 40 * 3645719 * 2
def baseEnd_3645719 : Nat := 1248004118819284560897433

theorem tailTrace_3645719 : CollatzResearch.WordTrace tailWord_3645719 prefixEnd_3645719 1248004118819284560897433 := by
  unfold tailWord_3645719
  simp only [CollatzResearch.WordTrace]
  refine ⟨132970295879190177079468211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88646863919460118052978807 132970295879190177079468211)
  ·
    refine ⟨199455443818785265619202317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132970295879190177079468211 199455443818785265619202317)
    ·
      refine ⟨74795791432044474607200869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199455443818785265619202317 74795791432044474607200869)
      ·
        refine ⟨14024210893508338988850163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74795791432044474607200869 14024210893508338988850163)
        ·
          refine ⟨21036316340262508483275245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14024210893508338988850163 21036316340262508483275245)
          ·
            refine ⟨7888618627598440681228217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21036316340262508483275245 7888618627598440681228217)
            ·
              refine ⟨5916463970698830510921163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7888618627598440681228217 5916463970698830510921163)
              ·
                refine ⟨8874695956048245766381745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916463970698830510921163 8874695956048245766381745)
                ·
                  refine ⟨6656021967036184324786309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8874695956048245766381745 6656021967036184324786309)
                  ·
                    refine ⟨1248004118819284560897433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6656021967036184324786309 1248004118819284560897433)
                    ·
                      rfl

theorem cell22_3645719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_3645719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645719 prefixEnd_3645719 := by exact prefixLift 3645719
  have htrace : WordTrace (prefixWord ++ tailWord_3645719) baseStart_3645719 baseEnd_3645719 := by
    simpa [prefixWord, tailWord_3645719, baseEnd_3645719] using wordTrace_append hprefix tailTrace_3645719
  have hstable : (prefixWord ++ tailWord_3645719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645719).length < 2 ^ (prefixWord ++ tailWord_3645719).sum := by decide
  have hdescent : baseEnd_3645719 < baseStart_3645719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645738 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3645738 : Nat := 118140960795 + 3645738 * 2 ^ 59
def prefixEnd_3645738 : Nat := 4983230072969 + 3 ^ 40 * 3645738 * 2
def baseEnd_3645738 : Nat := 1248010622907574844672375

theorem tailTrace_3645738 : CollatzResearch.WordTrace tailWord_3645738 prefixEnd_3645738 1248010622907574844672375 := by
  unfold tailWord_3645738
  simp only [CollatzResearch.WordTrace]
  refine ⟨33242747216530335831102467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88647325910747562216273245 33242747216530335831102467)
  ·
    refine ⟨49864120824795503746653701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33242747216530335831102467 49864120824795503746653701)
    ·
      refine ⟨9349522654649156952497569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49864120824795503746653701 9349522654649156952497569)
      ·
        refine ⟨7012141990986867714373177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9349522654649156952497569 7012141990986867714373177)
        ·
          refine ⟨5259106493240150785779883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7012141990986867714373177 5259106493240150785779883)
          ·
            refine ⟨7888659739860226178669825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259106493240150785779883 7888659739860226178669825)
            ·
              refine ⟨5916494804895169634002369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7888659739860226178669825 5916494804895169634002369)
              ·
                refine ⟨4437371103671377225501777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916494804895169634002369 4437371103671377225501777)
                ·
                  refine ⟨3328028327753532919126333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4437371103671377225501777 3328028327753532919126333)
                  ·
                    refine ⟨1248010622907574844672375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3328028327753532919126333 1248010622907574844672375)
                    ·
                      rfl

theorem cell22_3645738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3645738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645738 prefixEnd_3645738 := by exact prefixLift 3645738
  have htrace : WordTrace (prefixWord ++ tailWord_3645738) baseStart_3645738 baseEnd_3645738 := by
    simpa [prefixWord, tailWord_3645738, baseEnd_3645738] using wordTrace_append hprefix tailTrace_3645738
  have hstable : (prefixWord ++ tailWord_3645738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645738).length < 2 ^ (prefixWord ++ tailWord_3645738).sum := by decide
  have hdescent : baseEnd_3645738 < baseStart_3645738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645749 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_3645749 : Nat := 118140960795 + 3645749 * 2 ^ 59
def prefixEnd_3645749 : Nat := 4983230072969 + 3 ^ 40 * 3645749 * 2
def baseEnd_3645749 : Nat := 1248014388432374482647341

theorem tailTrace_3645749 : CollatzResearch.WordTrace tailWord_3645749 prefixEnd_3645749 1248014388432374482647341 := by
  unfold tailWord_3645749
  simp only [CollatzResearch.WordTrace]
  refine ⟨132971390069081492203060301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88647593379387661468706867 132971390069081492203060301)
  ·
    refine ⟨49864271275905559576147613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132971390069081492203060301 49864271275905559576147613)
    ·
      refine ⟨18699101728464584841055355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49864271275905559576147613 18699101728464584841055355)
      ·
        refine ⟨28048652592696877261583033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18699101728464584841055355 28048652592696877261583033)
        ·
          refine ⟨21036489444522657946187275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28048652592696877261583033 21036489444522657946187275)
          ·
            refine ⟨31554734166783986919280913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21036489444522657946187275 31554734166783986919280913)
            ·
              refine ⟨23666050625087990189460685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31554734166783986919280913 23666050625087990189460685)
              ·
                refine ⟨8874768984407996321047757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23666050625087990189460685 8874768984407996321047757)
                ·
                  refine ⟨3328038369152998620392909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8874768984407996321047757 3328038369152998620392909)
                  ·
                    refine ⟨1248014388432374482647341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3328038369152998620392909 1248014388432374482647341)
                    ·
                      rfl

theorem cell22_3645749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_3645749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645749 prefixEnd_3645749 := by exact prefixLift 3645749
  have htrace : WordTrace (prefixWord ++ tailWord_3645749) baseStart_3645749 baseEnd_3645749 := by
    simpa [prefixWord, tailWord_3645749, baseEnd_3645749] using wordTrace_append hprefix tailTrace_3645749
  have hstable : (prefixWord ++ tailWord_3645749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645749).length < 2 ^ (prefixWord ++ tailWord_3645749).sum := by decide
  have hdescent : baseEnd_3645749 < baseStart_3645749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645794 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3645794 : Nat := 118140960795 + 3645794 * 2 ^ 59
def prefixEnd_3645794 : Nat := 4983230072969 + 3 ^ 40 * 3645794 * 2
def baseEnd_3645794 : Nat := 1248029792852009365272203

theorem tailTrace_3645794 : CollatzResearch.WordTrace tailWord_3645794 prefixEnd_3645794 1248029792852009365272203 := by
  unfold tailWord_3645794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33243257838479616222112109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88648687569278976592298957 33243257838479616222112109)
  ·
    refine ⟨12466221689429856083292041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33243257838479616222112109 12466221689429856083292041)
    ·
      refine ⟨9349666267072392062469031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12466221689429856083292041 9349666267072392062469031)
      ·
        refine ⟨14024499400608588093703547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9349666267072392062469031 14024499400608588093703547)
        ·
          refine ⟨21036749100912882140555321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14024499400608588093703547 21036749100912882140555321)
          ·
            refine ⟨15777561825684661605416491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21036749100912882140555321 15777561825684661605416491)
            ·
              refine ⟨23666342738526992408124737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15777561825684661605416491 23666342738526992408124737)
              ·
                refine ⟨17749757053895244306093553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23666342738526992408124737 17749757053895244306093553)
                ·
                  refine ⟨13312317790421433229570165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17749757053895244306093553 13312317790421433229570165)
                  ·
                    refine ⟨1248029792852009365272203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13312317790421433229570165 1248029792852009365272203)
                    ·
                      rfl

theorem cell22_3645794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3645794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645794 prefixEnd_3645794 := by exact prefixLift 3645794
  have htrace : WordTrace (prefixWord ++ tailWord_3645794) baseStart_3645794 baseEnd_3645794 := by
    simpa [prefixWord, tailWord_3645794, baseEnd_3645794] using wordTrace_append hprefix tailTrace_3645794
  have hstable : (prefixWord ++ tailWord_3645794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645794).length < 2 ^ (prefixWord ++ tailWord_3645794).sum := by decide
  have hdescent : baseEnd_3645794 < baseStart_3645794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645858 : List Nat := [3, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_3645858 : Nat := 118140960795 + 3645858 * 2 ^ 59
def prefixEnd_3645858 : Nat := 4983230072969 + 3 ^ 40 * 3645858 * 2
def baseEnd_3645858 : Nat := 416017233786644843890669

theorem tailTrace_3645858 : CollatzResearch.WordTrace tailWord_3645858 prefixEnd_3645858 416017233786644843890669 := by
  unfold tailWord_3645858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33243841406421650954694557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88650243750457735879185485 33243841406421650954694557)
  ·
    refine ⟨12466440527408119108010459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33243841406421650954694557 12466440527408119108010459)
    ·
      refine ⟨18699660791112178662015689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12466440527408119108010459 18699660791112178662015689)
      ·
        refine ⟨14024745593334133996511767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18699660791112178662015689 14024745593334133996511767)
        ·
          refine ⟨21037118390001200994767651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14024745593334133996511767 21037118390001200994767651)
          ·
            refine ⟨31555677585001801492151477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21037118390001200994767651 31555677585001801492151477)
            ·
              refine ⟨2958344773593918889889201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31555677585001801492151477 2958344773593918889889201)
              ·
                refine ⟨2218758580195439167416901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2958344773593918889889201 2218758580195439167416901)
                ·
                  refine ⟨416017233786644843890669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2218758580195439167416901 416017233786644843890669)
                  ·
                    rfl

theorem cell22_3645858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_3645858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645858 prefixEnd_3645858 := by exact prefixLift 3645858
  have htrace : WordTrace (prefixWord ++ tailWord_3645858) baseStart_3645858 baseEnd_3645858 := by
    simpa [prefixWord, tailWord_3645858, baseEnd_3645858] using wordTrace_append hprefix tailTrace_3645858
  have hstable : (prefixWord ++ tailWord_3645858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645858).length < 2 ^ (prefixWord ++ tailWord_3645858).sum := by decide
  have hdescent : baseEnd_3645858 < baseStart_3645858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645873 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 2, 3]
def baseStart_3645873 : Nat := 118140960795 + 3645873 * 2 ^ 59
def prefixEnd_3645873 : Nat := 4983230072969 + 3 ^ 40 * 3645873 * 2
def baseEnd_3645873 : Nat := 1248056836166479492546961

theorem tailTrace_3645873 : CollatzResearch.WordTrace tailWord_3645873 prefixEnd_3645873 1248056836166479492546961 := by
  unfold tailWord_3645873
  simp only [CollatzResearch.WordTrace]
  refine ⟨132975912720632261380574273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88650608480421507587049515 132975912720632261380574273)
  ·
    refine ⟨99731934540474196035430705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132975912720632261380574273 99731934540474196035430705)
    ·
      refine ⟨74798950905355647026573029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99731934540474196035430705 74798950905355647026573029)
      ·
        refine ⟨14024803294754183817482443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74798950905355647026573029 14024803294754183817482443)
        ·
          refine ⟨21037204942131275726223665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14024803294754183817482443 21037204942131275726223665)
          ·
            refine ⟨15777903706598456794667749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21037204942131275726223665 15777903706598456794667749)
            ·
              refine ⟨2958356944987210649000203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15777903706598456794667749 2958356944987210649000203)
              ·
                refine ⟨4437535417480815973500305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958356944987210649000203 4437535417480815973500305)
                ·
                  refine ⟨3328151563110611980125229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4437535417480815973500305 3328151563110611980125229)
                  ·
                    refine ⟨1248056836166479492546961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3328151563110611980125229 1248056836166479492546961)
                    ·
                      rfl

theorem cell22_3645873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_3645873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645873 prefixEnd_3645873 := by exact prefixLift 3645873
  have htrace : WordTrace (prefixWord ++ tailWord_3645873) baseStart_3645873 baseEnd_3645873 := by
    simpa [prefixWord, tailWord_3645873, baseEnd_3645873] using wordTrace_append hprefix tailTrace_3645873
  have hstable : (prefixWord ++ tailWord_3645873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645873).length < 2 ^ (prefixWord ++ tailWord_3645873).sum := by decide
  have hdescent : baseEnd_3645873 < baseStart_3645873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645897 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 9]
def baseStart_3645897 : Nat := 118140960795 + 3645897 * 2 ^ 59
def prefixEnd_3645897 : Nat := 4983230072969 + 3 ^ 40 * 3645897 * 2
def baseEnd_3645897 : Nat := 416021683952317143315629

theorem tailTrace_3645897 : CollatzResearch.WordTrace tailWord_3645897 prefixEnd_3645897 416021683952317143315629 := by
  unfold tailWord_3645897
  simp only [CollatzResearch.WordTrace]
  refine ⟨132976788072545313479447945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88651192048363542319631963 132976788072545313479447945)
  ·
    refine ⟨99732591054408985109585959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132976788072545313479447945 99732591054408985109585959)
    ·
      refine ⟨149598886581613477664378939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99732591054408985109585959 149598886581613477664378939)
      ·
        refine ⟨224398329872420216496568409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149598886581613477664378939 224398329872420216496568409)
        ·
          refine ⟨168298747404315162372426307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224398329872420216496568409 168298747404315162372426307)
          ·
            refine ⟨252448121106472743558639461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168298747404315162372426307 252448121106472743558639461)
            ·
              refine ⟨47334022707463639417244899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252448121106472743558639461 47334022707463639417244899)
              ·
                refine ⟨71001034061195459125867349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47334022707463639417244899 71001034061195459125867349)
                ·
                  refine ⟨416021683952317143315629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71001034061195459125867349 416021683952317143315629)
                  ·
                    rfl

theorem cell22_3645897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_3645897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645897 prefixEnd_3645897 := by exact prefixLift 3645897
  have htrace : WordTrace (prefixWord ++ tailWord_3645897) baseStart_3645897 baseEnd_3645897 := by
    simpa [prefixWord, tailWord_3645897, baseEnd_3645897] using wordTrace_append hprefix tailTrace_3645897
  have hstable : (prefixWord ++ tailWord_3645897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645897).length < 2 ^ (prefixWord ++ tailWord_3645897).sum := by decide
  have hdescent : baseEnd_3645897 < baseStart_3645897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645944 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_3645944 : Nat := 118140960795 + 3645944 * 2 ^ 59
def prefixEnd_3645944 : Nat := 4983230072969 + 3 ^ 40 * 3645944 * 2
def baseEnd_3645944 : Nat := 1248081140917458974021743

theorem tailTrace_3645944 : CollatzResearch.WordTrace tailWord_3645944 prefixEnd_3645944 1248081140917458974021743 := by
  unfold tailWord_3645944
  simp only [CollatzResearch.WordTrace]
  refine ⟨66489251151687520253204443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88652334868916693670939257 66489251151687520253204443)
  ·
    refine ⟨99733876727531280379806665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66489251151687520253204443 99733876727531280379806665)
    ·
      refine ⟨74800407545648460284854999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99733876727531280379806665 74800407545648460284854999)
      ·
        refine ⟨112200611318472690427282499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74800407545648460284854999 112200611318472690427282499)
        ·
          refine ⟨168300916977709035640923749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112200611318472690427282499 168300916977709035640923749)
          ·
            refine ⟨31556421933320444182673203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168300916977709035640923749 31556421933320444182673203)
            ·
              refine ⟨47334632899980666274009805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31556421933320444182673203 47334632899980666274009805)
              ·
                refine ⟨17750487337492749852753677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47334632899980666274009805 17750487337492749852753677)
                ·
                  refine ⟨6656432751559781194782629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17750487337492749852753677 6656432751559781194782629)
                  ·
                    refine ⟨1248081140917458974021743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6656432751559781194782629 1248081140917458974021743)
                    ·
                      rfl

theorem cell22_3645944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_3645944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645944 prefixEnd_3645944 := by exact prefixLift 3645944
  have htrace : WordTrace (prefixWord ++ tailWord_3645944) baseStart_3645944 baseEnd_3645944 := by
    simpa [prefixWord, tailWord_3645944, baseEnd_3645944] using wordTrace_append hprefix tailTrace_3645944
  have hstable : (prefixWord ++ tailWord_3645944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645944).length < 2 ^ (prefixWord ++ tailWord_3645944).sum := by decide
  have hdescent : baseEnd_3645944 < baseStart_3645944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645965 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3645965 : Nat := 118140960795 + 3645965 * 2 ^ 59
def prefixEnd_3645965 : Nat := 4983230072969 + 3 ^ 40 * 3645965 * 2
def baseEnd_3645965 : Nat := 416029443215540639748893

theorem tailTrace_3645965 : CollatzResearch.WordTrace tailWord_3645965 prefixEnd_3645965 416029443215540639748893 := by
  unfold tailWord_3645965
  simp only [CollatzResearch.WordTrace]
  refine ⟨132979268236298961092923349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88652845490865974061948899 132979268236298961092923349)
  ·
    refine ⟨3116701599288256900615391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 132979268236298961092923349 3116701599288256900615391)
    ·
      refine ⟨4675052398932385350923087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3116701599288256900615391 4675052398932385350923087)
      ·
        refine ⟨7012578598398578026384631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4675052398932385350923087 7012578598398578026384631)
        ·
          refine ⟨10518867897597867039576947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7012578598398578026384631 10518867897597867039576947)
          ·
            refine ⟨15778301846396800559365421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10518867897597867039576947 15778301846396800559365421)
            ·
              refine ⟨5916863192398800209762033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15778301846396800559365421 5916863192398800209762033)
              ·
                refine ⟨4437647394299100157321525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916863192398800209762033 4437647394299100157321525)
                ·
                  refine ⟨416029443215540639748893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4437647394299100157321525 416029443215540639748893)
                  ·
                    rfl

theorem cell22_3645965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3645965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645965 prefixEnd_3645965 := by exact prefixLift 3645965
  have htrace : WordTrace (prefixWord ++ tailWord_3645965) baseStart_3645965 baseEnd_3645965 := by
    simpa [prefixWord, tailWord_3645965, baseEnd_3645965] using wordTrace_append hprefix tailTrace_3645965
  have hstable : (prefixWord ++ tailWord_3645965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645965).length < 2 ^ (prefixWord ++ tailWord_3645965).sum := by decide
  have hdescent : baseEnd_3645965 < baseStart_3645965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645976 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 6]
def baseStart_3645976 : Nat := 118140960795 + 3645976 * 2 ^ 59
def prefixEnd_3645976 : Nat := 4983230072969 + 3 ^ 40 * 3645976 * 2
def baseEnd_3645976 : Nat := 416030698390473852407215

theorem tailTrace_3645976 : CollatzResearch.WordTrace tailWord_3645976 prefixEnd_3645976 416030698390473852407215 := by
  unfold tailWord_3645976
  simp only [CollatzResearch.WordTrace]
  refine ⟨66489834719629554985786891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88653112959506073314382521 66489834719629554985786891)
  ·
    refine ⟨99734752079444332478680337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66489834719629554985786891 99734752079444332478680337)
    ·
      refine ⟨74801064059583249359010253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99734752079444332478680337 74801064059583249359010253)
      ·
        refine ⟨28050399022343718509628845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74801064059583249359010253 28050399022343718509628845)
        ·
          refine ⟨10518899633378894441110817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28050399022343718509628845 10518899633378894441110817)
          ·
            refine ⟨7889174725034170830833113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10518899633378894441110817 7889174725034170830833113)
            ·
              refine ⟨5916881043775628123124835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7889174725034170830833113 5916881043775628123124835)
              ·
                refine ⟨8875321565663442184687253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916881043775628123124835 8875321565663442184687253)
                ·
                  refine ⟨416030698390473852407215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8875321565663442184687253 416030698390473852407215)
                  ·
                    rfl

theorem cell22_3645976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_3645976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645976 prefixEnd_3645976 := by exact prefixLift 3645976
  have htrace : WordTrace (prefixWord ++ tailWord_3645976) baseStart_3645976 baseEnd_3645976 := by
    simpa [prefixWord, tailWord_3645976, baseEnd_3645976] using wordTrace_append hprefix tailTrace_3645976
  have hstable : (prefixWord ++ tailWord_3645976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645976).length < 2 ^ (prefixWord ++ tailWord_3645976).sum := by decide
  have hdescent : baseEnd_3645976 < baseStart_3645976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645989 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_3645989 : Nat := 118140960795 + 3645989 * 2 ^ 59
def prefixEnd_3645989 : Nat := 4983230072969 + 3 ^ 40 * 3645989 * 2
def baseEnd_3645989 : Nat := 1248096545337093856646605

theorem tailTrace_3645989 : CollatzResearch.WordTrace tailWord_3645989 prefixEnd_3645989 1248096545337093856646605 := by
  unfold tailWord_3645989
  simp only [CollatzResearch.WordTrace]
  refine ⟨132980143588212013191797021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88653429058808008794531347 132980143588212013191797021)
  ·
    refine ⟨49867553845579504946923883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132980143588212013191797021 49867553845579504946923883)
    ·
      refine ⟨74801330768369257420385825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49867553845579504946923883 74801330768369257420385825)
      ·
        refine ⟨56100998076276943065289369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74801330768369257420385825 56100998076276943065289369)
        ·
          refine ⟨42075748557207707298967027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56100998076276943065289369 42075748557207707298967027)
          ·
            refine ⟨63113622835811560948450541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42075748557207707298967027 63113622835811560948450541)
            ·
              refine ⟨23667608563429335355668953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63113622835811560948450541 23667608563429335355668953)
              ·
                refine ⟨17750706422572001516751715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23667608563429335355668953 17750706422572001516751715)
                ·
                  refine ⟨26626059633858002275127573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17750706422572001516751715 26626059633858002275127573)
                  ·
                    refine ⟨1248096545337093856646605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26626059633858002275127573 1248096545337093856646605)
                    ·
                      rfl

theorem cell22_3645989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_3645989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3645989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3645989 prefixEnd_3645989 := by exact prefixLift 3645989
  have htrace : WordTrace (prefixWord ++ tailWord_3645989) baseStart_3645989 baseEnd_3645989 := by
    simpa [prefixWord, tailWord_3645989, baseEnd_3645989] using wordTrace_append hprefix tailTrace_3645989
  have hstable : (prefixWord ++ tailWord_3645989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645989).length < 2 ^ (prefixWord ++ tailWord_3645989).sum := by decide
  have hdescent : baseEnd_3645989 < baseStart_3645989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646046 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3646046 : Nat := 118140960795 + 3646046 * 2 ^ 59
def prefixEnd_3646046 : Nat := 4983230072969 + 3 ^ 40 * 3646046 * 2
def baseEnd_3646046 : Nat := 1248116057601964707971431

theorem tailTrace_3646046 : CollatzResearch.WordTrace tailWord_3646046 prefixEnd_3646046 1248116057601964707971431 := by
  unfold tailWord_3646046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16622777818625688990827749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88654815032670341284414661 16622777818625688990827749)
  ·
    refine ⟨3116770840992316685780203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16622777818625688990827749 3116770840992316685780203)
    ·
      refine ⟨4675156261488475028670305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3116770840992316685780203 4675156261488475028670305)
      ·
        refine ⟨3506367196116356271502729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4675156261488475028670305 3506367196116356271502729)
        ·
          refine ⟨2629775397087267203627047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3506367196116356271502729 2629775397087267203627047)
          ·
            refine ⟨3944663095630900805440571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629775397087267203627047 3944663095630900805440571)
            ·
              refine ⟨5916994643446351208160857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944663095630900805440571 5916994643446351208160857)
              ·
                refine ⟨4437745982584763406120643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916994643446351208160857 4437745982584763406120643)
                ·
                  refine ⟨6656618973877145109180965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437745982584763406120643 6656618973877145109180965)
                  ·
                    refine ⟨1248116057601964707971431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6656618973877145109180965 1248116057601964707971431)
                    ·
                      rfl

theorem cell22_3646046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3646046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646046 prefixEnd_3646046 := by exact prefixLift 3646046
  have htrace : WordTrace (prefixWord ++ tailWord_3646046) baseStart_3646046 baseEnd_3646046 := by
    simpa [prefixWord, tailWord_3646046, baseEnd_3646046] using wordTrace_append hprefix tailTrace_3646046
  have hstable : (prefixWord ++ tailWord_3646046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646046).length < 2 ^ (prefixWord ++ tailWord_3646046).sum := by decide
  have hdescent : baseEnd_3646046 < baseStart_3646046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646081 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3646081 : Nat := 118140960795 + 3646081 * 2 ^ 59
def prefixEnd_3646081 : Nat := 4983230072969 + 3 ^ 40 * 3646081 * 2
def baseEnd_3646081 : Nat := 1248128038817236283346323

theorem tailTrace_3646081 : CollatzResearch.WordTrace tailWord_3646081 prefixEnd_3646081 1248128038817236283346323 := by
  unfold tailWord_3646081
  simp only [CollatzResearch.WordTrace]
  refine ⟨132983499103878712904146097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88655666069252475269430731 132983499103878712904146097)
  ·
    refine ⟨99737624327909034678109573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132983499103878712904146097 99737624327909034678109573)
    ·
      refine ⟨18700804561482944002145545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99737624327909034678109573 18700804561482944002145545)
      ·
        refine ⟨14025603421112208001609159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18700804561482944002145545 14025603421112208001609159)
        ·
          refine ⟨21038405131668312002413739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14025603421112208001609159 21038405131668312002413739)
          ·
            refine ⟨31557607697502468003620609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21038405131668312002413739 31557607697502468003620609)
            ·
              refine ⟨23668205773126851002715457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31557607697502468003620609 23668205773126851002715457)
              ·
                refine ⟨17751154329845138252036593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23668205773126851002715457 17751154329845138252036593)
                ·
                  refine ⟨13313365747383853689027445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17751154329845138252036593 13313365747383853689027445)
                  ·
                    refine ⟨1248128038817236283346323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13313365747383853689027445 1248128038817236283346323)
                    ·
                      rfl

theorem cell22_3646081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3646081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646081 prefixEnd_3646081 := by exact prefixLift 3646081
  have htrace : WordTrace (prefixWord ++ tailWord_3646081) baseStart_3646081 baseEnd_3646081 := by
    simpa [prefixWord, tailWord_3646081, baseEnd_3646081] using wordTrace_append hprefix tailTrace_3646081
  have hstable : (prefixWord ++ tailWord_3646081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646081).length < 2 ^ (prefixWord ++ tailWord_3646081).sum := by decide
  have hdescent : baseEnd_3646081 < baseStart_3646081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646098 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3646098 : Nat := 118140960795 + 3646098 * 2 ^ 59
def prefixEnd_3646098 : Nat := 4983230072969 + 3 ^ 40 * 3646098 * 2
def baseEnd_3646098 : Nat := 1248133858264653905671271

theorem tailTrace_3646098 : CollatzResearch.WordTrace tailWord_3646098 prefixEnd_3646098 1248133858264653905671271 := by
  unfold tailWord_3646098
  simp only [CollatzResearch.WordTrace]
  refine ⟨33246029786204281201878737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88656079429878083205009965 33246029786204281201878737)
  ·
    refine ⟨24934522339653210901409053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33246029786204281201878737 24934522339653210901409053)
    ·
      refine ⟨9350445877369954088028395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24934522339653210901409053 9350445877369954088028395)
      ·
        refine ⟨14025668816054931132042593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9350445877369954088028395 14025668816054931132042593)
        ·
          refine ⟨10519251612041198349031945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14025668816054931132042593 10519251612041198349031945)
          ·
            refine ⟨7889438709030898761773959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10519251612041198349031945 7889438709030898761773959)
            ·
              refine ⟨11834158063546348142660939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7889438709030898761773959 11834158063546348142660939)
              ·
                refine ⟨17751237095319522213991409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11834158063546348142660939 17751237095319522213991409)
                ·
                  refine ⟨13313427821489641660493557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17751237095319522213991409 13313427821489641660493557)
                  ·
                    refine ⟨1248133858264653905671271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13313427821489641660493557 1248133858264653905671271)
                    ·
                      rfl

theorem cell22_3646098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3646098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646098 prefixEnd_3646098 := by exact prefixLift 3646098
  have htrace : WordTrace (prefixWord ++ tailWord_3646098) baseStart_3646098 baseEnd_3646098 := by
    simpa [prefixWord, tailWord_3646098, baseEnd_3646098] using wordTrace_append hprefix tailTrace_3646098
  have hstable : (prefixWord ++ tailWord_3646098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646098).length < 2 ^ (prefixWord ++ tailWord_3646098).sum := by decide
  have hdescent : baseEnd_3646098 < baseStart_3646098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646134 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_3646134 : Nat := 118140960795 + 3646134 * 2 ^ 59
def prefixEnd_3646134 : Nat := 4983230072969 + 3 ^ 40 * 3646134 * 2
def baseEnd_3646134 : Nat := 416048727266787270590387

theorem tailTrace_3646134 : CollatzResearch.WordTrace tailWord_3646134 prefixEnd_3646134 416048727266787270590387 := by
  unfold tailWord_3646134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8311589510792918934739091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88656954781791135303883637 8311589510792918934739091)
  ·
    refine ⟨12467384266189378402108637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8311589510792918934739091 12467384266189378402108637)
    ·
      refine ⟨4675269099821016900790739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12467384266189378402108637 4675269099821016900790739)
      ·
        refine ⟨7012903649731525351186109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4675269099821016900790739 7012903649731525351186109)
        ·
          refine ⟨2629838868649322006694791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7012903649731525351186109 2629838868649322006694791)
          ·
            refine ⟨3944758302973983010042187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629838868649322006694791 3944758302973983010042187)
            ·
              refine ⟨5917137454460974515063281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944758302973983010042187 5917137454460974515063281)
              ·
                refine ⟨4437853090845730886297461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5917137454460974515063281 4437853090845730886297461)
                ·
                  refine ⟨416048727266787270590387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4437853090845730886297461 416048727266787270590387)
                  ·
                    rfl

theorem cell22_3646134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_3646134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646134 prefixEnd_3646134 := by exact prefixLift 3646134
  have htrace : WordTrace (prefixWord ++ tailWord_3646134) baseStart_3646134 baseEnd_3646134 := by
    simpa [prefixWord, tailWord_3646134, baseEnd_3646134] using wordTrace_append hprefix tailTrace_3646134
  have hstable : (prefixWord ++ tailWord_3646134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646134).length < 2 ^ (prefixWord ++ tailWord_3646134).sum := by decide
  have hdescent : baseEnd_3646134 < baseStart_3646134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646143 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 4, 3]
def baseStart_3646143 : Nat := 118140960795 + 3646143 * 2 ^ 59
def prefixEnd_3646143 : Nat := 4983230072969 + 3 ^ 40 * 3646143 * 2
def baseEnd_3646143 : Nat := 1248149262684288788296133

theorem tailTrace_3646143 : CollatzResearch.WordTrace tailWord_3646143 prefixEnd_3646143 1248149262684288788296133 := by
  unfold tailWord_3646143
  simp only [CollatzResearch.WordTrace]
  refine ⟨132985760429654097492903083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88657173619769398328602055 132985760429654097492903083)
  ·
    refine ⟨199478640644481146239354625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132985760429654097492903083 199478640644481146239354625)
    ·
      refine ⟨149608980483360859679515969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199478640644481146239354625 149608980483360859679515969)
      ·
        refine ⟨112206735362520644759636977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149608980483360859679515969 112206735362520644759636977)
        ·
          refine ⟨84155051521890483569727733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112206735362520644759636977 84155051521890483569727733)
          ·
            refine ⟨7889536080177232834661975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84155051521890483569727733 7889536080177232834661975)
            ·
              refine ⟨11834304120265849251992963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7889536080177232834661975 11834304120265849251992963)
              ·
                refine ⟨17751456180398773877989445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11834304120265849251992963 17751456180398773877989445)
                ·
                  refine ⟨3328398033824770102123021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17751456180398773877989445 3328398033824770102123021)
                  ·
                    refine ⟨1248149262684288788296133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3328398033824770102123021 1248149262684288788296133)
                    ·
                      rfl

theorem cell22_3646143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_3646143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646143 prefixEnd_3646143 := by exact prefixLift 3646143
  have htrace : WordTrace (prefixWord ++ tailWord_3646143) baseStart_3646143 baseEnd_3646143 := by
    simpa [prefixWord, tailWord_3646143, baseEnd_3646143] using wordTrace_append hprefix tailTrace_3646143
  have hstable : (prefixWord ++ tailWord_3646143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646143).length < 2 ^ (prefixWord ++ tailWord_3646143).sum := by decide
  have hdescent : baseEnd_3646143 < baseStart_3646143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646186 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_3646186 : Nat := 118140960795 + 3646186 * 2 ^ 59
def prefixEnd_3646186 : Nat := 4983230072969 + 3 ^ 40 * 3646186 * 2
def baseEnd_3646186 : Nat := 1248163982463051009471001

theorem tailTrace_3646186 : CollatzResearch.WordTrace tailWord_3646186 prefixEnd_3646186 1248163982463051009471001 := by
  unfold tailWord_3646186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33246832192124578959179603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88658219178998877224478941 33246832192124578959179603)
  ·
    refine ⟨49870248288186868438769405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33246832192124578959179603 49870248288186868438769405)
    ·
      refine ⟨18701343108070075664538527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49870248288186868438769405 18701343108070075664538527)
      ·
        refine ⟨28052014662105113496807791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18701343108070075664538527 28052014662105113496807791)
        ·
          refine ⟨42078021993157670245211687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28052014662105113496807791 42078021993157670245211687)
          ·
            refine ⟨63117032989736505367817531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42078021993157670245211687 63117032989736505367817531)
            ·
              refine ⟨94675549484604758051726297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63117032989736505367817531 94675549484604758051726297)
              ·
                refine ⟨71006662113453568538794723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94675549484604758051726297 71006662113453568538794723)
                ·
                  refine ⟨106509993170180352808192085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71006662113453568538794723 106509993170180352808192085)
                  ·
                    refine ⟨1248163982463051009471001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106509993170180352808192085 1248163982463051009471001)
                    ·
                      rfl

theorem cell22_3646186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_3646186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646186 prefixEnd_3646186 := by exact prefixLift 3646186
  have htrace : WordTrace (prefixWord ++ tailWord_3646186) baseStart_3646186 baseEnd_3646186 := by
    simpa [prefixWord, tailWord_3646186, baseEnd_3646186] using wordTrace_append hprefix tailTrace_3646186
  have hstable : (prefixWord ++ tailWord_3646186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646186).length < 2 ^ (prefixWord ++ tailWord_3646186).sum := by decide
  have hdescent : baseEnd_3646186 < baseStart_3646186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646196 : List Nat := [2, 6, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3646196 : Nat := 118140960795 + 3646196 * 2 ^ 59
def prefixEnd_3646196 : Nat := 4983230072969 + 3 ^ 40 * 3646196 * 2
def baseEnd_3646196 : Nat := 416055801889138105573657

theorem tailTrace_3646196 : CollatzResearch.WordTrace tailWord_3646196 prefixEnd_3646196 416055801889138105573657 := by
  unfold tailWord_3646196
  simp only [CollatzResearch.WordTrace]
  refine ⟨66493846749231043772291221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88658462332308058363054961 66493846749231043772291221)
  ·
    refine ⟨3116899066370205176826151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66493846749231043772291221 3116899066370205176826151)
    ·
      refine ⟨4675348599555307765239227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3116899066370205176826151 4675348599555307765239227)
      ·
        refine ⟨7013022899332961647858841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4675348599555307765239227 7013022899332961647858841)
        ·
          refine ⟨5259767174499721235894131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7013022899332961647858841 5259767174499721235894131)
          ·
            refine ⟨7889650761749581853841197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259767174499721235894131 7889650761749581853841197)
            ·
              refine ⟨2958619035656093195190449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7889650761749581853841197 2958619035656093195190449)
              ·
                refine ⟨2218964276742069896392837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2958619035656093195190449 2218964276742069896392837)
                ·
                  refine ⟨416055801889138105573657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2218964276742069896392837 416055801889138105573657)
                  ·
                    rfl

theorem cell22_3646196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3646196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646196 prefixEnd_3646196 := by exact prefixLift 3646196
  have htrace : WordTrace (prefixWord ++ tailWord_3646196) baseStart_3646196 baseEnd_3646196 := by
    simpa [prefixWord, tailWord_3646196, baseEnd_3646196] using wordTrace_append hprefix tailTrace_3646196
  have hstable : (prefixWord ++ tailWord_3646196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646196).length < 2 ^ (prefixWord ++ tailWord_3646196).sum := by decide
  have hdescent : baseEnd_3646196 < baseStart_3646196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646218 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_3646218 : Nat := 118140960795 + 3646218 * 2 ^ 59
def prefixEnd_3646218 : Nat := 4983230072969 + 3 ^ 40 * 3646218 * 2
def baseEnd_3646218 : Nat := 416058312239004530890301

theorem tailTrace_3646218 : CollatzResearch.WordTrace tailWord_3646218 prefixEnd_3646218 416058312239004530890301 := by
  unfold tailWord_3646218
  simp only [CollatzResearch.WordTrace]
  refine ⟨33247123976095596325470827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88658997269588256867922205 33247123976095596325470827)
  ·
    refine ⟨49870685964143394488206241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33247123976095596325470827 49870685964143394488206241)
    ·
      refine ⟨37403014473107545866154681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49870685964143394488206241 37403014473107545866154681)
      ·
        refine ⟨28052260854830659399616011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37403014473107545866154681 28052260854830659399616011)
        ·
          refine ⟨42078391282245989099424017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28052260854830659399616011 42078391282245989099424017)
          ·
            refine ⟨31558793461684491824568013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42078391282245989099424017 31558793461684491824568013)
            ·
              refine ⟨11834547548131684434213005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31558793461684491824568013 11834547548131684434213005)
              ·
                refine ⟨4437955330549381662829877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11834547548131684434213005 4437955330549381662829877)
                ·
                  refine ⟨416058312239004530890301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4437955330549381662829877 416058312239004530890301)
                  ·
                    rfl

theorem cell22_3646218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_3646218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646218 prefixEnd_3646218 := by exact prefixLift 3646218
  have htrace : WordTrace (prefixWord ++ tailWord_3646218) baseStart_3646218 baseEnd_3646218 := by
    simpa [prefixWord, tailWord_3646218, baseEnd_3646218] using wordTrace_append hprefix tailTrace_3646218
  have hstable : (prefixWord ++ tailWord_3646218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646218).length < 2 ^ (prefixWord ++ tailWord_3646218).sum := by decide
  have hdescent : baseEnd_3646218 < baseStart_3646218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646291 : List Nat := [1, 1, 1, 2, 1, 1, 3, 12]
def baseStart_3646291 : Nat := 118140960795 + 3646291 * 2 ^ 59
def prefixEnd_3646291 : Nat := 4983230072969 + 3 ^ 40 * 3646291 * 2
def baseEnd_3646291 : Nat := 138688880678762859510631

theorem tailTrace_3646291 : CollatzResearch.WordTrace tailWord_3646291 prefixEnd_3646291 138688880678762859510631 := by
  unfold tailWord_3646291
  simp only [CollatzResearch.WordTrace]
  refine ⟨132991158433117918769290727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88660772288745279179527151 132991158433117918769290727)
  ·
    refine ⟨199486737649676878153936091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132991158433117918769290727 199486737649676878153936091)
    ·
      refine ⟨299230106474515317230904137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199486737649676878153936091 299230106474515317230904137)
      ·
        refine ⟨224422579855886487923178103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299230106474515317230904137 224422579855886487923178103)
        ·
          refine ⟨336633869783829731884767155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224422579855886487923178103 336633869783829731884767155)
          ·
            refine ⟨504950804675744597827150733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336633869783829731884767155 504950804675744597827150733)
            ·
              refine ⟨189356551753404224185181525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504950804675744597827150733 189356551753404224185181525)
              ·
                refine ⟨138688880678762859510631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 189356551753404224185181525 138688880678762859510631)
                ·
                  rfl

theorem cell22_3646291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 12].length) (baseStart_3646291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646291 prefixEnd_3646291 := by exact prefixLift 3646291
  have htrace : WordTrace (prefixWord ++ tailWord_3646291) baseStart_3646291 baseEnd_3646291 := by
    simpa [prefixWord, tailWord_3646291, baseEnd_3646291] using wordTrace_append hprefix tailTrace_3646291
  have hstable : (prefixWord ++ tailWord_3646291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646291).length < 2 ^ (prefixWord ++ tailWord_3646291).sum := by decide
  have hdescent : baseEnd_3646291 < baseStart_3646291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646293 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_3646293 : Nat := 118140960795 + 3646293 * 2 ^ 59
def prefixEnd_3646293 : Nat := 4983230072969 + 3 ^ 40 * 3646293 * 2
def baseEnd_3646293 : Nat := 1248200610749738397045673

theorem tailTrace_3646293 : CollatzResearch.WordTrace tailWord_3646293 prefixEnd_3646293 1248200610749738397045673 := by
  unfold tailWord_3646293
  simp only [CollatzResearch.WordTrace]
  refine ⟨132991231379110673110863533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88660820919407115407242355 132991231379110673110863533)
  ·
    refine ⟨49871711767166502416573825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132991231379110673110863533 49871711767166502416573825)
    ·
      refine ⟨37403783825374876812430369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49871711767166502416573825 37403783825374876812430369)
      ·
        refine ⟨28052837869031157609322777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37403783825374876812430369 28052837869031157609322777)
        ·
          refine ⟨21039628401773368206992083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28052837869031157609322777 21039628401773368206992083)
          ·
            refine ⟨31559442602660052310488125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21039628401773368206992083 31559442602660052310488125)
            ·
              refine ⟨11834790975997519616433047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31559442602660052310488125 11834790975997519616433047)
              ·
                refine ⟨17752186463996279424649571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11834790975997519616433047 17752186463996279424649571)
                ·
                  refine ⟨26628279695994419136974357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17752186463996279424649571 26628279695994419136974357)
                  ·
                    refine ⟨1248200610749738397045673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26628279695994419136974357 1248200610749738397045673)
                    ·
                      rfl

theorem cell22_3646293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_3646293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646293 prefixEnd_3646293 := by exact prefixLift 3646293
  have htrace : WordTrace (prefixWord ++ tailWord_3646293) baseStart_3646293 baseEnd_3646293 := by
    simpa [prefixWord, tailWord_3646293, baseEnd_3646293] using wordTrace_append hprefix tailTrace_3646293
  have hstable : (prefixWord ++ tailWord_3646293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646293).length < 2 ^ (prefixWord ++ tailWord_3646293).sum := by decide
  have hdescent : baseEnd_3646293 < baseStart_3646293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646308 : List Nat := [2, 3, 1, 1, 4, 2, 9]
def baseStart_3646308 : Nat := 118140960795 + 3646308 * 2 ^ 59
def prefixEnd_3646308 : Nat := 4983230072969 + 3 ^ 40 * 3646308 * 2
def baseEnd_3646308 : Nat := 46229842428010494737801

theorem tailTrace_3646308 : CollatzResearch.WordTrace tailWord_3646308 prefixEnd_3646308 46229842428010494737801 := by
  unfold tailWord_3646308
  simp only [CollatzResearch.WordTrace]
  refine ⟨66495889237028165336329789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88661185649370887115106385 66495889237028165336329789)
  ·
    refine ⟨24935958463885562001123671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66495889237028165336329789 24935958463885562001123671)
    ·
      refine ⟨37403937695828343001685507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24935958463885562001123671 37403937695828343001685507)
      ·
        refine ⟨56105906543742514502528261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37403937695828343001685507 56105906543742514502528261)
        ·
          refine ⟨10519857476951721469224049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56105906543742514502528261 10519857476951721469224049)
          ·
            refine ⟨7889893107713791101918037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10519857476951721469224049 7889893107713791101918037)
            ·
              refine ⟨46229842428010494737801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7889893107713791101918037 46229842428010494737801)
              ·
                rfl

theorem cell22_3646308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 9].length) (baseStart_3646308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646308 prefixEnd_3646308 := by exact prefixLift 3646308
  have htrace : WordTrace (prefixWord ++ tailWord_3646308) baseStart_3646308 baseEnd_3646308 := by
    simpa [prefixWord, tailWord_3646308, baseEnd_3646308] using wordTrace_append hprefix tailTrace_3646308
  have hstable : (prefixWord ++ tailWord_3646308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646308).length < 2 ^ (prefixWord ++ tailWord_3646308).sum := by decide
  have hdescent : baseEnd_3646308 < baseStart_3646308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646312 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 2, 3]
def baseStart_3646312 : Nat := 118140960795 + 3646312 * 2 ^ 59
def prefixEnd_3646312 : Nat := 4983230072969 + 3 ^ 40 * 3646312 * 2
def baseEnd_3646312 : Nat := 1248207114838028680820615

theorem tailTrace_3646312 : CollatzResearch.WordTrace tailWord_3646312 prefixEnd_3646312 1248207114838028680820615 := by
  unfold tailWord_3646312
  simp only [CollatzResearch.WordTrace]
  refine ⟨66495962183020919677902595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88661282910694559570536793 66495962183020919677902595)
  ·
    refine ⟨99743943274531379516853893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66495962183020919677902595 99743943274531379516853893)
    ·
      refine ⟨18701989363974633659410105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99743943274531379516853893 18701989363974633659410105)
      ·
        refine ⟨14026492022980975244557579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18701989363974633659410105 14026492022980975244557579)
        ·
          refine ⟨21039738034471462866836369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14026492022980975244557579 21039738034471462866836369)
          ·
            refine ⟨15779803525853597150127277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21039738034471462866836369 15779803525853597150127277)
            ·
              refine ⟨5917426322195098931297729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15779803525853597150127277 5917426322195098931297729)
              ·
                refine ⟨4438069741646324198473297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5917426322195098931297729 4438069741646324198473297)
                ·
                  refine ⟨3328552306234743148854973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4438069741646324198473297 3328552306234743148854973)
                  ·
                    refine ⟨1248207114838028680820615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3328552306234743148854973 1248207114838028680820615)
                    ·
                      rfl

theorem cell22_3646312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_3646312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646312 prefixEnd_3646312 := by exact prefixLift 3646312
  have htrace : WordTrace (prefixWord ++ tailWord_3646312) baseStart_3646312 baseEnd_3646312 := by
    simpa [prefixWord, tailWord_3646312, baseEnd_3646312] using wordTrace_append hprefix tailTrace_3646312
  have hstable : (prefixWord ++ tailWord_3646312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646312).length < 2 ^ (prefixWord ++ tailWord_3646312).sum := by decide
  have hdescent : baseEnd_3646312 < baseStart_3646312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646368 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_3646368 : Nat := 118140960795 + 3646368 * 2 ^ 59
def prefixEnd_3646368 : Nat := 4983230072969 + 3 ^ 40 * 3646368 * 2
def baseEnd_3646368 : Nat := 1248226284782463201420443

theorem tailTrace_3646368 : CollatzResearch.WordTrace tailWord_3646368 prefixEnd_3646368 1248226284782463201420443 := by
  unfold tailWord_3646368
  simp only [CollatzResearch.WordTrace]
  refine ⟨66496983426919480459921879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88662644569225973946562505 66496983426919480459921879)
  ·
    refine ⟨99745475140379220689882819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66496983426919480459921879 99745475140379220689882819)
    ·
      refine ⟨149618212710568831034824229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99745475140379220689882819 149618212710568831034824229)
      ·
        refine ⟨28053414883231655819029543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149618212710568831034824229 28053414883231655819029543)
        ·
          refine ⟨42080122324847483728544315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28053414883231655819029543 42080122324847483728544315)
          ·
            refine ⟨63120183487271225592816473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42080122324847483728544315 63120183487271225592816473)
            ·
              refine ⟨47340137615453419194612355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63120183487271225592816473 47340137615453419194612355)
              ·
                refine ⟨71010206423180128791918533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47340137615453419194612355 71010206423180128791918533)
                ·
                  refine ⟨13314413704346274148484725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71010206423180128791918533 13314413704346274148484725)
                  ·
                    refine ⟨1248226284782463201420443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13314413704346274148484725 1248226284782463201420443)
                    ·
                      rfl

theorem cell22_3646368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_3646368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646368 prefixEnd_3646368 := by exact prefixLift 3646368
  have htrace : WordTrace (prefixWord ++ tailWord_3646368) baseStart_3646368 baseEnd_3646368 := by
    simpa [prefixWord, tailWord_3646368, baseEnd_3646368] using wordTrace_append hprefix tailTrace_3646368
  have hstable : (prefixWord ++ tailWord_3646368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646368).length < 2 ^ (prefixWord ++ tailWord_3646368).sum := by decide
  have hdescent : baseEnd_3646368 < baseStart_3646368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646370 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_3646370 : Nat := 118140960795 + 3646370 * 2 ^ 59
def prefixEnd_3646370 : Nat := 4983230072969 + 3 ^ 40 * 3646370 * 2
def baseEnd_3646370 : Nat := 416075656474445287623479

theorem tailTrace_3646370 : CollatzResearch.WordTrace tailWord_3646370 prefixEnd_3646370 416075656474445287623479 := by
  unfold tailWord_3646370
  simp only [CollatzResearch.WordTrace]
  refine ⟨33248509949957928815354141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88662693199887810174277709 33248509949957928815354141)
  ·
    refine ⟨12468191231234223305757803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33248509949957928815354141 12468191231234223305757803)
    ·
      refine ⟨18702286846851334958636705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12468191231234223305757803 18702286846851334958636705)
      ·
        refine ⟨14026715135138501218977529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18702286846851334958636705 14026715135138501218977529)
        ·
          refine ⟨10520036351353875914233147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14026715135138501218977529 10520036351353875914233147)
          ·
            refine ⟨15780054527030813871349721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10520036351353875914233147 15780054527030813871349721)
            ·
              refine ⟨11835040895273110403512291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15780054527030813871349721 11835040895273110403512291)
              ·
                refine ⟨17752561342909665605268437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11835040895273110403512291 17752561342909665605268437)
                ·
                  refine ⟨416075656474445287623479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17752561342909665605268437 416075656474445287623479)
                  ·
                    rfl

theorem cell22_3646370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_3646370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646370 prefixEnd_3646370 := by exact prefixLift 3646370
  have htrace : WordTrace (prefixWord ++ tailWord_3646370) baseStart_3646370 baseEnd_3646370 := by
    simpa [prefixWord, tailWord_3646370, baseEnd_3646370] using wordTrace_append hprefix tailTrace_3646370
  have hstable : (prefixWord ++ tailWord_3646370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646370).length < 2 ^ (prefixWord ++ tailWord_3646370).sum := by decide
  have hdescent : baseEnd_3646370 < baseStart_3646370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646400 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_3646400 : Nat := 118140960795 + 3646400 * 2 ^ 59
def prefixEnd_3646400 : Nat := 4983230072969 + 3 ^ 40 * 3646400 * 2
def baseEnd_3646400 : Nat := 1248237239036425784620345

theorem tailTrace_3646400 : CollatzResearch.WordTrace tailWord_3646400 prefixEnd_3646400 1248237239036425784620345 := by
  unfold tailWord_3646400
  simp only [CollatzResearch.WordTrace]
  refine ⟨66497566994861515192504327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88663422659815353590005769 66497566994861515192504327)
  ·
    refine ⟨99746350492292272788756491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66497566994861515192504327 99746350492292272788756491)
    ·
      refine ⟨149619525738438409183134737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99746350492292272788756491 149619525738438409183134737)
      ·
        refine ⟨112214644303828806887351053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149619525738438409183134737 112214644303828806887351053)
        ·
          refine ⟨42080491613935802582756645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112214644303828806887351053 42080491613935802582756645)
          ·
            refine ⟨7890092177612962984266871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42080491613935802582756645 7890092177612962984266871)
            ·
              refine ⟨11835138266419444476400307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7890092177612962984266871 11835138266419444476400307)
              ·
                refine ⟨17752707399629166714600461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11835138266419444476400307 17752707399629166714600461)
                ·
                  refine ⟨6657265274860937517975173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17752707399629166714600461 6657265274860937517975173)
                  ·
                    refine ⟨1248237239036425784620345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657265274860937517975173 1248237239036425784620345)
                    ·
                      rfl

theorem cell22_3646400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_3646400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646400 prefixEnd_3646400 := by exact prefixLift 3646400
  have htrace : WordTrace (prefixWord ++ tailWord_3646400) baseStart_3646400 baseEnd_3646400 := by
    simpa [prefixWord, tailWord_3646400, baseEnd_3646400] using wordTrace_append hprefix tailTrace_3646400
  have hstable : (prefixWord ++ tailWord_3646400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646400).length < 2 ^ (prefixWord ++ tailWord_3646400).sum := by decide
  have hdescent : baseEnd_3646400 < baseStart_3646400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646417 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 1, 4]
def baseStart_3646417 : Nat := 118140960795 + 3646417 * 2 ^ 59
def prefixEnd_3646417 : Nat := 4983230072969 + 3 ^ 40 * 3646417 * 2
def baseEnd_3646417 : Nat := 1248243058483843406945293

theorem tailTrace_3646417 : CollatzResearch.WordTrace tailWord_3646417 prefixEnd_3646417 1248243058483843406945293 := by
  unfold tailWord_3646417
  simp only [CollatzResearch.WordTrace]
  refine ⟨132995754030661442288377505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88663836020440961525585003 132995754030661442288377505)
  ·
    refine ⟨99746815522996081716283129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132995754030661442288377505 99746815522996081716283129)
    ·
      refine ⟨74810111642247061287212347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99746815522996081716283129 74810111642247061287212347)
      ·
        refine ⟨112215167463370591930818521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74810111642247061287212347 112215167463370591930818521)
        ·
          refine ⟨84161375597527943948113891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112215167463370591930818521 84161375597527943948113891)
          ·
            refine ⟨126242063396291915922170837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84161375597527943948113891 126242063396291915922170837)
            ·
              refine ⟨2958798360850591779425879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 126242063396291915922170837 2958798360850591779425879)
              ·
                refine ⟨4438197541275887669138819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958798360850591779425879 4438197541275887669138819)
                ·
                  refine ⟨6657296311913831503708229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438197541275887669138819 6657296311913831503708229)
                  ·
                    refine ⟨1248243058483843406945293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657296311913831503708229 1248243058483843406945293)
                    ·
                      rfl

theorem cell22_3646417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_3646417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646417 prefixEnd_3646417 := by exact prefixLift 3646417
  have htrace : WordTrace (prefixWord ++ tailWord_3646417) baseStart_3646417 baseEnd_3646417 := by
    simpa [prefixWord, tailWord_3646417, baseEnd_3646417] using wordTrace_append hprefix tailTrace_3646417
  have hstable : (prefixWord ++ tailWord_3646417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646417).length < 2 ^ (prefixWord ++ tailWord_3646417).sum := by decide
  have hdescent : baseEnd_3646417 < baseStart_3646417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646447 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 2, 3]
def baseStart_3646447 : Nat := 118140960795 + 3646447 * 2 ^ 59
def prefixEnd_3646447 : Nat := 4983230072969 + 3 ^ 40 * 3646447 * 2
def baseEnd_3646447 : Nat := 1248253328096933328695201

theorem tailTrace_3646447 : CollatzResearch.WordTrace tailWord_3646447 prefixEnd_3646447 1248253328096933328695201 := by
  unfold tailWord_3646447
  simp only [CollatzResearch.WordTrace]
  refine ⟨132996848220552757411969595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88664565480368504941313063 132996848220552757411969595)
  ·
    refine ⟨199495272330829136117954393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132996848220552757411969595 199495272330829136117954393)
    ·
      refine ⟨149621454248121852088465795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199495272330829136117954393 149621454248121852088465795)
      ·
        refine ⟨224432181372182778132698693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149621454248121852088465795 224432181372182778132698693)
        ·
          refine ⟨42081034007284270899881005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224432181372182778132698693 42081034007284270899881005)
          ·
            refine ⟨15780387752731601587455377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42081034007284270899881005 15780387752731601587455377)
            ·
              refine ⟨11835290814548701190591533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15780387752731601587455377 11835290814548701190591533)
              ·
                refine ⟨4438234055455762946471825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11835290814548701190591533 4438234055455762946471825)
                ·
                  refine ⟨3328675541591822209853869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4438234055455762946471825 3328675541591822209853869)
                  ·
                    refine ⟨1248253328096933328695201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3328675541591822209853869 1248253328096933328695201)
                    ·
                      rfl

theorem cell22_3646447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_3646447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646447 prefixEnd_3646447 := by exact prefixLift 3646447
  have htrace : WordTrace (prefixWord ++ tailWord_3646447) baseStart_3646447 baseEnd_3646447 := by
    simpa [prefixWord, tailWord_3646447, baseEnd_3646447] using wordTrace_append hprefix tailTrace_3646447
  have hstable : (prefixWord ++ tailWord_3646447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646447).length < 2 ^ (prefixWord ++ tailWord_3646447).sum := by decide
  have hdescent : baseEnd_3646447 < baseStart_3646447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646569 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 1, 4]
def baseStart_3646569 : Nat := 118140960795 + 3646569 * 2 ^ 59
def prefixEnd_3646569 : Nat := 4983230072969 + 3 ^ 40 * 3646569 * 2
def baseEnd_3646569 : Nat := 1248295091190165677144827

theorem tailTrace_3646569 : CollatzResearch.WordTrace tailWord_3646569 prefixEnd_3646569 1248295091190165677144827 := by
  unfold tailWord_3646569
  simp only [CollatzResearch.WordTrace]
  refine ⟨133001297926110772247910761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88667531950740514831940507 133001297926110772247910761)
  ·
    refine ⟨99750973444583079185933071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133001297926110772247910761 99750973444583079185933071)
    ·
      refine ⟨149626460166874618778899607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99750973444583079185933071 149626460166874618778899607)
      ·
        refine ⟨224439690250311928168349411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149626460166874618778899607 224439690250311928168349411)
        ·
          refine ⟨336659535375467892252524117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224439690250311928168349411 336659535375467892252524117)
          ·
            refine ⟨3945228930181264362334267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 336659535375467892252524117 3945228930181264362334267)
            ·
              refine ⟨5917843395271896543501401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945228930181264362334267 5917843395271896543501401)
              ·
                refine ⟨4438382546453922407626051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5917843395271896543501401 4438382546453922407626051)
                ·
                  refine ⟨6657573819680883611439077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438382546453922407626051 6657573819680883611439077)
                  ·
                    refine ⟨1248295091190165677144827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657573819680883611439077 1248295091190165677144827)
                    ·
                      rfl

theorem cell22_3646569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_3646569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646569 prefixEnd_3646569 := by exact prefixLift 3646569
  have htrace : WordTrace (prefixWord ++ tailWord_3646569) baseStart_3646569 baseEnd_3646569 := by
    simpa [prefixWord, tailWord_3646569, baseEnd_3646569] using wordTrace_append hprefix tailTrace_3646569
  have hstable : (prefixWord ++ tailWord_3646569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646569).length < 2 ^ (prefixWord ++ tailWord_3646569).sum := by decide
  have hdescent : baseEnd_3646569 < baseStart_3646569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646601 : List Nat := [1, 2, 1, 1, 4, 5, 2, 2, 4]
def baseStart_3646601 : Nat := 118140960795 + 3646601 * 2 ^ 59
def prefixEnd_3646601 : Nat := 4983230072969 + 3 ^ 40 * 3646601 * 2
def baseEnd_3646601 : Nat := 416102015148042753448243

theorem tailTrace_3646601 : CollatzResearch.WordTrace tailWord_3646601 prefixEnd_3646601 416102015148042753448243 := by
  unfold tailWord_3646601
  simp only [CollatzResearch.WordTrace]
  refine ⟨133002465061994841713075657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88668310041329894475383771 133002465061994841713075657)
  ·
    refine ⟨99751848796496131284806743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133002465061994841713075657 99751848796496131284806743)
    ·
      refine ⟨149627773194744196927210115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99751848796496131284806743 149627773194744196927210115)
      ·
        refine ⟨224441659792116295390815173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149627773194744196927210115 224441659792116295390815173)
        ·
          refine ⟨42082811211021805385777845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224441659792116295390815173 42082811211021805385777845)
          ·
            refine ⟨3945263551033294254916673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42082811211021805385777845 3945263551033294254916673)
            ·
              refine ⟨2958947663274970691187505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3945263551033294254916673 2958947663274970691187505)
              ·
                refine ⟨2219210747456228018390629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2958947663274970691187505 2219210747456228018390629)
                ·
                  refine ⟨416102015148042753448243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219210747456228018390629 416102015148042753448243)
                  ·
                    rfl

theorem cell22_3646601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 4].length) (baseStart_3646601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646601 prefixEnd_3646601 := by exact prefixLift 3646601
  have htrace : WordTrace (prefixWord ++ tailWord_3646601) baseStart_3646601 baseEnd_3646601 := by
    simpa [prefixWord, tailWord_3646601, baseEnd_3646601] using wordTrace_append hprefix tailTrace_3646601
  have hstable : (prefixWord ++ tailWord_3646601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646601).length < 2 ^ (prefixWord ++ tailWord_3646601).sum := by decide
  have hdescent : baseEnd_3646601 < baseStart_3646601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646631 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3646631 : Nat := 118140960795 + 3646631 * 2 ^ 59
def prefixEnd_3646631 : Nat := 4983230072969 + 3 ^ 40 * 3646631 * 2
def baseEnd_3646631 : Nat := 1248316315057218182094637

theorem tailTrace_3646631 : CollatzResearch.WordTrace tailWord_3646631 prefixEnd_3646631 1248316315057218182094637 := by
  unfold tailWord_3646631
  simp only [CollatzResearch.WordTrace]
  refine ⟨133003559251886156836667747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88669039501257437891111831 133003559251886156836667747)
  ·
    refine ⟨199505338877829235255001621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133003559251886156836667747 199505338877829235255001621)
    ·
      refine ⟨9351812759898245402578201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199505338877829235255001621 9351812759898245402578201)
      ·
        refine ⟨7013859569923684051933651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9351812759898245402578201 7013859569923684051933651)
        ·
          refine ⟨10520789354885526077900477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7013859569923684051933651 10520789354885526077900477)
          ·
            refine ⟨3945296008082072279212679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10520789354885526077900477 3945296008082072279212679)
            ·
              refine ⟨5917944012123108418819019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945296008082072279212679 5917944012123108418819019)
              ·
                refine ⟨8876916018184662628228529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917944012123108418819019 8876916018184662628228529)
                ·
                  refine ⟨6657687013638496971171397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8876916018184662628228529 6657687013638496971171397)
                  ·
                    refine ⟨1248316315057218182094637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657687013638496971171397 1248316315057218182094637)
                    ·
                      rfl

theorem cell22_3646631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3646631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646631 prefixEnd_3646631 := by exact prefixLift 3646631
  have htrace : WordTrace (prefixWord ++ tailWord_3646631) baseStart_3646631 baseEnd_3646631 := by
    simpa [prefixWord, tailWord_3646631, baseEnd_3646631] using wordTrace_append hprefix tailTrace_3646631
  have hstable : (prefixWord ++ tailWord_3646631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646631).length < 2 ^ (prefixWord ++ tailWord_3646631).sum := by decide
  have hdescent : baseEnd_3646631 < baseStart_3646631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646640 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 9]
def baseStart_3646640 : Nat := 118140960795 + 3646640 * 2 ^ 59
def prefixEnd_3646640 : Nat := 4983230072969 + 3 ^ 40 * 3646640 * 2
def baseEnd_3646640 : Nat := 416106465313715052873203

theorem tailTrace_3646640 : CollatzResearch.WordTrace tailWord_3646640 prefixEnd_3646640 416106465313715052873203 := by
  unfold tailWord_3646640
  simp only [CollatzResearch.WordTrace]
  refine ⟨66501943754426775686872687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88669258339235700915830249 66501943754426775686872687)
  ·
    refine ⟨99752915631640163530309031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66501943754426775686872687 99752915631640163530309031)
    ·
      refine ⟨149629373447460245295463547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99752915631640163530309031 149629373447460245295463547)
      ·
        refine ⟨224444060171190367943195321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149629373447460245295463547 224444060171190367943195321)
        ·
          refine ⟨168333045128392775957396491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224444060171190367943195321 168333045128392775957396491)
          ·
            refine ⟨252499567692589163936094737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168333045128392775957396491 252499567692589163936094737)
            ·
              refine ⟨189374675769441872952071053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252499567692589163936094737 189374675769441872952071053)
              ·
                refine ⟨71015503413540702357026645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189374675769441872952071053 71015503413540702357026645)
                ·
                  refine ⟨416106465313715052873203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71015503413540702357026645 416106465313715052873203)
                  ·
                    rfl

theorem cell22_3646640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_3646640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646640 prefixEnd_3646640 := by exact prefixLift 3646640
  have htrace : WordTrace (prefixWord ++ tailWord_3646640) baseStart_3646640 baseEnd_3646640 := by
    simpa [prefixWord, tailWord_3646640, baseEnd_3646640] using wordTrace_append hprefix tailTrace_3646640
  have hstable : (prefixWord ++ tailWord_3646640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646640).length < 2 ^ (prefixWord ++ tailWord_3646640).sum := by decide
  have hdescent : baseEnd_3646640 < baseStart_3646640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646646 : List Nat := [5, 1, 3, 2, 1, 1, 9]
def baseStart_3646646 : Nat := 118140960795 + 3646646 * 2 ^ 59
def prefixEnd_3646646 : Nat := 4983230072969 + 3 ^ 40 * 3646646 * 2
def baseEnd_3646646 : Nat := 46234127772731968258133

theorem tailTrace_3646646 : CollatzResearch.WordTrace tailWord_3646646 prefixEnd_3646646 46234127772731968258133 := by
  unfold tailWord_3646646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312756646676988399903987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88669404231221209598975861 8312756646676988399903987)
  ·
    refine ⟨12469134970015482599855981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312756646676988399903987 12469134970015482599855981)
    ·
      refine ⟨4675925613755805974945993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12469134970015482599855981 4675925613755805974945993)
      ·
        refine ⟨3506944210316854481209495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4675925613755805974945993 3506944210316854481209495)
        ·
          refine ⟨5260416315475281721814243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3506944210316854481209495 5260416315475281721814243)
          ·
            refine ⟨7890624473212922582721365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260416315475281721814243 7890624473212922582721365)
            ·
              refine ⟨46234127772731968258133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7890624473212922582721365 46234127772731968258133)
              ·
                rfl

theorem cell22_3646646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 9].length) (baseStart_3646646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646646 prefixEnd_3646646 := by exact prefixLift 3646646
  have htrace : WordTrace (prefixWord ++ tailWord_3646646) baseStart_3646646 baseEnd_3646646 := by
    simpa [prefixWord, tailWord_3646646, baseEnd_3646646] using wordTrace_append hprefix tailTrace_3646646
  have hstable : (prefixWord ++ tailWord_3646646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646646).length < 2 ^ (prefixWord ++ tailWord_3646646).sum := by decide
  have hdescent : baseEnd_3646646 < baseStart_3646646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646687 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 3, 4]
def baseStart_3646687 : Nat := 118140960795 + 3646687 * 2 ^ 59
def prefixEnd_3646687 : Nat := 4983230072969 + 3 ^ 40 * 3646687 * 2
def baseEnd_3646687 : Nat := 1248335485001652702694465

theorem tailTrace_3646687 : CollatzResearch.WordTrace tailWord_3646687 prefixEnd_3646687 1248335485001652702694465 := by
  unfold tailWord_3646687
  simp only [CollatzResearch.WordTrace]
  refine ⟨133005601739683278400706315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88670401159788852267137543 133005601739683278400706315)
  ·
    refine ⟨199508402609524917601059473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133005601739683278400706315 199508402609524917601059473)
    ·
      refine ⟨149631301957143688200794605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199508402609524917601059473 149631301957143688200794605)
      ·
        refine ⟨56111738233928883075297977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149631301957143688200794605 56111738233928883075297977)
        ·
          refine ⟨42083803675446662306473483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56111738233928883075297977 42083803675446662306473483)
          ·
            refine ⟨63125705513169993459710225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42083803675446662306473483 63125705513169993459710225)
            ·
              refine ⟨47344279134877495094782669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63125705513169993459710225 47344279134877495094782669)
              ·
                refine ⟨17754104675579060660543501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47344279134877495094782669 17754104675579060660543501)
                ·
                  refine ⟨6657789253342147747703813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17754104675579060660543501 6657789253342147747703813)
                  ·
                    refine ⟨1248335485001652702694465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657789253342147747703813 1248335485001652702694465)
                    ·
                      rfl

theorem cell22_3646687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_3646687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646687 prefixEnd_3646687 := by exact prefixLift 3646687
  have htrace : WordTrace (prefixWord ++ tailWord_3646687) baseStart_3646687 baseEnd_3646687 := by
    simpa [prefixWord, tailWord_3646687, baseEnd_3646687] using wordTrace_append hprefix tailTrace_3646687
  have hstable : (prefixWord ++ tailWord_3646687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646687).length < 2 ^ (prefixWord ++ tailWord_3646687).sum := by decide
  have hdescent : baseEnd_3646687 < baseStart_3646687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646695 : List Nat := [1, 1, 5, 3, 2, 2, 1, 3, 1, 3]
def baseStart_3646695 : Nat := 118140960795 + 3646695 * 2 ^ 59
def prefixEnd_3646695 : Nat := 4983230072969 + 3 ^ 40 * 3646695 * 2
def baseEnd_3646695 : Nat := 1248338223565143348494441

theorem tailTrace_3646695 : CollatzResearch.WordTrace tailWord_3646695 prefixEnd_3646695 1248338223565143348494441 := by
  unfold tailWord_3646695
  simp only [CollatzResearch.WordTrace]
  refine ⟨133005893523654295766997539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88670595682436197177998359 133005893523654295766997539)
  ·
    refine ⟨199508840285481443650496309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133005893523654295766997539 199508840285481443650496309)
    ·
      refine ⟨18703953776763885342234029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199508840285481443650496309 18703953776763885342234029)
      ·
        refine ⟨7013982666286457003337761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18703953776763885342234029 7013982666286457003337761)
        ·
          refine ⟨5260486999714842752503321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7013982666286457003337761 5260486999714842752503321)
          ·
            refine ⟨3945365249786132064377491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5260486999714842752503321 3945365249786132064377491)
            ·
              refine ⟨5918047874679198096566237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945365249786132064377491 5918047874679198096566237)
              ·
                refine ⟨2219267953004699286212339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5918047874679198096566237 2219267953004699286212339)
                ·
                  refine ⟨3328901929507048929318509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219267953004699286212339 3328901929507048929318509)
                  ·
                    refine ⟨1248338223565143348494441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3328901929507048929318509 1248338223565143348494441)
                    ·
                      rfl

theorem cell22_3646695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_3646695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646695 prefixEnd_3646695 := by exact prefixLift 3646695
  have htrace : WordTrace (prefixWord ++ tailWord_3646695) baseStart_3646695 baseEnd_3646695 := by
    simpa [prefixWord, tailWord_3646695, baseEnd_3646695] using wordTrace_append hprefix tailTrace_3646695
  have hstable : (prefixWord ++ tailWord_3646695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646695).length < 2 ^ (prefixWord ++ tailWord_3646695).sum := by decide
  have hdescent : baseEnd_3646695 < baseStart_3646695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646702 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_3646702 : Nat := 118140960795 + 3646702 * 2 ^ 59
def prefixEnd_3646702 : Nat := 4983230072969 + 3 ^ 40 * 3646702 * 2
def baseEnd_3646702 : Nat := 416113539936065887856473

theorem tailTrace_3646702 : CollatzResearch.WordTrace tailWord_3646702 prefixEnd_3646702 416113539936065887856473 := by
  unfold tailWord_3646702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16625768604328616995312795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88670765889752623975001573 16625768604328616995312795)
  ·
    refine ⟨24938652906492925492969193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16625768604328616995312795 24938652906492925492969193)
    ·
      refine ⟨18703989679869694119726895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24938652906492925492969193 18703989679869694119726895)
      ·
        refine ⟨28055984519804541179590343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18703989679869694119726895 28055984519804541179590343)
        ·
          refine ⟨42083976779706811769385515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28055984519804541179590343 42083976779706811769385515)
          ·
            refine ⟨63125965169560217654078273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42083976779706811769385515 63125965169560217654078273)
            ·
              refine ⟨47344473877170163240558705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63125965169560217654078273 47344473877170163240558705)
              ·
                refine ⟨35508355407877622430419029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47344473877170163240558705 35508355407877622430419029)
                ·
                  refine ⟨416113539936065887856473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35508355407877622430419029 416113539936065887856473)
                  ·
                    rfl

theorem cell22_3646702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_3646702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646702 prefixEnd_3646702 := by exact prefixLift 3646702
  have htrace : WordTrace (prefixWord ++ tailWord_3646702) baseStart_3646702 baseEnd_3646702 := by
    simpa [prefixWord, tailWord_3646702, baseEnd_3646702] using wordTrace_append hprefix tailTrace_3646702
  have hstable : (prefixWord ++ tailWord_3646702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646702).length < 2 ^ (prefixWord ++ tailWord_3646702).sum := by decide
  have hdescent : baseEnd_3646702 < baseStart_3646702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646719 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 6]
def baseStart_3646719 : Nat := 118140960795 + 3646719 * 2 ^ 59
def prefixEnd_3646719 : Nat := 4983230072969 + 3 ^ 40 * 3646719 * 2
def baseEnd_3646719 : Nat := 416115479751871761964789

theorem tailTrace_3646719 : CollatzResearch.WordTrace tailWord_3646719 prefixEnd_3646719 416115479751871761964789 := by
  unfold tailWord_3646719
  simp only [CollatzResearch.WordTrace]
  refine ⟨133006768875567347865871211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88671179250378231910580807 133006768875567347865871211)
  ·
    refine ⟨199510153313351021798806817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133006768875567347865871211 199510153313351021798806817)
    ·
      refine ⟨149632614985013266349105113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199510153313351021798806817 149632614985013266349105113)
      ·
        refine ⟨112224461238759949761828835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149632614985013266349105113 112224461238759949761828835)
        ·
          refine ⟨168336691858139924642743253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112224461238759949761828835 168336691858139924642743253)
          ·
            refine ⟨3945391215425154483814295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168336691858139924642743253 3945391215425154483814295)
            ·
              refine ⟨5918086823137731725721443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945391215425154483814295 5918086823137731725721443)
              ·
                refine ⟨8877130234706597588582165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918086823137731725721443 8877130234706597588582165)
                ·
                  refine ⟨416115479751871761964789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8877130234706597588582165 416115479751871761964789)
                  ·
                    rfl

theorem cell22_3646719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 6].length) (baseStart_3646719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646719 prefixEnd_3646719 := by exact prefixLift 3646719
  have htrace : WordTrace (prefixWord ++ tailWord_3646719) baseStart_3646719 baseEnd_3646719 := by
    simpa [prefixWord, tailWord_3646719, baseEnd_3646719] using wordTrace_append hprefix tailTrace_3646719
  have hstable : (prefixWord ++ tailWord_3646719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646719).length < 2 ^ (prefixWord ++ tailWord_3646719).sum := by decide
  have hdescent : baseEnd_3646719 < baseStart_3646719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646738 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3646738 : Nat := 118140960795 + 3646738 * 2 ^ 59
def prefixEnd_3646738 : Nat := 4983230072969 + 3 ^ 40 * 3646738 * 2
def baseEnd_3646738 : Nat := 1248352943343905569669309

theorem tailTrace_3646738 : CollatzResearch.WordTrace tailWord_3646738 prefixEnd_3646738 1248352943343905569669309 := by
  unfold tailWord_3646738
  simp only [CollatzResearch.WordTrace]
  refine ⟨33251865465624628527703217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88671641241665676073875245 33251865465624628527703217)
  ·
    refine ⟨24938899099218471395777413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33251865465624628527703217 24938899099218471395777413)
    ·
      refine ⟨4676043581103463386708265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24938899099218471395777413 4676043581103463386708265)
      ·
        refine ⟨3507032685827597540031199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4676043581103463386708265 3507032685827597540031199)
        ·
          refine ⟨5260549028741396310046799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507032685827597540031199 5260549028741396310046799)
          ·
            refine ⟨7890823543112094465070199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260549028741396310046799 7890823543112094465070199)
            ·
              refine ⟨11836235314668141697605299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7890823543112094465070199 11836235314668141697605299)
              ·
                refine ⟨17754352972002212546407949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11836235314668141697605299 17754352972002212546407949)
                ·
                  refine ⟨6657882364500829704902981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17754352972002212546407949 6657882364500829704902981)
                  ·
                    refine ⟨1248352943343905569669309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657882364500829704902981 1248352943343905569669309)
                    ·
                      rfl

theorem cell22_3646738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3646738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646738 prefixEnd_3646738 := by exact prefixLift 3646738
  have htrace : WordTrace (prefixWord ++ tailWord_3646738) baseStart_3646738 baseEnd_3646738 := by
    simpa [prefixWord, tailWord_3646738, baseEnd_3646738] using wordTrace_append hprefix tailTrace_3646738
  have hstable : (prefixWord ++ tailWord_3646738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646738).length < 2 ^ (prefixWord ++ tailWord_3646738).sum := by decide
  have hdescent : baseEnd_3646738 < baseStart_3646738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646792 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 9]
def baseStart_3646792 : Nat := 118140960795 + 3646792 * 2 ^ 59
def prefixEnd_3646792 : Nat := 4983230072969 + 3 ^ 40 * 3646792 * 2
def baseEnd_3646792 : Nat := 416123809549155809606381

theorem tailTrace_3646792 : CollatzResearch.WordTrace tailWord_3646792 prefixEnd_3646792 416123809549155809606381 := by
  unfold tailWord_3646792
  simp only [CollatzResearch.WordTrace]
  refine ⟨66504715702151440666639315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88672954269535254222185753 66504715702151440666639315)
  ·
    refine ⟨99757073553227160999958973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66504715702151440666639315 99757073553227160999958973)
    ·
      refine ⟨37408902582460185374984615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99757073553227160999958973 37408902582460185374984615)
      ·
        refine ⟨56113353873690278062476923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37408902582460185374984615 56113353873690278062476923)
        ·
          refine ⟨84170030810535417093715385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56113353873690278062476923 84170030810535417093715385)
          ·
            refine ⟨63127523107901562820286539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84170030810535417093715385 63127523107901562820286539)
            ·
              refine ⟨94691284661852344230429809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63127523107901562820286539 94691284661852344230429809)
              ·
                refine ⟨71018463496389258172822357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94691284661852344230429809 71018463496389258172822357)
                ·
                  refine ⟨416123809549155809606381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71018463496389258172822357 416123809549155809606381)
                  ·
                    rfl

theorem cell22_3646792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_3646792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646792 prefixEnd_3646792 := by exact prefixLift 3646792
  have htrace : WordTrace (prefixWord ++ tailWord_3646792) baseStart_3646792 baseEnd_3646792 := by
    simpa [prefixWord, tailWord_3646792, baseEnd_3646792] using wordTrace_append hprefix tailTrace_3646792
  have hstable : (prefixWord ++ tailWord_3646792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646792).length < 2 ^ (prefixWord ++ tailWord_3646792).sum := by decide
  have hdescent : baseEnd_3646792 < baseStart_3646792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646796 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_3646796 : Nat := 118140960795 + 3646796 * 2 ^ 59
def prefixEnd_3646796 : Nat := 4983230072969 + 3 ^ 40 * 3646796 * 2
def baseEnd_3646796 : Nat := 1248372797929212751719131

theorem tailTrace_3646796 : CollatzResearch.WordTrace tailWord_3646796 prefixEnd_3646796 1248372797929212751719131 := by
  unfold tailWord_3646796
  simp only [CollatzResearch.WordTrace]
  refine ⟨66504788648144195008212121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88673051530858926677616161 66504788648144195008212121)
  ·
    refine ⟨49878591486108146256159091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66504788648144195008212121 49878591486108146256159091)
    ·
      refine ⟨74817887229162219384238637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49878591486108146256159091 74817887229162219384238637)
      ·
        refine ⟨28056707710935832269089489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74817887229162219384238637 28056707710935832269089489)
        ·
          refine ⟨21042530783201874201817117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28056707710935832269089489 21042530783201874201817117)
          ·
            refine ⟨7890949043700702825681419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21042530783201874201817117 7890949043700702825681419)
            ·
              refine ⟨11836423565551054238522129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7890949043700702825681419 11836423565551054238522129)
              ·
                refine ⟨8877317674163290678891597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11836423565551054238522129 8877317674163290678891597)
                ·
                  refine ⟨3328994127811234004584349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8877317674163290678891597 3328994127811234004584349)
                  ·
                    refine ⟨1248372797929212751719131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3328994127811234004584349 1248372797929212751719131)
                    ·
                      rfl

theorem cell22_3646796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_3646796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646796 prefixEnd_3646796 := by exact prefixLift 3646796
  have htrace : WordTrace (prefixWord ++ tailWord_3646796) baseStart_3646796 baseEnd_3646796 := by
    simpa [prefixWord, tailWord_3646796, baseEnd_3646796] using wordTrace_append hprefix tailTrace_3646796
  have hstable : (prefixWord ++ tailWord_3646796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646796).length < 2 ^ (prefixWord ++ tailWord_3646796).sum := by decide
  have hdescent : baseEnd_3646796 < baseStart_3646796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646806 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3646806 : Nat := 118140960795 + 3646806 * 2 ^ 59
def prefixEnd_3646806 : Nat := 4983230072969 + 3 ^ 40 * 3646806 * 2
def baseEnd_3646806 : Nat := 1248376221133576058969101

theorem tailTrace_3646806 : CollatzResearch.WordTrace tailWord_3646806 prefixEnd_3646806 1248376221133576058969101 := by
  unfold tailWord_3646806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8313121376640760107768017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88673294684168107816192181 8313121376640760107768017)
  ·
    refine ⟨6234841032480570080826013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8313121376640760107768017 6234841032480570080826013)
    ·
      refine ⟨2338065387180213780309755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6234841032480570080826013 2338065387180213780309755)
      ·
        refine ⟨3507098080770320670464633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2338065387180213780309755 3507098080770320670464633)
        ·
          refine ⟨2630323560577740502848475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3507098080770320670464633 2630323560577740502848475)
          ·
            refine ⟨3945485340866610754272713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630323560577740502848475 3945485340866610754272713)
            ·
              refine ⟨2959114005649958065704535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3945485340866610754272713 2959114005649958065704535)
              ·
                refine ⟨4438671008474937098556803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959114005649958065704535 4438671008474937098556803)
                ·
                  refine ⟨6658006512712405647835205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438671008474937098556803 6658006512712405647835205)
                  ·
                    refine ⟨1248376221133576058969101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6658006512712405647835205 1248376221133576058969101)
                    ·
                      rfl

theorem cell22_3646806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3646806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646806 prefixEnd_3646806 := by exact prefixLift 3646806
  have htrace : WordTrace (prefixWord ++ tailWord_3646806) baseStart_3646806 baseEnd_3646806 := by
    simpa [prefixWord, tailWord_3646806, baseEnd_3646806] using wordTrace_append hprefix tailTrace_3646806
  have hstable : (prefixWord ++ tailWord_3646806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646806).length < 2 ^ (prefixWord ++ tailWord_3646806).sum := by decide
  have hdescent : baseEnd_3646806 < baseStart_3646806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646826 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_3646826 : Nat := 118140960795 + 3646826 * 2 ^ 59
def prefixEnd_3646826 : Nat := 4983230072969 + 3 ^ 40 * 3646826 * 2
def baseEnd_3646826 : Nat := 416127689180767557823013

theorem tailTrace_3646826 : CollatzResearch.WordTrace tailWord_3646826 prefixEnd_3646826 416127689180767557823013 := by
  unfold tailWord_3646826
  simp only [CollatzResearch.WordTrace]
  refine ⟨33252667871544926285004083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88673780990786470093344221 33252667871544926285004083)
  ·
    refine ⟨49879001807317389427506125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33252667871544926285004083 49879001807317389427506125)
    ·
      refine ⟨18704625677744021035314797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49879001807317389427506125 18704625677744021035314797)
      ·
        refine ⟨7014234629154007888243049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18704625677744021035314797 7014234629154007888243049)
        ·
          refine ⟨5260675971865505916182287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7014234629154007888243049 5260675971865505916182287)
          ·
            refine ⟨7891013957798258874273431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260675971865505916182287 7891013957798258874273431)
            ·
              refine ⟨11836520936697388311410147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891013957798258874273431 11836520936697388311410147)
              ·
                refine ⟨17754781405046082467115221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11836520936697388311410147 17754781405046082467115221)
                ·
                  refine ⟨416127689180767557823013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17754781405046082467115221 416127689180767557823013)
                  ·
                    rfl

theorem cell22_3646826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_3646826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646826 prefixEnd_3646826 := by exact prefixLift 3646826
  have htrace : WordTrace (prefixWord ++ tailWord_3646826) baseStart_3646826 baseEnd_3646826 := by
    simpa [prefixWord, tailWord_3646826, baseEnd_3646826] using wordTrace_append hprefix tailTrace_3646826
  have hstable : (prefixWord ++ tailWord_3646826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646826).length < 2 ^ (prefixWord ++ tailWord_3646826).sum := by decide
  have hdescent : baseEnd_3646826 < baseStart_3646826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646830 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_3646830 : Nat := 118140960795 + 3646830 * 2 ^ 59
def prefixEnd_3646830 : Nat := 4983230072969 + 3 ^ 40 * 3646830 * 2
def baseEnd_3646830 : Nat := 1248384436824047996369027

theorem tailTrace_3646830 : CollatzResearch.WordTrace tailWord_3646830 prefixEnd_3646830 1248384436824047996369027 := by
  unfold tailWord_3646830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16626352172270651727895243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88673878252110142548774629 16626352172270651727895243)
  ·
    refine ⟨24939528258405977591842865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16626352172270651727895243 24939528258405977591842865)
    ·
      refine ⟨18704646193804483193882149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24939528258405977591842865 18704646193804483193882149)
      ·
        refine ⟨3507121161338340598852903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18704646193804483193882149 3507121161338340598852903)
        ·
          refine ⟨5260681742007510898279355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507121161338340598852903 5260681742007510898279355)
          ·
            refine ⟨7891022613011266347419033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260681742007510898279355 7891022613011266347419033)
            ·
              refine ⟨5918266959758449760564275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7891022613011266347419033 5918266959758449760564275)
              ·
                refine ⟨8877400439637674640846413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918266959758449760564275 8877400439637674640846413)
                ·
                  refine ⟨3329025164864127990317405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8877400439637674640846413 3329025164864127990317405)
                  ·
                    refine ⟨1248384436824047996369027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3329025164864127990317405 1248384436824047996369027)
                    ·
                      rfl

theorem cell22_3646830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_3646830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646830 prefixEnd_3646830 := by exact prefixLift 3646830
  have htrace : WordTrace (prefixWord ++ tailWord_3646830) baseStart_3646830 baseEnd_3646830 := by
    simpa [prefixWord, tailWord_3646830, baseEnd_3646830] using wordTrace_append hprefix tailTrace_3646830
  have hstable : (prefixWord ++ tailWord_3646830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646830).length < 2 ^ (prefixWord ++ tailWord_3646830).sum := by decide
  have hdescent : baseEnd_3646830 < baseStart_3646830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646856 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_3646856 : Nat := 118140960795 + 3646856 * 2 ^ 59
def prefixEnd_3646856 : Nat := 4983230072969 + 3 ^ 40 * 3646856 * 2
def baseEnd_3646856 : Nat := 1248393337155392595218947

theorem tailTrace_3646856 : CollatzResearch.WordTrace tailWord_3646856 prefixEnd_3646856 1248393337155392595218947 := by
  unfold tailWord_3646856
  simp only [CollatzResearch.WordTrace]
  refine ⟨66505882838035510131804211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88674510450714013509072281 66505882838035510131804211)
  ·
    refine ⟨99758824257053265197706317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66505882838035510131804211 99758824257053265197706317)
    ·
      refine ⟨37409559096394974449139869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99758824257053265197706317 37409559096394974449139869)
      ·
        refine ⟨14028584661148115418427451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37409559096394974449139869 14028584661148115418427451)
        ·
          refine ⟨21042876991722173127641177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14028584661148115418427451 21042876991722173127641177)
          ·
            refine ⟨15782157743791629845730883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21042876991722173127641177 15782157743791629845730883)
            ·
              refine ⟨23673236615687444768596325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15782157743791629845730883 23673236615687444768596325)
              ·
                refine ⟨4438731865441395894111811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23673236615687444768596325 4438731865441395894111811)
                ·
                  refine ⟨6658097798162093841167717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438731865441395894111811 6658097798162093841167717)
                  ·
                    refine ⟨1248393337155392595218947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6658097798162093841167717 1248393337155392595218947)
                    ·
                      rfl

theorem cell22_3646856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_3646856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646856 prefixEnd_3646856 := by exact prefixLift 3646856
  have htrace : WordTrace (prefixWord ++ tailWord_3646856) baseStart_3646856 baseEnd_3646856 := by
    simpa [prefixWord, tailWord_3646856, baseEnd_3646856] using wordTrace_append hprefix tailTrace_3646856
  have hstable : (prefixWord ++ tailWord_3646856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646856).length < 2 ^ (prefixWord ++ tailWord_3646856).sum := by decide
  have hdescent : baseEnd_3646856 < baseStart_3646856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646869 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_3646869 : Nat := 118140960795 + 3646869 * 2 ^ 59
def prefixEnd_3646869 : Nat := 4983230072969 + 3 ^ 40 * 3646869 * 2
def baseEnd_3646869 : Nat := 1248397787321064894643907

theorem tailTrace_3646869 : CollatzResearch.WordTrace tailWord_3646869 prefixEnd_3646869 1248397787321064894643907 := by
  unfold tailWord_3646869
  simp only [CollatzResearch.WordTrace]
  refine ⟨133012239825023923483831661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88674826550015948989221107 133012239825023923483831661)
  ·
    refine ⟨49879589934383971306436873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133012239825023923483831661 49879589934383971306436873)
    ·
      refine ⟨37409692450787978479827655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49879589934383971306436873 37409692450787978479827655)
      ·
        refine ⟨56114538676181967719741483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37409692450787978479827655 56114538676181967719741483)
        ·
          refine ⟨84171808014272951579612225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56114538676181967719741483 84171808014272951579612225)
          ·
            refine ⟨63128856010704713684709169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84171808014272951579612225 63128856010704713684709169)
            ·
              refine ⟨47346642008028535263531877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63128856010704713684709169 47346642008028535263531877)
              ·
                refine ⟨8877495376505350361912227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47346642008028535263531877 8877495376505350361912227)
                ·
                  refine ⟨13316243064758025542868341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877495376505350361912227 13316243064758025542868341)
                  ·
                    refine ⟨1248397787321064894643907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13316243064758025542868341 1248397787321064894643907)
                    ·
                      rfl

theorem cell22_3646869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_3646869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646869 prefixEnd_3646869 := by exact prefixLift 3646869
  have htrace : WordTrace (prefixWord ++ tailWord_3646869) baseStart_3646869 baseEnd_3646869 := by
    simpa [prefixWord, tailWord_3646869, baseEnd_3646869] using wordTrace_append hprefix tailTrace_3646869
  have hstable : (prefixWord ++ tailWord_3646869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646869).length < 2 ^ (prefixWord ++ tailWord_3646869).sum := by decide
  have hdescent : baseEnd_3646869 < baseStart_3646869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646916 : List Nat := [2, 3, 3, 2, 1, 1, 2, 8]
def baseStart_3646916 : Nat := 118140960795 + 3646916 * 2 ^ 59
def prefixEnd_3646916 : Nat := 4983230072969 + 3 ^ 40 * 3646916 * 2
def baseEnd_3646916 : Nat := 138712652931285826524307

theorem tailTrace_3646916 : CollatzResearch.WordTrace tailWord_3646916 prefixEnd_3646916 138712652931285826524307 := by
  unfold tailWord_3646916
  simp only [CollatzResearch.WordTrace]
  refine ⟨66506977027926825255396301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88675969370569100340528401 66506977027926825255396301)
  ·
    refine ⟨24940116385472559470773613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66506977027926825255396301 24940116385472559470773613)
    ·
      refine ⟨9352543644552209801540105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24940116385472559470773613 9352543644552209801540105)
      ·
        refine ⟨7014407733414157351155079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9352543644552209801540105 7014407733414157351155079)
        ·
          refine ⟨10521611600121236026732619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014407733414157351155079 10521611600121236026732619)
          ·
            refine ⟨15782417400181854040098929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10521611600121236026732619 15782417400181854040098929)
            ·
              refine ⟨11836813050136390530074197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15782417400181854040098929 11836813050136390530074197)
              ·
                refine ⟨138712652931285826524307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11836813050136390530074197 138712652931285826524307)
                ·
                  rfl

theorem cell22_3646916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 8].length) (baseStart_3646916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646916 prefixEnd_3646916 := by exact prefixLift 3646916
  have htrace : WordTrace (prefixWord ++ tailWord_3646916) baseStart_3646916 baseEnd_3646916 := by
    simpa [prefixWord, tailWord_3646916, baseEnd_3646916] using wordTrace_append hprefix tailTrace_3646916
  have hstable : (prefixWord ++ tailWord_3646916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646916).length < 2 ^ (prefixWord ++ tailWord_3646916).sum := by decide
  have hdescent : baseEnd_3646916 < baseStart_3646916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646959 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 1, 7]
def baseStart_3646959 : Nat := 118140960795 + 3646959 * 2 ^ 59
def prefixEnd_3646959 : Nat := 4983230072969 + 3 ^ 40 * 3646959 * 2
def baseEnd_3646959 : Nat := 1248428596160334659893631

theorem tailTrace_3646959 : CollatzResearch.WordTrace tailWord_3646959 prefixEnd_3646959 1248428596160334659893631 := by
  unfold tailWord_3646959
  simp only [CollatzResearch.WordTrace]
  refine ⟨133015522394697868854607931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88677014929798579236405287 133015522394697868854607931)
  ·
    refine ⟨199523283592046803281911897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133015522394697868854607931 199523283592046803281911897)
    ·
      refine ⟨149642462694035102461433923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199523283592046803281911897 149642462694035102461433923)
      ·
        refine ⟨224463694041052653692150885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149642462694035102461433923 224463694041052653692150885)
        ·
          refine ⟨42086942632697372567278291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224463694041052653692150885 42086942632697372567278291)
          ·
            refine ⟨63130413949046058850917437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42086942632697372567278291 63130413949046058850917437)
            ·
              refine ⟨23673905230892272069094039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63130413949046058850917437 23673905230892272069094039)
              ·
                refine ⟨35510857846338408103641059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23673905230892272069094039 35510857846338408103641059)
                ·
                  refine ⟨53266286769507612155461589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35510857846338408103641059 53266286769507612155461589)
                  ·
                    refine ⟨1248428596160334659893631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53266286769507612155461589 1248428596160334659893631)
                    ·
                      rfl

theorem cell22_3646959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_3646959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646959 prefixEnd_3646959 := by exact prefixLift 3646959
  have htrace : WordTrace (prefixWord ++ tailWord_3646959) baseStart_3646959 baseEnd_3646959 := by
    simpa [prefixWord, tailWord_3646959, baseEnd_3646959] using wordTrace_append hprefix tailTrace_3646959
  have hstable : (prefixWord ++ tailWord_3646959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646959).length < 2 ^ (prefixWord ++ tailWord_3646959).sum := by decide
  have hdescent : baseEnd_3646959 < baseStart_3646959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646961 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 5]
def baseStart_3646961 : Nat := 118140960795 + 3646961 * 2 ^ 59
def prefixEnd_3646961 : Nat := 4983230072969 + 3 ^ 40 * 3646961 * 2
def baseEnd_3646961 : Nat := 416143093600402440447875

theorem tailTrace_3646961 : CollatzResearch.WordTrace tailWord_3646961 prefixEnd_3646961 416143093600402440447875 := by
  unfold tailWord_3646961
  simp only [CollatzResearch.WordTrace]
  refine ⟨133015595340690623196180737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88677063560460415464120491 133015595340690623196180737)
  ·
    refine ⟨99761696505517967397135553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133015595340690623196180737 99761696505517967397135553)
    ·
      refine ⟨74821272379138475547851665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99761696505517967397135553 74821272379138475547851665)
      ·
        refine ⟨56115954284353856660888749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74821272379138475547851665 56115954284353856660888749)
        ·
          refine ⟨21043482856632696247833281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56115954284353856660888749 21043482856632696247833281)
          ·
            refine ⟨15782612142474522185874961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21043482856632696247833281 15782612142474522185874961)
            ·
              refine ⟨11836959106855891639406221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15782612142474522185874961 11836959106855891639406221)
              ·
                refine ⟨4438859665070959364777333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11836959106855891639406221 4438859665070959364777333)
                ·
                  refine ⟨416143093600402440447875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4438859665070959364777333 416143093600402440447875)
                  ·
                    rfl

theorem cell22_3646961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_3646961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646961 prefixEnd_3646961 := by exact prefixLift 3646961
  have htrace : WordTrace (prefixWord ++ tailWord_3646961) baseStart_3646961 baseEnd_3646961 := by
    simpa [prefixWord, tailWord_3646961, baseEnd_3646961] using wordTrace_append hprefix tailTrace_3646961
  have hstable : (prefixWord ++ tailWord_3646961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646961).length < 2 ^ (prefixWord ++ tailWord_3646961).sum := by decide
  have hdescent : baseEnd_3646961 < baseStart_3646961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646965 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3646965 : Nat := 118140960795 + 3646965 * 2 ^ 59
def prefixEnd_3646965 : Nat := 4983230072969 + 3 ^ 40 * 3646965 * 2
def baseEnd_3646965 : Nat := 1248430650082952644243613

theorem tailTrace_3646965 : CollatzResearch.WordTrace tailWord_3646965 prefixEnd_3646965 1248430650082952644243613 := by
  unfold tailWord_3646965
  simp only [CollatzResearch.WordTrace]
  refine ⟨133015741232676131879326349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88677160821784087919550899 133015741232676131879326349)
  ·
    refine ⟨49880902962253549454747381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133015741232676131879326349 49880902962253549454747381)
    ·
      refine ⟨4676334652711270261382567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49880902962253549454747381 4676334652711270261382567)
      ·
        refine ⟨7014501979066905392073851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4676334652711270261382567 7014501979066905392073851)
        ·
          refine ⟨10521752968600358088110777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014501979066905392073851 10521752968600358088110777)
          ·
            refine ⟨7891314726450268566083083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10521752968600358088110777 7891314726450268566083083)
            ·
              refine ⟨11836972089675402849124625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891314726450268566083083 11836972089675402849124625)
              ·
                refine ⟨8877729067256552136843469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11836972089675402849124625 8877729067256552136843469)
                ·
                  refine ⟨3329148400221207051316301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8877729067256552136843469 3329148400221207051316301)
                  ·
                    refine ⟨1248430650082952644243613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3329148400221207051316301 1248430650082952644243613)
                    ·
                      rfl

theorem cell22_3646965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3646965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3646965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3646965 prefixEnd_3646965 := by exact prefixLift 3646965
  have htrace : WordTrace (prefixWord ++ tailWord_3646965) baseStart_3646965 baseEnd_3646965 := by
    simpa [prefixWord, tailWord_3646965, baseEnd_3646965] using wordTrace_append hprefix tailTrace_3646965
  have hstable : (prefixWord ++ tailWord_3646965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646965).length < 2 ^ (prefixWord ++ tailWord_3646965).sum := by decide
  have hdescent : baseEnd_3646965 < baseStart_3646965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
